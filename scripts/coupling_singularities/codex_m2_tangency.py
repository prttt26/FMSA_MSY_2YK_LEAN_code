"""Local zero-mode tangency on a selected real two-tail BH branch.

Uses rigorous real Arb constants and nested AD, with floating Newton only
for box predictors/preconditioners. This is not a global canonicity or
convergence-domain certificate. Default control: eta=.1, z=(1.8,12).

Example (python-flint 0.6.0):
  PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/coupling_singularities/codex_m2_tangency.py
"""
from __future__ import annotations

import argparse
import hashlib
from importlib.metadata import version
import json
import math
from pathlib import Path
import sys
import time

import numpy as np
from flint import arb, arb_mat, ctx

PACKAGE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(PACKAGE / "formalization/certificates"))
from f5_competing_tails import D, Model  # noqa: E402


def value_jacobian(f, x):
    n = len(x)
    out = f([D(y, [1 if i == j else 0 for j in range(n)]) for i, y in enumerate(x)])
    return ([q.v if isinstance(q, D) else q for q in out],
            [q.g if isinstance(q, D) else [0]*n for q in out])


def enclosing_endpoints(a, b):
    return arb(float(a)).union(arb(float(b)))


def interval_record(x):
    return [math.nextafter(float(x.lower()), -math.inf),
            math.nextafter(float(x.upper()), math.inf)]


def matvec(A, x):
    return [sum((a*b for a, b in zip(row, x)), 0) for row in A]


class TwoTail:
    def __init__(self, eta, z1, z2):
        e, zs = arb(eta), [arb(z1), arb(z2)]
        assert 0 < e < 1 and 0 < zs[0] < zs[1]
        self.label = {"eta": eta, "z": [z1, z2], "sigma": "1"}
        pi, v = arb.pi(), 1-e
        rho = 6*e/pi
        A0, B0, qp0 = 2*pi*(1+2*e)/v**2, -3*pi*e/v**2, 2*pi*(1+e/2)/v**2
        ez = [(-z).exp() for z in zs]
        k = {"rho": rho, "A0": A0, "B0": B0, "qp0": qp0, "twopi": 2*pi}
        k["cg"] = [2*pi*rho*ez[i]/zs[i] for i in range(2)]
        k["mA"] = [rho*(1+z)/z for z in zs]
        k["mB"] = [2*pi*rho**2/z**2 for z in zs]
        k["nA"] = [rho*(1+z+z**2/2)/z**2 for z in zs]
        k["nB"] = [2*pi*rho**2/z**3 for z in zs]
        k["phi1"] = [(1-z-ez[i])/z**2 for i, z in enumerate(zs)]
        k["phi2"] = [(1-z+z*z/2-ez[i])/z**3 for i, z in enumerate(zs)]
        k["xA"] = [[2*pi*rho/(zs[j]*(zs[i]+zs[j])) for j in range(2)] for i in range(2)]
        k["xB"] = [[ez[i]/(zs[i]+zs[j])+(1-ez[i])/zs[i] for j in range(2)] for i in range(2)]
        k["sA"] = [1/z**2 for z in zs]
        k["sQ"] = [1/z for z in zs]
        k["sD"] = [[zs[j]/(zs[i]+zs[j]) for j in range(2)] for i in range(2)]
        k["kt"] = [2*pi/z for z in zs]  # second component multiplied by unknown w
        self.k = k
        self.kf = Model._map(k, lambda x: float(x.mid()))
        self.template = object.__new__(Model)
        self.template.n = 2
        self.hs = (1+2*e)/v**2
        self.alpha = [rho*(6*e+(4*e-1)*z+(e-1)*z*z)/(v*v*z*z) for z in zs]
        self.beta = [12*e*rho/(v*v*z**3)*(
            -(1+2*e)*z*(1-(1+z)*ez[i])+6*e*(1-(1+z+z*z/2)*ez[i])) for i, z in enumerate(zs)]
        self.af = [float(x.mid()) for x in self.alpha]
        self.bf = [float(x.mid()) for x in self.beta]
        F = [1-rho*(k["phi1"][i]*qp0+k["phi2"][i]*A0) for i in range(2)]
        assert all(x > 0 for x in F)
        self.seed = [arb(0), arb(0)] + [(A0+zs[i]*qp0)/(2*pi*zs[i]**2*F[i]) for i in range(2)]
        self.seedf = np.array([float(x.mid()) for x in self.seed])
        self.w0 = -(1/zs[0]+1/zs[0]**2)/(1/zs[1]+1/zs[1]**2)

    def P(self, u, floating=False):
        return self.template.residual(u, 0, self.kf if floating else self.k)

    def PJ(self, u, floating=False):
        return value_jacobian(lambda y: self.P(y, floating), u)

    def forcing(self, w, floating=False):
        k = self.kf if floating else self.k
        return [k["kt"][0], k["kt"][1]*w, 0, 0]

    def zero_mode(self, u, floating=False):
        a, b = (self.af, self.bf) if floating else (self.alpha, self.beta)
        hs = float(self.hs.mid()) if floating else self.hs
        return hs + sum((u[i]*(a[i]+b[i]*u[i+2]) for i in range(2)), 0)

    def grad_zero(self, u, floating=False):
        a, b = (self.af, self.bf) if floating else (self.alpha, self.beta)
        return [a[i]+b[i]*u[i+2] for i in range(2)] + [b[i]*u[i] for i in range(2)]

    def residual(self, u, tau, w, floating=False):
        return [a-tau*b for a,b in zip(self.P(u, floating), self.forcing(w, floating))]

    def augmented(self, x, floating=False):
        u, tau, w, vel = x[:4], x[4], x[5], x[6:]
        p, J = self.PJ(u, floating)
        b = self.forcing(w, floating)
        return ([a-tau*bi for a,bi in zip(p,b)] +
                [a-bi for a,bi in zip(matvec(J,vel),b)] +
                [self.zero_mode(u,floating), sum((a*b for a,b in zip(self.grad_zero(u,floating),vel)),0)])


def newton(f, x, maxit=60):
    x = np.array(x, dtype=float)
    for _ in range(maxit):
        y, J = value_jacobian(f, list(x))
        y, J = np.asarray(y,dtype=float), np.asarray(J,dtype=float)
        delta = np.linalg.solve(J,-y)
        if np.max(np.abs(delta)/(1+np.abs(x))) < 3e-13 and np.max(np.abs(y)) < 2e-8:
            return x+delta
        old = np.linalg.norm(y)
        for step in (1.0,.5,.25,.125,.0625,.03125):
            xn = x+step*delta
            if np.linalg.norm(np.asarray(f(list(xn)),dtype=float)) < old:
                x = xn
                break
        else:
            if np.max(np.abs(y)) < 1e-9:
                return x
            raise RuntimeError("Newton line search failed")
    raise RuntimeError("Newton iteration limit")


def predictor_at(model, target, w):
    u, t, h = model.seedf.copy(), 0.0, min(.05,target/100)
    while t < target:
        tn = min(target,t+h)
        _, J = model.PJ(list(u),True)
        vel = np.linalg.solve(np.asarray(J,float),model.forcing(w,True))
        try:
            un = newton(lambda y: model.residual(y,tn,w,True),u+(tn-t)*vel)
        except (RuntimeError,np.linalg.LinAlgError):
            h /= 2
            if h < 1e-9:
                raise RuntimeError(f"Float branch predictor stalled at {t}")
            continue
        u,t = un,tn
        h = min(h*1.5,max(.05,target/50))
    return u


def krawczyk(f, center, radii, X=None, C=None, preconditioned_value=None):
    n = len(center)
    X = [arb(float(y),float(r)) for y,r in zip(center,radii)] if X is None else X
    point = [arb(float(y)) for y in center]
    Fy,Jy = value_jacobian(f,point)
    _,JX = value_jacobian(f,X)
    if C is None:
        C = np.linalg.inv(np.array([[float(a.mid()) for a in row] for row in Jy]))
    E = [[arb(1 if i==j else 0)-sum((arb(float(C[i,k]))*JX[k][j] for k in range(n)),arb(0))
          for j in range(n)] for i in range(n)]
    CF = (preconditioned_value(C,point) if preconditioned_value is not None else
          [sum((arb(float(C[i,k]))*Fy[k] for k in range(n)),arb(0)) for i in range(n)])
    K = [point[i]-CF[i] +
         sum((E[i][j]*(X[j]-point[j]) for j in range(n)),arb(0)) for i in range(n)]
    weights = [x.rad() for x in X]
    bounds = [sum((abs(E[i][j])*weights[j]/weights[i] for j in range(n)),arb(0)) for i in range(n)]
    inside = all(x.contains_interior(k) for x,k in zip(X,K))
    contraction = all(q < 1 for q in bounds)
    return inside and contraction,X,K,C,max(math.nextafter(float(q.upper()),math.inf) for q in bounds)


def branch_krawczyk(model, T, W, center, radii):
    def preconditioned(C, point):
        # Preserve the common tau factor through preconditioning. Evaluating
        # each residual first would replace cancellations in C*b by |C|*|b|,
        # so shrinking the slab cannot cure the resulting relative wrapping.
        P,b=model.P(point),model.forcing(W)
        return [sum((arb(float(C[i,j]))*P[j] for j in range(4)),arb(0))-
                T*sum((arb(float(C[i,j]))*b[j] for j in range(4)),arb(0)) for i in range(4)]
    return krawczyk(lambda y:model.residual(y,T,W),center,radii,
                    preconditioned_value=preconditioned)


def local_geometry(model,X):
    u,tau,w,vel = X[:4],X[4],X[5],X[6:]
    _,J = model.PJ(u)
    Jm = arb_mat(J)
    Jm.inv()  # rigorous nonsingularity over the whole u box
    nested = [D(D(ui,[vi]),[D(vi,[arb(0)])]) for ui,vi in zip(u,vel)]
    out = model.P(nested)
    Hvv = [q.g[0].g[0] if isinstance(q.g[0],D) else arb(0) for q in out]
    accel = Jm.solve(arb_mat([[-q] for q in Hvv]))
    grad = model.grad_zero(u)
    curvature = 2*sum((model.beta[i]*vel[i]*vel[i+2] for i in range(2)),arb(0)) + \
        sum((grad[i]*accel[i,0] for i in range(4)),arb(0))
    bw = arb_mat([[arb(0)],[model.k["kt"][1]],[arb(0)],[arb(0)]])
    dw = Jm.solve(bw)
    m_w = tau*sum((grad[i]*dw[i,0] for i in range(4)),arb(0))
    m_f = model.w0*m_w
    assert curvature > 0, ("nonpositive/unresolved curvature",curvature)
    assert not m_f.contains(arb(0)), ("unresolved parameter transversality",m_f)
    return {"BH_jacobian_nonsingular":True,"F0_second_tau_derivative":interval_record(curvature),
            "minimum_value_w_derivative":interval_record(m_w),"minimum_value_f_derivative":interval_record(m_f)}


def branch_link(model, Xroot, max_pieces=10000):
    W = Xroot[5]
    target = math.nextafter(float(Xroot[4].upper()),math.inf)+1e-5*(1+abs(float(Xroot[4].mid())))
    t,h,u = 0.0,min(.02,target/100),model.seedf.copy()
    Yprev,chain,worst = model.seed,[],0.0
    wm = float(W.mid())
    while t < target:
        tn = min(target,t+h);tm = (t+tn)/2
        T = enclosing_endpoints(t,tn)
        um = newton(lambda y:model.residual(y,tm,wm,True),u)
        ub = newton(lambda y:model.residual(y,tn,wm,True),um)
        _,Jf = model.PJ(list(um),True)
        vel = np.linalg.solve(np.asarray(Jf,float),model.forcing(wm,True))
        radii = 3*abs(vel)*(tn-t)/2+2*abs(ub-um)+1e-10*(1+abs(um))
        # A component can have zero velocity while the branch remains
        # regular. Keep a scaled isotropic floor so that a coordinate
        # turning point does not make the weighted norm singular.
        radii = np.maximum(radii,.2*(1+abs(um))*(tn-t))
        radii = np.maximum(radii,np.array([max(abs(float(y.lower())-m),abs(float(y.upper())-m))
                                          for y,m in zip(Yprev,um)])*1.5)
        ok,X,K,C,q = branch_krawczyk(model,T,W,um,radii)
        if not ok or not all(x.contains(y) for x,y in zip(X,Yprev)):
            h /= 2
            if h < 1e-10:
                raise RuntimeError(f"Interval branch link stalled at tau={t}")
            continue
        # Re-certify a tight endpoint box. Carrying the wide slab's endpoint
        # image alone is valid but accumulates interval wrapping and can
        # force the next step to zero. The new root equals the slab root
        # because its certified box is contained in the unique-root slab.
        _,Jb = model.PJ(list(ub),True)
        bw = np.array([0.,model.kf['kt'][1],0.,0.])
        uw = np.linalg.solve(np.asarray(Jb,float),tn*bw)
        end_rad = 4*abs(uw)*float(W.rad())+1e-10*(1+abs(ub))
        endpoint_ok = False
        for _ in range(12):
            oke,Y,Ke,_,qe = branch_krawczyk(model,arb(tn),W,ub,end_rad)
            if oke and all(x.contains(y) for x,y in zip(X,Y)):
                endpoint_ok=True
                break
            need = np.array([max(abs(float(a.lower())-m),abs(float(a.upper())-m)) for a,m in zip(Ke,ub)])
            end_rad=np.maximum(end_rad,1.5*need)
        if not endpoint_ok:
            h/=2
            if h<1e-10:
                raise RuntimeError(f'Endpoint box linkage stalled at tau={t}')
            continue
        Yprev=Y
        chain.append({"tau":[t,tn],"u_box":[interval_record(x) for x in X],"weighted_contraction":q,
                      "endpoint_box":[interval_record(y) for y in Y],"endpoint_contraction":qe})
        worst = max(worst,q)
        u,t = ub,tn
        if len(chain)>max_pieces:
            raise RuntimeError("Branch-link piece limit")
        if len(chain)%100==0:
            print(f"  branch link: {len(chain)} pieces, tau={t:.8g}/{target:.8g}",flush=True)
        h = min(h*1.25,max(.02,target/50))
    assert T.contains(Xroot[4]),("target tau not in final slab",T,Xroot[4])
    assert all(x.contains(y) for x,y in zip(X,Xroot[:4])),"Tangency box not inside final branch box"
    return {"linked":True,"w_parameter_box":interval_record(W),"tau_end":target,
            "pieces":len(chain),"worst_contraction":worst,"chain":chain,
            "argument":"PY seed in first box; fresh certified endpoint boxes contained in adjacent slabs glue the roots; tangency u/tau/w boxes lie in the final slab."}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--eta',default='0.1');ap.add_argument('--z1',default='1.8');ap.add_argument('--z2',default='12')
    ap.add_argument('--f-guess',type=float,default=.5047);ap.add_argument('--tau-guess',type=float,default=5.6)
    ap.add_argument('--precision',type=int,default=192)
    ap.add_argument('--predict-only',action='store_true')
    ap.add_argument('--out',default=str(PACKAGE/'results/coupling_singularities/codex_m2_tangency.json'))
    args = ap.parse_args();ctx.prec=args.precision;started=time.monotonic()
    model = TwoTail(args.eta,args.z1,args.z2)
    wg = float(model.w0.mid())*args.f_guess
    ug = predictor_at(model,args.tau_guess,wg)
    _,Jg = model.PJ(list(ug),True)
    vg = np.linalg.solve(np.asarray(Jg,float),model.forcing(wg,True))
    guess = np.r_[ug,args.tau_guess,wg,vg]
    x = newton(lambda y:model.augmented(y,True),guess)
    print('Float candidate:',x.tolist(),flush=True)
    print('f candidate:',x[5]/float(model.w0.mid()),flush=True)
    if args.predict_only:
        return
    fun = lambda y:model.augmented(y)
    ok = False
    for scale in (1e-8,1e-7,1e-6,1e-9):
        radii = scale*(1+abs(x))
        ok,X,K,C,q = krawczyk(fun,x,radii)
        if ok:break
    assert ok,'No strict Krawczyk/contraction box for augmented system'
    geometry = local_geometry(model,X)
    print('Certified local geometry (PY link pending):',geometry,flush=True)
    def negative(y):
        v = fun(y);v[8] += arb('0.001');return v
    bad,*_ = krawczyk(negative,x,radii,X=X,C=C)
    assert not bad,'Negative control unexpectedly accepted displaced F0 constraint'
    linkage = branch_link(model,X)
    result = {"status":"PASS_LOCAL_ZERO_MODE_TANGENCY","model":model.label,
        "unknown_order":["D1","D2","G1","G2","tau","w","vD1","vD2","vG1","vG2"],
        "root_box":[interval_record(a) for a in X],"f_box":interval_record(X[5]/model.w0),
        "strict_augmented_Krawczyk":True,"weighted_contraction":q,
        "geometry":geometry,"PY_branch_link":linkage,"negative_control_displaced_F0_rejected":True,
        "precision_bits":ctx.prec,"constants":"Computed directly with Arb exact-decimal, exp and pi operations",
        "dependencies":{"python_flint":version('python-flint'),"numpy":np.__version__},
        "scope":"A local zero-mode tangency with positive curvature and nonzero parameter derivative, linked to a real PY-seeded BH branch. Not global absence/firstness of instability, not finite-k exclusion, not a Taylor-radius or all-density certificate.",
        "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "residual_source_sha256":hashlib.sha256((PACKAGE/'formalization/certificates/f5_competing_tails.py').read_bytes()).hexdigest(),
        "seconds":round(time.monotonic()-started,3)}
    p=Path(args.out);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: local zero-mode tangency, curvature, transversality and PY branch link',flush=True)
    print(p)


if __name__=='__main__':
    main()
