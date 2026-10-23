"""Finite-order MSA audit using roots and independent real-space Baxter quadrature.

Run from any directory. Writes only /tmp/fmsa_finite_order_audit.json.
Spatial fits are diagnostics, not universal proofs. No Fourier inverse is used.
"""
import json
import sys
import warnings
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.optimize import root

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from msa_exact_mix import HCYMix, solve_bh_mix, qhat


def evaluator(sol):
    st, p = sol.st, sol.p
    def q(a, b, x, derivative=False):
        low, contact = (st.sigma[b] - st.sigma[a]) / 2, st.SIG[a, b]
        if x < low:
            return 0.0
        exp_w = np.sum(p['Wt'][:, a, b] * np.exp(-st.z * (x - low)))
        dexp_w = -np.sum(st.z * p['Wt'][:, a, b] * np.exp(-st.z * (x - low)))
        if x <= contact:
            if derivative:
                return p['qp'][a, b] + p['A'][b] * (x - contact) + dexp_w
            return p['qp'][a, b] * (x - contact) + p['A'][b] * (x - contact)**2 / 2 + exp_w + np.sum(p['Ct'][:, a, b])
        exp_c = np.sum(p['Ct'][:, a, b] * np.exp(-st.z * (x - contact)))
        dexp_c = -np.sum(st.z * p['Ct'][:, a, b] * np.exp(-st.z * (x - contact)))
        return dexp_w + dexp_c if derivative else exp_w + exp_c

    def numerator(i, j, r):
        result = -q(i, j, r, True)
        for ell in range(st.N):
            edges = sorted(set([(st.sigma[ell] - st.sigma[j]) / 2, st.SIG[j, ell],
                                (st.sigma[ell] - st.sigma[i]) / 2 - r, st.SIG[i, ell] - r]))
            # Integrate each physical region separately. A conservative exponential cutoff
            # makes the omitted tail negligible relative to finite-difference noise.
            cutoff = max(edges) + 35 / np.min(st.z)
            integral = quad(lambda t: q(i, ell, t + r, True) * q(j, ell, t),
                            min(edges), cutoff, points=edges, epsabs=2e-12,
                            epsrel=2e-12, limit=200)[0]
            result += st.rho[ell] * integral
        return result
    return numerator


def taylor(values, order, h):
    if order == 2:
        return (values[h] + values[-h] - 2 * values[0.0]) / (2 * h**2)
    return (values[2*h] - 2*values[h] + 2*values[-h] - values[-2*h]) / (12 * h**3)


def design(r, z, inner):
    if inner:
        return np.column_stack([r] + [np.sinh(zt*r) for zt in z])
    return np.column_stack([r**k for k in range(5)] +
                           [fun(sign*zt*r) for zt in z for sign in [-1, 1] for fun in [np.exp]])


def audit(name, sigma, rho, z, coupling, poles=False):
    sigma, rho, z, coupling = map(np.asarray, (sigma, rho, z, coupling))
    pieces = []
    for i in range(len(sigma)):
        for j in range(i+1):
            knot, contact = abs(sigma[i]-sigma[j])/2, (sigma[i]+sigma[j])/2
            intervals = [(0, knot), (knot, contact)] if knot > 0 else [(0, contact)]
            for low, high in intervals:
                train = low+(high-low)*np.linspace(.035, .965, 23)
                held = low+(high-low)*np.array([.069, .187, .351, .523, .677, .811, .941])
                pieces.append((i, j, low, high, train, held))
    all_points = [(i,j,r) for i,j,low,high,train,held in pieces for r in np.r_[train,held]]
    steps = [.08, .04, .02, .01]
    taus = sorted(set([0.] + [sgn*h for h in steps+[.16] for sgn in [-1,1]]))
    values, solutions = {}, {}
    for tau in taus:
        sol = solve_bh_mix(HCYMix(sigma, rho, z, tau*coupling), tol=5e-13)
        if sol is None:
            raise RuntimeError(f'{name}: root failed at {tau}')
        solutions[tau] = sol
        ev = evaluator(sol)
        values[tau] = np.array([ev(i,j,r) for i,j,r in all_points])
    report = dict(name=name, sigma=sigma.tolist(), rho=rho.tolist(), z=z.tolist(), K=coupling.tolist(),
                  root_residual_max=max(sol.residual for sol in solutions.values()),
                  contact_symmetry_defect_max=max(sol.symmetry_defect for sol in solutions.values()),
                  root_distance_from_HS={str(tau):float(np.linalg.norm(sol.Gt-solutions[0.].Gt))
                                         for tau,sol in solutions.items()}, orders={})
    fitted = {}
    for order in [2,3]:
        coeff = {h:taylor(values,order,h) for h in [.08,.04,.02]}
        rich = {h:(4*coeff[h/2]-coeff[h])/3 for h in [.08,.04]}
        reference = rich[.04]
        scale = np.max(np.abs(reference))
        checks, offset = [], 0
        for i,j,low,high,train,held in pieces:
            count=len(train)+len(held)
            y=reference[offset:offset+count]
            inner=low==0 and i!=j
            a,b=design(train,z,inner),design(held,z,inner)
            cs=np.max(np.abs(a),axis=0)
            c=np.linalg.lstsq(a/cs,y[:len(train)],rcond=None)[0]/cs
            checks.append(dict(pair=[i,j],interval=[low,high],basis_size=len(c),
                               max_abs_numerator=float(np.max(np.abs(y))),
                               relative_fit_error=float(np.max(np.abs(a@c-y[:len(train)]))/np.max(np.abs(y))),
                               relative_held_error=float(np.max(np.abs(b@c-y[len(train):]))/np.max(np.abs(y))),
                               scaled_design_condition=float(np.linalg.cond(a/cs))))
            if order==2:
                fitted[(i,j,low,high)]=(c,inner)
            offset+=count
        report['orders'][str(order)]=dict(relative_richardson_change=float(np.max(np.abs(rich[.08]-reference))/scale),
                                         max_abs_numerator=float(scale),pieces=checks)

    # Check the exterior separately; all coefficients of order >=2 must vanish.
    exterior={}
    for tau,sol in solutions.items():
        ev=evaluator(sol)
        exterior[tau]=np.array([ev(i,j,(sigma[i]+sigma[j])/2+d)
                               for i in range(len(sigma)) for j in range(i+1) for d in [.07,.4,1.3]])
    report['exterior_max_abs']={str(order):float(np.max(np.abs((4*taylor(exterior,order,.04)-taylor(exterior,order,.08))/3)))
                                for order in [2,3]}
    if poles:
        rr=np.sqrt(rho[:,None]*rho[None,:]); eye=np.eye(len(sigma))
        def factor(sol,s):
            return eye-rr*qhat(sol.st,sol.p,s)
        def c_transform(sol,s):
            # Transpose at reflected s, NOT Hermitian conjugate at complex s.
            return (eye-factor(sol,s)@factor(sol,-s).T)/rr
        def c2(s):
            vals={tau:c_transform(sol,s) for tau,sol in solutions.items()}
            return (4*taylor(vals,2,.02)-taylor(vals,2,.04))/3
        def c1(s):
            return (c_transform(solutions[.01],s)-c_transform(solutions[-.01],s))/.02
        def det_eq(v):
            d=np.linalg.det(factor(solutions[0.],v[0]+1j*v[1]))
            return [d.real,d.imag]
        roots=[]
        for guess in [(-2,6),(-3,9),(-4,12),(-3,15),(-4,18)]:
            result=root(det_eq,guess,tol=1e-11)
            s=result.x[0]+1j*result.x[1]
            if np.linalg.norm(det_eq(result.x))<1e-10 and abs(s.imag)>1 and not any(abs(s-prev)<1e-6 for prev in roots):
                roots.append(s)
        pole_checks=[]
        for s in roots[:3]:
            direct=c2(s)
            radial=np.empty_like(direct)
            for i in range(len(sigma)):
                for j in range(i+1):
                    total=0j
                    for (a,b,low,high),(c,inner) in fitted.items():
                        if (a,b)!=(i,j):
                            continue
                        def integrand(r):
                            num=float(design(np.array([r]),z,inner)[0]@c)
                            return 2*num*np.sinh(s*r)/s
                        total+=quad(lambda r:integrand(r).real,low,high,epsabs=1e-11)[0]
                        total+=1j*quad(lambda r:integrand(r).imag,low,high,epsabs=1e-11)[0]
                    radial[i,j]=radial[j,i]=total
            circles=[]
            for radius in [.02,.005]:
                theta=2*np.pi*np.arange(64)/64
                residues=sum(c2(s+radius*np.exp(1j*t))*radius*np.exp(1j*t) for t in theta)/64
                circles.append(dict(radius=radius,max_abs_residue=float(np.max(np.abs(residues)))))
            sources=[]
            for eps in [1e-3,1e-4,1e-5,1e-6]:
                sv=s+eps
                S0=factor(solutions[0.],sv)@factor(solutions[0.],-sv).T
                C1=rr*c1(sv)
                singular=C1@np.linalg.inv(S0)@C1
                sources.append(dict(distance=eps,quadratic_source_norm=float(np.linalg.norm(singular)),
                                    complete_C2_norm=float(np.linalg.norm(rr*c2(sv)))))
            pole_checks.append(dict(s=[float(s.real),float(s.imag)],det_residual=float(abs(np.linalg.det(factor(solutions[0.],s)))),
                                    complete_c2_norm=float(np.linalg.norm(direct)),
                                    radial_fourier_relative_error=float(np.linalg.norm(radial-direct)/np.linalg.norm(direct)),
                                    contour_residues=circles,quadratic_sources=sources))
        if not pole_checks:
            raise RuntimeError('No HS zeros found')
        report['HS_zero_checks']=pole_checks
    print(name, 'roots',report['root_residual_max'], 'held',
          {order:max(p['relative_held_error'] for p in row['pieces']) for order,row in report['orders'].items()}, flush=True)
    return report


with warnings.catch_warnings():
    warnings.simplefilter('ignore')
    reports=[audit('binary_single_rate',[1.,2.],[.1,.04],[1.8],[[.5,.3],[.3,.4]],True),
             audit('ternary_two_rates',[.8,1.3,2.1],[.08,.035,.018],[1.2,2.6],
                   [[[.4,.23,.16],[.23,.31,.19],[.16,.19,.26]],
                    [[-.18,-.11,-.07],[-.11,-.14,-.09],[-.07,-.09,-.12]]])]
Path('/tmp/fmsa_finite_order_audit.json').write_text(json.dumps(reports,indent=2))
