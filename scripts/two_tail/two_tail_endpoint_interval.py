"""EXTERNAL interval certificates at the M1 and M3 endpoint controls (follow-up to handoffs 136-139).
NOT a Lean proof.  Unlike M2, these controls have no previously certified root box, so a box is
produced here and certified by a Krawczyk test.

For each control and each exact coupling tau in {tau_hat, tau_lo, tau_hi}:
  tau_hat = the bisected beta (float, taken as its exact dyadic value);
  tau_lo, tau_hi = the ends of the bisection bracket of the det F(0) sign change.
Exact data: eta = 49/100, rho = 6 eta/pi, sigma = 1, rational z, f = the exact dyadic value of the
classifier's float, w = f*w0 (w0 exact rational), K = (1, w).  Interval arithmetic: mpmath iv,
outward rounding, 192 bits.  The Jacobian is forward-mode AD of the literal N = 1 two-tail Lean
residual (two_tail_m2_jacobian_interval.residual), evaluated over boxes.

Krawczyk: with x~ a high-precision Newton point, C an exact dyadic approximation of J(x~)^-1 and
X = x~ + [-r, r]^4,  K(X) = x~ - C f(x~) + (I - C J(X)) (X - x~).  K(X) strictly inside X proves
that X contains exactly one root, and ||I - C J(X)||_inf < 1 proves J invertible throughout X.
det F(0) = A/(2 pi) for N = 1 (msa_exact_mix.SolutionMix.A).  Its sign is enclosed over X.

Not certified: that the boxes at tau_lo and tau_hi lie on the same continuous branch as the
traced canonical prefix; that beta is the first loss; anything about Taylor radii.

Usage: two_tail_endpoint_interval.py OUT.json
"""
import sys, json
from fractions import Fraction
from pathlib import Path
import numpy as np
import mpmath
from mpmath import iv
sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_m2_jacobian_interval import D, residual

iv.prec = 192
LO = lambda x: mpmath.mp.make_mpf(x._mpi_[0])     # exact endpoints of an iv interval
HI = lambda x: mpmath.mp.make_mpf(x._mpi_[1])


def FX(m):
    """Exact rational value of a finite mpf, from its (sign, man, exp, bc) tuple (handoff 141)."""
    sign, man, exp, bc = m._mpf_
    assert mpmath.isfinite(m), m
    if man == 0:
        return Fraction(0)
    v = Fraction(int(man))*(Fraction(2)**int(exp))
    return -v if sign else v


def IX(x):
    """Exact rational endpoints of an iv interval, as strings (authoritative)."""
    return [str(FX(LO(x))), str(FX(HI(x)))]


def FQ(sx):
    return [Fraction(sx[0]), Fraction(sx[1])]


def strictly_inside(inner, outer):
    """Exact check on serialized boxes: every inner interval lies in the interior of the outer one."""
    return all(FQ(o)[0] < FQ(i)[0] and FQ(i)[1] < FQ(o)[1] for i, o in zip(inner, outer))


def sha(path):
    import hashlib
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
mpmath.mp.prec = 192
DIAG = Path(__file__).resolve().parents[2]/'results'/'two_tail'/'two_tail_fiber_diag.json'
CONTROLS = {'M1': dict(z=(Fraction(3, 5), Fraction(21, 25))), 'M3': dict(z=(Fraction(7), Fraction(14)))}
RADII = [Fraction(1, 10**k) for k in (6, 8, 10, 12, 14, 16, 18)]


def q2iv(q):
    return iv.mpf(q.numerator)/iv.mpf(q.denominator)


def amplitudeA(u, rho, sig, z):
    """A (= 2 pi det F(0) for N = 1), same formulas as the residual's A."""
    PI = D.c(iv.pi); rho, sig = D.c(rho), D.c(sig); z = [D.c(x) for x in z]
    eta = PI/6*rho*sig**3; vac = 1 - eta; xi2 = rho*sig**2
    Qpp0 = 2*PI/vac*(1 + PI*xi2*sig/(2*vac)); cN = 2*PI**2*xi2/vac**2
    Dt, G = u[:2], u[2:]
    E = lambda x: D.c(iv.exp(x.v))
    gam = [1 - 2*PI*rho*G[a]*E(-z[a]*sig)/z[a] for a in range(2)]
    Ct = [gam[a]*Dt[a] for a in range(2)]; Wt = [2*PI/z[a]*rho*G[a]*Dt[a] for a in range(2)]
    Mj = sum((-(1/z[a])*rho*(Wt[a] + (1 + z[a]*sig)*Ct[a]) for a in range(2)), D.c(0))
    Nj = sum((rho*(Wt[a]/z[a]**2 + (1 + z[a]*sig + (z[a]*sig)**2/2)/z[a]**2*Ct[a]) for a in range(2)), D.c(0))
    return Qpp0 + Qpp0*Mj + cN*Nj


def duals(us):
    return [D(us[i], [iv.mpf(1) if j == i else iv.mpf(0) for j in range(4)]) for i in range(4)]


def newton(x, F):
    for _ in range(60):
        r = F(duals([iv.mpf(xi) for xi in x]))
        Fm = mpmath.matrix([r[i].v.mid for i in range(4)])
        Jm = mpmath.matrix([[r[i].g[j].mid for j in range(4)] for i in range(4)])
        dx = mpmath.lu_solve(Jm, -Fm)
        x = [x[i] + dx[i] for i in range(4)]
        if mpmath.norm(dx) < mpmath.mpf(2)**-180*(1 + mpmath.norm(mpmath.matrix(x))):
            break
    return x, Jm


def krawczyk(x, F, r):
    _, Jm = newton(x, F)
    Cf = np.linalg.inv(np.array([[float(Jm[i, j]) for j in range(4)] for i in range(4)], dtype=float))
    Cq = [[Fraction(float(Cf[i, j])) for j in range(4)] for i in range(4)]
    C = [[q2iv(Cq[i][j]) for j in range(4)] for i in range(4)]
    xt = [iv.mpf(xi) for xi in x]
    rad = [iv.mpf(r.numerator)/r.denominator*max(1, abs(float(xi))) for xi in x]
    rad = [iv.mpf(ri.b) for ri in rad]
    X = [iv.mpf([(xt[i] - rad[i]).a, (xt[i] + rad[i]).b]) for i in range(4)]
    fx = F(duals(xt)); JX = F(duals(X))
    E = [[(iv.mpf(1) if i == j else iv.mpf(0)) - sum((C[i][k]*JX[k].g[j] for k in range(4)), iv.mpf(0))
          for j in range(4)] for i in range(4)]
    norm = max(HI(sum((abs(E[i][j]) for j in range(4)), iv.mpf(0))) for i in range(4))   # exact upper endpoints
    Kx = [xt[i] - sum((C[i][k]*fx[k].v for k in range(4)), iv.mpf(0))
          + sum((E[i][j]*(X[j] - xt[j]) for j in range(4)), iv.mpf(0)) for i in range(4)]
    inside = all(X[i].a < Kx[i].a and Kx[i].b < X[i].b for i in range(4))
    return dict(X=X, K=Kx, inside=inside, norm=norm, C=Cq, xt=xt, JX=[[JX[i].g[j] for j in range(4)] for i in range(4)],
                E=E, fx=[fx[i].v for i in range(4)])


def witness(k):
    """Exact serialization of one Krawczyk test (all endpoints as rationals)."""
    w = dict(center=[str(FX(LO(c))) for c in k['xt']], C_rational=[[str(q) for q in row] for row in k['C']],
             X=[IX(Xi) for Xi in k['X']], K=[IX(Ki) for Ki in k['K']], f_center=[IX(v) for v in k['fx']],
             J_over_X=[[IX(v) for v in row] for row in k['JX']], I_minus_CJ=[[IX(v) for v in row] for row in k['E']],
             inf_norm_upper=str(FX(k['norm'])), inf_norm_upper_display=mpmath.nstr(k['norm'], 8))
    w['exact_check_K_strictly_inside_X'] = strictly_inside(w['K'], w['X'])
    w['exact_check_norm_lt_1'] = Fraction(w['inf_norm_upper']) < 1
    return w


def shrink(x, F, X, C, n=40):
    """Iterate X <- X ∩ K(X) with fixed C; the unique root stays inside every iterate."""
    Ci = [[q2iv(q) for q in row] for row in C]
    xt = [iv.mpf(xi) for xi in x]
    for _ in range(n):
        xt = [iv.mpf(Xi.mid) for Xi in X]
        fx = F(duals(xt)); JX = F(duals(X))
        E = [[(iv.mpf(1) if i == j else iv.mpf(0)) - sum((Ci[i][k]*JX[k].g[j] for k in range(4)), iv.mpf(0))
              for j in range(4)] for i in range(4)]
        Kx = [xt[i] - sum((Ci[i][k]*fx[k].v for k in range(4)), iv.mpf(0))
              + sum((E[i][j]*(X[j] - xt[j]) for j in range(4)), iv.mpf(0)) for i in range(4)]
        X = [iv.mpf([max(X[i].a, Kx[i].a), min(X[i].b, Kx[i].b)]) for i in range(4)]
    return X


def certify(x0, tau, rho, sig, z, wq):
    """Krawczyk at exact tau; returns (record, shrunk box, sign of A over it)."""
    F = lambda u: residual(u, rho, sig, z, [tau*1, tau*q2iv(wq)])
    x, _ = newton(x0, F)
    for r in RADII:
        k = krawczyk(x, F, r)
        if k['inside'] and k['norm'] < 1:
            Xs = shrink(x, F, k['X'], k['C'])
            Aiv = amplitudeA(duals(Xs), rho, sig, z).v
            sgn = '+' if Aiv.a > 0 else '-' if Aiv.b < 0 else '0?'
            return dict(x=x, r=r, k=k, Xs=Xs, A=Aiv, sign=sgn)
    return None


def main():
    out = sys.argv[1]
    cmd = ' '.join([sys.executable] + sys.orig_argv[1:]); print('# ' + cmd, flush=True)
    print('# EXTERNAL interval certificates (mpmath iv, 192 bits); not a Lean proof', flush=True)
    diag = json.load(open(DIAG))
    here = Path(__file__).resolve().parent
    res = dict(command=cmd, label='EXTERNAL interval certificate (mpmath iv, 192 bits); not a Lean proof',
               serialization='All endpoints are EXACT rationals from the mpf (sign, man, exp, bc) tuples; '
                             'decimal displays are non-authoritative.',
               diag_source=str(DIAG), diag_sha256=sha(DIAG),
               source_sha256={'two_tail_endpoint_interval.py': sha(here/'two_tail_endpoint_interval.py'),
                              'two_tail_m2_jacobian_interval.py': sha(here/'two_tail_m2_jacobian_interval.py')},
               mpmath_version=mpmath.__version__, controls=[])
    eta = iv.mpf(49)/100; rho = 6*eta/iv.pi; sig = iv.mpf(1)
    for key, cfg in CONTROLS.items():
        c = next(c for c in diag['controls'] if c['name'].startswith(key))
        z1q, z2q = cfg['z']
        assert abs(float(z1q) - c['z'][0]) < 1e-15 and abs(float(z2q) - c['z'][1]) < 1e-15 and c['eta'] == 0.49
        fq = Fraction(c['f'])                                     # exact dyadic of the classifier float
        w0q = -(1/z1q + 1/z1q**2)/(1/z2q + 1/z2q**2)
        wq = fq*w0q
        z = [q2iv(z1q), q2iv(z2q)]
        taus = dict(tau_hat=Fraction(c['beta']), tau_lo=Fraction(c['beta_bracket'][0]), tau_hi=Fraction(c['beta_bracket'][1]))
        crec = dict(name=c['name'], z=[str(z1q), str(z2q)], eta='49/100', f=str(fq), w=str(wq), w_float=float(wq),
                    taus={k: str(v) for k, v in taus.items()}, runs={})
        print(f"\n== {c['name']}\n  f = {fq} (= {float(fq)!r}), w = f*w0 = {float(wq)!r}", flush=True)
        x0 = [mpmath.mpf(v) for v in c['u_traced']]

        def run_at(tq):
            out = certify(x0, q2iv(tq), rho, sig, z, wq)
            run = dict(tau=str(tq), tau_float=float(tq), certified=out is not None)
            if out:
                k = out['k']; w = witness(k)
                shr = [IX(Xi) for Xi in out['Xs']]
                A = IX(out['A'])
                sgn = '+' if Fraction(A[0]) > 0 else '-' if Fraction(A[1]) < 0 else '0?'
                assert sgn == out['sign']
                run.update(radius_rel=str(out['r']), krawczyk=w, root_enclosure_after_shrink=shr,
                           exact_check_shrunk_inside_X=all(FQ(a)[0] >= FQ(b)[0] and FQ(a)[1] <= FQ(b)[1]
                                                           for a, b in zip(shr, w['X'])),
                           A_over_root=A, detF0_sign=sgn,
                           display_nonauthoritative=dict(norm=w['inf_norm_upper_display'],
                                                         A=[mpmath.nstr(LO(out['A']), 12), mpmath.nstr(HI(out['A']), 12)]))
            return run

        for tk, tq in taus.items():
            run = run_at(tq); crec['runs'][tk] = run
            if run['certified']:
                print(f"  {tk}: tau={float(tq)!r}  radius {run['radius_rel']}  K inside X (exact): "
                      f"{run['krawczyk']['exact_check_K_strictly_inside_X']}, ||I-CJ(X)|| <= "
                      f"{float(Fraction(run['krawczyk']['inf_norm_upper'])):.4g};  A over shrunk root box = "
                      f"[{float(Fraction(run['A_over_root'][0])):.6e}, {float(Fraction(run['A_over_root'][1])):.6e}] -> {run['detF0_sign']}", flush=True)
            else:
                print(f"  {tk}: tau={float(tq)!r}  NOT certified", flush=True)
        lo, hi = crec['runs']['tau_lo'].get('detF0_sign'), crec['runs']['tau_hi'].get('detF0_sign')
        crec['float_bracket_sign_change'] = bool(lo and hi and lo in '+-' and hi in '+-' and lo != hi)
        print(f"  float bisection bracket: sign {lo} / {hi} -> rigorous opposite signs: {crec['float_bracket_sign_change']}", flush=True)
        if not crec['float_bracket_sign_change']:            # widen symmetrically about tau_hat
            th = taus['tau_hat']; found = None
            for kexp in range(13, 3, -1):
                dq = th*Fraction(1, 10**kexp)
                a, b = run_at(th - dq), run_at(th + dq)
                sa, sb = a.get('detF0_sign'), b.get('detF0_sign')
                print(f"    widen rel 1e-{kexp}: tau_hat -/+ {float(dq):.3e}: signs {sa} / {sb}", flush=True)
                if sa and sb and sa in '+-' and sb in '+-' and sa != sb:
                    found = dict(rel=f'1e-{kexp}', lo=a, hi=b); break
            crec['rigorous_bracket'] = found
            if found:
                print(f"  rigorous bracket: [{found['lo']['tau_float']!r}, {found['hi']['tau_float']!r}] "
                      f"(rel half-width {found['rel']}), signs {found['lo']['detF0_sign']} / {found['hi']['detF0_sign']}", flush=True)
        # parametric Krawczyk over the whole rigorous bracket: J does not depend on tau, so one box X with
        # K(X; tau-interval) inside X gives a unique root in X for EVERY tau in the bracket; by uniqueness
        # and the IFT these roots form ONE continuous branch segment, along which det F(0) changes sign.
        br = crec.get('rigorous_bracket') or ({'lo': crec['runs']['tau_lo'], 'hi': crec['runs']['tau_hi']}
                                              if crec['float_bracket_sign_change'] else None)
        crec['parametric'] = None
        if br:
            tl, th_ = Fraction(br['lo']['tau']), Fraction(br['hi']['tau'])
            T = iv.mpf([LO(q2iv(tl)), HI(q2iv(th_))])
            Fp = lambda u: residual(u, rho, sig, z, [T*1, T*q2iv(wq)])
            xm, _ = newton(x0, lambda u: residual(u, rho, sig, z, [q2iv((tl + th_)/2)*1, q2iv((tl + th_)/2)*q2iv(wq)]))
            par = None
            for r in [Fraction(1, 10**k) for k in (4, 5, 6, 7, 8, 9, 10, 11, 12)]:
                k = krawczyk(xm, Fp, r)
                if k['inside'] and k['norm'] < 1:
                    w = witness(k)
                    ends = {e: br[e]['root_enclosure_after_shrink'] for e in ('lo', 'hi')}
                    par = dict(radius_rel=str(r), tau_interval_exact=[str(tl), str(th_)], tau_interval_iv=IX(T),
                               krawczyk=w,
                               exact_check_endpoint_roots_strictly_inside_common_X={e: strictly_inside(b, w['X'])
                                                                                    for e, b in ends.items()})
                    break
            crec['parametric'] = par
            if par:
                print(f"  parametric Krawczyk over tau in [{float(tl)!r}, {float(th_)!r}]: PASS at radius {par['radius_rel']}"
                      f", K inside X (exact): {par['krawczyk']['exact_check_K_strictly_inside_X']}, ||I-CJ(X)|| <= "
                      f"{float(Fraction(par['krawczyk']['inf_norm_upper'])):.4g}; endpoint roots strictly inside the common X "
                      f"(exact): {par['exact_check_endpoint_roots_strictly_inside_common_X']}", flush=True)
            else:
                print(f"  parametric Krawczyk over the bracket: NOT certified at radii 1e-4 .. 1e-12; the two end roots are"
                      f" certified separately, but their lying on ONE branch is NOT certified", flush=True)
        print("  (the bracket is not certified to be the FIRST loss, nor connected to the PY seed by a certified chain)", flush=True)
        res['controls'].append(crec)
        json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
