"""EXTERNAL interval certificate: the two M1 endpoint roots lie on ONE continuous real BH branch
(follow-up to handoffs 140-143).  NOT a Lean proof.

Near the fold, tau is a bad parameter (|du/dtau| ~ 1e6), so the branch is parametrised by the
amplitude coordinate p = u_k with the largest tangent component.  The unknowns are
y = (the other three amplitudes, tau), and the equations are the same 4 literal Lean residuals
with tau now a variable (K = tau*(1, w)).  The Jacobian dR/d(v, tau) stays well conditioned
through the fold.

Certificate:
  slabs   P_j = [p_j, p_{j+1}] cover hull(p at the lo endpoint root, p at the hi endpoint root).
          For each slab, a parametric Krawczyk box Y_j, with the p dependence in mean-value form
          K = y~ - C f(y~; p~) - (C R_p(Y_j, P_j))(P_j - p~) + (I - C J_y(Y_j, P_j))(Y_j - y~):
          K strictly inside Y_j and
          ||I - C J(Y_j; P_j)||_inf < 1.  So for every p in P_j there is exactly one solution in
          Y_j, and these form a continuous curve (IFT).
  chain   at each interior break p_j, a point Krawczyk enclosure Z_j at p = p_j, shrunk, lies
          strictly inside both Y_{j-1} and Y_j.  By uniqueness in each box the two curves meet.
  ends    the certified endpoint root boxes (from two_tail_endpoint_interval_exact.json, fixed
          tau = tau_lo, tau_hi) lie inside the first and last Y (their v-part, with tau as a
          degenerate interval), and their p-part lies inside the first and last P.  So the endpoint
          roots are points of the curve.
Together with the certified opposite signs of det F(0) = A/(2 pi) at the two endpoint roots,
det F(0) vanishes somewhere on this continuous branch.  Its tau-range is enclosed by the Y_j.
Not certified: connection to the PY seed, first loss, anything about Taylor radii.

Exact data and arithmetic as in two_tail_endpoint_interval.py (mpmath iv, 192 bits, AD of the
literal residual).  All endpoints are serialised as exact rationals.

Usage: two_tail_m1_fold_branch.py OUT.json
"""
import sys, json
from fractions import Fraction
from pathlib import Path
import numpy as np
import mpmath
from mpmath import iv
sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_m2_jacobian_interval import D, residual
from two_tail_endpoint_interval import q2iv, LO, HI, FX, IX, FQ, strictly_inside, sha

iv.prec = 192
mpmath.mp.prec = 192
HERE = Path(__file__).resolve().parent
EXACT = HERE.parents[1]/'results'/'two_tail'/'two_tail_endpoint_interval_exact.json'


def make_G(k, p, rho, sig, z, wq):
    """G(y; p): y = (v_0, v_1, v_2, tau) as D's, p fixed (an interval constant) at coordinate k."""
    def G(ys):
        vs, tau = ys[:3], ys[3]
        u, it = [], iter(vs)
        for i in range(4):
            u.append(D.c(p) if i == k else next(it))
        return residual(u, rho, sig, z, [tau*1, tau*q2iv(wq)])
    return G


def Rp_over(k, Y, P, rho, sig, z, wq):
    """Enclosure of dR/dp over the box (Y, P): AD with p as the only variable (gradient slot 0) and
    the y-components as interval constants."""
    u, it = [], iter(Y[:3])
    for i in range(4):
        u.append(D(P, [iv.mpf(1)] + [iv.mpf(0)]*3) if i == k else D.c(next(it)))
    tau = D.c(Y[3])
    r = residual(u, rho, sig, z, [tau*1, tau*q2iv(wq)])
    return [ri.g[0] for ri in r]


def duals(us):
    return [D(us[i], [iv.mpf(1) if j == i else iv.mpf(0) for j in range(4)]) for i in range(4)]


def newton(y, G):
    for _ in range(80):
        r = G(duals([iv.mpf(yi) for yi in y]))
        Fm = mpmath.matrix([r[i].v.mid for i in range(4)])
        Jm = mpmath.matrix([[r[i].g[j].mid for j in range(4)] for i in range(4)])
        dy = mpmath.lu_solve(Jm, -Fm)
        y = [y[i] + dy[i] for i in range(4)]
        if mpmath.norm(dy) < mpmath.mpf(2)**-170*(1 + mpmath.norm(mpmath.matrix(y))):
            break
    return y, Jm


def krawczyk(y, G, rad, pm=None):
    """rad: absolute radii (list of iv); center y (mpf).  With pm = (k, P, p_center, G_center, data)
    the p dependence is handled in mean-value form,
        K = y~ - C f(y~; p~) - (C R_p(Y, P)) (P - p~) + (I - C J_y(Y, P)) (Y - y~),
    which avoids the dependency blow-up of evaluating f(y~; P) with p as an interval.  G must then
    use the full interval P (for J_y over the box); f(y~; p~) uses the point G_center."""
    _, Jm = newton(y, G if pm is None else pm[3])
    Cf = np.linalg.inv(np.array([[float(Jm[i, j]) for j in range(4)] for i in range(4)]))
    Cq = [[Fraction(float(Cf[i, j])) for j in range(4)] for i in range(4)]
    C = [[q2iv(q) for q in row] for row in Cq]
    yt = [iv.mpf(yi) for yi in y]
    Y = [iv.mpf([LO(yt[i] - rad[i]), HI(yt[i] + rad[i])]) for i in range(4)]
    fy = (G if pm is None else pm[3])(duals(yt)); JY = G(duals(Y))
    E = [[(iv.mpf(1) if i == j else iv.mpf(0)) - sum((C[i][m]*JY[m].g[j] for m in range(4)), iv.mpf(0))
          for j in range(4)] for i in range(4)]
    norm = max(HI(sum((abs(E[i][j]) for j in range(4)), iv.mpf(0))) for i in range(4))
    Kx = [yt[i] - sum((C[i][m]*fy[m].v for m in range(4)), iv.mpf(0))
          + sum((E[i][j]*(Y[j] - yt[j]) for j in range(4)), iv.mpf(0)) for i in range(4)]
    extra = {}
    if pm is not None:
        k, P, pt, _, data = pm
        Rp = Rp_over(k, Y, P, *data)
        CRp = [sum((C[i][m]*Rp[m] for m in range(4)), iv.mpf(0)) for i in range(4)]
        Kx = [Kx[i] - CRp[i]*(P - pt) for i in range(4)]
        extra = dict(p_center=str(FX(LO(pt))), R_p_over_box=[IX(v) for v in Rp], C_R_p=[IX(v) for v in CRp])
    inside = all(LO(Y[i]) < LO(Kx[i]) and HI(Kx[i]) < HI(Y[i]) for i in range(4))
    w = dict(**extra, center=[str(FX(LO(c))) for c in yt], C_rational=[[str(q) for q in row] for row in Cq],
             Y=[IX(v) for v in Y], K=[IX(v) for v in Kx], f_center=[IX(r.v) for r in fy],
             J_over_Y=[[IX(JY[i].g[j]) for j in range(4)] for i in range(4)],
             I_minus_CJ=[[IX(E[i][j]) for j in range(4)] for i in range(4)],
             inf_norm_upper=str(FX(norm)), inf_norm_display=mpmath.nstr(norm, 8))
    w['exact_check_K_strictly_inside_Y'] = strictly_inside(w['K'], w['Y'])
    w['exact_check_norm_lt_1'] = Fraction(w['inf_norm_upper']) < 1
    return w, inside and norm < 1, (Y, Kx, C, Cq)


def point_enclosure(y0, G, rad, n=40):
    """Point Krawczyk at fixed p, then shrink X <- X ∩ K(X); returns (witness, shrunk box)."""
    w, ok, (Y, Kx, C, Cq) = krawczyk(y0, G, rad)
    if not ok:
        return w, None
    for _ in range(n):
        yt = [iv.mpf(v.mid) for v in Y]
        fy = G(duals(yt)); JY = G(duals(Y))
        E = [[(iv.mpf(1) if i == j else iv.mpf(0)) - sum((C[i][m]*JY[m].g[j] for m in range(4)), iv.mpf(0))
              for j in range(4)] for i in range(4)]
        Kx = [yt[i] - sum((C[i][m]*fy[m].v for m in range(4)), iv.mpf(0))
              + sum((E[i][j]*(Y[j] - yt[j]) for j in range(4)), iv.mpf(0)) for i in range(4)]
        Y = [iv.mpf([max(LO(Y[i]), LO(Kx[i])), min(HI(Y[i]), HI(Kx[i]))]) for i in range(4)]
    return w, [IX(v) for v in Y]


def main():
    out = sys.argv[1]
    cmd = ' '.join([sys.executable] + sys.orig_argv[1:]); print('# ' + cmd, flush=True)
    print('# EXTERNAL interval certificate (mpmath iv, 192 bits); not a Lean proof', flush=True)
    ex = json.load(open(EXACT))
    c = next(c for c in ex['controls'] if c['name'].startswith('M1'))
    rb = c['rigorous_bracket']
    eta = iv.mpf(49)/100; rho = 6*eta/iv.pi; sig = iv.mpf(1)
    z1q, z2q = (Fraction(s) for s in c['z']); z = [q2iv(z1q), q2iv(z2q)]
    wq = Fraction(c['w'])
    ends = {e: dict(tau=Fraction(rb[e]['tau']), u=[FQ(b) for b in rb[e]['root_enclosure_after_shrink']],
                    sign=rb[e]['detF0_sign']) for e in ('lo', 'hi')}
    assert ends['lo']['sign'] != ends['hi']['sign'] and {ends['lo']['sign'], ends['hi']['sign']} <= {'+', '-'}
    mid = {e: [(a + b)/2 for a, b in ends[e]['u']] for e in ends}
    # tangent direction of the branch: null vector of [R_u | R_tau] at the lo endpoint
    tq = ends['lo']['tau']
    def Rfull(us, tau):
        return residual(us, rho, sig, z, [tau*1, tau*q2iv(wq)])
    ub = [D(q2iv(mid['lo'][i]), [iv.mpf(1) if j == i else iv.mpf(0) for j in range(4)]) for i in range(4)]
    Ju = np.array([[float(r.g[j].mid) for j in range(4)] for r in Rfull(ub, D.c(q2iv(tq)))])
    Jt = np.array([float(r.g[3].mid) for r in Rfull([D.c(q2iv(m)) for m in mid['lo']],
                                                       D(q2iv(tq), [iv.mpf(0)]*3 + [iv.mpf(1)]))])
    Jfull = np.column_stack([Ju, Jt])
    t = np.linalg.svd(Jfull)[2][-1]
    scale = np.array([max(1, abs(float(m))) for m in mid['lo']] + [float(tq)])
    k = int(np.argmax(np.abs(t[:4])/scale[:4]))
    dp = float(mid['hi'][k] - mid['lo'][k])
    print(f"tangent (u, tau) = {np.round(t, 6)}; parameter p = u_{k}; dp(lo->hi) = {dp:.3e}; "
          f"dtau(lo->hi) = {float(ends['hi']['tau'] - ends['lo']['tau']):.3e}", flush=True)
    pe = {e: ends[e]['u'][k] for e in ends}
    plo, phi = min(pe['lo'][0], pe['hi'][0]), max(pe['lo'][1], pe['hi'][1])
    first, last = ('lo', 'hi') if pe['lo'][0] < pe['hi'][0] else ('hi', 'lo')

    def y_of(e):   # endpoint root in y-coordinates (v-part exact boxes, tau degenerate)
        v = [b for i, b in enumerate(ends[e]['u']) if i != k]
        return v + [[ends[e]['tau'], ends[e]['tau']]]

    def center_at(pq):
        lam = (pq - pe[first][0])/(pe[last][1] - pe[first][0])
        y0 = [mid[first][i] + lam*(mid[last][i] - mid[first][i]) for i in range(4) if i != k]
        y0 += [ends[first]['tau'] + lam*(ends[last]['tau'] - ends[first]['tau'])]
        G = make_G(k, q2iv(pq), rho, sig, z, wq)
        return newton([mpmath.mpf(y.numerator)/y.denominator for y in y0], G)[0]

    def slab(a, b, depth=0):
        P = iv.mpf([LO(q2iv(a)), HI(q2iv(b))])
        G = make_G(k, P, rho, sig, z, wq)
        pc = (a + b)/2; pt = q2iv(pc)
        Gc = make_G(k, pt, rho, sig, z, wq)
        y = center_at(pc)
        for rexp in range(5, 16):
            rad = [iv.mpf(Fraction(1, 10**rexp).numerator)/10**rexp*max(1, abs(float(yi))) for yi in y]
            rad = [iv.mpf(HI(r)) for r in rad]
            w, ok, _ = krawczyk(y, G, rad, pm=(k, P, pt, Gc, (rho, sig, z, wq)))
            if ok:
                return [dict(P=[str(a), str(b)], P_iv=IX(P), radius_rel=f'1e-{rexp}', witness=w)]
        if depth >= 12:
            raise RuntimeError(f'slab [{float(a)}, {float(b)}] not certified at depth {depth}')
        m = (a + b)/2
        return slab(a, m, depth + 1) + slab(m, b, depth + 1)

    slabs = slab(plo, phi)
    print(f"{len(slabs)} slab(s) certified over p in [{float(plo)!r}, {float(phi)!r}]", flush=True)
    for s in slabs:
        print(f"  P=[{float(Fraction(s['P'][0]))!r}, {float(Fraction(s['P'][1]))!r}] radius {s['radius_rel']} "
              f"K in int Y: {s['witness']['exact_check_K_strictly_inside_Y']}  ||I-CJ|| <= {s['witness']['inf_norm_display']}", flush=True)
    # chain points
    chain = []
    for s0, s1 in zip(slabs, slabs[1:]):
        pj = Fraction(s0['P'][1]); assert pj == Fraction(s1['P'][0])
        G = make_G(k, q2iv(pj), rho, sig, z, wq)
        y = center_at(pj)
        rad = [iv.mpf(HI(iv.mpf(1)/10**14*max(1, abs(float(yi))))) for yi in y]
        w, Z = point_enclosure(y, G, rad)
        okc = Z is not None and strictly_inside(Z, s0['witness']['Y']) and strictly_inside(Z, s1['witness']['Y'])
        chain.append(dict(p=str(pj), witness=w, Z=Z, exact_check_Z_inside_both=okc))
        print(f"  chain at p={float(pj)!r}: Z inside both Y: {okc}", flush=True)
    # endpoints
    endchk = {}
    for e, s in ((first, slabs[0]), (last, slabs[-1])):
        P = FQ(s['P_iv'])
        p_in = P[0] <= pe[e][0] and pe[e][1] <= P[1]
        y_in = strictly_inside(y_of(e), s['witness']['Y'])
        endchk[e] = dict(p_box=[str(pe[e][0]), str(pe[e][1])], p_inside_P=p_in, root_inside_Y=y_in)
        print(f"  endpoint {e}: p-part inside P: {p_in}; (v, tau) inside Y: {y_in}; det F(0) sign {ends[e]['sign']}", flush=True)
    passed = (all(s['witness']['exact_check_K_strictly_inside_Y'] and s['witness']['exact_check_norm_lt_1'] for s in slabs)
              and all(ch['exact_check_Z_inside_both'] for ch in chain)
              and all(v['p_inside_P'] and v['root_inside_Y'] for v in endchk.values()))
    tau_hull = [min(FQ(s['witness']['Y'][3])[0] for s in slabs), max(FQ(s['witness']['Y'][3])[1] for s in slabs)]
    print(f"\nSAME-BRANCH CERTIFICATE: {'PASS' if passed else 'FAIL'}; the branch's tau-range is inside "
          f"[{float(tau_hull[0])!r}, {float(tau_hull[1])!r}]; det F(0) changes sign along it "
          f"({ends['lo']['sign']} at tau_lo, {ends['hi']['sign']} at tau_hi)", flush=True)
    json.dump(dict(command=cmd, label='EXTERNAL interval certificate (mpmath iv, 192 bits); not a Lean proof',
                   serialization='All endpoints are exact rationals; *_display fields are non-authoritative.',
                   endpoint_source=str(EXACT), endpoint_source_sha256=sha(EXACT),
                   source_sha256={n: sha(HERE/n) for n in ('two_tail_m1_fold_branch.py', 'two_tail_endpoint_interval.py',
                                                           'two_tail_m2_jacobian_interval.py')},
                   data=dict(eta='49/100', rho='6*eta/pi', sigma='1', z=c['z'], f=c['f'], w=c['w']),
                   parameter_coordinate=k, tangent_float=t.tolist(), p_hull=[str(plo), str(phi)],
                   endpoints={e: dict(tau=str(ends[e]['tau']), detF0_sign=ends[e]['sign'], **endchk[e]) for e in endchk},
                   slabs=slabs, chain=chain, tau_hull=[str(x) for x in tau_hull], passed=bool(passed)),
              open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
