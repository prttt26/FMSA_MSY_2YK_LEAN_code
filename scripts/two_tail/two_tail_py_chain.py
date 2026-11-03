"""EXTERNAL Arb interval certificate: the M1 / M3 det F(0) sign change lies on the PY-seeded branch
(user request, after handoffs 140-155).  NOT a Lean proof.

Data: the exact control data of two_tail_endpoint_interval_exact.json (eta = 49/100, sigma = 1,
rho = 6 eta/pi, rational z, w), K = tau*(1, w).  Variables x = (Dt1, Dt2, G1, G2, tau).  The residual
R(x) (4 equations), its exact derivatives and A are the SymPy transcription of the Lean polynomials
in two_tail_m3_arb_recheck (symbolic, TaylorPoly); every polynomial is evaluated over a box by its
exact Taylor expansion about the center with Arb coefficients.

Parametrised Krawczyk.  One coordinate x_k is the parameter (k = 4: tau; k = 0: p = Dt1), the other
four y are unknowns.  Over a slab P of the parameter and a box Y, in mean-value form
    K = y~ - C R(y~, p~) - (C R_p(B))(P - p~) + (I - C J_y(B)) (Y - y~),   B = Y x P,
with R_p = dR/dx_k and J_y = dR/dy enclosed over B, and C R_p formed as one interval vector.  (For
k = 4, R_p = R_tau is constant; enclosing R(y~, P) first and then multiplying by C loses the
correlation of the two first equations, which are linear in the same tau, and fails.)  K strictly
inside Y gives, for every p in P, exactly one root in Y, and the radius-weighted norm
    q = max_i sum_j |I - C J_y|_ij r_j / r_i < 1   (r = radii of Y; implied by K strictly inside Y)
gives J_y invertible throughout B.  All of this is formed in exact Fraction arithmetic from the
stored outward-rounded enclosures.

Certificate:
  (0) Seed.  At tau = 0 the HS (PY) seed is Dt = 0, G_t = -a0/a1 where a1 G_t + a0 is the t-th
      second equation at Dt = 0, tau = 0 (the first equations vanish identically at Dt = 0).  Its
      Arb enclosure lies inside the first slab box.
  (1) tau phase: slabs tiling [0, tau_end] (tau_end = tau_hi for M3, tau_s for M1).
  (2) p phase (M1 only; near its fold tau is a poor parameter): slabs in p = Dt1 tiling [p_0, p_end].
      On each, also dtau/dp > 0 along the curve, from d = -J_y^{-1} R_p, i.e. d = -C R_p + (I - C J_y) d:
      |d|_r <= |C R_p|_r/(1 - q), then d_tau >= -(C R_p)_tau - sum_j |E_tau,j| r_j |d|_r.  So tau is
      strictly increasing along the p curve; and since J_y = [dR/d(Dt2, G1, G2) | R_tau] is invertible,
      the kernel of [J_u | R_tau] is the tangent, whose tau component is nonzero, so J_u is invertible
      on the curve.
  (3) Chain.  Every link box Z (a tiny Krawczyk box at a fixed parameter value: the break; at tau_s the
      switch box at fixed tau) lies inside both neighbouring slab boxes (its slab-parameter coordinate
      inside the closed slab P, every other coordinate strictly inside Y).  Hence ONE continuous root
      curve from the HS seed, on which tau is strictly increasing and J_u is invertible: the PY-seeded
      branch u(tau), tau in [0, tau_hi] (the analytic IFT continuation of the PY seed in tau).
  (4) det F(0) = A/(2 pi).  Tiny boxes S_lo, S_hi at tau_lo, tau_hi (fixed tau) lie inside slab boxes;
      A > 0 on S_lo and A < 0 on S_hi.  A > 0 over every tau slab ending at or before tau_lo, and over
      every p slab ending at or before p_star >= the p range of S_lo; with tau increasing along the
      curve this gives A(u(tau)) > 0 on [0, tau_lo].  Hence the FIRST zero of det F(0) along the
      PY-seeded branch lies in (tau_lo, tau_hi).
Not certified: canonicity along the branch (det F(s) != 0 for complex s with Re s >= 0, i.e. first
loss), zero uniqueness in the bracket, all-wave statements, Taylor radii.

Storage: centers are 96-bit dyadics; every Arb enclosure is rounded OUTWARD to 96 significant bits;
numbers are 'm p e' = m*2^e or a plain rational.  Derived quantities (I - C J_y, C R_p, K, d) are not
stored; the checker recomputes them.  Output is gzipped JSON.

Requires python-flint 0.6.0 and SymPy 1.13.2, e.g.
  PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 two_tail_py_chain.py M3 OUT.json.gz
"""
import sys, json, hashlib, time, gzip, math
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import flint
from flint import arb, arb_mat, ctx
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_m3_arb_recheck import (PREC, SRC, LEAN, symbolic, ev, TaylorPoly, bounds, iball, strict_in,
                                     add, sub, mul, pt, exact)

HERE = Path(__file__).resolve().parent
BITS = 96                                 # centers and stored enclosures
TINY = Q(1, 10**20)                       # relative radius of link / endpoint boxes
EPS = Q(1, 10**18)                        # relative radius floor of slab boxes (> TINY, so link boxes fit)
GROW, SHRINK, SLACK = Q(3, 2), Q(1, 2), (Q(5, 4), Q(2), Q(4))
SWITCH = {'M1': Q(19, 2), 'M3': None}     # tau_s: tau phase -> p phase (None: tau phase to tau_hi)
TAU = 4
DEBUG = bool(__import__('os').environ.get('CHAIN_DEBUG'))


# ---------- dyadic rounding and compact serialization ----------
def _k(q, bits):
    a = abs(q)
    return bits - (a.numerator.bit_length() - a.denominator.bit_length())


def rdown(q, bits=BITS):
    if q == 0:
        return Q(0)
    k = _k(q, bits)
    return Q(math.floor(q*2**k), 2**k) if k >= 0 else Q(math.floor(q/2**-k)*2**-k)


def rup(q, bits=BITS):
    return -rdown(-q, bits)


def rnear(q, bits=BITS):
    if q == 0:
        return Q(0)
    k = _k(q, bits)
    return Q(round(q*2**k), 2**k) if k >= 0 else Q(round(q/2**-k)*2**-k)


def out(iv, bits=BITS):
    return (rdown(iv[0], bits), rup(iv[1], bits))


def dy(q):
    d = q.denominator
    if d & (d - 1) == 0:
        m, e = q.numerator, -(d.bit_length() - 1)
        while m and m % 2 == 0:
            m //= 2; e += 1
        return f'{m}p{e}'
    return str(q)


def P_(s):
    if 'p' in s:
        m, e = s.split('p'); return Q(int(m))*Q(2)**int(e)
    return Q(s)


def DI(iv): return [dy(iv[0]), dy(iv[1])]
def unk(k): return [i for i in range(5) if i != k]
def mag(iv): return max(abs(iv[0]), abs(iv[1]))


# ---------- parametrised Krawczyk ----------
def kcore(yc, pc, C, Y, P, f, Jy, Rp):
    """Exact Fraction Krawczyk (same algebra as the checker).  Returns K, weighted norm q, E, C R_p, r."""
    E = [[None]*4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            acc = pt(Q(int(i == j)))
            for m in range(4):
                acc = sub(acc, mul(pt(C[i][m]), Jy[m][j]))
            E[i][j] = acc
    dP = (P[0] - pc, P[1] - pc)
    K, CRp = [], []
    for i in range(4):
        crp = pt(Q(0))
        for m in range(4):
            crp = add(crp, mul(pt(C[i][m]), Rp[m]))
        CRp.append(crp)
        acc = pt(yc[i])
        for m in range(4):
            acc = sub(acc, mul(pt(C[i][m]), f[m]))
        acc = sub(acc, mul(crp, dP))
        for j in range(4):
            acc = add(acc, mul(E[i][j], sub(Y[j], pt(yc[j]))))
        K.append(acc)
    r = [(Y[j][1] - Y[j][0])/2 for j in range(4)]
    q = max(sum((mag(E[i][j])*r[j] for j in range(4)), Q(0))/r[i] for i in range(4))
    return K, q, E, CRp, r


def dtau_lower(E, CRp, r, q):
    """Lower bound of d_tau (unknown index 3 when k = 0) for d = -C R_p + E d."""
    if q >= 1:
        return None
    d0 = max(mag(CRp[i])/r[i] for i in range(4))/(1 - q)
    return -CRp[3][1] - sum((mag(E[3][j])*r[j] for j in range(4)), Q(0))*d0


class Model:
    def __init__(self, eta, z, w):
        self.V, R, _, A = symbolic(eta, z, w)
        self.Rp = [TaylorPoly(r, self.V) for r in R]
        self.JF = [[TaylorPoly(sp.expand(sp.diff(r, v)), self.V) for v in self.V] for r in R]   # 4 x 5
        self.Ap = TaylorPoly(A, self.V)
        assert all(not sp.diff(r, self.V[TAU], 2) for r in R)
        self.R = R

    def point(self, x):
        z5 = [arb(0)]*5
        return [r.over(x, z5) for r in self.Rp], [[e.over(x, z5) for e in row] for row in self.JF]

    def newton(self, k, x, iters=40):
        """Non-rigorous Newton in the unknowns at fixed x_k (Arb midpoints).  Returns the 96-bit center and
        float J_y, R_p there (for sizing and the preconditioner only)."""
        U = unk(k)
        for _ in range(iters):
            f, JF = self.point(x)
            Jy = arb_mat([[JF[i][j].mid() for j in U] for i in range(4)])
            dx = Jy.solve(arb_mat([[f[i].mid()] for i in range(4)]))
            x = list(x)
            step = [exact(dx[a, 0].mid()) for a in range(4)]
            for a, j in enumerate(U):
                x[j] = x[j] - step[a]
            if all(abs(step[a]) <= Q(1, 2**200)*(1 + abs(x[j])) for a, j in enumerate(U)):
                break
        x = [v if j == k else rnear(v) for j, v in enumerate(x)]     # the fixed parameter stays exact
        _, JF = self.point(x)
        return x, np.array([[float(JF[i][j].mid()) for j in U] for i in range(4)]), np.array([float(JF[i][k].mid()) for i in range(4)])

    def krawczyk(self, k, xc, C, Y, P):
        """xc: 5-vector center (xc[k] = parameter center); Y: 4 unknown intervals; P: parameter interval."""
        U = unk(k)
        B = [None]*5
        for a, j in enumerate(U):
            B[j] = Y[a]
        B[k] = P
        h = [iball(B[j][0] - xc[j], B[j][1] - xc[j]) for j in range(5)]
        z5 = [arb(0)]*5
        f = [out(bounds(r.over(xc, z5))) for r in self.Rp]
        Jy = [[out(bounds(self.JF[i][j].over(xc, h))) for j in U] for i in range(4)]
        Rp = [out(bounds(self.JF[i][k].over(xc, h))) for i in range(4)]
        K, q, E, CRp, r = kcore([xc[j] for j in U], xc[k], C, Y, P, f, Jy, Rp)
        qu = rup(q, 64)
        ok = all(strict_in(K[i], Y[i]) for i in range(4)) and qu < 1
        dl = dtau_lower(E, CRp, r, q) if k == 0 else None
        w = dict(k=k, c=[dy(v) for v in xc], C=[[dy(v) for v in row] for row in C], Y=[DI(v) for v in Y], P=DI(P),
                 f=[DI(v) for v in f], Jy=[[DI(v) for v in row] for row in Jy], Rp=[DI(v) for v in Rp], q=dy(qu))
        return w, ok, qu, B, dl

    def A_over(self, B):
        """A over the amplitude part of a 5-box (A does not depend on tau)."""
        c = [(b[0] + b[1])/2 for b in B]
        h = [iball(B[j][0] - c[j], B[j][1] - c[j]) for j in range(4)] + [arb(0)]
        return out(bounds(self.Ap.over(c, h)), 64)

    def tiny(self, k, x):
        """Tiny Krawczyk box at the fixed parameter value x[k] (point P)."""
        x, Jy, _ = self.newton(k, x)
        C = [[Q(float(v)) for v in row] for row in np.linalg.inv(Jy)]
        Y = [(x[j] - rup(TINY*max(1, abs(x[j])), 16), x[j] + rup(TINY*max(1, abs(x[j])), 16)) for j in unk(k)]
        w, ok, _, B, _ = self.krawczyk(k, x, C, Y, (x[k], x[k]))
        return x, w, ok, B


def inside(Bz, Bs, k):
    """Box Bz (5 intervals) inside slab box Bs with slab parameter k: coordinate k in the closed P, every
    other coordinate strictly inside."""
    return all((Bs[j][0] <= Bz[j][0] and Bz[j][1] <= Bs[j][1]) if j == k else strict_in(Bz[j], Bs[j]) for j in range(5))


def run_phase(M, k, x0, a0, end, A_until, log, t0, on_slab=None):
    """Adaptive slabs in the parameter x_k from a0 (curve point x0), up to `end` (None: open).
    A > 0 is required on slabs ending at or before A_until() (None: on every slab).  For k = 0,
    dtau/dp > 0 is required.  on_slab(slab) -> 'accept' | 'retry' | 'stop'."""
    slabs, links = [], []
    a, xa, width, fails = a0, x0, (Q(1, 2) if k == TAU else Q(1, 64)), 0
    _, Ja, Ra = M.newton(k, xa, 2)
    U = unk(k)
    while end is None or a < end:
        lim = A_until()
        b = rnear(a + width, 64)
        if end is not None:
            b = min(b, end)
        if lim is not None and a < lim:
            b = min(b, lim)
        assert b > a, 'slab width underflow'
        c = (a + b)/2
        ta = -np.linalg.solve(Ja, Ra)
        g = list(xa); g[k] = c
        for t_, j in enumerate(U):
            g[j] = xa[j] + Q(float(ta[t_]))*(c - a)
        xc, Jc, Rc = M.newton(k, g)
        tc = -np.linalg.solve(Jc, Rc)
        g = list(xc); g[k] = b
        for t_, j in enumerate(U):
            g[j] = xc[j] + Q(float(tc[t_]))*(b - c)
        xb, Jb, Rb = M.newton(k, g)
        disp = [max(abs(xa[j] - xc[j]), abs(xb[j] - xc[j])) for j in U]      # non-rigorous sizing
        C = [[Q(float(v)) for v in row] for row in np.linalg.inv(Jc)]
        need = lim is None or b <= lim
        got, why = None, []
        for s in SLACK:
            rad = [rup(s*disp[t_] + EPS*max(1, abs(xc[j])), 24) for t_, j in enumerate(U)]
            Y = [(xc[j] - rad[t_], xc[j] + rad[t_]) for t_, j in enumerate(U)]
            w, ok, qu, B, dl = M.krawczyk(k, xc, C, Y, (a, b))
            if not ok or (k == 0 and not (dl is not None and dl > 0)):
                why.append(f'K/q (q={float(qu):.3g}, ok={ok}, dl={None if dl is None else float(dl):.3g})' if k == 0 and dl is not None
                           else f'K/q (q={float(qu):.3g}, ok={ok})')
                continue
            Ab = M.A_over(B)
            if need and not Ab[0] > 0:
                why.append(f'A ({float(Ab[0]):.3g})')
                continue
            got = (w, B, Ab, qu, dl)
            break
        if got is not None and slabs:
            _, zw, zok, Bz = M.tiny(k, xa)
            if zok and inside(Bz, slabs[-1]['B'], k) and inside(Bz, got[1], k):
                link = dict(w=zw)
            else:
                got = None; why.append(f'link (zok={zok})')
        if got is None:
            if DEBUG:
                log(f'    reject x_{k} in [{float(a)!r}, {float(b)!r}] width {float(b - a):.3e}: {"; ".join(why)}')
            width = rnear(width*SHRINK, 20); fails += 1
            continue
        w, B, Ab, qu, dl = got
        slab = dict(w=w, A=DI(Ab), A_required=need, dtau_dp_lower=dy(rdown(dl, 64)) if dl is not None else None, B=B)
        act = on_slab(slab) if on_slab else 'accept'
        if act == 'retry':
            continue
        if slabs:
            links.append(link)
        slabs.append(slab)
        n = len(slabs)
        if n % 50 == 0 or act == 'stop' or b == end:
            log(f'  [{"tau" if k == TAU else "p"}] slab {n}: x_{k} in [{float(a):.15g}, {float(b):.15g}] (width {float(b - a):.3e}), '
                f'q <= {float(qu):.4f}, A >= {float(Ab[0]):.3e}'
                + (f', dtau/dp >= {float(dl):.3e}, tau in [{float(B[TAU][0]):.15g}, {float(B[TAU][1]):.15g}]' if k == 0 else '')
                + f'; rejected {fails}; {time.time() - t0:.0f} s')
        xa, Ja, Ra, a = xb, Jb, Rb, b
        width = rnear(width*GROW, 20)
        if act == 'stop':
            break
    return slabs, links, xa, fails


def main():
    assert __debug__, 'run without -O'
    name, outp = sys.argv[1], Path(sys.argv[2]).resolve()
    assert name in ('M1', 'M3') and 'MSA_and_1st_Truncation' not in str(outp) and outp.name.endswith('.json.gz')
    ctx.prec = PREC
    cmd = ' '.join([sys.executable] + sys.orig_argv[1:])
    log = lambda s: print(s, flush=True)
    log('# ' + cmd)
    log(f'# EXTERNAL Arb interval certificate (python-flint {flint.__version__}, SymPy {sp.__version__}, {PREC} bits); '
        'not a Lean proof')
    src_sha = {n: hashlib.sha256((HERE/n).read_bytes()).hexdigest() for n in ('two_tail_py_chain.py', 'two_tail_m3_arb_recheck.py')}
    raw = SRC.read_bytes(); d = json.loads(raw)
    c = next(c for c in d['controls'] if c['name'].startswith(name))
    eta, z, w = sp.Rational(c['eta']), [sp.Rational(x) for x in c['z']], sp.Rational(c['w'])
    tl, th = Q(c['rigorous_bracket']['lo']['tau']), Q(c['rigorous_bracket']['hi']['tau'])
    M = Model(eta, z, w)
    t0 = time.time()
    # (0) seed
    V = M.V
    G = []
    for t, g in ((2, V[2]), (3, V[3])):
        e = sp.expand(M.R[t].subs({V[0]: 0, V[1]: 0, V[4]: 0}))
        a1, a0 = sp.Poly(e, g, domain='EX').all_coeffs()
        assert not (a1.free_symbols | a0.free_symbols)
        G.append(-a0/a1)
    for r in M.R[:2]:
        assert sp.expand(r.subs({V[0]: 0, V[1]: 0, V[4]: 0})) == 0
    seed = [(Q(0), Q(0)), (Q(0), Q(0))] + [out(bounds(ev(g))) for g in G] + [(Q(0), Q(0))]
    x0 = [Q(0), Q(0), rnear(seed[2][0]), rnear(seed[3][0]), Q(0)]
    log(f'(0) seed: Dt = 0, G = {float(seed[2][0]):.12g}, {float(seed[3][0]):.12g}')
    ts = SWITCH[name]

    def endpoint(e, tau, xg):
        x = list(xg); x[TAU] = tau
        _, sw, sok, Bs = M.tiny(TAU, x)
        Ab = M.A_over(Bs)
        sign = '+' if Ab[0] > 0 else '-' if Ab[1] < 0 else '0?'
        return dict(tau=str(tau), w=sw, ok=sok, A=DI(Ab), detF0_sign=sign,
                    endpoint_certificate_sign=c['rigorous_bracket'][e]['detF0_sign']), Bs

    # (1) tau phase
    tau_end = ts if ts is not None else th
    s1, links, xe, fails = run_phase(M, TAU, x0, Q(0), tau_end, lambda: min(tl, tau_end), log, t0)
    assert inside(seed, s1[0]['B'], TAU), 'seed not inside the first box'
    slabs = [dict(s, phase='tau') for s in s1]
    switch, p_star, ends = None, None, {}
    if ts is not None:
        # (2) switch box at tau_s, then the p phase
        x, zw, zok, Bz = M.tiny(TAU, xe)
        assert zok and inside(Bz, slabs[-1]['B'], TAU), 'switch box not inside the last tau slab'
        p0 = rdown(Bz[0][0], 64)
        xs = list(x); xs[0] = p0
        xs, _, _ = M.newton(0, xs)
        st = dict(p_star=None)

        def on_slab(sl):
            B = sl['B']
            if st['p_star'] is None and B[TAU][1] >= tl:
                lo, Blo = endpoint('lo', tl, [(b[0] + b[1])/2 for b in B])
                assert lo['ok'] and Blo[0][0] > B[0][0], 'S_lo not ahead of the slab start'
                st['p_star'] = rup(Blo[0][1], 64)
                log(f'  S_lo: p range [{float(Blo[0][0]):.17g}, {float(Blo[0][1]):.17g}]; p_star = {float(st["p_star"]):.17g}')
                if B[0][1] > st['p_star']:
                    return 'retry'                    # redo this slab with the A requirement up to p_star
            return 'stop' if B[TAU][0] > th else 'accept'

        s2, l2, _, f2 = run_phase(M, 0, xs, p0, None, lambda: st['p_star'], log, t0, on_slab)
        assert inside(Bz, s2[0]['B'], 0), 'switch box not inside the first p slab'
        slabs += [dict(s, phase='p') for s in s2]; links += l2; fails += f2
        switch = dict(tau=str(ts), w=zw); p_star = st['p_star']
    # (4) endpoint boxes
    for e, tau in (('lo', tl), ('hi', th)):
        cand = [j for j, s_ in enumerate(slabs) if s_['B'][TAU][0] <= tau <= s_['B'][TAU][1]]
        rec_e, Bs = endpoint(e, tau, [(b[0] + b[1])/2 for b in slabs[cand[0]]['B']])
        hit = [j for j in cand if inside(Bs, slabs[j]['B'], slabs[j]['w']['k'])]
        rec_e.update(slab=hit[0] if hit else None)
        ends[e] = rec_e
        log(f'(4) {e}: tau = {float(tau)!r}: tiny box Krawczyk {rec_e["ok"]}, inside slab {rec_e["slab"]}; '
            f'A over it = {float(P_(rec_e["A"][0])):.6e}, sign {rec_e["detF0_sign"]} '
            f'(endpoint certificate: {rec_e["endpoint_certificate_sign"]})')
        if e == 'lo' and p_star is not None:
            assert Bs[0][1] <= p_star
    qmax = max(P_(s_['w']['q']) for s_ in slabs)
    n_tau = sum(s_['phase'] == 'tau' for s_ in slabs); n_p = len(slabs) - n_tau
    passed = (all(ends[e]['ok'] and ends[e]['slab'] is not None for e in ends)
              and ends['lo']['detF0_sign'] == '+' and ends['hi']['detF0_sign'] == '-'
              and len(links) == len(slabs) - 1 - (1 if switch else 0) and qmax < 1)
    log(f"\n{len(slabs)} slabs ({n_tau} tau, {n_p} p), {len(links)} links{' + 1 switch box' if switch else ''}, "
        f"{fails} rejected trial slabs; max q <= {float(qmax):.6f}")
    log(f"RESULT: {'PASS' if passed else 'FAIL'} -- one continuous regular root curve from the HS seed at tau = 0, with tau "
        f"strictly increasing, through tau_hi; A > 0 on [0, tau_lo] and A < 0 at tau_hi, so the first zero of det F(0) "
        f"along the PY-seeded branch lies in (tau_lo, tau_hi).  First loss (complex s) is NOT certified.")
    for s_ in slabs:
        del s_['B']
    rec = dict(command=cmd, label='EXTERNAL Arb interval certificate; NOT a Lean proof',
               serialization="Numbers are exact: 'm p e' = m*2^e, otherwise a rational a/b.  Every Arb enclosure is "
                             "rounded outward; centers are exact 96-bit dyadics.",
               coordinates=['Dt1', 'Dt2', 'G1', 'G2', 'tau'],
               control=c['name'], data=dict(eta=c['eta'], z=c['z'], w=c['w'], sigma='1', rho='6*eta/pi'),
               source=str(SRC), source_sha256=hashlib.sha256(raw).hexdigest(),
               lean_sha256={str(p.relative_to(HERE.parents[2])): hashlib.sha256(p.read_bytes()).hexdigest() for p in LEAN},
               script_sha256=src_sha,
               versions=dict(python=sys.version.split()[0], python_flint=flint.__version__, sympy=sp.__version__),
               precision_bits=PREC, bracket=[str(tl), str(th)], tau_switch=str(ts) if ts is not None else None,
               p_star=dy(p_star) if p_star is not None else None,
               seed=dict(description='Dt = 0, G_t = -a0/a1 of the second equations at Dt = 0, tau = 0',
                         G_srepr=[sp.srepr(g) for g in G], enclosure=[DI(v) for v in seed]),
               slabs=slabs, links=links, switch=switch, endpoints=ends, max_q_upper=dy(qmax),
               counts=dict(slabs=len(slabs), tau_slabs=n_tau, p_slabs=n_p, links=len(links), rejected_trials=fails),
               passed=passed)
    with gzip.open(outp, 'wt') as fh:
        json.dump(rec, fh, separators=(',', ':'))
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())
