"""EXTERNAL Arb interval certificate: full canonicity along the PY-seeded M1 / M3 branch up to tau_lo
(user request, after handoffs 157-165).  NOT a Lean proof.

Target (Lean interface).  CanonicalFirstLoss.canonical_path_of_physical_factor_units: a continuous
amplitude path on a connected parameter set, starting at a canonical seed, stays fully canonical if
the physical Fourier factor is a unit at every point and every real k.  For N = 1 the factor is the
scalar
    F(u, k) = 1 - rho Phi(u, k),   Phi = int q(r) e^{-ikr} dr  (fourierQ),
with q the literal Baxter q (MSAMultiTailMixtureBaxter.q; sigma = 1, edgeLo = 0, edgeHi = 1), so that
for s = ik
    Phi = qp e1(s) + A e2(s) + sum_t [ W_t/(s + z_t) + C_t (e3(s) + e^{-s}/(s + z_t)) ],
    e1 = int_0^1 (r-1) e^{-sr} = (1 - s - e^{-s})/s^2,   e2 = int_0^1 (r-1)^2/2 e^{-sr} = (1 - s + s^2/2 - e^{-s})/s^3,
    e3 = int_0^1 e^{-sr} = (1 - e^{-s})/s,
and qp, A, W_t, C_t are the literal amplitude polynomials (BHResidualPolynomials eval_qpPoly, eval_aPoly,
eval_wPoly, eval_cPoly).  F(-k) = conj F(k) (fourierQ_conj), so k >= 0 suffices; F(u, 0) = A(u)/(2 pi) at
EVERY amplitude u (BaxterZeroMode.scalar_fourierFactor_zero), which is checked here symbolically.

Certificate, for each control.  The PY-seeded branch u(tau), tau in [0, tau_lo], lies in the boxes of the
certified chain slabs that end at or before tau_lo (tau slabs) / p_star (p slabs) of
two_tail_py_chain_{M}.json.gz (hash-pinned).  These slabs are grouped; for a group with amplitude hull U:
  * large k: for k >= K, |F - 1| <= rho (|q0|/k + B2/k^2 + 2|A|/k^3) < 1/2, with q0 = q(0+) =
    -qp + A/2 + sum(W + C) and B2 = 2|qp| + |A| + sum z_t (|W_t| + |C_t|) (from e1 = -1/s + (1-e^{-s})/s^2,
    e2 = 1/(2s) + (1 - s - e^{-s})/s^3, W/(s+z) = W/s - Wz/(s(s+z)), C(e3 + e^{-s}/(s+z)) = C/s - C e^{-s}
    z/(s(s+z)), |s + z| >= k);
  * 0 <= k <= K: a march k_0 = k_start < k_1 < ... with, at each k_i, m_i <= min_U |F(u, k_i)| and
    d_i >= max_U |dF/dk(u, k_i)|, and the step h_i = k_{i+1} - k_i satisfying
        m_i - d_i h_i - L_i h_i^2/2 > 0,   L_i = L2 if k_i = 0, else min(L2, H2(k_i)),
    with the global bound
        L2 = rho [ |qp|/12 + |A|/60 + sum_t ( 2|W_t|/z_t^3 + |C_t| (1/3 + 1/z_t + 2/z_t^2 + 2/z_t^3) ) ]
           >= rho int r^2 |q| >= sup_k |d^2F/dk^2|      (the coefficient sum is a triangle bound)
    and the decreasing high-frequency bound (s = ik, E = e^{-s}, |E| = 1, |s + z| >= k):
        d^2F/dk^2 = rho Phi''(s),  Phi'' = qp e1'' + A e2'' + sum_t [2 W_t/(s+z_t)^3 + C_t h_t''],
        e1'' = -E/s^2 - (2 + 4E)/s^3 + 6(1 - E)/s^4,
        e2'' = (1 - E)/s^3 - 6(1 + E)/s^4 + 12(1 - E)/s^5,
        h''  = -zE/(s(s+z)) - 2zE(2s+z)/(s^2 (s+z)^2) + 2E/(s+z)^3 + 2(1 - E)/s^3
    (identities checked symbolically at startup), hence
        H2(k) = rho [ |qp|(1/k^2 + 6/k^3 + 12/k^4) + |A|(2/k^3 + 12/k^4 + 24/k^5)
                + sum_t ( 2|W_t|/k^3 + |C_t|(z_t/k^2 + (6 + 4 z_t)/k^3 + 2 z_t^2/k^4) ) ] >= |d^2F/dk^2(k')|
    for every k' >= k.  So F != 0 on [k_i, k_{i+1}] for every u in U.
F(U, k_i) and dF/dk(U, k_i) are enclosed as exact centered Taylor forms over U of the polynomials
Re/Im sum_m alpha_m(k_i) P_m(u), with alpha_m(k_i) in Arb (series for k <= 1/2).  A group that fails is
split in two and its halves continue from the failing k.  Conclusion, with the Lean interface and the
seed canonicity (Codex 109): the PY-seeded branch is fully canonical on [0, tau_lo]; with the chain
(det F(0) = 0 at some tau in (tau_lo, tau_hi)) the FIRST LOSS of full canonicity lies in (tau_lo, tau_hi).
Not certified: which k carries the first loss, its uniqueness, Taylor radii, all-wave statements beyond
the Lean interface.

Storage: m_i, d_i rounded (down / up) to 24-bit dyadics, k_i 48-bit dyadics, 'm p e' = m*2^e.

Requires python-flint 0.6.0 and SymPy 1.13.2, e.g.
  PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 two_tail_first_loss.py M3 OUT.json.gz
"""
import sys, json, hashlib, time, gzip, math
from fractions import Fraction as Q
from itertools import product
from math import comb, factorial
from pathlib import Path
import flint
from flint import arb, acb, ctx
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_m3_arb_recheck import PREC, SRC, LEAN, symbolic, ev, ball, bounds, iball, ipow
from two_tail_py_chain import P_, dy, DI, rdown, rup, rnear, out, TAU

HERE = Path(__file__).resolve().parent
THETA = Q(7, 8)                 # fraction of the admissible step taken
GROUP_SPAN = Q(1, 4)            # max relative hull extent when forming initial groups
GROUP_MAX = 256                 # max slabs per initial group
MAX_STEPS = 200000              # per group before it is split


# ---------- amplitude polynomials ----------
def base_polys(eta, z):
    D1, D2, G1, G2 = V = sp.symbols('D1 D2 G1 G2')
    Dv, Gv = (D1, D2), (G1, G2)
    pi = sp.pi
    rho = 6*eta/pi; vac = 1 - eta; xi2 = rho
    Q0 = 2*pi/vac*(1 + pi*xi2/(4*vac)); Qpp = 2*pi/vac*(1 + pi*xi2/(2*vac))
    gam = [1 - 2*pi*rho*sp.exp(-z[t])/z[t]*Gv[t] for t in range(2)]
    W = [2*pi/z[t]*rho*Gv[t]*Dv[t] for t in range(2)]
    C = [gam[t]*Dv[t] for t in range(2)]
    M = [-(1/z[t])*rho*(W[t] + (1 + z[t])*C[t]) for t in range(2)]
    Nn = [rho*(1/z[t]**2*W[t] + (1 + z[t] + z[t]**2/2)/z[t]**2*C[t]) for t in range(2)]
    A = Qpp + sum(Qpp*M[t] + 2*pi**2*xi2/vac**2*Nn[t] for t in range(2))
    qp = Q0 + sum(Q0*M[t] + Qpp*Nn[t] for t in range(2))
    P = [sp.expand(e) for e in (qp, A, W[0], W[1], C[0], C[1])]
    return V, P, rho


class TP:
    """Polynomial in 4 amplitudes with Arb coefficients; exact Taylor coefficients about a center."""
    def __init__(self, expr, V):
        self.terms = [(m, ev(c)) for m, c in sp.Poly(expr, *V, domain='EX').as_dict().items()]

    def taylor(self, center):
        c = [ball(x) for x in center]
        tay = {}
        for m, a in self.terms:
            for beta in product(*[range(k + 1) for k in m]):
                t = a
                for k in range(4):
                    if m[k] - beta[k]:
                        t = t*comb(m[k], beta[k])*ipow(c[k], m[k] - beta[k])
                tay[beta] = tay.get(beta, arb(0)) + t
        return tay


class Box:
    """Amplitude hull U with Taylor data of the six base polynomials."""
    def __init__(self, polys, U):
        self.U = U
        self.c = [rnear((a + b)/2) for a, b in U]
        h = [iball(U[i][0] - self.c[i], U[i][1] - self.c[i]) for i in range(4)]
        self.T = [p.taylor(self.c) for p in polys]
        self.betas = sorted(set().union(*[t.keys() for t in self.T]))
        self.hp = {}
        for beta in self.betas:
            v = arb(1)
            for k in range(4):
                if beta[k]:
                    v = v*ipow(h[k], beta[k])
            self.hp[beta] = v

    def comb_real(self, coef):
        """Enclosure over U of sum_m coef_m P_m(u) for real Arb coefficients."""
        out_ = arb(0)
        for beta in self.betas:
            t = arb(0)
            for m, cm in enumerate(coef):
                if beta in self.T[m]:
                    t += cm*self.T[m][beta]
            out_ += t*self.hp[beta]
        return out_

    def mag(self, m):
        return bounds(self.comb_real([arb(int(i == m)) for i in range(6)]))


def alphas(k, z):
    """alpha_m(s), d alpha_m/ds at s = i k (exact dyadic k >= 0), m over (qp, A, W1, W2, C1, C2)."""
    s = acb(0, ball(k))
    if k <= Q(1, 2):
        # e1 = -sum p_n/((n+1)(n+2)), e2 = sum p_n/((n+1)(n+2)(n+3)), e3 = sum p_n/(n+1), p_n = (-s)^n/n!;
        # d/ds p_n = -p_{n-1}.  For |s| <= 1/2 the omitted tails (n >= 70) are < 2^-300.
        Nt = 70
        e1 = e2 = e3 = d1 = d2 = d3 = acb(0)
        p, prev = acb(1), None
        for n in range(Nt):
            e1 -= p/((n + 1)*(n + 2)); e2 += p/((n + 1)*(n + 2)*(n + 3)); e3 += p/(n + 1)
            if prev is not None:
                d1 += prev/((n + 1)*(n + 2)); d2 -= prev/((n + 1)*(n + 2)*(n + 3)); d3 -= prev/(n + 1)
            prev = p
            p = p*(-s)/(n + 1)
        tail = acb(arb(0, 2.0**-300), arb(0, 2.0**-300))
        e1, e2, e3, d1, d2, d3 = (x + tail for x in (e1, e2, e3, d1, d2, d3))
    else:
        E = (-s).exp()
        e1 = (1 - s - E)/s**2; e2 = (1 - s + s**2/2 - E)/s**3; e3 = (1 - E)/s
        d1 = (-1 + E)/s**2 - 2*(1 - s - E)/s**3
        d2 = (-1 + s + E)/s**3 - 3*(1 - s + s**2/2 - E)/s**4
        d3 = E/s - (1 - E)/s**2
    E = (-s).exp()
    zb = [acb(ev(zt)) for zt in z]
    g = [1/(s + zt) for zt in zb]
    al = [e1, e2, g[0], g[1], e3 + E*g[0], e3 + E*g[1]]
    da = [d1, d2, -g[0]**2, -g[1]**2, d3 - E*g[0] - E*g[0]**2, d3 - E*g[1] - E*g[1]**2]
    return al, da


def dist0(iv):
    lo, hi = iv
    return lo if lo > 0 else (-hi if hi < 0 else Q(0))


def F_bounds(B, rho, al, da):
    """Lower bound of |F| and upper bound of |dF/dk| over the box at one k."""
    # F = 1 - rho sum al_m P_m ;  dF/dk = -rho sum (i da_m) P_m
    reF = 1 - rho*B.comb_real([a.real for a in al])
    imF = -rho*B.comb_real([a.imag for a in al])
    idre = [(-a.imag) for a in da]               # Re(i da) = -Im da
    idim = [a.real for a in da]                  # Im(i da) =  Re da
    reD = -rho*B.comb_real(idre); imD = -rho*B.comb_real(idim)
    r, i = bounds(reF), bounds(imF)
    m2 = dist0(r)**2 + dist0(i)**2
    m = Q(math.isqrt(int(m2*2**96)), 2**48) if m2 > 0 else Q(0)          # <= sqrt(m2)
    dr, di = bounds(reD), bounds(imD)
    d = max(abs(dr[0]), abs(dr[1])) + max(abs(di[0]), abs(di[1]))
    return rdown(m, 24) if m > 0 else Q(0), rup(d, 24), (r, i)


def group_constants(B, rho_u, z):
    """Upper bounds |qp|, |A|, |W_t|, |C_t|, |q0| over U; L2; B2; tail K."""
    mags = [B.mag(m) for m in range(6)]
    up_ = [max(abs(a), abs(b)) for a, b in mags]
    q0 = bounds(B.comb_real([arb(-1), arb(1)/2, arb(1), arb(1), arb(1), arb(1)]))
    q0u = max(abs(q0[0]), abs(q0[1]))
    return [rup(v, 32) for v in up_], rup(q0u, 32)


def L2_of(up_, rho_u, zq):
    qp, A, W1, W2, C1, C2 = up_
    s = qp/12 + A/60
    for Wt, Ct, zt in ((W1, C1, zq[0]), (W2, C2, zq[1])):
        s += 2*Wt/zt**3 + Ct*(Q(1, 3) + 1/zt + 2/zt**2 + 2/zt**3)
    return rho_u*s


def H2_of(k, up_, rho_u, zq):
    qp, A, W1, W2, C1, C2 = up_
    s = qp*(1/k**2 + 6/k**3 + 12/k**4) + A*(2/k**3 + 12/k**4 + 24/k**5)
    for Wt, Ct, zt in ((W1, C1, zq[0]), (W2, C2, zq[1])):
        s += 2*Wt/k**3 + Ct*(zt/k**2 + (6 + 4*zt)/k**3 + 2*zt**2/k**4)
    return rho_u*s


def check_second_derivative_identities():
    s, zs = sp.symbols('s z', nonzero=True); E = sp.exp(-s)
    pairs = [((1 - s - E)/s**2, -E/s**2 - (2 + 4*E)/s**3 + 6*(1 - E)/s**4),
             ((1 - s + s**2/2 - E)/s**3, (1 - E)/s**3 - 6*(1 + E)/s**4 + 12*(1 - E)/s**5),
             ((1 - E)/s + E/(s + zs), -zs*E/(s*(s + zs)) - 2*zs*E*(2*s + zs)/(s**2*(s + zs)**2) + 2*E/(s + zs)**3 + 2*(1 - E)/s**3),
             (1/(s + zs), 2/(s + zs)**3)]
    assert all(sp.simplify(sp.diff(a, s, 2) - b) == 0 for a, b in pairs), 'second-derivative identity failed'


def tail_K(up_, q0u, rho_u, zq):
    qp, A, W1, W2, C1, C2 = up_
    B2 = 2*qp + A + zq[0]*(W1 + C1) + zq[1]*(W2 + C2)
    f = lambda K: rho_u*(q0u/K + B2/K**2 + 2*A/K**3)
    K = Q(1)
    while f(K) >= Q(1, 2):
        K *= 2
    lo, hi = K/2, K
    for _ in range(20):
        mid = (lo + hi)/2
        lo, hi = (lo, mid) if f(mid) < Q(1, 2) else (mid, hi)
    K = rup(hi, 16)
    assert f(K) < Q(1, 2)
    return K, B2


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
    src_sha = {n: hashlib.sha256((HERE/n).read_bytes()).hexdigest()
               for n in ('two_tail_first_loss.py', 'two_tail_py_chain.py', 'two_tail_m3_arb_recheck.py')}
    chain_path = HERE.parents[1]/'results'/'two_tail'/f'two_tail_py_chain_{name}.json.gz'
    craw = chain_path.read_bytes()
    ch = json.loads(gzip.decompress(craw))
    raw = SRC.read_bytes(); d = json.loads(raw)
    c = next(c for c in d['controls'] if c['name'] == ch['control'])
    assert ch['source_sha256'] == hashlib.sha256(raw).hexdigest()
    eta, z, w = sp.Rational(c['eta']), [sp.Rational(x) for x in c['z']], sp.Rational(c['w'])
    zq = [Q(int(x.p), int(x.q)) for x in z]
    tl = Q(c['rigorous_bracket']['lo']['tau'])
    V, P, rho_s = base_polys(eta, z)
    # consistency with the chain model and the Lean k = 0 identity
    V5, _, _, A5 = symbolic(eta, z, w)
    assert sp.expand(A5.subs(dict(zip(V5[:4], V))) - P[1]) == 0, 'A differs from the chain model'
    qp, A, W1, W2, C1, C2 = P
    F0 = 1 - rho_s*(-qp/2 + A/6 + W1/z[0] + W2/z[1] + C1*(1 + 1/z[0]) + C2*(1 + 1/z[1]))
    assert sp.simplify(sp.expand(F0 - A/(2*sp.pi))) == 0, 'F(u, 0) != A(u)/(2 pi) symbolically'
    check_second_derivative_identities()
    log('symbolic checks: A equals the chain model; F(u, 0) = A(u)/(2 pi) identically (scalar_fourierFactor_zero); '
        'the four second-derivative identities behind H2')
    polys = [TP(p, V) for p in P]
    rho_b = ev(rho_s); rho_iv = out(bounds(rho_b), 64); rho_u = rho_iv[1]
    # series / closed-form agreement at k = 1/2 (self-test of the coefficient functions)
    ctx_k = Q(1, 2)
    a1, b1 = alphas(ctx_k, z)
    s = acb(0, ball(ctx_k)); E = (-s).exp()
    for x, y in ((a1[0], (1 - s - E)/s**2), (a1[1], (1 - s + s**2/2 - E)/s**3), (b1[0], (-1 + E)/s**2 - 2*(1 - s - E)/s**3)):
        assert x.overlaps(y), 'series and closed form disagree'
    # required slabs: those whose A > 0 was certified (they cover the branch on [0, tau_lo])
    sl = ch['slabs']
    req = [j for j, s_ in enumerate(sl) if s_['A_required']]
    boxes = []
    for j in req:
        wj = sl[j]['w']; k = wj['k']; U5 = [None]*5
        Y = [tuple(map(P_, v)) for v in wj['Y']]; Pp = tuple(map(P_, wj['P']))
        for a, jj in enumerate([i for i in range(5) if i != k]):
            U5[jj] = Y[a]
        U5[k] = Pp
        boxes.append(U5[:4])
    log(f'{len(req)} required slabs (A certified > 0) cover the branch on [0, tau_lo]')

    def hull(js):
        return [(min(boxes[j][i][0] for j in js), max(boxes[j][i][1] for j in js)) for i in range(4)]

    # initial groups
    groups, cur = [], []
    for jj in range(len(req)):
        trial = cur + [jj]
        H = hull(trial)
        if cur and (len(trial) > GROUP_MAX or any(b - a > GROUP_SPAN*max(1, abs(a), abs(b)) for a, b in H)):
            groups.append(cur); cur = [jj]
        else:
            cur = trial
    groups.append(cur)
    log(f'{len(groups)} initial groups')
    records = []
    t0 = time.time()
    stack = [(g, Q(0)) for g in reversed(groups)]
    nsplit = 0
    while stack:
        g, kst = stack.pop()
        U = hull(g)
        B = Box(polys, U)
        up_, q0u = group_constants(B, rho_u, zq)
        L2 = L2_of(up_, rho_u, zq)
        K, B2 = tail_K(up_, q0u, rho_u, zq)
        ks, ms, ds = [kst], [], []
        k, ok = kst, True
        while k < K:
            al, da = alphas(k, z)
            m, dd, _ = F_bounds(B, rho_b, al, da)
            if m <= 0 or len(ms) >= MAX_STEPS:
                ok = False; break
            Lk = L2 if k == 0 else min(L2, H2_of(k, up_, rho_u, zq))
            hstar = (-dd + Q(math.isqrt(int((dd*dd + 2*Lk*m)*2**120))) / 2**60)/Lk if Lk > 0 else m/(dd + 1)
            h = rdown(THETA*hstar, 24)
            if not (m - dd*h - Lk*h*h/2 > 0) or h <= 0:
                ok = False; break
            knew = rdown(k + h, 48)
            if knew <= k:
                ok = False; break
            ms.append(m); ds.append(dd); ks.append(knew); k = knew
        rec = dict(slabs=[req[g[0]], req[g[-1]]], U=[DI(x) for x in U], k=[dy(x) for x in ks], m=[dy(x) for x in ms],
                   d=[dy(x) for x in ds], L2=dy(rup(L2, 32)), up=[dy(x) for x in up_], q0=dy(q0u), K=dy(K), B2=dy(rup(B2, 32)),
                   tail=ok)
        if not ok:
            # keep the covered part [kst, k], split and continue from k
            rec['k'] = rec['k'][:len(ms) + 1]
            if len(ms) > 0:
                records.append(rec)
            if len(g) == 1:
                log(f'FAIL: single slab {req[g[0]]} at k = {float(k):.6g}')
                raise SystemExit(2)
            half = len(g)//2
            stack.append((g[half:], k)); stack.append((g[:half], k))
            nsplit += 1
            continue
        records.append(rec)
        if len(records) % 20 == 0 or not stack:
            log(f'  group slabs {req[g[0]]}..{req[g[-1]]}: k from {float(kst):.4g} to K = {float(K):.4g} in {len(ms)} steps '
                f'(L2 {float(L2):.3g}, min m {float(min(ms)) if ms else float("nan"):.3g}); {len(records)} records, {nsplit} splits, '
                f'{time.time() - t0:.0f} s')
    nsteps = sum(len(r['m']) for r in records)
    log(f'\n{len(records)} records ({sum(r["tail"] for r in records)} with tail), {nsplit} splits, {nsteps} k steps')
    log(f"RESULT: PASS -- for every certified slab box on [0, tau_lo] and every real k, F(u, k) != 0; with the Lean "
        f"interface canonical_path_of_physical_factor_units and seed canonicity, the PY-seeded branch is fully canonical "
        f"on [0, tau_lo], so its first loss of full canonicity lies in (tau_lo, tau_hi).")
    rec = dict(command=cmd, label='EXTERNAL Arb interval certificate; NOT a Lean proof',
               serialization="Numbers are exact: 'm p e' = m*2^e, otherwise a rational a/b.",
               control=c['name'], data=dict(eta=c['eta'], z=c['z'], w=c['w'], sigma='1', rho='6*eta/pi'),
               rho_enclosure=DI(rho_iv), chain=str(chain_path), chain_sha256=hashlib.sha256(craw).hexdigest(),
               source=str(SRC), source_sha256=hashlib.sha256(raw).hexdigest(), script_sha256=src_sha,
               lean_sha256={str(p.relative_to(HERE.parents[2])): hashlib.sha256(p.read_bytes()).hexdigest() for p in LEAN},
               versions=dict(python=sys.version.split()[0], python_flint=flint.__version__, sympy=sp.__version__),
               precision_bits=PREC, required_slabs=req, records=records,
               counts=dict(records=len(records), splits=nsplit, k_steps=nsteps), passed=True)
    with gzip.open(outp, 'wt') as fh:
        json.dump(rec, fh, separators=(',', ':'))
    return 0


if __name__ == '__main__':
    sys.exit(main())
