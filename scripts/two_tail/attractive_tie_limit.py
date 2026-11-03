"""Exact first correction to Lam = sqrt 3 in the weak-tail limit, pure fluid (float64 evidence, NOT a Lean proof).

In (D, P = G D) the factors F_t and S_t are affine, so the system is D_t F_t = tau k_t, 2 pi P_t F_t = D_t S_t.
Take strong tails s and one weak tail w, r = k_w/k_s -> 0, kappa = tau k_s. Write y = D_w, p = P_w. The strong tails solve
Phi(q; y, p, kappa) = 0, q = (D_s, P_s), which defines g(kappa, y, p) = F_w and h(kappa, y, p) = S_w. The weak tail reads
    g = r kappa / y,     p = h y^2 / (2 pi r kappa).
A near tie exists wherever g(kappa, 0, 0) reaches 0 at kappa_1 before the fold of the strong curve. With t = kappa_1 - kappa,
c = -g_kappa, gamma = -g_p > 0, h1 = h(kappa_1, 0, 0), bhat = gamma h1/(2 pi kappa_1), the scales are y ~ r^(2/3), t, p ~ r^(1/3):
    c t = r kappa_1/y + (bhat/r) y^2 + next order.
The next order is of relative size r^(1/3) and has terms y, y^4/r^2, r^2/y^2, which all take the same value class at the three
critical points y_c w^j, w^3 = 1, y_c^3 = r^2 kappa_1/(2 bhat), so they act as one coefficient a y. In the variable ln(kappa_1/kappa),
which is what Lam reads (Lam = cot(direction) + gap at this order),
    a = -g_y + (gamma h1/(4 pi)) Xi,
    Xi = 3/(2 c kappa_1) - 9 g_kk/(2 c^2) - 3 h_k/(c h1) + h_p/(gamma h1) + 3 g_kp/(c gamma) - g_pp/(2 gamma^2),
    Lam - sqrt 3 = Lambda r^(1/3) + O(r^(2/3)),  Lambda = 2 sqrt 3 a / (3 bhat^(2/3) (kappa_1/2)^(1/3)),
    gap = Gamma r^(1/3),  Gamma = 3 sqrt 3 bhat^(1/3) (kappa_1/2)^(2/3) / (c kappa_1).
So Lam < sqrt 3 at small r exactly where Lambda < 0, a function of (z_w, z_s, eta) alone for one strong tail. Control: Lam and gap of
real two-tail states from the exact branch points of attractive_pair_fast, as r decreases.

Usage: attractive_tie_limit.py --control | --control3 | --signs N | --grid N | --minutes M [--workers W] [--seed S] [--strong NS] [--random]
"""
import sys, time, warnings
import numpy as np
from multiprocessing import Pool
from scipy.optimize import minimize, brentq
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import attractive_pair_fast as AF
warnings.simplefilter('ignore')
R3 = np.sqrt(3.0)


class Affine:
    """F_t, S_t as exact affine functions of (D, P); index tails from 0, last tail index = weak."""
    def __init__(self, z, eta):
        self.z = z = np.asarray(z, float); self.T = T = len(z); self.eta = eta; self.rho = rho = 6*eta/np.pi
        d = 2*np.pi/(1 - eta)**2
        self.A0, self.B0, self.QP0 = d*((1 - eta) + 3*eta), d*(-1.5*eta), d*(1.5*eta + (1 - eta))
        F0, S0 = self.fs(np.zeros(2*T)); self.F0, self.S0 = F0, S0
        self.FV = np.array([self.fs(e)[0] - F0 for e in np.eye(2*T)]).T
        self.SV = np.array([self.fs(e)[1] - S0 for e in np.eye(2*T)]).T

    def fs(self, v):
        T, z, rho = self.T, self.z, self.rho; D, P = v[:T], v[T:]
        Ct = D - 2*np.pi*rho*P*np.exp(-z)/z; Wt = (2*np.pi/z)*rho*P
        Mv = -np.sum(rho*(Wt + (1 + z)*Ct)/z); Nc = np.sum(rho*(Wt/z**2 + (1 + z + z**2/2)/z**2*Ct))
        A = self.A0*(1 + Mv) - 4*self.B0*Nc; qp = self.QP0*(1 + Mv) + self.A0*Nc
        F, S = np.zeros(T), np.zeros(T)
        for t in range(T):
            x = z[t]
            Q = AF.phi1(x)*qp + AF.phi2(x)*A + np.sum(Wt/(x + z) + Ct*(np.exp(-x)/(x + z) + AF.exprel(x)))
            F[t] = 1 - rho*Q; S[t] = (A + x*qp + np.sum((x**2*z/(x + z))*Ct))/x**2
        return F, S


def strong_curve(f):
    """One strong tail (index 1), weak index 0: D grid along the physical root, up to the strong fold. Returns (D, P, kappa, F1) arrays."""
    i, w = 1, 0; T = 2
    a0, a1, a2 = f.F0[i], f.FV[i, i], f.FV[i, T + i]; b0, b1, b2 = f.S0[i], f.SV[i, i], f.SV[i, T + i]
    D = np.exp(np.linspace(np.log(1e-9), np.log(1e7), 6001))
    A = 2*np.pi*a2; B = 2*np.pi*(a0 + a1*D) - b2*D; C = -D*(b0 + b1*D)
    disc = B*B - 4*A*C
    P = -2*C/(B + np.sqrt(np.maximum(disc, 0)))
    bad = np.where((disc < 0) | (B + np.sqrt(np.maximum(disc, 0)) <= 0))[0]
    end = bad[0] if len(bad) else len(D)
    D, P = D[:end], P[:end]
    Fi = a0 + a1*D + a2*P; kap = D*Fi
    up = np.where(np.diff(kap) <= 0)[0]
    if len(up): end = up[0] + 1; D, P, kap = D[:end + 1], P[:end + 1], kap[:end + 1]
    Fw = f.F0[w] + f.FV[w, i]*D + f.FV[w, T + i]*P
    return D, P, kap, Fw


def tie(z_w, z_s, eta):
    """Quantities of the limit at the first zero of F_w on the strong curve; None if F_w stays positive up to the strong fold."""
    f = Affine([z_w, z_s], eta); i, w = 1, 0; T = 2
    a0, a1, a2 = f.F0[i], f.FV[i, i], f.FV[i, T + i]; b0, b1, b2 = f.S0[i], f.SV[i, i], f.SV[i, T + i]
    D, P, kap, Fw = strong_curve(f)
    if f.F0[w] <= 0 or len(D) < 3: return None
    cr = np.where(Fw <= 0)[0]
    if not len(cr): return None
    j = cr[0]
    if j == 0: return None
    def Pof(d):
        A = 2*np.pi*a2; B = 2*np.pi*(a0 + a1*d) - b2*d; C = -d*(b0 + b1*d)
        return -2*C/(B + np.sqrt(max(B*B - 4*A*C, 0.0)))
    d1 = brentq(lambda d: f.F0[w] + f.FV[w, i]*d + f.FV[w, T + i]*Pof(d), D[j - 1], D[j], xtol=1e-14*D[j], rtol=1e-14)
    p1 = Pof(d1); k1 = d1*(a0 + a1*d1 + a2*p1)
    # coordinates Z = (D_s, P_s, y, p, kappa)
    FsG = np.array([f.FV[i, i], f.FV[i, T + i], f.FV[i, w], f.FV[i, T + w], 0.0])
    SsG = np.array([f.SV[i, i], f.SV[i, T + i], f.SV[i, w], f.SV[i, T + w], 0.0])
    FwG = np.array([f.FV[w, i], f.FV[w, T + i], f.FV[w, w], f.FV[w, T + w], 0.0])
    SwG = np.array([f.SV[w, i], f.SV[w, T + i], f.SV[w, w], f.SV[w, T + w], 0.0])
    Z = np.array([d1, p1, 0.0, 0.0, k1]); Fs = a0 + a1*d1 + a2*p1; Ss = b0 + b1*d1 + b2*p1
    e = np.eye(5)
    grad1 = e[0]*Fs + d1*FsG - e[4]; grad2 = 2*np.pi*(e[1]*Fs + p1*FsG) - (e[0]*Ss + d1*SsG)
    H1 = np.outer(e[0], FsG) + np.outer(FsG, e[0])
    H2 = 2*np.pi*(np.outer(e[1], FsG) + np.outer(FsG, e[1])) - (np.outer(e[0], SsG) + np.outer(SsG, e[0]))
    Jq = np.array([grad1[:2], grad2[:2]])
    if abs(np.linalg.det(Jq)) < 1e-14: return None
    tang = {}
    for name, idx in (('y', 2), ('p', 3), ('k', 4)):
        qa = -np.linalg.solve(Jq, np.array([grad1[idx], grad2[idx]]))
        v = np.zeros(5); v[:2] = qa; v[idx] = 1.0; tang[name] = v
    def second(a, b):
        va, vb = tang[a], tang[b]
        qab = -np.linalg.solve(Jq, np.array([va @ H1 @ vb, va @ H2 @ vb]))
        return qab
    g = lambda a: FwG @ tang[a]; h = lambda a: SwG @ tang[a]
    g2 = lambda a, b: FwG[:2] @ second(a, b); h1 = f.S0[w] + f.SV[w, i]*d1 + f.SV[w, T + i]*p1
    c = -g('k'); gamma = -g('p')
    out = dict(k1=k1, d1=d1, p1=p1, c=c, gamma=gamma, h1=h1, kmax=kap[-1], g_y=g('y'), g_kk=g2('k', 'k'), g_kp=g2('k', 'p'), g_pp=g2('p', 'p'), h_k=h('k'), h_p=h('p'))
    if c <= 0 or gamma <= 0 or h1 <= 0: out['ok'] = False; return out
    Xi = 3/(2*c*k1) - 9*out['g_kk']/(2*c*c) - 3*out['h_k']/(c*h1) + out['h_p']/(gamma*h1) + 3*out['g_kp']/(c*gamma) - out['g_pp']/(2*gamma*gamma)
    a = -out['g_y'] + gamma*h1/(4*np.pi)*Xi
    bhat = gamma*h1/(2*np.pi*k1)
    out.update(ok=True, Xi=Xi, a=a, bhat=bhat, Lambda=2*R3*a/(3*bhat**(2/3)*(k1/2)**(1/3)), Gamma=3*R3*bhat**(1/3)*(k1/2)**(2/3)/(c*k1))
    return out


def tie_multi(z_w, zs, m, eta):
    """Same limit with several strong tails, k_s = m_s k_ref, kappa = tau k_ref: the strong curve is traced from kappa -> 0 with Newton steps
    in kappa, stopping at its fold (det of the Jacobian changes sign, or the step collapses) or at the first zero of F_w."""
    ns = len(zs); T = ns + 1; f = Affine(np.r_[z_w, zs], eta); S = np.arange(1, T); m = np.asarray(m, float)
    if f.F0[0] <= 0 or np.any(f.F0[1:] <= 0): return None
    def col(X): return np.r_[X[S], X[T + S], X[0], X[T], 0.0]
    gF = [col(f.FV[s]) for s in S]; gS = [col(f.SV[s]) for s in S]; gFw, gSw = col(f.FV[0]), col(f.SV[0])
    n = 2*ns; I = np.eye(n + 3)
    def parts(q, y=0.0, p=0.0):
        Z = np.r_[q, y, p]
        return np.array([f.F0[s] + gF[i][:n + 2] @ Z for i, s in enumerate(S)]), np.array([f.S0[s] + gS[i][:n + 2] @ Z for i, s in enumerate(S)])
    def system(q, kap):
        Fs, Ss = parts(q); D, P = q[:ns], q[ns:]
        return np.r_[D*Fs - kap*m, 2*np.pi*P*Fs - D*Ss]
    def full_jac(q):
        """Rows: gradient of Phi in Z = (q, y, p, kappa)."""
        Fs, Ss = parts(q); D, P = q[:ns], q[ns:]; A = np.zeros((n, n + 3))
        for i in range(ns):
            A[i] = I[i]*Fs[i] + D[i]*gF[i] - I[n + 2]*m[i]
            A[ns + i] = 2*np.pi*(I[ns + i]*Fs[i] + P[i]*gF[i]) - (I[i]*Ss[i] + D[i]*gS[i])
        return A
    def newton(q, kap):
        for _ in range(12):
            r = system(q, kap); dq = np.linalg.solve(full_jac(q)[:, :n], -r); q = q + dq
            if not np.all(np.isfinite(q)): return q, False
            if np.linalg.norm(dq) < 1e-13*(1 + np.linalg.norm(q)): return q, True
        return q, False
    Fw = lambda q: f.F0[0] + gFw[:n] @ q
    kap = 1e-6; D0 = kap*m/f.F0[S]; q = np.r_[D0, D0*f.S0[S]/(2*np.pi*f.F0[S])]; q, ok = newton(q, kap)
    if not ok: return None
    sgn = np.sign(np.linalg.det(full_jac(q)[:, :n])); dl = 0.2; steps = 0
    while steps < 2000 and dl > 1e-7:
        steps += 1
        kn = kap*(1 + dl); A = full_jac(q); pred = q + np.linalg.solve(A[:, :n], m_col(A, n))*(kn - kap)
        qn, ok = newton(pred, kn)
        # component by component: a norm is blind to a middle tail whose D is small, and a jump there lands on another branch
        if not ok or np.any(np.abs(qn - pred) > 0.02*np.abs(qn)) or np.any(np.abs(qn - q) > 0.25*np.abs(qn)) or np.any(qn <= 0): dl /= 2; continue
        if np.sign(np.linalg.det(full_jac(qn)[:, :n])) != sgn: dl /= 2; continue
        if Fw(qn) <= 0: break
        q, kap = qn, kn; dl = min(dl*1.3, 0.1)
    else:
        return None
    if steps >= 2000: return None
    a, b = kap, kn; qa, qb = q, qn
    for _ in range(80):
        x = a + (b - a)*Fw(qa)/(Fw(qa) - Fw(qb)); x = x if a < x < b else (a + b)/2
        qx, ok = newton(qa + (qb - qa)*(x - a)/(b - a), x)
        if not ok: return None
        if Fw(qx) > 0: a, qa = x, qx
        else: b, qb = x, qx
        if abs(Fw(qx)) < 1e-13 or b - a < 1e-14*b: break
    k1, q1 = x, qx
    A = full_jac(q1); Jq = A[:, :n]
    H = np.zeros((n, n + 3, n + 3))
    for i in range(ns):
        H[i] = np.outer(I[i], gF[i]) + np.outer(gF[i], I[i])
        H[ns + i] = 2*np.pi*(np.outer(I[ns + i], gF[i]) + np.outer(gF[i], I[ns + i])) - (np.outer(I[i], gS[i]) + np.outer(gS[i], I[i]))
    tang = {}
    for name, idx in (('y', n), ('p', n + 1), ('k', n + 2)):
        v = np.zeros(n + 3); v[:n] = -np.linalg.solve(Jq, A[:, idx]); v[idx] = 1.0; tang[name] = v
    second = lambda a, b: -np.linalg.solve(Jq, np.array([tang[a] @ H[i] @ tang[b] for i in range(n)]))
    g = lambda a: gFw @ tang[a]; h = lambda a: gSw @ tang[a]; g2 = lambda a, b: gFw[:n] @ second(a, b)
    c, gamma = -g('k'), -g('p'); h1 = f.S0[0] + gSw[:n] @ q1
    out = dict(k1=k1, c=c, gamma=gamma, h1=h1, kmax=np.nan, g_y=g('y'), g_kk=g2('k', 'k'), g_kp=g2('k', 'p'), g_pp=g2('p', 'p'), h_k=h('k'), h_p=h('p'))
    if c <= 0 or gamma <= 0 or h1 <= 0: out['ok'] = False; return out
    Xi = 3/(2*c*k1) - 9*out['g_kk']/(2*c*c) - 3*out['h_k']/(c*h1) + out['h_p']/(gamma*h1) + 3*out['g_kp']/(c*gamma) - out['g_pp']/(2*gamma*gamma)
    a_ = -out['g_y'] + gamma*h1/(4*np.pi)*Xi; bhat = gamma*h1/(2*np.pi*k1)
    out.update(ok=True, Xi=Xi, a=a_, bhat=bhat, Lambda=2*R3*a_/(3*bhat**(2/3)*(k1/2)**(1/3)), Gamma=3*R3*bhat**(1/3)*(k1/2)**(2/3)/(c*k1))
    return out


def m_col(A, n):
    """dq/dkappa right side: -dPhi/dkappa."""
    return -A[:, n + 2]


def exact3(z_w, zs, m, r, eta):
    """Exact Lam, gap at weak strength r = k_w/k_ref."""
    z = np.r_[z_w, zs]; K = np.r_[r*z_w, np.asarray(m)*np.asarray(zs)]
    A = AF.analyse(z, K/np.max(K), eta, {})
    if A['tf'] is None: return None
    L = [(np.log(p[0])/abs(np.angle(p[1])), p) for p in A['pts'] if abs(p[1].imag) > 1e-12*abs(p[1])]
    if not L: return None
    lam, p = min(L, key=lambda v: v[0])
    return lam, abs(1 - p[1]/A['tf']), np.degrees(np.angle(p[1]/A['tf'] - 1))


def control3():
    q1, q2 = tie(1.0722, 56.33, .79), tie_multi(1.0722, [56.33], [1.0], .79)
    print(f'one strong tail by both routes: Lambda {q1["Lambda"]:.9g} {q2["Lambda"]:.9g}, kappa_1 {q1["k1"]:.9g} {q2["k1"]:.9g}', flush=True)
    for zw, zs, m, e in [(1.0, [20., 60.], [1.0, 1.0], .4), (.8, [5., 40.], [.3, 1.0], .25), (2.0, [30., 200.], [1.0, .2], .15)]:
        q = tie_multi(zw, zs, m, e)
        if q is None or not q.get('ok'): print(f'z_w={zw} z_s={zs} m={m} eta={e}: no tie {q}', flush=True); continue
        print(f'z_w={zw} z_s={zs} m={m} eta={e}: kappa_1={q["k1"]:.6g} a={q["a"]:.5g} Lambda={q["Lambda"]:.5g} Gamma={q["Gamma"]:.5g}', flush=True)
        for r in (1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8):
            X = exact3(zw, zs, m, r, e)
            if X is None: print(f'   r={r:.0e}: no exact pair', flush=True); continue
            print(f'   r={r:.0e}: exact Lam-sqrt3={X[0] - R3:+.3e} gap={X[1]:.4e} dir={X[2]:.3f}; limit Lam-sqrt3={q["Lambda"]*r**(1/3):+.3e} gap={q["Gamma"]*r**(1/3):.4e}', flush=True)


def search3(args):
    wid, seed, minutes, ns = args
    rng = np.random.default_rng([seed, wid, ns]); end = time.time() + 60*minutes; n = t = neg = 0; best = (np.inf, None); bad = []
    def f(q):
        nonlocal n, t, neg, best
        if time.time() > end: raise TimeoutError
        zw, zs, m, e = np.exp(q[0]), np.exp(q[1:1 + ns]), np.r_[1.0, np.exp(q[1 + ns:2*ns])], q[2*ns]
        if not (1e-3 < e < .8) or not (.01 < zw < 5000) or np.any(zs < .01) or np.any(zs > 5000) or np.any(m < 1e-6) or np.any(m > 1e6): return 1e3
        try: o = tie_multi(zw, zs, m, e)
        except np.linalg.LinAlgError: return 1e3
        n += 1
        if o is None or not o.get('ok'): return 1e3
        t += 1; v = o['Lambda']/o['Gamma']; rec = (float(zw), zs.tolist(), m.tolist(), float(e), o['Lambda'], o['Gamma'], o['a'], o['k1'])
        if o['a'] < 0:
            neg += 1
            if len(bad) < 20: bad.append(rec)
        if v < best[0]: best = (v, rec)
        return v
    try:
        while True:
            q = np.r_[rng.uniform(np.log(.01), np.log(5000), 1 + ns), rng.uniform(np.log(1e-6), np.log(1e6), ns - 1), rng.uniform(.001, .8)]
            if f(q) < 1e3: minimize(f, q, method='Nelder-Mead', options=dict(maxiter=400, xatol=1e-5, fatol=1e-7))
    except TimeoutError:
        pass
    print(f'worker {wid}: {n} evaluations, {t} ties, {neg} with a < 0; smallest Lambda/Gamma {best[0]:.6g} at (z_w, z_s, m, eta, Lambda, Gamma, a, kappa_1) = {best[1]}; first negatives {bad[:3]}', flush=True)
    return n, t, neg, best


def random3(args):
    """No descent: uniform samples, half of them with a middle tail whose rate is within 20 % of z_w, the region descents do not stay in."""
    wid, seed, minutes, ns = args
    rng = np.random.default_rng([seed, wid, ns, 77]); end = time.time() + 60*minutes; n = t = neg = 0; best = (np.inf, None); bad = []; near = 0
    while time.time() < end:
        zw = np.exp(rng.uniform(np.log(.01), np.log(100))); zs = np.exp(rng.uniform(np.log(.01), np.log(5000), ns)); m = np.r_[1.0, np.exp(rng.uniform(np.log(1e-6), np.log(1e6), ns - 1))]; e = rng.uniform(.001, .8)
        close = rng.random() < 0.5
        if close: zs[0] = zw*np.exp(rng.uniform(-.2, .2))
        try: o = tie_multi(zw, zs, m, e)
        except np.linalg.LinAlgError: continue
        n += 1
        if o is None or not o.get('ok'): continue
        t += 1; near += close; v = o['Lambda']/o['Gamma']; rec = (float(zw), zs.tolist(), m.tolist(), float(e), o['Lambda'], o['Gamma'], o['a'], o['k1'])
        if o['a'] < 0:
            neg += 1
            if len(bad) < 20: bad.append(rec)
        if v < best[0]: best = (v, rec)
    print(f'worker {wid}: {n} samples, {t} ties ({near} with a middle tail near z_w), {neg} with a < 0; smallest Lambda/Gamma {best[0]:.6g} at {best[1]}; first negatives {bad[:3]}', flush=True)
    return n, t, neg, best


def signs(N):
    """Do the sign conditions of the limit hold, and is a a sum of terms of one sign? Random one-strong-tail states, no descent."""
    rng = np.random.default_rng(7); none = ok = past = other = 0; lo = dict(c=np.inf, gamma=np.inf, h1=np.inf)
    names = ['-g_y', '3/(2 c k1)', '-9 g_kk/(2 c^2)', '-3 h_k/(c h1)', 'h_p/(gamma h1)', '3 g_kp/(c gamma)', '-g_pp/(2 gamma^2)']; neg = np.zeros(7); pos = np.zeros(7)
    for _ in range(N):
        zw, zs = np.exp(rng.uniform(np.log(.01), np.log(5000), 2)); e = rng.uniform(.001, .8); q = tie(zw, zs, e)
        if q is None: none += 1; continue
        if not q.get('ok'):
            f = Affine([zw, zs], e); D, P, kap, _ = strong_curve(f); i = int(np.argmax(kap))
            a0, a1, a2 = f.F0[1], f.FV[1, 1], f.FV[1, 3]; b0, b1, b2 = f.S0[1], f.SV[1, 1], f.SV[1, 3]
            d = np.linspace(D[i - 1], D[-1], 200001); A = 2*np.pi*a2; B = 2*np.pi*(a0 + a1*d) - b2*d; C = -d*(b0 + b1*d)
            p = -2*C/(B + np.sqrt(np.maximum(B*B - 4*A*C, 0))); df = d[np.argmax(d*(a0 + a1*d + a2*p))]
            if q['d1'] > df: past += 1
            else: other += 1
            continue
        ok += 1
        for k in lo: lo[k] = min(lo[k], q[k])
        c, g, h1, k1 = q['c'], q['gamma'], q['h1'], q['k1']; pre = g*h1/(4*np.pi)
        t = np.array([-q['g_y'], pre*3/(2*c*k1), -pre*9*q['g_kk']/(2*c*c), -pre*3*q['h_k']/(c*h1), pre*q['h_p']/(g*h1), pre*3*q['g_kp']/(c*g), -pre*q['g_pp']/(2*g*g)])
        pos += t > 0; neg += t < 0
    print(f'{N} samples: no tie {none}, tie with c, gamma, h1 > 0: {ok}; F_w = 0 only past the strong fold (grid end, c and gamma < 0): {past}; any other failure of the sign conditions: {other}; smallest c, gamma, h1 {lo}', flush=True)
    for i, nm in enumerate(names): print(f'   term {nm}: positive {int(pos[i])}, negative {int(neg[i])}', flush=True)


def false_candidates():
    """Three states the first tracer reported with a < 0. Its step test used a norm, blind to a middle tail with small D, so it jumped branches."""
    for zw, zs, m, e in [(0.49407682645734047, [0.4792503921853161, 38.68519985197134], [1.0, 23311.35181554655], 0.3558289608494153),
                         (0.9629086293094512, [4.5697130797984755, 65.04128554817328, 0.950792361692655], [1.0, 57325.14141539844, 6.071233766700462], 0.15422826892958158),
                         (0.4005846519999247, [0.40131905420700426, 1256.6711496937978, 712.0285465506996], [1.0, 0.0003483170113235569, 216480.00876374624], 0.40734679928109374)]:
        print(f'former a < 0 candidate z_w={zw:.5f} z_s={np.round(zs, 4).tolist()} m={np.round(m, 6).tolist()} eta={e:.5f}: fixed tracer gives {tie_multi(zw, zs, m, e)}', flush=True)
    zw, zs, m, e = 0.49407682645734047, [0.4792503921853161, 38.68519985197134], np.array([1.0, 23311.35181554655]), 0.3558289608494153
    f = Affine(np.r_[zw, zs], e)
    def FS(q):
        v = np.zeros(6); v[1:3] = q[:2]; v[4:6] = q[2:]; return f.F0 + f.FV @ v, f.S0 + f.SV @ v
    def sy(q, k):
        F, Sv = FS(q); return np.r_[q[:2]*F[1:] - k*m, 2*np.pi*q[2:]*F[1:] - q[:2]*Sv[1:]]
    def J(q, k):
        A = np.zeros((4, 4))
        for i in range(4):
            d = np.zeros(4); d[i] = 1e-7*(1 + abs(q[i])); A[:, i] = (sy(q + d, k) - sy(q - d, k))/(2*d[i])
        return A
    D0 = 1e-7*m/f.F0[1:]; q = np.r_[D0, D0*f.S0[1:]/(2*np.pi*f.F0[1:])]; last = None
    for k in np.exp(np.linspace(np.log(1e-7), np.log(3e-4), 4001)):
        for _ in range(30):
            dq = np.linalg.solve(J(q, k), -sy(q, k)); q = q + dq
            if np.linalg.norm(dq) < 1e-12*(1 + np.linalg.norm(q)): break
        F, _ = FS(q)
        if F[0] < 0 or F[1] < 0: print(f'first candidate, fine direct trace: last kappa with both F > 0 {last[0]:.5e}, F_w {last[1]:.4f}, F_m {last[2]:.4f}; next kappa {k:.5e}, F_w {F[0]:.4f}, F_m {F[1]:.4f} (the old tracer reported kappa_1 = 1.768e-04)', flush=True); break
        last = (k, F[0], F[1])


def exact(z_w, z_s, Kw_over_Ks, eta):
    """Lam, gap, direction of the closest principal-sheet pair of the real state, from the branch points."""
    z = np.array([z_w, z_s]); K = np.array([Kw_over_Ks, 1.0])
    A = AF.analyse(z, K, eta, {})
    if A['tf'] is None: return None
    L = [(np.log(p[0])/abs(np.angle(p[1])), p) for p in A['pts'] if abs(p[1].imag) > 1e-12*abs(p[1])]
    if not L: return None
    lam, p = min(L, key=lambda v: v[0]); tf = A['tf']
    return lam, abs(1 - p[1]/tf), np.degrees(np.angle(p[1]/tf - 1)), tf


def control():
    for zw, zs, e in [(1.0722, 56.33, .79), (2.6429, 56.529, .2641), (1.7218, 232.82, .3309), (.9374, 29.4236, .1169), (.5, 20., .5)]:
        q = tie(zw, zs, e)
        if q is None or not q.get('ok'): print(f'z=({zw},{zs}) eta={e}: no tie, {q}', flush=True); continue
        print(f'z=({zw},{zs}) eta={e}: kappa_1={q["k1"]:.6g} (strong fold {q["kmax"]:.6g}) c={q["c"]:.4g} gamma={q["gamma"]:.4g} h1={q["h1"]:.4g} a={q["a"]:.5g} Lambda={q["Lambda"]:.5g} Gamma={q["Gamma"]:.5g}', flush=True)
        for w in (1e-4, 1e-5, 1e-6, 1e-7, 1e-8, 1e-9, 1e-10):
            r = w*zs/zw; X = exact(zw, zs, w, e)
            if X is None: print(f'   K_w/K_s={w:.0e}: no exact pair', flush=True); continue
            lam, gap, dirn, tf = X; pr = q['Lambda']*r**(1/3); pg = q['Gamma']*r**(1/3)
            print(f'   K_w/K_s={w:.0e} r^(1/3)={r**(1/3):.4f}: exact Lam-sqrt3={lam - R3:+.3e} gap={gap:.4e} dir={dirn:.3f}; limit Lam-sqrt3={pr:+.3e} gap={pg:.4e}; tau_f k_s/kappa_1={tf*2*np.pi/zs/q["k1"]:.5f}', flush=True)


def grid(N):
    zs = np.exp(np.linspace(np.log(.05), np.log(1000), N)); es = np.linspace(.01, .79, max(N//3, 3))
    tot = ties = neg = 0; best = (np.inf, None)
    for e in es:
        for a in zs:
            for b in zs:
                if a == b: continue
                q = tie(a, b, e); tot += 1
                if q is None or not q.get('ok'): continue
                ties += 1
                if q['a'] < 0: neg += 1
                nor = q['Lambda']/q['Gamma']
                if nor < best[0]: best = (nor, (a, b, e, q['Lambda'], q['Gamma'], q['a'], q['k1'], q['kmax']))
    print(f'grid: {tot} (z_w, z_s, eta), {ties} with a tie, {neg} with a < 0; smallest Lambda/Gamma {best[0]:.6g} at (z_w, z_s, eta, Lambda, Gamma, a, kappa_1, strong fold) = {best[1]}', flush=True)


def search(args):
    wid, seed, minutes = args
    rng = np.random.default_rng([seed, wid]); end = time.time() + 60*minutes; n = t = neg = 0; best = (np.inf, None); bad = []
    def f(q):
        nonlocal n, t, neg, best
        if time.time() > end: raise TimeoutError
        a, b, e = np.exp(q[0]), np.exp(q[1]), q[2]
        if not (1e-3 < e < .8) or not (.01 < a < 5000) or not (.01 < b < 5000): return 1e3
        o = tie(a, b, e); n += 1
        if o is None or not o.get('ok'): return 1e3
        t += 1; v = o['Lambda']/o['Gamma']
        if o['a'] < 0:
            neg += 1
            if len(bad) < 20: bad.append((a, b, e, o['Lambda'], o['Gamma'], o['a'], o['k1'], o['kmax']))
        if v < best[0]: best = (v, (float(a), float(b), float(e), o['Lambda'], o['Gamma'], o['a'], o['k1'], o['kmax']))
        return v
    try:
        while True:
            q = np.r_[rng.uniform(np.log(.01), np.log(5000), 2), rng.uniform(.001, .8)]
            if f(q) < 1e3: minimize(f, q, method='Nelder-Mead', options=dict(maxiter=400, xatol=1e-5, fatol=1e-7))
    except TimeoutError:
        pass
    print(f'worker {wid}: {n} evaluations, {t} ties, {neg} with a < 0; smallest Lambda/Gamma {best[0]:.6g} at (z_w, z_s, eta, Lambda, Gamma, a, kappa_1, strong fold) = {best[1]}; first negatives {bad[:3]}', flush=True)
    return n, t, neg, best


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)', flush=True)
    val = lambda f, d: type(d)(sys.argv[sys.argv.index(f) + 1]) if f in sys.argv else d
    if '--signs' in sys.argv: signs(val('--signs', 20000))
    if '--control3' in sys.argv: control3(); false_candidates()
    elif '--control' in sys.argv: control()
    if '--grid' in sys.argv: grid(val('--grid', 20))
    if '--minutes' in sys.argv and '--strong' in sys.argv:
        W, seed, ns = val('--workers', 16), val('--seed', 1), val('--strong', 2)
        with Pool(W) as ex: res = ex.map(random3 if '--random' in sys.argv else search3, [(i, seed, val('--minutes', 5.0), ns) for i in range(W)], chunksize=1)
        b = min(res, key=lambda r: r[3][0])[3]
        print(f'== total {sum(r[0] for r in res)} evaluations, {sum(r[1] for r in res)} ties, {sum(r[2] for r in res)} with a < 0; smallest Lambda/Gamma {b[0]:.6g} at {b[1]}', flush=True)
    elif '--minutes' in sys.argv:
        W, seed = val('--workers', 16), val('--seed', 1)
        with Pool(W) as ex: res = ex.map(search, [(i, seed, val('--minutes', 5.0)) for i in range(W)], chunksize=1)
        b = min(res, key=lambda r: r[3][0])[3]
        print(f'== total {sum(r[0] for r in res)} evaluations, {sum(r[1] for r in res)} ties, {sum(r[2] for r in res)} with a < 0; smallest Lambda/Gamma {b[0]:.6g} at {b[1]}', flush=True)
