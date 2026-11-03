"""FLOAT diagnostics of the endpoint fiber {BH roots at tau = beta}, for one species and two tails.

Requested by Codex (handoff 134).  This is NOT a finiteness, isolation or multiplicity certificate:
a finite set of numerical path endpoints cannot exclude other components or nonisolated real roots,
and a rank-deficient Jacobian also occurs at isolated multiple roots.

The residual is transcribed literally from the frozen Lean definitions (MSAMultiTailMixtureSystem:
firstLHS / secondLHS / secondRHS / dressedQhat / Qhat; MSAMixtureCancellation: gam, Ct, Wt;
MSAMixtureConcrete: mixM, mixN, mixDA, mixDqp; MatrixQ0: Q0phys, Qppphys) at N = 1, edgeLo = 0,
edgeHi = sigma.  Unknowns u = (Dt_1, Dt_2, G_1, G_2); every equation is a cubic polynomial in u,
so a total-degree homotopy has 3^4 = 81 paths.  The transcription is checked against
msa_exact_mix._residuals at the traced root and at random points.

beta for each control:
  k=0 crossing: bisected on the sign of det F(0) along the traced branch (seeded re-solves);
  M2 touch: tau_touch of the 10-equation locator (Codex 009/011), not a sign change;
  otherwise the detector value is reported and FLAGGED, never replaced by tau_f or R_c.

Usage: two_tail_fiber_diag.py OUT.json
"""
import os, sys, json, time
os.environ.setdefault('OMP_NUM_THREADS', '1')
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_margin import state, margin, M
from two_tail_scan import w0

PI = np.pi
CONTROLS = [
    dict(name='M2 control (Codex 009/011)', z1=1.8, z2=12.0, eta=0.1, f=0.5044323206321593,
         beta_mode='touch', tau_touch=5.613571646217654),
    dict(name='M1 delicate: z=(0.6,0.84) eta=0.49, last corrected pass', z1=0.6, z2=0.84, eta=0.49,
         f=0.8380859375000002, beta_mode='detector'),
    dict(name='M3: z=(7,14) eta=0.49, first fail (complex pair inside beta)', z1=7.0, z2=14.0, eta=0.49,
         f=0.5114746093750000, beta_mode='detector'),
]


# ---------------------------------------------------------------- literal Lean residual (N = 1)
def make_residual(rho, sig, z, Kt):
    """Kt = tau*K (contact normalisation of HCYMix).  Returns f(u) for complex u (4,)."""
    z = np.asarray(z, float); Kt = np.asarray(Kt, float)
    eta = PI/6*rho*sig**3; vac = 1 - eta; xi2 = rho*sig**2
    Qpp0 = 2*PI/vac*(1 + PI*xi2*sig/(2*vac))
    Q0p0 = 2*PI/vac*(sig + PI*xi2*sig**2/(4*vac))
    cN = 2*PI**2*xi2/vac**2

    def f(u):
        Dt, G = u[:2], u[2:]
        gam = 1 - 2*PI*rho*G*np.exp(-z*sig)/z
        Ct = gam*Dt
        Wt = 2*PI/z*rho*G*Dt
        Mj = np.sum(-(1/z)*rho*(Wt + (1 + z*sig)*Ct))
        Nj = np.sum(rho*(Wt/z**2 + (1 + z*sig + (z*sig)**2/2)/z**2*Ct))
        A = Qpp0 + Qpp0*Mj + cN*Nj
        Qp = Q0p0 + Q0p0*Mj + Qpp0*Nj
        out = np.empty(4, complex)
        for a in range(2):
            s = z[a]; x = s*sig; e = np.exp(-x)
            Qh = ((1 - x - e)/s**2*Qp + (1 - x + x**2/2 - e)/s**3*A
                  + np.sum(Wt/(s + z) + Ct*(1 - e)/s) + np.sum(Ct*e/(s + z)))
            out[a] = Dt[a]*(1 - rho*Qh) - 2*PI*Kt[a]/s
            src = (A + s*Qp + np.sum(s**2*z/(s + z)*Ct))/s**2
            out[2 + a] = 2*PI*G[a]*(1 - rho*Qh) - src
        return out
    return f


def jac(f, u, h=1e-7):
    J = np.empty((4, 4), complex)
    for j in range(4):
        d = np.zeros(4, complex); d[j] = h*(1 + abs(u[j]))
        J[:, j] = (f(u + d) - f(u - d))/(2*d[j])
    return J


# ---------------------------------------------------------------- traced root and beta
def root_at(st0, tau, seed_sol):
    """Seeded solve at coupling tau (K scaled by tau, as trace_coupling_mix does), from a nearby
    traced solution; returns (state, SolutionMix or None)."""
    st = M.HCYMix(st0.sigma, st0.rho, st0.z, st0.K*tau)
    sc1, sc2 = M._scales(st0)                       # the scales trace_coupling_mix uses
    seed = np.concatenate([seed_sol.Dt.ravel(), seed_sol.Gt.ravel()])
    u = M._solve_seeded(st, seed, sc1, sc2)
    if u is None:
        return st, None
    n2 = st.N*st.N
    Dt = u[:st.T*n2].reshape(st.T, st.N, st.N); Gt = u[st.T*n2:].reshape(st.T, st.N, st.N)
    return st, M.SolutionMix(st, Dt, Gt, M._pieces(st, Dt, Gt), 0.0)


def beta_k0(st0, tr, t_inst):
    """Bisect the sign change of det F(0) along the traced branch around the detector t_inst."""
    lam = np.array([l for l, _ in tr])
    i = int(np.searchsorted(lam, t_inst))
    lo, hi = lam[i - 1], lam[i]; slo = tr[i - 1][1]
    dlo = np.real(slo.detF(0.0))
    for _ in range(60):
        mid = 0.5*(lo + hi)
        _, sm = root_at(st0, mid, slo)
        if sm is None:
            return None, (lo, hi), 'reseed failed'
        if np.sign(np.real(sm.detF(0.0))) == np.sign(dlo):
            lo, slo = mid, sm
        else:
            hi = mid
        if hi - lo < 1e-13*hi:
            break
    return 0.5*(lo + hi), (lo, hi), 'bisected det F(0) sign change'


# ---------------------------------------------------------------- total-degree homotopy
def homotopy(f, scale, rng, d=3, n=4):
    F = lambda x: f(scale*x)
    fs = np.abs(F(rng.normal(size=n) + 1j*rng.normal(size=n))) + 1e-300
    Fn = lambda x: F(x)/fs
    g = lambda x: x**d - 1
    gamma = np.exp(2j*PI*rng.random())
    H = lambda x, t: (1 - t)*gamma*g(x) + t*Fn(x)
    roots = np.exp(2j*PI*np.arange(d)/d)
    starts = np.array(np.meshgrid(*[roots]*n, indexing='ij')).reshape(n, -1).T
    out = []
    for x0 in starts:
        x, t, dt, status = x0.astype(complex), 0.0, 0.01, 'ok'
        while t < 1 - 1e-15:
            dt = min(dt, 1 - t)
            Jx = jac(lambda y: H(y, t), x)
            Ht = Fn(x) - gamma*g(x)
            try:
                v = -np.linalg.solve(Jx, Ht)
            except np.linalg.LinAlgError:
                status = 'singular predictor'; break
            xp, tp = x + dt*v, t + dt
            ok = False
            for _ in range(6):
                try:
                    dx = np.linalg.solve(jac(lambda y: H(y, tp), xp), -H(xp, tp))
                except np.linalg.LinAlgError:
                    break
                xp = xp + dx
                if np.linalg.norm(dx) < 1e-11*(1 + np.linalg.norm(xp)):
                    ok = True; break
            if ok:
                x, t = xp, tp; dt = min(2*dt, 0.05)
            else:
                dt *= 0.5
                if dt < 1e-14:
                    status = 'step underflow'; break
            if np.linalg.norm(x) > 1e8:
                status = 'diverged'; break
        if status == 'ok':                                    # polish on the target system
            for _ in range(20):
                try:
                    dx = np.linalg.solve(jac(Fn, x), -Fn(x))
                except np.linalg.LinAlgError:
                    break
                x = x + dx
                if np.linalg.norm(dx) < 1e-14*(1 + np.linalg.norm(x)):
                    break
        out.append(dict(status=status, t_end=t, x=x))
    return out


def summarise(f, scale, paths, u_star):
    res = []
    for p in paths:
        u = scale*p['x']
        r = f(u); sv = np.linalg.svd(jac(f, u), compute_uv=False)
        res.append(dict(status=p['status'], t_end=p['t_end'], u=[[c.real, c.imag] for c in u],
                        resid=float(np.max(np.abs(r))), sv=[float(s) for s in sv],
                        dist_to_traced=float(np.max(np.abs(u - u_star)/np.maximum(1, np.abs(u_star))))))
    fin = [r for r in res if r['status'] == 'ok' and r['resid'] < 1e-8]
    groups = []                                           # cluster coincident endpoints
    for r in sorted(fin, key=lambda r: r['dist_to_traced']):
        u = np.array([a + 1j*b for a, b in r['u']])
        for g in groups:
            if np.max(np.abs(u - g['u'])/np.maximum(1, np.abs(g['u']))) < 1e-6:
                g['n'] += 1; break
        else:
            groups.append(dict(u=u, n=1, rec=r))
    return res, groups


def main():
    out_path = sys.argv[1]
    cmd = ' '.join([sys.executable] + sys.orig_argv[1:]); print('# ' + cmd, flush=True)
    print('# FLOAT diagnostics only: not a finiteness/isolation/multiplicity certificate', flush=True)
    rng = np.random.default_rng(20261028)
    report = dict(command=cmd, controls=[])
    for c in CONTROLS:
        t0 = time.time()
        W = c['f']*w0(c['z1'], c['z2'])
        st0 = state(c['z1'], c['z2'], W, c['eta'])
        r = margin(c['z1'], c['z2'], W, c['eta'], lam_max=4000.0)
        rec = dict(name=c['name'], z=[c['z1'], c['z2']], eta=c['eta'], f=c['f'], w=W,
                   margin_status=r['status'], detector_tau_inst=r['tau_inst'], detector_kind=r['kind'],
                   tau_f=r['tau_f'], R_c=r['R_c'], tau_star=r['tau_star'], binding=r['binding'],
                   n_scales=r['n_scales'])
        cap = 1.3*max(x for x in (r['tau_inst'], c.get('tau_touch'), r['R_c']) if x)
        tr = M.trace_coupling_mix(st0, lam_max=cap)
        if c['beta_mode'] == 'touch':
            beta, br, how = c['tau_touch'], None, 'tau_touch of the M2 locator (tangential, no sign change)'
        elif r['kind'] == 'k=0':
            beta, br, how = beta_k0(st0, tr, r['tau_inst'])
        else:
            beta, br, how = r['tau_inst'], None, f"FLAG: detector value, kind={r['kind']}, not refined"
        lam = np.array([l for l, _ in tr]); i = max(int(np.searchsorted(lam, beta)) - 1, 0)
        st_b, sol = root_at(st0, beta, tr[i][1])
        rec.update(beta=beta, beta_bracket=br, beta_definition=how,
                   traced_endpoint_ok=sol is not None)
        if sol is None:
            print(f"{c['name']}: seeded solve at beta failed", flush=True)
            report['controls'].append(rec); continue
        u_star = np.concatenate([sol.Dt.ravel(), sol.Gt.ravel()]).astype(complex)
        f = make_residual(float(st0.rho[0]), float(st0.sigma[0]), st0.z, st_b.K[:, 0, 0])
        # transcription check against msa_exact_mix._residuals (unscaled)
        one = (np.ones((2, 1, 1)), np.ones((2, 1, 1)))
        pyres = lambda u: M._residuals(u, st_b, *one)
        chk = [float(np.max(np.abs(f(u_star) - pyres(u_star.real))))]
        for _ in range(5):
            v = u_star.real*(1 + 0.3*rng.normal(size=4))
            chk.append(float(np.max(np.abs(f(v.astype(complex)) - pyres(v)))))
        rec.update(u_traced=u_star.real.tolist(), lean_vs_python_max_abs=chk,
                   resid_at_traced=float(np.max(np.abs(f(u_star)))),
                   sv_at_traced=[float(s) for s in np.linalg.svd(jac(f, u_star), compute_uv=False)],
                   detF0_at_beta=float(np.real(sol.detF(0.0))))
        scale = np.maximum(np.abs(u_star), 1e-3)
        paths = homotopy(f, scale, rng)
        res, groups = summarise(f, scale, paths, u_star)
        acc = {s: sum(p['status'] == s for p in res) for s in sorted({p['status'] for p in res})}
        n_fin = sum(1 for p in res if p['status'] == 'ok' and p['resid'] < 1e-8)
        rec.update(polynomials=dict(n_equations=4, n_unknowns=4, degrees=[3, 3, 3, 3], bezout=81),
                   path_status=acc, finite_converged=n_fin,
                   distinct_roots=[dict(n_paths=g['n'], u=g['rec']['u'], resid=g['rec']['resid'],
                                        sv=g['rec']['sv'], dist_to_traced=g['rec']['dist_to_traced'],
                                        real=bool(np.max(np.abs(np.array(g['rec']['u'])[:, 1])) < 1e-8))
                                   for g in groups],
                   paths=res, seconds=time.time() - t0)
        near = groups[0] if groups else None
        print(f"\n== {c['name']}\n  margin: {r['status']} tau_inst={r['tau_inst']} ({r['kind']}) tau_f={r['tau_f']} "
              f"R_c={r['R_c']} [{r['binding']}] n_scales={r['n_scales']}\n  beta={beta!r}  ({how}); bracket={br}"
              f"\n  traced root u*={u_star.real}  |f(u*)|={rec['resid_at_traced']:.2e}  det F(0)={rec['detF0_at_beta']:.3e}"
              f"\n  Lean-vs-python residual max |diff| (traced, 5 random) = {[f'{x:.1e}' for x in chk]}"
              f"\n  sv(J) at u* = {[f'{x:.3e}' for x in rec['sv_at_traced']]}"
              f"\n  paths: {acc}; finite converged {n_fin}; distinct finite roots {len(groups)} "
              f"(real {sum(1 for g in rec['distinct_roots'] if g['real'])})", flush=True)
        for g in rec['distinct_roots'][:12]:
            print(f"    n={g['n_paths']} real={g['real']} dist={g['dist_to_traced']:.2e} resid={g['resid']:.1e} "
                  f"sv_min/sv_max={g['sv'][-1]/g['sv'][0]:.2e}  u={[complex(a, b) for a, b in g['u']]}", flush=True)
        if near:
            print(f"  nearest to traced endpoint: dist {near['rec']['dist_to_traced']:.2e}, paths {near['n']}, "
                  f"sv={[f'{x:.2e}' for x in near['rec']['sv']]}", flush=True)
        report['controls'].append(rec)
        json.dump(report, open(out_path, 'w'), indent=1, default=float)
    json.dump(report, open(out_path, 'w'), indent=1, default=float)


if __name__ == '__main__':
    main()
