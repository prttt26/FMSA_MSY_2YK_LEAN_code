"""Float locator of the zero-mode disappearance (M2) boundary for K = (1, w), z = (z1, z2).

The system and the closed zero-mode factor are those of Codex's audit note
(`proof_notes/codex_two_tail_reduction_audit.md` §3-4, handoff 004), transcribed independently
here; nothing is imported from `codex_*` files.  Unknowns x = (u, tau, w, v), u = (D1, D2, G1, G2):

    P(u) - tau b(w) = 0,   J(u) v - b(w) = 0,   F0(u) = 0,   g(u).v = 0,

with b(w) = (2 pi/z1, 2 pi w/z2, 0, 0), J = DP, F0 = det F(0) and g = grad F0.  A root with
det J != 0 is a stationary zero of F0 along the regular BH branch, i.e. the touching point
where two k = 0 crossings appear or disappear.  Reported along with it: the curvature
F0'' = v^T H v + g.a (J a = -D2P[v, v]) and the transversality m_f = w0 tau g adj(J) b_w/det J.
The touching point is not linked to the PY branch here (seeded from the traced branch only);
Codex's codex_m2_tangency.py certifies that.  Float64; evidence, not proof.

Usage: two_tail_m2_locate.py z1 z2 eta f_guess [lam_max]
       two_tail_m2_locate.py --control      (Codex's certified point, handoff 009)
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

_HERE = Path(__file__).resolve().parent
_FOUNDATION = _HERE.parents[2]/'MSA_and_1st_Truncation'/'scripts'   # frozen 1.0.17, imported read-only
sys.path[:0] = [str(_HERE), str(_FOUNDATION/'coupling_singularities'), str(_FOUNDATION)]
from nearest import M, jac  # noqa: E402
from msa_coupling_series_sign_probe import residual_c  # noqa: E402
from two_tail_margin import state  # noqa: E402
from two_tail_scan import w0  # noqa: E402


def zero_mode(u, eta, z):
    """F0(u) = (1+2 eta)/v^2 + sum_i D_i (alpha_i + beta_i G_i), its gradient and Hessian."""
    v = 1 - eta; rho = 6*eta/np.pi; T = len(z)
    D, G = u[:T], u[T:]
    al = np.array([rho/(v**2*zi**2)*(6*eta + (4*eta - 1)*zi + (eta - 1)*zi**2) for zi in z])
    be = np.array([12*eta*rho/(v**2*zi**3)*(-(1 + 2*eta)*zi*(1 - (1 + zi)*np.exp(-zi))
                                             + 6*eta*(1 - (1 + zi + zi**2/2)*np.exp(-zi))) for zi in z])
    F0 = (1 + 2*eta)/v**2 + np.sum(D*(al + be*G))
    g = np.r_[al + be*G, be*D]
    H = np.zeros((2*T, 2*T)); H[range(T), range(T, 2*T)] = be; H[range(T, 2*T), range(T)] = be
    return F0, g, H


def bvec(w, z):
    return np.array([2*np.pi/z[0], 2*np.pi*w/z[1], 0.0, 0.0])


def P(u, st):
    return np.real(residual_c(u.astype(complex), st)[0])


def Jr(u, st):
    return np.real(jac(u.astype(complex), st))


def system(x, st, eta, z):
    u, tau, w, v = x[:4], x[4], x[5], x[6:]
    b = bvec(w, z); F0, g, _ = zero_mode(u, eta, z)
    return np.r_[P(u, st) - tau*b, Jr(u, st) @ v - b, F0, g @ v]


def newton(x, st, eta, z, it=40, tol=1e-12):
    for _ in range(it):
        r = system(x, st, eta, z)
        Jx = np.empty((10, 10))
        for j in range(10):
            h = 1e-6*max(1.0, abs(x[j])); e = np.zeros(10); e[j] = h
            Jx[:, j] = (system(x + e, st, eta, z) - system(x - e, st, eta, z))/(2*h)
        dx = np.linalg.solve(Jx, -r); x = x + dx
        if np.linalg.norm(dx) < tol*(1 + np.linalg.norm(x)):
            break
    return x, float(np.linalg.norm(system(x, st, eta, z)))


def seed(z1, z2, eta, f, lam_max):
    """Trace the branch at f; seed at the sampled interior minimum of det F(0)."""
    st = state(z1, z2, f*w0(z1, z2), eta)
    tr = M.trace_coupling_mix(st, lam_max=lam_max)
    lam = np.array([l for l, _ in tr]); d0 = np.array([float(np.real(s.detF(0.0))) for _, s in tr])
    i = int(np.argmin(d0[1:-1])) + 1 if len(d0) > 2 else len(d0) - 1
    u = np.concatenate([tr[i][1].Dt.ravel(), tr[i][1].Gt.ravel()]).real
    F0 = zero_mode(u, eta, [z1, z2])[0]
    return st, u, lam[i], d0[i], F0


def locate(z1, z2, eta, f_guess, lam_max=160.0):
    z = [z1, z2]; W0 = w0(z1, z2)
    st, u, tau, d0min, F0chk = seed(z1, z2, eta, f_guess, lam_max)
    tau_seed = float(tau)
    b = bvec(f_guess*W0, z)
    v = np.linalg.solve(Jr(u, st), b)
    x, res = newton(np.r_[u, tau, f_guess*W0, v], st, eta, z)
    u, tau, w, v = x[:4], x[4], x[5], x[6:]
    st = state(z1, z2, w, eta)                      # P does not depend on K; b carries w
    J = Jr(u, st); F0, g, H = zero_mode(u, eta, z)
    h = 1e-3*max(1.0, np.linalg.norm(u))/max(1.0, np.linalg.norm(v))
    d2P = (P(u + h*v, st) - 2*P(u, st) + P(u - h*v, st))/h**2       # exact for a cubic
    a = np.linalg.solve(J, -d2P)
    curv = float(v @ H @ v + g @ a)
    bw = np.array([0.0, 2*np.pi/z2, 0.0, 0.0])
    m_w = float(tau*(g @ np.linalg.solve(J, bw)))   # = tau g adj(J) b_w / det J
    return dict(z1=z1, z2=z2, eta=eta, f_guess=f_guess, seed_tau=tau_seed,
                seed_detF0_min=d0min, seed_F0_formula=F0chk, f=float(w/W0), w=float(w), tau=float(tau),
                u=u.tolist(), v=v.tolist(), residual=res, detJ=float(np.linalg.det(J)), F0=float(F0),
                F0_dd=curv, m_w=m_w, m_f=float(W0*m_w))


def main(argv):
    if argv and argv[0] == '--control':
        z1, z2, eta, f = 1.8, 12.0, 0.1, 0.5045; L = 40.0
    else:
        z1, z2, eta, f = map(float, argv[:4]); L = float(argv[4]) if len(argv) > 4 else 160.0
    r = locate(z1, z2, eta, f, L)
    r['command'] = ' '.join([sys.executable] + sys.orig_argv[1:])
    print(json.dumps(r, indent=1))
    out = Path(__file__).resolve().parents[2]/'results'/'two_tail'/'two_tail_m2_locate.jsonl'
    with out.open('a') as fh:
        fh.write(json.dumps(r) + '\n')


if __name__ == '__main__':
    main(sys.argv[1:])
