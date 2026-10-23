"""Instability before fold: does the exact-MSA branch from tau=0 reach a fold of the
Blum-Hoye system only after its Baxter factor has stopped being canonical?

Claim under test (proof_notes_msa_exact.md, section "Instability before fold"): along
the physical branch the BH Jacobian is invertible as long as det F(s) has no zero in
Re s >= 0, and a zero can enter the right half-plane only through s = ik, i.e. where
det(I - C(k)) = 0 for some real k.  So every fold must sit at a point where the
winding of det F(ik) is nonzero, and the BH root there must fail the OZ core condition.

Per state the script traces the branch in a multiplier lambda on K, records along it
  W(lambda)   winding number of det F(ik), k in [-400, 400]
  m(lambda)   min_k lambda_min(I - rho^1/2 c(k) rho^1/2)   (>= 0 on every real root)
and reports the first winding change, the fold (end of the traced branch, with
sigma_min/sigma_max of the finite-difference Jacobian), and the OZ consistency of the
BH root: max |h_OZ + 1| inside the core and the relative mismatch of g^(z) between
the OZ h and the BH value, at lambda = 0 (transform floor), just before the winding
change, and at the fold.

Gate: every fold has |W| >= 1, the first winding change comes before it, and that
change brackets a sign change of det F(0) (the detector reads the k = 0 crossing).
Diagnostic (reported, not gated): oz_contrast = g^ mismatch at the fold over its value
at lambda = 0 / just before the flip.  The core value max|h_OZ + 1| is limited by the
contact-jump ringing at k_max and is recorded only.  Window r_max = 400: at 40 the
near-lambda-line SALR state reads a spurious 12 % g^ mismatch (1.5e-3 at r_max = 2000).  The k != 0 crossing is
NOT exercised: no state with a microphase instability before the fold was found.

Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python3 scripts/msa_instability_before_fold_check.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
from scipy.fft import dst
from scipy.integrate import trapezoid

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
import msa_exact_mix as M  # noqa: E402

RESULTS = Path(__file__).resolve().parents[1]/'results'/'instability_before_fold'
KP = np.concatenate([np.linspace(0, 2, 2001)[1:], np.linspace(2.001, 400, 40000)])
KG = np.concatenate([-KP[::-1], [0.0], KP])


def eta_rho(e):
    return 6*e/np.pi


def cases():
    out = []
    for e in (0.1, 0.2, 0.3, 0.4):
        out.append((f'HC1Y z=1.8 eta={e}', M.HCYMix([1.0], [eta_rho(e)], [1.8], [[[1.0]]]), 8.0))
    for e in (0.15, 0.25, 0.35):
        out.append((f'HC2Y-LJ eta={e}', M.HCYMix([1.0], [eta_rho(e)], [2.9637, 14.0167],
                                                np.array([2.1714, -2.1714]).reshape(2, 1, 1)), 8.0))
    s = np.array([1.0, 1.3]); eps = np.array([[1.0, 0.9], [0.9, 0.8]])
    SIG = 0.5*(s[:, None] + s[None, :])
    for e in (0.15, 0.3):
        rho = np.array([0.5, 0.5]); rho *= e/((np.pi/6)*np.sum(rho*s**3))
        out.append((f'binary sigma 1:1.3 eta={e}', M.HCYMix(s, rho, [1.8], (eps*SIG)[None]), 8.0))
    for k12 in (0.2, 0.0):
        out.append((f'equal-sigma binary K12={k12} eta=0.3',
                    M.HCYMix([1.0, 1.0], np.array([.5, .5])*eta_rho(0.3), [1.8],
                             np.array([[1.0, k12], [k12, 1.0]])[None]), 8.0))
    out.append(('SALR z=(4,0.5) w=-0.1 eta=0.3',
                M.HCYMix([1.0], [eta_rho(0.3)], [4.0, 0.5], np.array([1.0, -0.1]).reshape(2, 1, 1)), 60.0))
    return out


def diag(sol):
    rho = sol.st.rho; rr = np.sqrt(rho[:, None]*rho[None, :]); N = sol.st.N
    Fk = np.eye(N)[None] - rr[None]*M._qhat_vec(sol.st, sol.p, 1j*KG)
    d = np.linalg.det(Fk)
    W = float(np.sum(np.angle(d[1:]/d[:-1]))/(2*np.pi))
    C = M.chat_k(sol, KP)*rr[None]
    Mk = np.eye(N)[None] - C; Mk = 0.5*(Mk + np.transpose(Mk, (0, 2, 1)))
    ev = np.linalg.eigvalsh(Mk)[:, 0]; i = int(np.argmin(ev))
    return dict(W=W, m=float(ev[i]), k_m=float(KP[i]), detF0=float(np.real(sol.detF(0.0))))


def oz_defects(sol, n_r=2**18, r_max=400.0):
    dr = r_max/n_r; r = (np.arange(n_r)+.5)*dr; dk = np.pi/r_max; k = (np.arange(n_r)+.5)*dk
    st = sol.st; rho = st.rho; N = st.N; rr = np.sqrt(rho[:, None]*rho[None, :])
    C = M.chat_k(sol, k)*rr[None]
    hk = np.linalg.solve(np.eye(N)[None] - C, C)/rr[None]
    h = dst(k[:, None, None]*hk, type=4, axis=0)*(dk/(4*np.pi**2))/r[:, None, None]
    core = float(np.max(np.abs(h[(r > 0.1) & (r < 0.85*np.min(st.SIG))] + 1.0)))
    z = st.z[0]; g = np.where(r[:, None, None] < st.SIG[None], 0.0, 1.0 + h)
    gl = trapezoid(np.exp(-z*r)[:, None, None]*r[:, None, None]*g, r, axis=0)
    return dict(core_defect=core, ghat_mismatch=float(np.max(np.abs(gl - sol.gL[0])/np.abs(sol.gL[0]))))


def run(name, st, lam_max):
    tr = M.trace_coupling_mix(st, lam_max=lam_max)
    D = [diag(s) for _, s in tr]
    flip = next((i for i in range(1, len(D)) if round(D[i]['W']) != round(D[0]['W'])), None)
    lend, send = tr[-1]
    fold = lend < lam_max - 1e-9
    sc1, sc2 = M._scales(send.st)
    u = np.concatenate([send.Dt.ravel(), send.Gt.ravel()])
    sv = np.linalg.svd(M._jacobian(u, send.st, sc1, sc2), compute_uv=False)
    row = dict(case=name, lam_max=lam_max, n_trace=len(tr), fold=fold, lam_end=lend,
               jac_cond_inv_end=float(sv[-1]/sv[0]), end=D[-1], start=D[0],
               oz_floor=oz_defects(tr[0][1]), oz_end=oz_defects(send))
    if flip is not None:
        row.update(flip_interval=[tr[flip-1][0], tr[flip][0]], before_flip=D[flip-1], after_flip=D[flip],
                   oz_before_flip=oz_defects(tr[flip-1][1]))
    if fold:
        # the gate: the fold sits on a non-canonical factor, reached through a k = 0 crossing
        row['pass'] = bool(flip is not None and abs(round(D[-1]['W'])) >= 1
                           and tr[flip][0] <= lend
                           and np.sign(D[flip-1]['detF0']) != np.sign(D[flip]['detF0']))
        # diagnostic, not gated: the BH root stops being an OZ solution after the flip
        pre = max(row['oz_floor']['ghat_mismatch'], row['oz_before_flip']['ghat_mismatch'])
        row['oz_contrast'] = row['oz_end']['ghat_mismatch']/pre
    else:
        row['pass'] = bool(flip is None)       # no fold and no instability: nothing to order
    print(json.dumps({k: row[k] for k in ('case', 'fold', 'lam_end', 'pass')}
                     | {'flip': row.get('flip_interval'), 'W_end': round(D[-1]['W'], 3),
                        'oz_end': row['oz_end'], 'oz_floor': row['oz_floor']}), flush=True)
    return row


def main():
    RESULTS.mkdir(parents=True, exist_ok=True)
    rows = [run(*c) for c in cases()]
    summary = dict(command=' '.join(sys.argv), n_cases=len(rows),
                   min_oz_contrast=min(r['oz_contrast'] for r in rows if r['fold']),
                   n_folds=sum(r['fold'] for r in rows), all_pass=all(r['pass'] for r in rows),
                   untested='k != 0 (microphase) crossing: no state found where it precedes a fold',
                   rows=rows)
    (RESULTS/'results.json').write_text(json.dumps(summary, indent=1))
    print('ALL PASS' if summary['all_pass'] else 'FAIL', f"({summary['n_folds']} folds / {len(rows)} cases)")


if __name__ == '__main__':
    main()
