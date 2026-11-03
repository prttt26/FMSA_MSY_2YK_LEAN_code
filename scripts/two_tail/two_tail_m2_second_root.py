"""EXTERNAL interval certificate: the second real root r2 at the M2 control is not on the PY-seeded
branch (user request, after handoffs 136-144).  NOT a Lean proof.

Setting: eta = 1/10, z = (9/5, 12), sigma = 1, K = tau*(1, w).  tau and w range over the tau and w
boxes of Codex's certified root box (011 JSON, read-only, sha256 recorded).  Since tau and w enter
the residual only in the constant term -2 pi tau K/z, f is evaluated with tau and w as intervals.
Arithmetic: mpmath iv, 192 bits.  J is AD of the literal Lean residual; all endpoints are
serialised as exact rationals.

Certificates:
  (1) X2: Krawczyk box with K inside X2 and ||I - C J(X2)|| < 1, for all (tau, w) in Codex's boxes.
      So r2 is a unique regular root in X2.  X2 is disjoint from Codex's amplitude box.
  (2) A window T = [tau_lo - delta, tau_hi + delta] around tau_touch.  Parametric Krawczyk boxes Y1,
      with tau in mean-value form K = x~ - C f(x~; tau_c) - (C R_tau)(T - tau_c) + (I - C J)(X - x~),
      (through r1, containing Codex's amplitude box) and Y2 (through r2, containing X2) hold for
      every tau in T and w in W.  If Y1 and Y2 are disjoint, the two local branch segments over T
      are distinct and never meet.
  (3) Codex 009/011 certify the PY-seeded branch over [0, tau_touch] with a unique root per tau in
      every slab, so it is a single-valued function of tau there.  Its only point at tau_touch is
      the root in Codex's box, so r2 (in X2, disjoint) is not on it.  By (2) the separation
      persists over the window T.
Not certified: that r2's branch never reconnects with the PY branch outside T (e.g. through a fold
beyond the window).  The float continuation (two_tail_m2_branch_explore.py) found no fold on either
forward branch up to tau ~ 17, and found r2's backward branch folding at tau ~ -0.035 and heading to
G1 ~ 2e3 as tau -> 0.  That is evidence, not proof.

Usage: two_tail_m2_second_root.py OUT.json
"""
import sys, json, hashlib
from fractions import Fraction
from pathlib import Path
import numpy as np
import mpmath
from mpmath import iv
sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_m2_jacobian_interval import D, residual, ROOT
from two_tail_endpoint_interval import q2iv, LO, HI, FX, IX, FQ, strictly_inside, sha, newton, duals

iv.prec = 192
mpmath.mp.prec = 192
HERE = Path(__file__).resolve().parent
DIAG = HERE.parents[1]/'results'/'two_tail'/'two_tail_fiber_diag.json'


def krawczyk(x, F, rad_abs, mv=None):
    """With mv = (F_center, R_tau, T, tau_c) the tau dependence is in mean-value form,
        K = x~ - C f(x~; tau_c) - (C R_tau)(T - tau_c) + (I - C J(X)) (X - x~),
    where R_tau = dR/dtau = (-2 pi/z1, -2 pi w/z2, 0, 0) is exact (tau enters only the constant
    term).  This avoids the wrapping of tau through C f."""
    _, Jm = newton(x, F if mv is None else mv[0])
    Cf = np.linalg.inv(np.array([[float(Jm[i, j]) for j in range(4)] for i in range(4)]))
    Cq = [[Fraction(float(Cf[i, j])) for j in range(4)] for i in range(4)]
    C = [[q2iv(q) for q in row] for row in Cq]
    xt = [iv.mpf(v) for v in x]
    X = [iv.mpf([LO(xt[i] - rad_abs[i]), HI(xt[i] + rad_abs[i])]) for i in range(4)]
    fx = (F if mv is None else mv[0])(duals(xt)); JX = F(duals(X))
    E = [[(iv.mpf(1) if i == j else iv.mpf(0)) - sum((C[i][m]*JX[m].g[j] for m in range(4)), iv.mpf(0))
          for j in range(4)] for i in range(4)]
    norm = max(HI(sum((abs(E[i][j]) for j in range(4)), iv.mpf(0))) for i in range(4))
    Kx = [xt[i] - sum((C[i][m]*fx[m].v for m in range(4)), iv.mpf(0))
          + sum((E[i][j]*(X[j] - xt[j]) for j in range(4)), iv.mpf(0)) for i in range(4)]
    extra = {}
    if mv is not None:
        _, Rt, T, tc = mv
        CRt = [sum((C[i][m]*Rt[m] for m in range(4)), iv.mpf(0)) for i in range(4)]
        Kx = [Kx[i] - CRt[i]*(T - tc) for i in range(4)]
        extra = dict(tau_center=str(FX(LO(tc))), R_tau=[IX(v) for v in Rt], C_R_tau=[IX(v) for v in CRt], T=IX(T))
    w = dict(**extra, center=[str(FX(LO(c))) for c in xt], C_rational=[[str(q) for q in row] for row in Cq],
             X=[IX(v) for v in X], K=[IX(v) for v in Kx], f_center=[IX(r.v) for r in fx],
             J_over_X=[[IX(JX[i].g[j]) for j in range(4)] for i in range(4)],
             I_minus_CJ=[[IX(E[i][j]) for j in range(4)] for i in range(4)],
             inf_norm_upper=str(FX(norm)), inf_norm_display=mpmath.nstr(norm, 8))
    w['exact_check_K_strictly_inside_X'] = strictly_inside(w['K'], w['X'])
    w['exact_check_norm_lt_1'] = Fraction(w['inf_norm_upper']) < 1
    return w, w['exact_check_K_strictly_inside_X'] and w['exact_check_norm_lt_1']


def first_pass(x, F, rels, mv=None):
    for r in rels:
        rad = [iv.mpf(HI(iv.mpf(r.numerator)/r.denominator*max(1, abs(float(v))))) for v in x]
        w, ok = krawczyk(x, F, rad, mv)
        if ok:
            return dict(radius_rel=str(r), witness=w)
    return None


def disjoint(A, B):
    """Exact: some coordinate interval of A and B is disjoint."""
    return any(FQ(a)[1] < FQ(b)[0] or FQ(b)[1] < FQ(a)[0] for a, b in zip(A, B))


def contains(big, small):
    return all(FQ(b)[0] <= FQ(s)[0] and FQ(s)[1] <= FQ(b)[1] for b, s in zip(big, small))


def main():
    out = sys.argv[1]
    cmd = ' '.join([sys.executable] + sys.orig_argv[1:]); print('# ' + cmd, flush=True)
    print('# EXTERNAL interval certificate (mpmath iv, 192 bits); not a Lean proof', flush=True)
    raw = ROOT.read_bytes(); cert = json.loads(raw)
    assert cert['status'] == 'PASS_FIRST_ZERO_MODE_CONTACT' and cert['model'] == {'eta': '0.1', 'z': ['1.8', '12'], 'sigma': '1'}
    rb = cert['root_box']
    ubox = [[Fraction(str(lo)), Fraction(str(hi))] for lo, hi in rb[:4]]       # Codex amplitude box (decimal tokens, exact)
    Tq, Wq = [Fraction(str(v)) for v in rb[4]], [Fraction(str(v)) for v in rb[5]]
    eta = iv.mpf(1)/10; rho = 6*eta/iv.pi; sig = iv.mpf(1); z = [iv.mpf(9)/5, iv.mpf(12)]
    W = iv.mpf([LO(q2iv(Wq[0])), HI(q2iv(Wq[1]))])
    def F_at(T):
        return lambda u: residual(u, rho, sig, z, [T*1, T*W])
    T0 = iv.mpf([LO(q2iv(Tq[0])), HI(q2iv(Tq[1]))])
    diag = json.load(open(DIAG)); c = diag['controls'][0]
    r2f = next(g for g in c['distinct_roots'] if g['real'] and 1e-3 < g['dist_to_traced'] < 0.1)['u']
    x2 = [mpmath.mpf(a) for a, b in r2f]
    x1 = [mpmath.mpf((lo + hi)/2) for lo, hi in rb[:4]]
    rels = [Fraction(1, 10**k) for k in range(2, 13)]
    # (1) r2 over Codex's (tau, w) boxes
    c2 = first_pass(x2, F_at(T0), rels)
    ok1 = c2 is not None and disjoint(c2['witness']['X'], [[str(a), str(b)] for a, b in ubox])
    print(f"(1) r2 box over Codex tau/w boxes: {'PASS' if c2 else 'FAIL'} "
          f"(radius {c2 and c2['radius_rel']}, ||I-CJ|| <= {c2 and c2['witness']['inf_norm_display']}); "
          f"disjoint from Codex amplitude box: {ok1}", flush=True)
    # (2) window T
    res2 = None
    Rt = [-2*iv.pi/z[0], -2*iv.pi*W/z[1], iv.mpf(0), iv.mpf(0)]
    tcq = (Tq[0] + Tq[1])/2; tc = q2iv(tcq)
    for dexp in (1, 2, 3, 4, 5, 6):
        delta = Fraction(1, 10**dexp)
        T = iv.mpf([LO(q2iv(Tq[0] - delta)), HI(q2iv(Tq[1] + delta))])
        mv = (F_at(tc), Rt, T, tc)
        y1 = first_pass(x1, F_at(T), rels, mv); y2 = first_pass(x2, F_at(T), rels, mv)
        if y1 and y2:
            Y1, Y2 = y1['witness']['X'], y2['witness']['X']
            chk = dict(Y1_contains_codex_box=contains(Y1, [[str(a), str(b)] for a, b in ubox]),
                       Y2_contains_X2=contains(Y2, c2['witness']['X']) if c2 else False,
                       Y1_Y2_disjoint=disjoint(Y1, Y2))
            res2 = dict(delta=str(delta), T_iv=IX(T), Y1=y1, Y2=y2, checks=chk)
            print(f"(2) window tau in [{float(Tq[0] - delta)!r}, {float(Tq[1] + delta)!r}] (delta {delta}): "
                  f"Y1 radius {y1['radius_rel']} (||.|| <= {y1['witness']['inf_norm_display']}), "
                  f"Y2 radius {y2['radius_rel']} (||.|| <= {y2['witness']['inf_norm_display']}); {chk}", flush=True)
            if all(chk.values()):
                break
        else:
            print(f"(2) delta {delta}: parametric boxes not certified (Y1 {bool(y1)}, Y2 {bool(y2)})", flush=True)
    passed = bool(ok1 and res2 and all(res2['checks'].values()))
    print(f"\nRESULT: {'PASS' if passed else 'FAIL'} -- r2 is a unique regular root disjoint from the certified root; "
          f"the local branches through r1 and r2 are disjoint over the window; with Codex 009/011 (PY branch a graph "
          f"over [0, tau_touch]) r2 is not on the PY-seeded branch.  Global non-reconnection is NOT certified.", flush=True)
    json.dump(dict(command=cmd, label='EXTERNAL interval certificate (mpmath iv, 192 bits); not a Lean proof',
                   serialization='All endpoints are exact rationals; *_display fields are non-authoritative.',
                   root_box_source=str(ROOT), root_box_sha256=hashlib.sha256(raw).hexdigest(),
                   diag_source=str(DIAG), diag_sha256=sha(DIAG),
                   source_sha256={n: sha(HERE/n) for n in ('two_tail_m2_second_root.py', 'two_tail_endpoint_interval.py',
                                                           'two_tail_m2_jacobian_interval.py')},
                   data=dict(eta='1/10', rho='6*eta/pi', sigma='1', z=['9/5', '12'], tau_box=[str(v) for v in Tq],
                             w_box=[str(v) for v in Wq], codex_amplitude_box=[[str(a), str(b)] for a, b in ubox]),
                   r2_box=c2, r2_disjoint_from_codex_box=ok1, window=res2, passed=passed),
              open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
