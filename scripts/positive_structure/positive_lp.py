"""Exact feasibility: is there a sign pattern R and M >= 0 (row sums <= 1-eps) such that
w = tau*(I-M)y + M w + (I-M) Xhat(w) has nonnegative coefficients, with
y = (J0 R)^{-1} b,  Xhat = -(J0 R)^{-1}[Q2(Rw) + Q3(Rw)]?  One LP per row of M."""
import sys, itertools, numpy as np
from scipy.optimize import linprog
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent)); sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[1]))
from positive_system import taylor, M as Mx, eta

def monomial_table(J, H, Tt, b, R):
    n = len(b); A = np.linalg.inv(J@R)
    y = A@b
    H2 = np.einsum('ajk,jp,kq->apq', H, R, R)/2
    T3 = np.einsum('ajkl,jp,kq,lr->apqr', Tt, R, R, R)/6
    X2 = -np.einsum('ia,ajk->ijk', A, H2); X3 = -np.einsum('ia,ajkl->ijkl', A, T3)
    cols = []
    for j in range(n):
        for k in range(j, n):
            cols.append(X2[:, j, k] + (X2[:, k, j] if k != j else 0))
            for l in range(k, n):
                cols.append(sum(X3[(slice(None),) + p] for p in set(itertools.permutations((j, k, l)))))
    X = np.array(cols).T                      # X[a, m]: monomial m in equation a
    return y, X

def row_feasible(i, y, X, eps=0.5):
    n = len(y); sc = max(np.max(np.abs(X)), np.max(np.abs(y)))
    keep = np.max(np.abs(X), axis=0) > 1e-11*sc
    Xk = X[:, keep]/sc; yk = y/sc
    # row i of (I-M)X:  X_i[m] - sum_a m_a X_a[m] >= t ;  y_i - sum_a m_a y_a >= t ; m >= 0 ; sum m <= 1-eps
    nm = Xk.shape[1]
    c = np.r_[np.zeros(n), -1.0]
    A_ub = np.vstack([np.c_[Xk.T, np.ones(nm)],                    # m.X + t <= X_i
                      np.r_[yk, 1.0][None, :],                     # m.y + t <= y_i
                      np.r_[np.ones(n), 0.0][None, :]])            # sum m <= 1-eps
    b_ub = np.r_[Xk[i], yk[i], 1-eps]
    bounds = [(0, None)]*n + [(None, 1.0)]
    r = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
    return (r.x[-1], r.x[:n]) if r.success else (-np.inf, None)

def analyse(name, st, eps=0.5):
    u0, J, H, Tt, b, err = taylor(st); n = len(b)
    best = None
    for s in itertools.product((1, -1), repeat=n):
        R = np.diag(s).astype(float)
        y, X = monomial_table(J, H, Tt, b, R)
        rows = [row_feasible(i, y, X, eps) for i in range(n)]
        worst = min(t for t, _ in rows)
        if best is None or worst > best[0]:
            best = (worst, s, rows)
    worst, s, rows = best
    print(f"{name} [row sums <= {1-eps:.2f}]: n={n} best sign pattern {s}: worst row margin {worst:+.3e} ({'POSITIVE SYSTEM' if worst >= -1e-12 else 'infeasible'})", flush=True)
    return best

if __name__ == "__main__":
    cases = [("1 tail z=1.8 eta=0.2", Mx.HCYMix([1.0], [eta(0.2)], [1.8], [[[1.0]]])),
             ("2 attr z=(1.8,4) eta=0.3", Mx.HCYMix([1.0], [eta(0.3)], [1.8, 4.0], np.array([1.0, .5]).reshape(2, 1, 1))),
             ("2 attr z=(1.8,.8) eta=0.3", Mx.HCYMix([1.0], [eta(0.3)], [1.8, 0.8], np.array([1.0, .3]).reshape(2, 1, 1))),
             ("2YK eta=0.25", Mx.HCYMix([1.0], [eta(0.25)], [2.9637, 14.0167], np.array([2.1714, -2.1714]).reshape(2, 1, 1))),
             ("F5 eta=0.3", Mx.HCYMix([1.0], [eta(0.3)], [1.8, 12.0], np.array([1.0, -6.0]).reshape(2, 1, 1)))]
    for name, st in cases:
        for eps in (0.5, 0.1, 0.01):
            analyse(name, st, eps)
