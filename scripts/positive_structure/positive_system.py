"""Is the BH system v = tau*beta + Phi(v) (expanded exactly at the HS seed) a positive
polynomial system after a sign change v_i -> s_i v_i?"""
import sys, itertools, numpy as np
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[1]))
from msa_coupling_series_sign_probe import residual_c, M

def taylor(st):
    T, N = st.T, st.N; n2 = N*N; n = 2*T*n2
    _, G0 = M.seed_zero_K(M.HCYMix(st.sigma, st.rho, st.z, 0*st.K))
    u0 = np.concatenate([np.zeros(T*n2), G0.ravel()])
    P = lambda u: residual_c(u.astype(complex), st)[0].real
    E = np.eye(n); h = 0.5
    # exact for a cubic: central differences
    J = np.array([(P(u0+h*E[j]) - P(u0-h*E[j]))/(2*h) - 0*0 for j in range(n)]).T
    # the cubic term contaminates the central first difference by h^2/6 T_jjj: fix after T
    H = np.empty((n, n, n)); Tt = np.empty((n, n, n, n))
    for j in range(n):
        for k in range(n):
            H[:, j, k] = (P(u0+h*E[j]+h*E[k]) - P(u0+h*E[j]-h*E[k]) - P(u0-h*E[j]+h*E[k]) + P(u0-h*E[j]-h*E[k]))/(4*h*h)
            for l in range(n):
                f = lambda a, b, c: P(u0 + h*(a*E[j] + b*E[k] + c*E[l]))
                Tt[:, j, k, l] = sum((-1)**(3-a-b-c)*f(a, b, c) for a in (0, 1) for b in (0, 1) for c in (0, 1))/h**3
    # forward third difference of a cubic is exact; correct J for the h^2 T_jjj/6 term
    for j in range(n):
        J[:, j] -= h*h*Tt[:, j, j, j]/6
    # sanity: reconstruct P at a random point
    v = 0.3*np.random.default_rng(0).standard_normal(n)
    rec = P(u0) + J@v + 0.5*np.einsum('ijk,j,k->i', H, v, v) + np.einsum('ijkl,j,k,l->i', Tt, v, v, v)/6
    err = np.max(np.abs(rec - P(u0+v)))
    b = np.concatenate([(2*np.pi*st.K/st.z[:, None, None]).ravel(), np.zeros(T*n2)])
    return u0, J, H, Tt, b, err

def monomials(st):
    u0, J, H, Tt, b, err = taylor(st)
    n = len(u0); Ji = np.linalg.inv(J)
    beta = Ji@b
    A2 = -np.einsum('ia,ajk->ijk', Ji, H)/2          # Phi quadratic coefficients (symmetric tensor)
    A3 = -np.einsum('ia,ajkl->ijkl', Ji, Tt)/6
    active = [i for i in range(n) if np.max(np.abs(A2[i]))+np.max(np.abs(A3[i]))+abs(beta[i]) > 1e-12]
    return beta, A2, A3, err, n

def best_sign(beta, A2, A3, n):
    scale = max(np.max(np.abs(A2)), np.max(np.abs(A3)), np.max(np.abs(beta)))
    best = None
    for s in itertools.product((1, -1), repeat=n):
        s = np.array(s)
        bb = s*beta
        q = s[:, None, None]*A2*s[None, :, None]*s[None, None, :]
        c = s[:, None, None, None]*A3*s[None, :, None, None]*s[None, None, :, None]*s[None, None, None, :]
        q = q + np.transpose(q, (0, 2, 1)); c = c  # monomial sums: symmetric already
        neg = -min(bb.min(), q.min(), c.min())/scale
        if best is None or neg < best[0]:
            best = (neg, s, bb, q, c)
    return best, scale

eta = lambda e: 6*e/np.pi
cases = [("1 tail z=1.8 eta=0.2", M.HCYMix([1.0], [eta(0.2)], [1.8], [[[1.0]]])),
         ("1 tail z=1.8 eta=0.4", M.HCYMix([1.0], [eta(0.4)], [1.8], [[[1.0]]])),
         ("2 attr z=(1.8,4) eta=0.3", M.HCYMix([1.0], [eta(0.3)], [1.8, 4.0], np.array([1.0, .5]).reshape(2, 1, 1))),
         ("2YK eta=0.25", M.HCYMix([1.0], [eta(0.25)], [2.9637, 14.0167], np.array([2.1714, -2.1714]).reshape(2, 1, 1))),
         ("F5 eta=0.3", M.HCYMix([1.0], [eta(0.3)], [1.8, 12.0], np.array([1.0, -6.0]).reshape(2, 1, 1)))]
if __name__ == "__main__":
  for name, st in cases:
      beta, A2, A3, err, n = monomials(st)
      (neg, s, bb, q, c), scale = best_sign(beta, A2, A3, n)
      print(f"{name}: n={n} recon err={err:.1e}  best signs={s}  worst negative coeff / max = {neg:.3e}")
      print("   beta=", bb.round(5))
      for i in range(n):
          qi = [(j, k, round(q[i, j, k]/(1 if j == k else 2)*(1), 5)) for j in range(n) for k in range(j, n) if abs(q[i, j, k]) > 1e-10*scale]
          ci = [(j, k, l, round(c[i, j, k, l], 5)) for j in range(n) for k in range(j, n) for l in range(k, n) if abs(c[i, j, k, l]) > 1e-10*scale]
          print(f"   comp {i}: quad {qi}")
          print(f"            cubic {ci}")
