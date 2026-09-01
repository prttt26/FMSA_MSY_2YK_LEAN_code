#!/usr/bin/env python3
"""Numerical confirmation that MixBHRootUneq's (29')/(33') need the RECENTERED Baxter
transform e^{z.edgeLo}.Qhat at unequal sigma (the sigma-edge FINDING).

Solves a physical unequal-sigma MSA-Yukawa mixture via msa_exact_mix.solve_bh_mix
(parent dir; its _residuals passes the Tang & Lu gate at sigma2/sigma1=1.5), then
evaluates the Lean MixBHRootUneq forms at the root:
  (29') recentered residual ~ 1.7e-16   (matches, machine precision)
  (33') recentered residual ~ 3.6e-15   (matches, machine precision)
  (33') BARE (no recentering) ~ 4.96     (WRONG -- confirms recentering is required)
Lean edgeLo sigma a b = (sig_b - sig_a)/2; the (29') factor is e^{z edgeLo(j,l)},
the (33') factor e^{z edgeLo(l,j)} (opposite sign, transposed Qhat index).
"""
import numpy as np, sys
sys.path.insert(0, '/home/rpan/YK_tail_FMSA')
from msa_exact_mix import HCYMix, solve_bh_mix, qhat
# UNEQUAL-sigma 2-species case, single tail, modest Yukawa coupling
sigma = np.array([1.0, 1.5]); rho = np.array([0.30, 0.15]); z = np.array([1.8])
eps = np.array([[0.20, 0.10],[0.10, 0.15]])
SIG = 0.5*(sigma[:,None]+sigma[None,:])
K = (eps*SIG)[None]      # K = beta eps sigma_ij (contact normalisation)
st = HCYMix(sigma, rho, z, K)
sol = solve_bh_mix(st, tol=1e-11)
assert sol is not None, "solver failed"
print("solver converged")
Dt, Gt, p = sol.Dt[0], sol.Gt[0], sol.p
zt = z[0]; N=2; eye=np.eye(N)
Q = qhat(st, p, zt).real          # Q[i,j] = Qhat_ij(z)  (my qhatMixRuneq)
eLo = lambda a,b: (sigma[b]-sigma[a])/2.0   # Lean edgeLo sigma a b = (sig_b - sig_a)/2
# --- MY LEAN (29'): sum_l Dt_il (delta_lj - rho_l * exp(z*edgeLo(j,l)) * Qhat_jl) = 2pi K_ij/z ---
r29 = np.zeros((N,N))
for i in range(N):
  for j in range(N):
    s = sum(Dt[i,l]*((1.0 if l==j else 0.0) - rho[l]*np.exp(zt*eLo(j,l))*Q[j,l]) for l in range(N))
    r29[i,j] = s - 2*np.pi*st.K[0][i,j]/zt
# --- MY LEAN (33'): 2pi sum_l Gt_il (delta_lj - rho_l * exp(z*edgeLo(l,j)) * Qhat_lj) = (A_j+z qp_ij+z^2 Ct_ij/2)/z^2 ---
r33 = np.zeros((N,N))
for i in range(N):
  for j in range(N):
    s = sum(Gt[i,l]*((1.0 if l==j else 0.0) - rho[l]*np.exp(zt*eLo(l,j))*Q[l,j]) for l in range(N))
    rhs = (p['A'][j] + zt*p['qp'][i,j] + zt**2 * p['Ct'][0][i,j]/2.0)/zt**2
    r33[i,j] = 2*np.pi*s - rhs
print("MY Lean (29') recentered residual  max|r| =", np.max(np.abs(r29)))
print("MY Lean (33') recentered residual  max|r| =", np.max(np.abs(r33)))
# --- for contrast: BARE (33') (no recentering, what I wrongly reverted to) ---
r33bare = np.zeros((N,N))
for i in range(N):
  for j in range(N):
    s = sum(Gt[i,l]*((1.0 if l==j else 0.0) - rho[l]*Q[l,j]) for l in range(N))
    rhs = (p['A'][j] + zt*p['qp'][i,j] + zt**2 * p['Ct'][0][i,j]/2.0)/zt**2
    r33bare[i,j] = 2*np.pi*s - rhs
print("BARE (33') (my wrong revert)        max|r| =", np.max(np.abs(r33bare)))
