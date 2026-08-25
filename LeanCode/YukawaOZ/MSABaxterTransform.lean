/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRealSpace

/-!
# MSAEXACT.1 (bounded down-payment) — the MSA Baxter function and its Laplace transform

Group **MSAEXACT** (`proof_notes_msa_exact.md`).  Numerical partner: Group **MSAX**.

The Baxter function of the single-component MSA closure is the **hard-sphere quadratic plus one
exponential per Yukawa tail** (theory note §4):

    q_MSA(r) = q₀(r) + D·e^{−z r}          on the core `[0, σ]`

with `q₀ = q0_poly` the existing hard-sphere Baxter function.  Its one-sided Laplace transform is the
object that enters the Baxter factorization `Q̂(s)·Q̂(−s) = 1 − ρĉ(s)`.

This file supplies the **infrastructure** the factorization is assembled from, all reusing the
`φ`-integral machinery of `HardSphere/BaxterFactor.lean` as the source note prescribes:

* `msaBaxterFn`, `msaBaxterFn_yukawa_zero` — the ansatz, and its `D = 0` reduction **to the exact
  hard-sphere Baxter function `q0_poly`** (the note's own sanity-check corollary);
* `yukawa_laplace_unit` — the Yukawa term's core transform `∫₀^1 e^{−z r}e^{−s r} = (1−e^{−(s+z)})/(s+z)`,
  so `Q̂(s) = Q̂₀(s) − 2πρ·D·(1−e^{−(s+z)})/(s+z)`: the transform is the hard-sphere one plus one
  simple pole per Yukawa tail;
* `yukawa_tail_laplace` — the **exterior** Yukawa tail transform `∫_{r>σ} e^{−z(r−σ)}e^{−s r} = e^{−sσ}/(s+z)`
  (`σ = 1`), the piece the DCF side `1 − ρĉ(s)` needs.

⚠ **Scope.** This is the transform infrastructure only. The full factorization
`|Q̂_MSA(k)|² = 1 − ρ𝓕[c_MSA](k)` — the statement that the ansatz *recovers the MSA closure* `c = −βu`
on the exterior — is the remaining analytic core of MSAEXACT.1: it re-runs
`baxter_wiener_hopf_factorization` with the modified coefficients and the Yukawa tails in both `q` and
`c`, and is not attempted here.  See `proof_notes_msa_exact.md`, MSAEXACT.1.
-/

open MeasureTheory intervalIntegral Real Set

namespace FMSA.ExactMSA

/-- The single-component MSA Baxter function on the core: the hard-sphere Baxter function `q0_poly`
plus one Yukawa exponential (theory note §4). -/
noncomputable def msaBaxterFn (eta sigma rho z Dq : ℝ) (r : ℝ) : ℝ :=
  FMSA.HardSphere.q0_poly eta sigma rho r + Dq * Real.exp (-z * r)

/-- **The `D = 0` reduction (the note's sanity-check corollary).**  With no Yukawa tail the MSA Baxter
function is exactly the hard-sphere one, `q0_poly`. -/
@[simp] theorem msaBaxterFn_yukawa_zero (eta sigma rho z : ℝ) (r : ℝ) :
    msaBaxterFn eta sigma rho z 0 r = FMSA.HardSphere.q0_poly eta sigma rho r := by
  simp [msaBaxterFn]

/-- **The Yukawa term's core Laplace transform** `∫₀^1 e^{−z r}·e^{−s r} dr = (1 − e^{−(s+z)})/(s+z)`,
for `s + z ≠ 0`.  Proved by FTC with antiderivative `−e^{−(s+z)r}/(s+z)`. -/
theorem yukawa_laplace_unit {s z : ℝ} (hsz : s + z ≠ 0) :
    ∫ r in (0 : ℝ)..1, Real.exp (-z * r) * Real.exp (-s * r)
      = (1 - Real.exp (-(s + z))) / (s + z) := by
  have hcomb : (fun r => Real.exp (-z * r) * Real.exp (-s * r))
      = fun r => Real.exp (-(s + z) * r) := by
    funext r; rw [← Real.exp_add]; congr 1; ring
  rw [hcomb]
  have hd : ∀ r : ℝ, HasDerivAt (fun r => -(Real.exp (-(s + z) * r) / (s + z)))
      (Real.exp (-(s + z) * r)) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => -(s + z) * r) (-(s + z)) r := by
      simpa using (hasDerivAt_id r).const_mul (-(s + z))
    have h2 : HasDerivAt (fun r => Real.exp (-(s + z) * r))
        (Real.exp (-(s + z) * r) * -(s + z)) r := h1.exp
    refine ((h2.div_const (s + z)).neg).congr_deriv ?_
    rw [mul_div_assoc, neg_div, div_self hsz, mul_neg_one, neg_neg]
  have hint : IntervalIntegrable (fun r => Real.exp (-(s + z) * r)) volume 0 1 :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hint]
  simp only [mul_one, mul_zero, Real.exp_zero]
  rw [sub_neg_eq_add, ← neg_div, ← add_div, neg_add_eq_sub]

/-- **The exterior Yukawa tail transform** `∫_{r>1} e^{−z(r−1)}·e^{−s r} dr = e^{−s}/(s+z)`, for
`s + z > 0` (`σ = 1`).  This is the DCF-side piece: on the exterior the MSA closure is `c = −βu`, a
Yukawa, and `r·c(r)` is exactly `K e^{−z(r−1)}`, so the `1/r` of the radial transform cancels and the
tail contributes this elementary integral. -/
theorem yukawa_tail_laplace {s z : ℝ} (hsz : 0 < s + z) :
    ∫ r in Ioi (1 : ℝ), Real.exp (-z * (r - 1)) * Real.exp (-s * r)
      = Real.exp (-s) / (s + z) := by
  have hcomb : (fun r => Real.exp (-z * (r - 1)) * Real.exp (-s * r))
      = fun r => Real.exp z * Real.exp (-(s + z) * r) := by
    funext r; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hcomb, MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi (by linarith : -(s + z) < 0) 1,
    mul_one, neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add,
    show z + -(s + z) = -s from by ring]

end FMSA.ExactMSA

