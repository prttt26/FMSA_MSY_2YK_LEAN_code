/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterPoles

/-!
# `G_baxter` has an EXACT triple zero at the origin, with leading coefficient `i(1+2η)/(1−η)²`

This file supplies **input 3** of the homotopy route to `MA.14`
(`baxter_no_open_lhp_pole_core`); see `proof_notes_pole.md` → "POLE.11-general / MA.14".

## Why this is needed

Any contour count of `G_baxter`'s zeros in the *open lower half-plane* has the origin sitting **on
the contour**, and `G_baxter 0 = 0`.  Numerically this poisons the count outright: the raw winding
number over a lower box is unstable garbage (it reads `−1` at some radii, `−2` at others), and only
after deflating `k³` does it settle to the true value `0` for every `η ∈ (0,1)`
(`verify_ma14_route.py`).  So the homotopy argument needs to know the zero at the origin is of
*exactly* order 3 — never order 4 — uniformly in the parameters: otherwise a zero could split off
from the origin into the half-plane as `η` varies, and the count would not be locally constant.

## The clean route (no Taylor remainder needed)

The naive approach expands `exp (-ikσ)` to third order and fights an `O(k³)` Peano remainder.  That
is unnecessary here: the bridge `baxter_cube_mul_F_eq_G` **already** factors the cube out exactly,

  `(-ik)³ · (1 - Qhat_complex k) = G_baxter k`      (`k ≠ 0`),

and `(-i)³ = i`, so `G_baxter k / k³ = i · (1 - Qhat_complex k)` *identically* — an equation, not a
limit.  The leading coefficient is therefore just `i · (1 - Qhat_complex 0)`, and `Qhat_complex 0`
is a **plain polynomial integral** (`exp 0 = 1`), evaluated here in closed form.  The
transcendental part of the problem disappears entirely.

## Result

`one_sub_Qhat_complex_zero`:   `1 - Qhat_complex η σ ρ 0 = (1+2η)/(1−η)²`

which is `σ`- and `ρ`-free after using `η = πρσ³/6`, manifestly nonzero on `η ∈ (0,1)`, and matches
the numerics to `≲1e-6` over `η ∈ [0.01,0.99] × σ ∈ {0.7,1.0,2.3}`.

Consistency check: this says `Qhat_complex 0 = -η(4−η)/(1−η)²`, so `‖Qhat_complex 0‖ = M(η)`, the
kernel mass `∫₀^σ|q0_poly|` computed for the dilute route (`BaxterDiluteDecay.lean`) — as it must
be, `q0_poly` being single-signed on the core.  The dilute wall `M(η) < 1 ⟺ η < (3−√7)/2` is
exactly the statement that this leading-coefficient fact is *not* by itself enough at larger `η`.
-/

open intervalIntegral

namespace FMSA.HardSphere

noncomputable section

/-- Antiderivative of `q0_poly`'s inner quadratic form. -/
private noncomputable def q0PolyPrimitive (eta sigma rho : ℝ) (r : ℝ) : ℝ :=
  rho * q_prime_py eta sigma * (r - sigma) ^ 2 / 2 +
    rho * q_doubleprime_py eta * (r - sigma) ^ 3 / 6

private theorem hasDerivAt_q0PolyPrimitive (eta sigma rho : ℝ) (r : ℝ) :
    HasDerivAt (q0PolyPrimitive eta sigma rho)
      (rho * q_prime_py eta sigma * (r - sigma) +
        rho * q_doubleprime_py eta * (r - sigma) ^ 2 / 2) r := by
  have hbase : HasDerivAt (fun x : ℝ => x - sigma) 1 r := (hasDerivAt_id r).sub_const sigma
  -- `.pow` produces the *pointwise* function power `(fun x => x - σ) ^ 2`, which does not
  -- definitionally match `fun x => (x - σ) ^ 2` (and drags in a different module instance), so
  -- build the powers by `.mul` with the target type pinned explicitly.
  have h2 : HasDerivAt (fun x : ℝ => (x - sigma) ^ 2) (2 * (r - sigma)) r := by
    have h := hbase.mul hbase
    have : HasDerivAt (fun x : ℝ => (x - sigma) * (x - sigma))
        (1 * (r - sigma) + (r - sigma) * 1) r := h
    simpa [pow_two] using this.congr_deriv (by ring)
  have h3 : HasDerivAt (fun x : ℝ => (x - sigma) ^ 3) (3 * (r - sigma) ^ 2) r := by
    have h := h2.mul hbase
    have : HasDerivAt (fun x : ℝ => (x - sigma) ^ 2 * (x - sigma))
        (2 * (r - sigma) * (r - sigma) + (r - sigma) ^ 2 * 1) r := h
    simpa [pow_succ] using this.congr_deriv (by ring)
  have hsum : HasDerivAt
      (fun x : ℝ => rho * q_prime_py eta sigma * (x - sigma) ^ 2 / 2 +
        rho * q_doubleprime_py eta * (x - sigma) ^ 3 / 6)
      (rho * q_prime_py eta sigma * (2 * (r - sigma)) / 2 +
        rho * q_doubleprime_py eta * (3 * (r - sigma) ^ 2) / 6) r :=
    ((h2.const_mul (rho * q_prime_py eta sigma)).div_const 2).add
      ((h3.const_mul (rho * q_doubleprime_py eta)).div_const 6)
  exact hsum.congr_deriv (by ring)

/-- `∫₀^σ q0_poly = -ρq'σ²/2 + ρq''σ³/6`.  Elementary FTC on the inner quadratic. -/
theorem integral_q0_poly_zero_sigma (eta sigma rho : ℝ) (hsigma : 0 < sigma) :
    (∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r) =
      -(rho * q_prime_py eta sigma * sigma ^ 2 / 2) +
        rho * q_doubleprime_py eta * sigma ^ 3 / 6 := by
  have hcongr : (∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r) =
      ∫ r in (0:ℝ)..sigma, (rho * q_prime_py eta sigma * (r - sigma) +
        rho * q_doubleprime_py eta * (r - sigma) ^ 2 / 2) := by
    refine intervalIntegral.integral_congr (fun r hr => ?_)
    rw [Set.uIcc_of_le hsigma.le] at hr
    exact q0_poly_inner hr.2
  rw [hcongr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hasDerivAt_q0PolyPrimitive eta sigma rho r)
      ((Continuous.intervalIntegrable (by continuity) _ _))]
  simp only [q0PolyPrimitive]
  ring

/-- `Qhat_complex` at the origin: the exponential is `1`, so this is the plain integral above. -/
theorem Qhat_complex_zero (eta sigma rho : ℝ) (hsigma : 0 < sigma) :
    Qhat_complex eta sigma rho 0 =
      ((-(rho * q_prime_py eta sigma * sigma ^ 2 / 2) +
        rho * q_doubleprime_py eta * sigma ^ 3 / 6 : ℝ) : ℂ) := by
  have hexp : ∀ r : ℝ, Complex.exp (-Complex.I * 0 * r) = 1 := by
    intro r; simp
  calc Qhat_complex eta sigma rho 0
      = ∫ r in (0:ℝ)..sigma, ((q0_poly eta sigma rho r : ℝ) : ℂ) := by
        unfold Qhat_complex
        exact intervalIntegral.integral_congr (fun r _ => by rw [hexp r, mul_one])
    _ = ((∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r : ℝ) : ℂ) := by
        rw [intervalIntegral.integral_ofReal]
    _ = _ := by rw [integral_q0_poly_zero_sigma eta sigma rho hsigma]

/-- **Input 3 of the `MA.14` homotopy route — closed form of the leading coefficient.**
`1 - Qhat_complex 0 = (1+2η)/(1−η)²`.  Note this is `σ`- and `ρ`-free: the physical relation
`η = πρσ³/6` collapses everything. -/
theorem one_sub_Qhat_complex_zero {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta1 : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    1 - Qhat_complex eta sigma rho 0 = (((1 + 2 * eta) / (1 - eta) ^ 2 : ℝ) : ℂ) := by
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hs : (sigma : ℝ) ≠ 0 := ne_of_gt hsigma
  have hden : ((1 : ℝ) - eta) ≠ 0 := by linarith
  have hrho : rho = 6 * eta / (Real.pi * sigma ^ 3) := by
    field_simp at heta_def ⊢; linarith [heta_def]
  rw [Qhat_complex_zero eta sigma rho hsigma]
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) from by norm_num, ← Complex.ofReal_sub]
  norm_cast
  rw [q_prime_py, q_doubleprime_py, hrho]
  field_simp
  ring

/-- `1 - Qhat_complex 0 ≠ 0` for every physical `η ∈ (0,1)` — so the origin zero of `G_baxter` is of
order **exactly** 3, never higher, uniformly in the parameters. -/
theorem one_sub_Qhat_complex_zero_ne_zero {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (hsigma : 0 < sigma) (heta1 : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    1 - Qhat_complex eta sigma rho 0 ≠ 0 := by
  rw [one_sub_Qhat_complex_zero hsigma heta1 heta_def]
  have hden : (0 : ℝ) < 1 - eta := by linarith
  have hpos : (0 : ℝ) < (1 + 2 * eta) / (1 - eta) ^ 2 :=
    div_pos (by linarith) (by positivity)
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)

/-- **`G_baxter k = i·k³·(1 - Q̂(k))`.**  The cube is factored out *exactly*: this is
`baxter_cube_mul_F_eq_G` with `(-i)³ = i` evaluated.  No limit, no Taylor remainder. -/
theorem G_baxter_eq_I_mul_cube (eta sigma rho : ℝ) (hsigma : 0 < sigma) {k : ℂ} (hk : k ≠ 0) :
    G_baxter eta sigma rho k = Complex.I * k ^ 3 * (1 - Qhat_complex eta sigma rho k) := by
  rw [← baxter_cube_mul_F_eq_G eta sigma rho hsigma hk]
  have hI3 : (-Complex.I) ^ 3 = Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, neg_pow, Complex.I_sq]; ring
  rw [mul_pow, hI3]

/-- **The deflated quotient is `i·(1 - Q̂)`, identically.**  This is the object whose zeros the
`MA.14` homotopy count is taken over — see the file docstring for why the undeflated `G_baxter`
cannot be counted. -/
theorem G_baxter_div_cube (eta sigma rho : ℝ) (hsigma : 0 < sigma) {k : ℂ} (hk : k ≠ 0) :
    G_baxter eta sigma rho k / k ^ 3 = Complex.I * (1 - Qhat_complex eta sigma rho k) := by
  rw [G_baxter_eq_I_mul_cube eta sigma rho hsigma hk]
  field_simp

/-- **Exact order-3 zero at the origin.**  `G_baxter k / k³ → i(1+2η)/(1−η)² ≠ 0` as `k → 0`, so the
origin carries a zero of order exactly 3 and no zero can split off it into the lower half-plane as
`η` varies — input 3 of the homotopy route to `MA.14`. -/
theorem G_baxter_div_cube_tendsto_origin {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta1 : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    Filter.Tendsto (fun k => G_baxter eta sigma rho k / k ^ 3) (nhdsWithin 0 {(0 : ℂ)}ᶜ)
      (nhds (Complex.I * (((1 + 2 * eta) / (1 - eta) ^ 2 : ℝ) : ℂ))) := by
  have hcont : Filter.Tendsto (fun k => Complex.I * (1 - Qhat_complex eta sigma rho k))
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (Complex.I * (1 - Qhat_complex eta sigma rho 0))) := by
    refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact (((Qhat_complex_entire eta sigma rho hsigma).continuous.tendsto 0).const_sub
      1).const_mul Complex.I
  rw [one_sub_Qhat_complex_zero hsigma heta1 heta_def] at hcont
  refine hcont.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  exact (G_baxter_div_cube eta sigma rho hsigma hk).symm

end

end FMSA.HardSphere
