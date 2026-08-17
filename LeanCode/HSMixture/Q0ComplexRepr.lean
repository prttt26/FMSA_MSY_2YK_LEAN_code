/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.Q0Complex
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Analytic representative of the complex Baxter entry at `s = 0` (removable singularity)

The complex Baxter entry `q0_entry_c s …` carries `1/s²` and `1/s³` factors
(`(1 − sσ − e^{−sσ})/s²`, `(1 − sσ + (sσ)²/2 − e^{−sσ})/s³`).  Their singularity at `s = 0` is
**removable** — the numerators vanish to matching order — but the literal expression is undefined at
`s = 0`, so `q0_entry_c` is *not* differentiable there.  For the Tang & Lu contour integral this
matters: the contour crosses `y = 0` (i.e. `s = 0`), where the matrix-inverse holomorphy engine
(`Analysis/MatrixInverseHolomorphic`) needs the Baxter entries `DifferentiableAt`.

This file supplies the fix (item (i) of the eq (20) `A(−iy)`-term wiring): an **entire
representative** `q0_entry_c_repr`, defined by redefining the value at `0` to the removable limit
(`Function.update … (limUnder …)`), with

* `q0_entry_c_repr_eq_of_ne` — it agrees with `q0_entry_c` for `s ≠ 0` (so all existing
  `q0_entry_c`/`Q0_mat_c` theorems transfer, and the integral is unchanged: `{0}` is null);
* `differentiable_q0_entry_c_repr` — it is `DifferentiableAt` **everywhere**, including `s = 0`.

The removable point is handled by Riemann's theorem via **boundedness**
(`differentiableOn_update_limUnder_of_bddAbove`): on a small ball `‖s‖ < 1/(1+‖σ‖)` (so `‖sσ‖ < 1`)
the two pole pieces are bounded by `‖σ‖²`, `‖σ‖³` — from the `exp` Taylor remainders
`Complex.norm_exp_sub_one_sub_id_le` (`‖eᶻ−1−z‖ ≤ ‖z‖²`) and `Complex.exp_bound` (`n = 3`, constant
`4/18 ≤ 1`) — so no explicit limit value is needed.  Everything is axiom-clean
(`propext, Classical.choice, Quot.sound`).
-/

set_option linter.style.longLine false

open Complex Metric Filter Topology Set

namespace FMSA.Q0Complex

/-- Norm bound on the quadratic-pole piece: `‖(1 − sσ − e^{−sσ})/s²‖ ≤ ‖σ‖²` when `‖sσ‖ ≤ 1`. -/
theorem normP2_le {s sigma : ℂ} (hs : s ≠ 0) (hw : ‖s * sigma‖ ≤ 1) :
    ‖(1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2‖ ≤ ‖sigma‖ ^ 2 := by
  have hnum : ‖1 - s * sigma - Complex.exp (-(s * sigma))‖ ≤ ‖s‖ ^ 2 * ‖sigma‖ ^ 2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le (x := -(s * sigma)) (by rwa [norm_neg])
    calc ‖1 - s * sigma - Complex.exp (-(s * sigma))‖
        = ‖Complex.exp (-(s * sigma)) - 1 - -(s * sigma)‖ := by
          rw [show (1 - s * sigma - Complex.exp (-(s * sigma)))
            = -(Complex.exp (-(s * sigma)) - 1 - -(s * sigma)) from by ring, norm_neg]
      _ ≤ ‖-(s * sigma)‖ ^ 2 := h
      _ = ‖s‖ ^ 2 * ‖sigma‖ ^ 2 := by rw [norm_neg, norm_mul, mul_pow]
  rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
  calc ‖1 - s * sigma - Complex.exp (-(s * sigma))‖ ≤ ‖s‖ ^ 2 * ‖sigma‖ ^ 2 := hnum
    _ = ‖sigma‖ ^ 2 * ‖s‖ ^ 2 := by ring

/-- Norm bound on the cubic-pole piece: `‖(1 − sσ + (sσ)²/2 − e^{−sσ})/s³‖ ≤ ‖σ‖³` when `‖sσ‖ ≤ 1`
(the `exp_bound` remainder constant `4/18 ≤ 1`). -/
theorem normP3_le {s sigma : ℂ} (hs : s ≠ 0) (hw : ‖s * sigma‖ ≤ 1) :
    ‖(1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3‖ ≤ ‖sigma‖ ^ 3 := by
  have hsum : ∑ m ∈ Finset.range 3, (-(s * sigma)) ^ m / (m.factorial : ℂ)
      = 1 - s * sigma + (s * sigma) ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]; ring
  have hb := Complex.exp_bound (x := -(s * sigma)) (by rwa [norm_neg]) (n := 3) (by norm_num)
  rw [hsum] at hb
  have hconst : ((3:ℕ).succ : ℝ) * ((3:ℕ).factorial * 3 : ℝ)⁻¹ ≤ 1 := by
    norm_num [Nat.factorial]
  have hnum : ‖1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))‖ ≤ ‖s‖ ^ 3 * ‖sigma‖ ^ 3 := by
    calc ‖1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))‖
        = ‖Complex.exp (-(s * sigma)) - (1 - s * sigma + (s * sigma) ^ 2 / 2)‖ := by
          rw [show (1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma)))
            = -(Complex.exp (-(s * sigma)) - (1 - s * sigma + (s * sigma) ^ 2 / 2)) from by ring, norm_neg]
      _ ≤ ‖-(s * sigma)‖ ^ 3 * (((3:ℕ).succ : ℝ) * ((3:ℕ).factorial * 3 : ℝ)⁻¹) := hb
      _ ≤ ‖-(s * sigma)‖ ^ 3 * 1 := by gcongr
      _ = ‖s‖ ^ 3 * ‖sigma‖ ^ 3 := by rw [mul_one, norm_neg, norm_mul, mul_pow]
  rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
  calc ‖1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))‖ ≤ ‖s‖ ^ 3 * ‖sigma‖ ^ 3 := hnum
    _ = ‖sigma‖ ^ 3 * ‖s‖ ^ 3 := by ring

/-- `q0_entry_c` (as a function of `s`) is holomorphic away from `s = 0`. -/
theorem differentiableAt_q0_entry_c_of_ne {s0 : ℂ} (hs : s0 ≠ 0) (sigma lam Qp Qpp rho δ : ℂ) :
    DifferentiableAt ℂ (fun s => q0_entry_c s sigma lam Qp Qpp rho δ) s0 := by
  have h2 : s0 ^ 2 ≠ 0 := pow_ne_zero _ hs
  have h3 : s0 ^ 3 ≠ 0 := pow_ne_zero _ hs
  simp only [q0_entry_c]
  fun_prop (disch := assumption)

/-- Uniform norm bound on `q0_entry_c` near `s = 0` (via the removable-piece bounds and a bound `B`
on the Yukawa exponential). -/
theorem norm_q0_entry_c_le {s sigma lam Qp Qpp rho δ B : ℂ} (hs : s ≠ 0) (hw : ‖s * sigma‖ ≤ 1)
    (hexp : ‖Complex.exp (-(lam * s))‖ ≤ ‖B‖) :
    ‖q0_entry_c s sigma lam Qp Qpp rho δ‖
      ≤ ‖δ‖ + ‖rho‖ * ‖B‖ * (‖Qp‖ * ‖sigma‖ ^ 2 + ‖Qpp‖ * ‖sigma‖ ^ 3) := by
  have hP2 := normP2_le hs hw
  have hP3 := normP3_le hs hw
  simp only [q0_entry_c]
  have hT : ‖Qp * ((1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2)
        + Qpp * ((1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3)‖
      ≤ ‖Qp‖ * ‖sigma‖ ^ 2 + ‖Qpp‖ * ‖sigma‖ ^ 3 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    gcongr
  calc ‖δ - rho * Complex.exp (-(lam * s))
          * (Qp * ((1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2)
             + Qpp * ((1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3))‖
      ≤ ‖δ‖ + ‖rho * Complex.exp (-(lam * s))
          * (Qp * ((1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2)
             + Qpp * ((1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3))‖ :=
        norm_sub_le _ _
    _ = ‖δ‖ + ‖rho‖ * ‖Complex.exp (-(lam * s))‖
          * ‖Qp * ((1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2)
             + Qpp * ((1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3)‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ ‖δ‖ + ‖rho‖ * ‖B‖ * (‖Qp‖ * ‖sigma‖ ^ 2 + ‖Qpp‖ * ‖sigma‖ ^ 3) := by gcongr

/-- **Analytic (entire) representative of `q0_entry_c` at `s = 0`.**  `q0_entry_c` carries `1/s²`,
`1/s³` factors literally undefined at `s = 0`, but the singularity is removable; this redefines the
value at `0` to the removable limit (`Function.update … (limUnder …)`). -/
noncomputable def q0_entry_c_repr (sigma lam Qp Qpp rho δ : ℂ) : ℂ → ℂ :=
  Function.update (fun s => q0_entry_c s sigma lam Qp Qpp rho δ) 0
    (limUnder (𝓝[≠] (0 : ℂ)) (fun s => q0_entry_c s sigma lam Qp Qpp rho δ))

/-- The representative agrees with `q0_entry_c` away from `s = 0`. -/
theorem q0_entry_c_repr_eq_of_ne {s : ℂ} (hs : s ≠ 0) (sigma lam Qp Qpp rho δ : ℂ) :
    q0_entry_c_repr sigma lam Qp Qpp rho δ s = q0_entry_c s sigma lam Qp Qpp rho δ :=
  Function.update_of_ne hs _ _

/-- **The representative is entire** — `DifferentiableAt` everywhere, including the removable point
`s = 0` (Riemann removable singularity via boundedness). -/
theorem differentiable_q0_entry_c_repr (sigma lam Qp Qpp rho δ : ℂ) :
    Differentiable ℂ (q0_entry_c_repr sigma lam Qp Qpp rho δ) := by
  set f : ℂ → ℂ := fun s => q0_entry_c s sigma lam Qp Qpp rho δ with hf
  set r : ℝ := 1 / (1 + ‖sigma‖) with hr_def
  have hr : 0 < r := by positivity
  have hwbound : ∀ s ∈ ball (0 : ℂ) r, ‖s * sigma‖ ≤ 1 := by
    intro s hsb
    rw [mem_ball_zero_iff] at hsb
    calc ‖s * sigma‖ = ‖s‖ * ‖sigma‖ := norm_mul _ _
      _ ≤ r * ‖sigma‖ := by gcongr
      _ = ‖sigma‖ / (1 + ‖sigma‖) := by rw [hr_def]; ring
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith [norm_nonneg sigma]
  have hexpbound : ∀ s ∈ ball (0 : ℂ) r,
      ‖Complex.exp (-(lam * s))‖ ≤ ‖(Real.exp (‖lam‖ * r) : ℂ)‖ := by
    intro s hsb
    rw [mem_ball_zero_iff] at hsb
    rw [Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    calc (-(lam * s)).re ≤ ‖-(lam * s)‖ := Complex.re_le_norm _
      _ = ‖lam‖ * ‖s‖ := by rw [norm_neg, norm_mul]
      _ ≤ ‖lam‖ * r := by gcongr
  have hDiffOn : DifferentiableOn ℂ f (ball 0 r \ {0}) := fun x hx =>
    (differentiableAt_q0_entry_c_of_ne (by simpa using hx.2) sigma lam Qp Qpp rho δ
      ).differentiableWithinAt
  have hbdd : BddAbove ((norm ∘ f) '' (ball (0 : ℂ) r \ {0})) := by
    refine ⟨‖δ‖ + ‖rho‖ * ‖(Real.exp (‖lam‖ * r) : ℂ)‖ * (‖Qp‖ * ‖sigma‖ ^ 2 + ‖Qpp‖ * ‖sigma‖ ^ 3), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact norm_q0_entry_c_le (by simpa using hx.2) (hwbound x hx.1) (hexpbound x hx.1)
  have hDiffRepr : DifferentiableOn ℂ (q0_entry_c_repr sigma lam Qp Qpp rho δ) (ball 0 r) :=
    differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hr) hDiffOn hbdd
  intro s0
  by_cases hs0 : s0 = 0
  · subst hs0
    exact hDiffRepr.differentiableAt (ball_mem_nhds 0 hr)
  · have heq : q0_entry_c_repr sigma lam Qp Qpp rho δ =ᶠ[𝓝 s0] f := by
      filter_upwards [isOpen_ne.mem_nhds hs0] with x hx
      exact q0_entry_c_repr_eq_of_ne hx sigma lam Qp Qpp rho δ
    exact (differentiableAt_q0_entry_c_of_ne hs0 sigma lam Qp Qpp rho δ).congr_of_eventuallyEq heq

end FMSA.Q0Complex
