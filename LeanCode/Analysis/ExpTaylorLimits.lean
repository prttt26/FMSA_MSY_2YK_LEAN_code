/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Taylor limits of `exp` at the origin, and the two Laplace kernels

Removable-singularity limits as `s → 0`, all for an **arbitrary** complex parameter — no physics
enters, which is why this lives in `Analysis/` (split out of `HSMixture/MixtureHSCounting.lean` on
2026-07-19).

* `remainder_div_tendsto_zero` — an analytic function vanishing to order `> n` at `0`, divided by
  `w ^ n`, tends to `0`. The engine for the two Taylor limits below.
* `expTaylor2`, `expTaylor3` — `(eᵂ − 1 − w)/w²  → 1/2` and `(eᵂ − 1 − w − w²/2)/w³ → 1/6`.
* `phi1_tendsto`, `phi2_tendsto` — the two Baxter Laplace kernels `(1 − sσ − e^{−sσ})/s²` and
  `(1 − sσ + (sσ)²/2 − e^{−sσ})/s³` have removable singularities at `s = 0`, with limits `−σ²/2`
  and `σ³/6`. Stated for any `σ ≠ 0`; the hard-sphere reading (σ = a diameter) is not used.
-/

set_option linter.style.longLine false

open Filter Topology

namespace FMSA.ExpTaylorLimits

/-- **Reusable remainder limit.**  If `f` is analytic at `0` with `analyticOrderAt f 0 ≥ n+1` (a zero
of order `> n`), then `f w / wⁿ → 0`.  (`natCast_le_analyticOrderAt` factors `f =ᶠ w^{n+1}·g`, so
`f w / wⁿ = w·g w → 0`.) -/
theorem remainder_div_tendsto_zero {f : ℂ → ℂ} {n : ℕ} (hf : AnalyticAt ℂ f 0)
    (hn : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f 0) :
    Tendsto (fun w : ℂ => f w / w ^ n) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  obtain ⟨g, hg, hgeq⟩ := (natCast_le_analyticOrderAt hf).mp hn
  have hcong : (fun w : ℂ => f w / w ^ n) =ᶠ[𝓝[≠] (0 : ℂ)] fun w => w * g w := by
    filter_upwards [hgeq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hw0
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hw0
    rw [hw]
    simp only [sub_zero, smul_eq_mul, pow_succ]
    field_simp
  rw [tendsto_congr' hcong]
  have h1 : Tendsto (fun w : ℂ => w) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) :=
    hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simpa using h1.mul h2

/-- **Order-2 exp-Taylor limit:** `(e^w − 1 − w)/w² → 1/2` (`w → 0`, `w ≠ 0`). -/
theorem expTaylor2 :
    Tendsto (fun w : ℂ => (Complex.exp w - 1 - w) / w ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 2)) := by
  set q3 : ℂ → ℂ := fun w => Complex.exp w - 1 - w - w ^ 2 / 2 with hq3
  have hq3an : AnalyticAt ℂ q3 0 := by rw [hq3]; fun_prop
  have hd3 : deriv q3 = fun w => Complex.exp w - 1 - w := by
    funext w
    exact (((Complex.hasDerivAt_exp w).sub_const 1).sub (hasDerivAt_id w)).sub
      (by simpa using (hasDerivAt_pow 2 w).div_const 2) |>.deriv
  have hd2 : deriv (fun w : ℂ => Complex.exp w - 1 - w) = fun w => Complex.exp w - 1 := by
    funext w
    exact (((Complex.hasDerivAt_exp w).sub_const 1).sub (hasDerivAt_id w)).deriv
  have hord : ((3 : ℕ) : ℕ∞) ≤ analyticOrderAt q3 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hq3an]
    intro i hi
    interval_cases i
    · simp [hq3]
    · rw [iteratedDeriv_one, hd3]; simp
    · rw [iteratedDeriv_succ, iteratedDeriv_one, hd3, hd2]; simp
  have hrem := remainder_div_tendsto_zero (n := 2) hq3an hord
  have hcong : (fun w : ℂ => (Complex.exp w - 1 - w) / w ^ 2)
      =ᶠ[𝓝[≠] (0 : ℂ)] fun w => 1 / 2 + q3 w / w ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with w hw0
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hw0
    rw [hq3]; field_simp; ring
  rw [tendsto_congr' hcong]
  simpa using tendsto_const_nhds.add hrem

/-- **Order-3 exp-Taylor limit:** `(e^w − 1 − w − w²/2)/w³ → 1/6` (`w → 0`, `w ≠ 0`). -/
theorem expTaylor3 :
    Tendsto (fun w : ℂ => (Complex.exp w - 1 - w - w ^ 2 / 2) / w ^ 3) (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 6)) := by
  have hp2 : ∀ w : ℂ, HasDerivAt (fun w : ℂ => w ^ 2 / 2) w w := fun w => by
    simpa using (hasDerivAt_pow 2 w).div_const 2
  have hp3 : ∀ w : ℂ, HasDerivAt (fun w : ℂ => w ^ 3 / 6) (w ^ 2 / 2) w := fun w => by
    have h : HasDerivAt (fun w : ℂ => w ^ 3) (3 * w ^ 2) w := by simpa using hasDerivAt_pow 3 w
    have h6 := h.div_const 6
    rwa [show 3 * w ^ 2 / 6 = w ^ 2 / 2 from by ring] at h6
  set q4 : ℂ → ℂ := fun w => Complex.exp w - 1 - w - w ^ 2 / 2 - w ^ 3 / 6 with hq4
  have hq4an : AnalyticAt ℂ q4 0 := by rw [hq4]; fun_prop
  have hd4 : deriv q4 = fun w => Complex.exp w - 1 - w - w ^ 2 / 2 := by
    funext w
    exact ((((Complex.hasDerivAt_exp w).sub_const 1).sub (hasDerivAt_id w)).sub
      (hp2 w)).sub (hp3 w) |>.deriv
  have hd3 : deriv (fun w : ℂ => Complex.exp w - 1 - w - w ^ 2 / 2)
      = fun w => Complex.exp w - 1 - w := by
    funext w
    exact (((Complex.hasDerivAt_exp w).sub_const 1).sub (hasDerivAt_id w)).sub (hp2 w) |>.deriv
  have hd2 : deriv (fun w : ℂ => Complex.exp w - 1 - w) = fun w => Complex.exp w - 1 := by
    funext w
    exact (((Complex.hasDerivAt_exp w).sub_const 1).sub (hasDerivAt_id w)).deriv
  have hord : ((4 : ℕ) : ℕ∞) ≤ analyticOrderAt q4 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hq4an]
    intro i hi
    interval_cases i
    · simp [hq4]
    · rw [iteratedDeriv_one, hd4]; simp
    · rw [iteratedDeriv_succ, iteratedDeriv_one, hd4, hd3]; simp
    · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, hd4, hd3, hd2]; simp
  have hrem := remainder_div_tendsto_zero (n := 3) hq4an hord
  have hcong : (fun w : ℂ => (Complex.exp w - 1 - w - w ^ 2 / 2) / w ^ 3)
      =ᶠ[𝓝[≠] (0 : ℂ)] fun w => 1 / 6 + q4 w / w ^ 3 := by
    filter_upwards [self_mem_nhdsWithin] with w hw0
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hw0
    rw [hq4]; field_simp; ring
  rw [tendsto_congr' hcong]
  simpa using tendsto_const_nhds.add hrem

/-- The substitution map `s ↦ −sσ` sends `𝓝[≠] 0` to `𝓝[≠] 0` (for `σ ≠ 0`). -/
theorem neg_mul_tendsto_punctured {σ : ℂ} (hσ : σ ≠ 0) :
    Tendsto (fun s : ℂ => -(s * σ)) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun s : ℂ => -(s * σ)) (𝓝 (0 : ℂ)) (𝓝 0) := by
      simpa using ((continuous_id.mul continuous_const).neg).tendsto (0 : ℂ)
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
    exact neg_ne_zero.mpr (mul_ne_zero hs hσ)

/-- **Baxter `φ₁` removable value:** `φ₁(s) = (1 − sσ − e^{−sσ})/s² → −σ²/2` as `s → 0`.  The `s=0`
Taylor coefficient of the Baxter entry (cf. MPOLY, GAP.9). -/
theorem phi1_tendsto (σ : ℂ) (hσ : σ ≠ 0) :
    Tendsto (fun s : ℂ => (1 - s * σ - Complex.exp (-(s * σ))) / s ^ 2) (𝓝[≠] (0 : ℂ))
      (𝓝 (-σ ^ 2 / 2)) := by
  have hg := (expTaylor2.comp (neg_mul_tendsto_punctured hσ)).const_mul (-σ ^ 2)
  rw [show -σ ^ 2 * (1 / 2) = -σ ^ 2 / 2 from by ring] at hg
  refine hg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  have hsσ : s * σ ≠ 0 := mul_ne_zero hs hσ
  simp only [Function.comp_apply]
  field_simp
  ring

/-- **Baxter `φ₂` removable value:** `φ₂(s) = (1 − sσ + (sσ)²/2 − e^{−sσ})/s³ → σ³/6` as `s → 0`. -/
theorem phi2_tendsto (σ : ℂ) (hσ : σ ≠ 0) :
    Tendsto (fun s : ℂ => (1 - s * σ + (s * σ) ^ 2 / 2 - Complex.exp (-(s * σ))) / s ^ 3)
      (𝓝[≠] (0 : ℂ)) (𝓝 (σ ^ 3 / 6)) := by
  have hg := (expTaylor3.comp (neg_mul_tendsto_punctured hσ)).const_mul (σ ^ 3)
  rw [show σ ^ 3 * (1 / 6) = σ ^ 3 / 6 from by ring] at hg
  refine hg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  have hsσ : s * σ ≠ 0 := mul_ne_zero hs hσ
  simp only [Function.comp_apply]
  field_simp
  ring

/-! ### MZERO.9 (i) — chaining the `φ`-limits into `det` -/

end FMSA.ExpTaylorLimits
