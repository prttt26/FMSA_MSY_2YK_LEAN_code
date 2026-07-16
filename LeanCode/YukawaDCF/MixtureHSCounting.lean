/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.MixtureHSZeros

/-!
# Tasks MZERO.9–MZERO.11 (Route B) — Rouché / Jensen zero-counting for `det(Q̂₀)`

The **second, independent** proof that `det(Q̂₀(s))` (N=2) has infinitely many complex zeros — the
Rouché/argument-principle route, run through **Jensen's formula** (Mathlib has no ready Rouché, but
`MeromorphicOn.circleAverage_log_norm` + the zero/pole `divisor` give the same zero-counting).  Route A
(Banach contraction, `Q0_det_c_zeros_infinite` in `MixtureHSZeros.lean`) already closes MZERO.1; this file
provides the independent counting proof, conditional on a *different* analytic input (boundary growth
of `log‖det‖`, MZERO.10) rather than Route A's magnitude bounds (MZERO.5).

## The argument

`det` is `MeromorphicOn` everywhere (`det_meromorphicOn`, MZERO.8) with **no poles**, so
`divisor det ≥ 0`.  Jensen's formula (`MeromorphicOn.circleAverage_log_norm`) reads the boundary
log-average `circleAverage (log‖det‖) 0 R` off the zeros inside `closedBall 0 R`.  If `det` had only
**finitely many** zeros, the divisor stabilises and the RHS is `O(log R)` — but the boundary average
grows `≥ c·R` (MZERO.10, the `e^{−sσ}` growth), and `R ≫ log R`, a contradiction.

## Results

* `DetBoundaryGrowth f` — **MZERO.10**: the boundary average `circleAverage (Real.log ‖f·‖) 0 R` beats
  every log-linear bound `M·log R + C` (implied by the physical `≥ c·R` growth; the sole remaining
  analytic input, numerically confirmed by MZERO.2's quasi-periodic family with `Re(s_n) ~ log Im`).
* `infinite_zeros_of_growth` — **MZERO.11 (structural capstone)**: a Jensen log-bound for the
  finite-zeros case together with `DetBoundaryGrowth` forces `{s : f s = 0}` to be infinite.  Pure
  contradiction; no analysis.
* `detC_zeros_infinite_of_growth` — the capstone specialized to `detC` (Route A's determinant), giving
  the independent Route-B proof of `Set.Infinite {s | detC … s = 0}` (matches
  `Q0_det_c_zeros_infinite`), modulo the Jensen-counting bound (MZERO.9 + Jensen) and `DetBoundaryGrowth`.
* **MZERO.9 `divisor det ≥ 0` — now UNCONDITIONAL** (`det_divisor_nonneg`, axiom-clean).  The only
  hypothesis of `det_divisor_nonneg_of_tendsto` (`det` has a limit at `0`) is discharged by the
  **removable values of the Baxter factors at `s = 0`**: `φ₁(0) = −σ²/2`, `φ₂(0) = σ³/6`
  (`phi1_tendsto`, `phi2_tendsto`), themselves from the exp-Taylor limits `(eʷ−1−w)/w² → ½`,
  `(eʷ−1−w−w²/2)/w³ → ⅙` (`expTaylor2`, `expTaylor3`).  These `s = 0` Taylor coefficients of the Baxter
  entries are **independently reusable for the inner-core polynomial / numerical construction** (cf.
  MPOLY, B.9): `q0_entry_c_tendsto` gives the entry limit `δ − ρ·(Qp·(−σ²/2) + Qpp·(σ³/6))` and
  `detC_tendsto` the `det_fin_two` combination.

Status: structural capstone + `divisor ≥ 0` (MZERO.9) axiom-clean; the only remaining Route-B step is the
Jensen-counting bound (`MeromorphicOn.circleAverage_log_norm` + `divisor ≥ 0` + finite support) with
MZERO.10 the analytic input.
-/

set_option linter.style.longLine false

open MeasureTheory Metric Real Filter Topology

namespace FMSA.MixtureHSPoles

/-! ### MZERO.10 — boundary-growth hypothesis -/

/-- **MZERO.10 — boundary growth of `log‖f‖`.**  The circle-average `circleAverage (Real.log ‖f·‖) 0 R`
eventually exceeds *every* log-linear bound `M·log R + C`.  This is implied by the physical estimate
`circleAverage (log‖det‖) 0 R ≥ c·R − C` (`c > 0`, from the `e^{−sσ}` growth on the `Re s < 0` arc) —
the single analytic input Route B needs, numerically confirmed by MZERO.2 (the quasi-periodic zero family
with `Re(s_n) ~ log Im(s_n)`). -/
def DetBoundaryGrowth (f : ℂ → ℂ) : Prop :=
  ∀ M C R₀ : ℝ, ∃ R : ℝ, R₀ ≤ R ∧ M * Real.log R + C < circleAverage (fun s => Real.log ‖f s‖) 0 R

/-- The physical `≥ c·R` growth (`c > 0`) implies `DetBoundaryGrowth`: an `R`-linear term eventually
dominates any `M·log R + C` (since `Real.log =o[atTop] id`).  Records that `DetBoundaryGrowth` is the
*weaker*, log-comparison form actually consumed by the capstone. -/
theorem detBoundaryGrowth_of_linear {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c) (C₀ : ℝ)
    (hlin : ∀ R : ℝ, c * R - C₀ ≤ circleAverage (fun s => Real.log ‖f s‖) 0 R) :
    DetBoundaryGrowth f := by
  intro M C R₀
  have hlittle : (fun R : ℝ => M * Real.log R) =o[atTop] fun R : ℝ => R :=
    Real.isLittleO_log_id_atTop.const_mul_left M
  have h1 : ∀ᶠ R : ℝ in atTop, ‖M * Real.log R‖ ≤ (c / 2) * ‖R‖ := hlittle.def (by positivity)
  have h2 : ∀ᶠ R : ℝ in atTop, C + C₀ < (c / 2) * R :=
    (Tendsto.const_mul_atTop (by positivity : (0:ℝ) < c / 2) tendsto_id).eventually_gt_atTop (C + C₀)
  obtain ⟨R, ⟨⟨hR1, hR2⟩, hR0⟩, hRge⟩ :=
    (((h1.and h2).and (eventually_ge_atTop (0 : ℝ))).and (eventually_ge_atTop R₀)).exists
  refine ⟨R, hRge, lt_of_lt_of_le ?_ (hlin R)⟩
  have hlog_le : M * Real.log R ≤ (c / 2) * R :=
    le_trans (le_abs_self _) (le_trans hR1 (by rw [Real.norm_eq_abs, abs_of_nonneg hR0]))
  linarith

/-! ### MZERO.11 — structural capstone (Jensen-bound + growth ⟹ infinitely many zeros) -/

/-- **MZERO.11 — structural capstone.**  If (for the finite-zero case) the boundary log-average is bounded
by some `M·log R + C`, but `DetBoundaryGrowth` makes it exceed every such bound, then the zero set is
infinite.  Pure contradiction — the analytic content lives entirely in the two hypotheses. -/
theorem infinite_zeros_of_growth {f : ℂ → ℂ}
    (hJensen : Set.Finite {s : ℂ | f s = 0} →
        ∃ M C R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          circleAverage (fun s => Real.log ‖f s‖) 0 R ≤ M * Real.log R + C)
    (hgrow : DetBoundaryGrowth f) :
    Set.Infinite {s : ℂ | f s = 0} := by
  intro hfin
  obtain ⟨M, C, R₀, hle⟩ := hJensen hfin
  obtain ⟨R, hR0, hlt⟩ := hgrow M C R₀
  exact absurd (hle R hR0) (not_le.mpr hlt)

/-- **MZERO.11 (Route B, specialized to `detC`).**  Independent Rouché/Jensen proof that the N=2
determinant has infinitely many zeros — the same conclusion as Route A's `Q0_det_c_zeros_infinite`,
but conditional on a Jensen-counting bound (`hJensen`, MZERO.9 + `MeromorphicOn.circleAverage_log_norm`)
and boundary growth (`DetBoundaryGrowth`, MZERO.10) instead of Route A's magnitude bounds (MZERO.5).
`det_meromorphicOn` (MZERO.8) already supplies the meromorphy hypothesis Jensen needs. -/
theorem detC_zeros_infinite_of_growth (sigma : Fin 2 → ℝ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ)
    (hJensen : Set.Finite {s : ℂ | detC sigma rho_geo Qp Qpp s = 0} →
        ∃ M C R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          circleAverage (fun s => Real.log ‖detC sigma rho_geo Qp Qpp s‖) 0 R ≤ M * Real.log R + C)
    (hgrow : DetBoundaryGrowth (detC sigma rho_geo Qp Qpp)) :
    Set.Infinite {s : ℂ | detC sigma rho_geo Qp Qpp s = 0} :=
  infinite_zeros_of_growth hJensen hgrow

/-! ### MZERO.9 — `det` has no poles ⇒ `divisor ≥ 0` (the sign input the Jensen bound needs)

The Jensen-counting bound `hJensen` above is discharged from `MeromorphicOn.circleAverage_log_norm`
(Jensen) once (i) `det_meromorphicOn` (MZERO.8, done), (ii) `divisor det U ≥ 0` — `det` has **no poles**:
each `φ = num/sⁿ` has `num` vanishing to order `n` at `s=0` (e.g. `1−sσ−e^{−sσ} ~ −σ²s²/2`), so
`meromorphicOrderAt φ 0 = 0`, and away from `0` `det` is analytic (`Q0_det_c_differentiableAt`) — and
(iii) the finite-support sum bound.  Steps (ii)+(iii) are the mechanical Route-B remainder; (i) is the
already-proved `det_meromorphicOn`. -/

/-- **MZERO.9 (ii) — `det` has no poles ⇒ `divisor det U ≥ 0`, modulo the (obvious) limit at `0`.**
Away from `s = 0` `det` is analytic (`Q0_det_c_differentiableAt` ⇒ `AnalyticAt.meromorphicOrderAt_nonneg`);
at `s = 0` the Lean `det` (`0/0`-valued) still has a *limit* along `𝓝[≠] 0` (its removable value), and
`tendsto_nhds_iff_meromorphicOrderAt_nonneg` turns that limit into `meromorphicOrderAt det 0 ≥ 0`.  The
`∃ c, Tendsto det (𝓝[≠] 0) (𝓝 c)` hypothesis is the physically-obvious "det bounded near 0" fact (its
Lean proof reduces to the exp limit `(e^w−1−w)/w² → 1/2` for `φ₁,φ₂`, not yet formalized). -/
theorem det_divisor_nonneg_of_tendsto (sigma : Fin 2 → ℝ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ)
    (U : Set ℂ) (h0 : ∃ c, Tendsto (detC sigma rho_geo Qp Qpp) (𝓝[≠] (0 : ℂ)) (𝓝 c)) :
    0 ≤ MeromorphicOn.divisor (detC sigma rho_geo Qp Qpp) U := by
  have hmero : ∀ x : ℂ, MeromorphicAt (detC sigma rho_geo Qp Qpp) x :=
    fun x => det_meromorphicAt (fun i => (sigma i : ℂ)) rho_geo Qp Qpp x
  have hdiffOn : DifferentiableOn ℂ (detC sigma rho_geo Qp Qpp) {(0 : ℂ)}ᶜ := fun z hz =>
    (Q0_det_c_differentiableAt (fun i => (sigma i : ℂ)) rho_geo Qp Qpp hz).differentiableWithinAt
  intro z
  by_cases hz : z ∈ U
  · by_cases hz0 : z = 0
    · subst hz0
      have hord : 0 ≤ meromorphicOrderAt (detC sigma rho_geo Qp Qpp) 0 :=
        (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hmero 0)).mp h0
      simp [MeromorphicOn.divisor_apply (fun x _ => hmero x) hz, hord]
    · have hana : AnalyticAt ℂ (detC sigma rho_geo Qp Qpp) z :=
        hdiffOn.analyticAt (isOpen_compl_singleton.mem_nhds hz0)
      simp [MeromorphicOn.divisor_apply (fun x _ => hmero x) hz, hana.meromorphicOrderAt_nonneg]
  · simp [hz]

/-! ### MZERO.9 (i) — the exp-Taylor limits: `det` has a limit at `0`, so `divisor ≥ 0` is unconditional

The `s=0` removable values of the Baxter factors `φ₁,φ₂` — `φ₁(0) = −σ²/2`, `φ₂(0) = σ³/6` — are the
`s=0` Taylor coefficients of the Baxter entries (cf. MPOLY / B.9); proving them discharges the "det has
a limit at 0" hypothesis of `det_divisor_nonneg_of_tendsto` and is independently useful for numerics. -/

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
Taylor coefficient of the Baxter entry (cf. MPOLY, B.9). -/
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

/-- **Removable value of a Baxter matrix entry.**  As `s → 0` the complex entry `q0_entry_c` tends to
`δ − ρ·(Qp·(−σ²/2) + Qpp·(σ³/6))` (`e^{−λs} → 1`, `φ₁ → −σ²/2`, `φ₂ → σ³/6`).  These are the `s = 0`
Taylor coefficients of the Baxter entry (cf. MPOLY / B.9). -/
theorem q0_entry_c_tendsto (σ lam Qp Qpp ρ δ : ℂ) (hσ : σ ≠ 0) :
    Tendsto (fun s : ℂ => FMSA.Q0Complex.q0_entry_c s σ lam Qp Qpp ρ δ) (𝓝[≠] (0 : ℂ))
      (𝓝 (δ - ρ * (Qp * (-σ ^ 2 / 2) + Qpp * (σ ^ 3 / 6)))) := by
  have hexp : Tendsto (fun s : ℂ => Complex.exp (-(lam * s))) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have hc : Continuous (fun s : ℂ => Complex.exp (-(lam * s))) := by fun_prop
    have h := hc.tendsto (0 : ℂ)
    simp only [mul_zero, neg_zero, Complex.exp_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hbracket := ((phi1_tendsto σ hσ).const_mul Qp).add ((phi2_tendsto σ hσ).const_mul Qpp)
  have hprod := (hexp.const_mul ρ).mul hbracket
  have hconst : Tendsto (fun _ : ℂ => δ) (𝓝[≠] (0 : ℂ)) (𝓝 δ) := tendsto_const_nhds
  have hfin := hconst.sub hprod
  simp only [mul_one] at hfin
  exact hfin

/-- **MZERO.9 (i), `det` has a limit at `0`.**  For `N = 2` with nonzero diameters, `det(Q̂₀(s))` has a
(finite) removable limit as `s → 0`: `det = M₀₀·M₁₁ − M₀₁·M₁₀` (`det_fin_two`) and every entry
`Mᵢⱼ = q0_entry_c` has the removable value of `q0_entry_c_tendsto`. -/
theorem detC_tendsto (sigma : Fin 2 → ℝ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ)
    (hσ : ∀ i, (sigma i : ℂ) ≠ 0) :
    ∃ c, Tendsto (detC sigma rho_geo Qp Qpp) (𝓝[≠] (0 : ℂ)) (𝓝 c) := by
  have h00 : Tendsto
      (fun s => FMSA.Q0Complex.Q0_mat_c s (fun i => (sigma i : ℂ)) rho_geo Qp Qpp 0 0)
      (𝓝[≠] (0 : ℂ)) (𝓝 _) := q0_entry_c_tendsto _ _ _ _ _ _ (hσ 0)
  have h11 : Tendsto
      (fun s => FMSA.Q0Complex.Q0_mat_c s (fun i => (sigma i : ℂ)) rho_geo Qp Qpp 1 1)
      (𝓝[≠] (0 : ℂ)) (𝓝 _) := q0_entry_c_tendsto _ _ _ _ _ _ (hσ 1)
  have h01 : Tendsto
      (fun s => FMSA.Q0Complex.Q0_mat_c s (fun i => (sigma i : ℂ)) rho_geo Qp Qpp 0 1)
      (𝓝[≠] (0 : ℂ)) (𝓝 _) := q0_entry_c_tendsto _ _ _ _ _ _ (hσ 0)
  have h10 : Tendsto
      (fun s => FMSA.Q0Complex.Q0_mat_c s (fun i => (sigma i : ℂ)) rho_geo Qp Qpp 1 0)
      (𝓝[≠] (0 : ℂ)) (𝓝 _) := q0_entry_c_tendsto _ _ _ _ _ _ (hσ 1)
  have heq : (fun s => FMSA.Q0Complex.Q0_mat_c s (fun i => (sigma i : ℂ)) rho_geo Qp Qpp 0 0
        * FMSA.Q0Complex.Q0_mat_c s (fun i => (sigma i : ℂ)) rho_geo Qp Qpp 1 1
        - FMSA.Q0Complex.Q0_mat_c s (fun i => (sigma i : ℂ)) rho_geo Qp Qpp 0 1
        * FMSA.Q0Complex.Q0_mat_c s (fun i => (sigma i : ℂ)) rho_geo Qp Qpp 1 0)
      =ᶠ[𝓝[≠] (0 : ℂ)] detC sigma rho_geo Qp Qpp := by
    filter_upwards with s
    unfold detC
    exact (Matrix.det_fin_two _).symm
  exact ⟨_, ((h00.mul h11).sub (h01.mul h10)).congr' heq⟩

/-- **MZERO.9, unconditional.**  `divisor(det(Q̂₀)) ≥ 0` on any `U` (no pole at `0`): the removable
limit `detC_tendsto` discharges the `∃ c, Tendsto` hypothesis of `det_divisor_nonneg_of_tendsto`.
This nails the MZERO.9(ii) obligation with no remaining `Tendsto` hypothesis. -/
theorem det_divisor_nonneg (sigma : Fin 2 → ℝ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ)
    (hσ : ∀ i, sigma i ≠ 0) (U : Set ℂ) :
    0 ≤ MeromorphicOn.divisor (detC sigma rho_geo Qp Qpp) U :=
  det_divisor_nonneg_of_tendsto sigma rho_geo Qp Qpp U
    (detC_tendsto sigma rho_geo Qp Qpp (fun i => Complex.ofReal_ne_zero.mpr (hσ i)))

end FMSA.MixtureHSPoles
