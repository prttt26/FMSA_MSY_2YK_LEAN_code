/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.MixtureHSZeros
import LeanCode.Analysis.JensenCounting
import LeanCode.Analysis.BoundaryGrowth
import LeanCode.Analysis.ExpTaylorLimits

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
  MPOLY, GAP.9): `q0_entry_c_tendsto` gives the entry limit `δ − ρ·(Qp·(−σ²/2) + Qpp·(σ³/6))` and
  `detC_tendsto` the `det_fin_two` combination.

Status: structural capstone + `divisor ≥ 0` (MZERO.9) axiom-clean; the only remaining Route-B step is the
Jensen-counting bound (`MeromorphicOn.circleAverage_log_norm` + `divisor ≥ 0` + finite support) with
MZERO.10 the analytic input.
-/

set_option linter.style.longLine false

open MeasureTheory Metric Real Filter Topology

open FMSA.BoundaryGrowth FMSA.ExpTaylorLimits

namespace FMSA.MixtureHSPoles

/-! ### MZERO.10 — boundary-growth hypothesis -/

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
`s=0` Taylor coefficients of the Baxter entries (cf. MPOLY / GAP.9); proving them discharges the "det has
a limit at 0" hypothesis of `det_divisor_nonneg_of_tendsto` and is independently useful for numerics. -/

/-- **Removable value of a Baxter matrix entry.**  As `s → 0` the complex entry `q0_entry_c` tends to
`δ − ρ·(Qp·(−σ²/2) + Qpp·(σ³/6))` (`e^{−λs} → 1`, `φ₁ → −σ²/2`, `φ₂ → σ³/6`).  These are the `s = 0`
Taylor coefficients of the Baxter entry (cf. MPOLY / GAP.9). -/
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

/-! ### MZERO.9 (iii) — the Jensen-counting bound `hJensen`, now PROVED

The final Route-B piece.  The **abstract** Jensen counting bound is `MA.5`
(`circleAverage_log_norm_le_of_finite_zeros`, `Analysis/JensenCounting.lean`): for `f` meromorphic on
`ℂ` with no poles (`divisor ≥ 0`) and **finite divisor support**, `circleAverage (log‖f·‖) 0 R ≤
M·log R + C`.  What was left to the MZERO owner is the **`detC`-specific bridge**: the *literal* finite
zero set `{s | detC s = 0}` ⇒ the divisor support is finite.  That bridge is `hfindiv` below — every
`u` with `divisor detC univ u ≠ 0` is either `0` (the removable point, whose Lean junk value need not
vanish) or a point where `detC` is analytic (`Q0_det_c_differentiableAt`, `u ≠ 0`) with positive order,
hence a genuine zero (`AnalyticAt.analyticOrderAt_ne_zero`).  So the support sits in `{0} ∪ zeros`,
finite.  Feeding MA.5 discharges the `hJensen` hypothesis of `infinite_zeros_of_growth`. -/

/-- **MZERO.9 (iii) — the Jensen-counting bound for `detC`.**  If `detC` has finitely many zeros, its
boundary log-average is `O(log R)`: `circleAverage (log‖detC·‖) 0 R ≤ M·log R + C` eventually.  The
`detC`-specific bridge (finite literal zeros ⇒ finite divisor support) feeding the abstract MA.5
`circleAverage_log_norm_le_of_finite_zeros`.  Axiom-clean; the exact statement consumed by
`infinite_zeros_of_growth`'s `hJensen`. -/
theorem detC_jensen_log_bound (sigma : Fin 2 → ℝ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ)
    (hσ : ∀ i, sigma i ≠ 0) :
    Set.Finite {s : ℂ | detC sigma rho_geo Qp Qpp s = 0} →
      ∃ M C R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        circleAverage (fun s => Real.log ‖detC sigma rho_geo Qp Qpp s‖) 0 R
          ≤ M * Real.log R + C := by
  intro hfin
  set f := detC sigma rho_geo Qp Qpp with hf
  have hmero : MeromorphicOn f Set.univ := by
    rw [hf]; exact det_meromorphicOn (fun i => (sigma i : ℂ)) rho_geo Qp Qpp Set.univ
  have hdiv : 0 ≤ MeromorphicOn.divisor f Set.univ := by
    rw [hf]; exact det_divisor_nonneg sigma rho_geo Qp Qpp hσ Set.univ
  -- the `detC`-specific bridge: finite literal zeros ⇒ finite divisor support
  have hfindiv : (MeromorphicOn.divisor f Set.univ).support.Finite := by
    refine Set.Finite.subset (hfin.insert 0) ?_
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.mem_insert_iff]
    by_cases hu0 : u = 0
    · exact Or.inl hu0
    · refine Or.inr ?_
      change f u = 0
      have hdiffOn : DifferentiableOn ℂ f {(0 : ℂ)}ᶜ := by
        rw [hf]; exact fun z hz =>
          (Q0_det_c_differentiableAt (fun i => (sigma i : ℂ)) rho_geo Qp Qpp hz).differentiableWithinAt
      have hA : AnalyticAt ℂ f u := hdiffOn.analyticAt (isOpen_compl_singleton.mem_nhds hu0)
      rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ u)] at hu
      have hord : meromorphicOrderAt f u ≠ 0 := by
        intro h; rw [h] at hu; simp at hu
      rw [← hA.analyticOrderAt_ne_zero]
      intro h0
      exact hord (by rw [hA.meromorphicOrderAt_eq, h0]; simp)
  exact circleAverage_log_norm_le_of_finite_zeros hmero hdiv hfindiv

/-- **MZERO.11 (Route B), now needing only boundary growth (MZERO.10).**  With the Jensen-counting
bound `detC_jensen_log_bound` proved, the independent Route-B infinitude of the zeros of `det(Q̂₀)`
rests on **only** `DetBoundaryGrowth` (MZERO.10, the `e^{−sσ}` boundary growth) — the `hJensen`
hypothesis of `detC_zeros_infinite_of_growth` is discharged.  This is Route B's counterpart to Route
A's `Q0_det_c_zeros_infinite` (which rests on the MZERO.5 magnitude bounds). -/
theorem detC_zeros_infinite_of_boundaryGrowth (sigma : Fin 2 → ℝ)
    (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ) (hσ : ∀ i, sigma i ≠ 0)
    (hgrow : DetBoundaryGrowth (detC sigma rho_geo Qp Qpp)) :
    Set.Infinite {s : ℂ | detC sigma rho_geo Qp Qpp s = 0} :=
  infinite_zeros_of_growth (detC_jensen_log_bound sigma rho_geo Qp Qpp hσ) hgrow

/-! ### The equivalence `DetBoundaryGrowth detC ↔ Set.Infinite {detC = 0}` (Route B ≡ MZERO.1)

Route B's `DetBoundaryGrowth` input (MZERO.10) is, via Jensen's formula, **logically equivalent** to
MZERO.1 itself (`det(Q̂₀)` has infinitely many zeros): with no poles (`divisor ≥ 0`), the integrated
Jensen identity reads `circleAverage (log‖detC·‖) 0 R = ∫₀ᴿ n(t)/t dt + const` (`n(t)` = zeros in the
ball), so super-log growth of the boundary log-average ⟺ `n(t) → ∞` ⟺ infinitely many zeros.  A
zero-*free* exponential `e^{−sτ}` has boundary average `0` (∫cos θ = 0), so the growth comes **entirely
from the zeros** — the MZERO.10 "`e^{−sσ}` growth ⇒ ≥c·R" reading is imprecise.  The `⟸` half is
`detC_zeros_infinite_of_boundaryGrowth` (`hJensen`'s contrapositive); the `⟹` half is the Jensen LOWER
bound: keeping `K` zeros inside the ball, `circleAverage ≥ ∑_z (log R − log‖z‖) + log‖tc‖ ≥ K·log R −
const`, which beats every `M·log R + C`.  **Conclusion:** Route B is a *reformulation* of MZERO.1, not an
independent closure — the genuine route is Route A (MZERO.5).  (The `⟹` half needs `0 < σᵢ` for the
non-vanishing witness `Q0_det_c_tendsto_one`.) -/

/-- **Route B ≡ MZERO.1, the `⟹` half.**  Infinitely many zeros of `detC` ⇒ `DetBoundaryGrowth detC`
(the boundary log-average `circleAverage (log‖detC·‖) 0 R` beats every `M·log R + C`), via the Jensen
LOWER bound.  Needs `0 < σᵢ` (for the non-vanishing witness `Q0_det_c_tendsto_one`, which rules out
`detC` locally-zero so each zero has a genuine positive order). -/
theorem detC_boundaryGrowth_of_infinite_zeros (sigma : Fin 2 → ℝ)
    (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ) (hσ : ∀ i, 0 < sigma i)
    (hinf : Set.Infinite {s : ℂ | detC sigma rho_geo Qp Qpp s = 0}) :
    DetBoundaryGrowth (detC sigma rho_geo Qp Qpp) := by
  set f := detC sigma rho_geo Qp Qpp with hf
  have hmeroOn : ∀ U : Set ℂ, MeromorphicOn f U := by
    intro U; rw [hf]; exact det_meromorphicOn (fun i => (sigma i : ℂ)) rho_geo Qp Qpp U
  have hnn : ∀ (U : Set ℂ) (u : ℂ), 0 ≤ MeromorphicOn.divisor f U u := by
    intro U u; have h := det_divisor_nonneg sigma rho_geo Qp Qpp (fun i => (hσ i).ne') U
    rw [← hf] at h; exact h u
  have hdetC0 : f 0 = 1 := by
    rw [hf]
    change (FMSA.Q0Complex.Q0_mat_c 0 (fun i => (sigma i : ℂ)) rho_geo Qp Qpp).det = 1
    rw [Q0_mat_c_at_zero, Matrix.det_one]
  have hdiffOn : DifferentiableOn ℂ f {(0 : ℂ)}ᶜ := by
    rw [hf]; exact fun z hz =>
      (Q0_det_c_differentiableAt (fun i => (sigma i : ℂ)) rho_geo Qp Qpp hz).differentiableWithinAt
  have hAnalOn : AnalyticOnNhd ℂ f {(0 : ℂ)}ᶜ := hdiffOn.analyticOnNhd isOpen_compl_singleton
  obtain ⟨x₀, hx₀ne, hx₀⟩ : ∃ x : ℂ, x ≠ 0 ∧ f x ≠ 0 := by
    have htend : Tendsto (fun t : ℝ => f (t : ℂ)) atTop (𝓝 1) :=
      Q0_det_c_tendsto_one hσ rho_geo Qp Qpp
    have h1 : ∀ᶠ t : ℝ in atTop, f (t : ℂ) ≠ 0 := by
      have hb : ∀ᶠ t : ℝ in atTop, ‖f (t : ℂ) - 1‖ < 1 := by
        have h0 := htend.sub_const 1
        rw [sub_self] at h0
        have hnorm := h0.norm
        rw [norm_zero] at hnorm
        exact hnorm.eventually_lt_const (by norm_num)
      filter_upwards [hb] with t ht hzero
      rw [hzero] at ht; simp at ht
    have h2 : ∀ᶠ t : ℝ in atTop, (t : ℂ) ≠ 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
    exact ⟨(t : ℂ), ht2, ht1⟩
  have hord_ne_top : ∀ z : ℂ, z ≠ 0 → meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz0 htop
    have hA : AnalyticAt ℂ f z := hdiffOn.analyticAt (isOpen_compl_singleton.mem_nhds hz0)
    rw [hA.meromorphicOrderAt_eq, ENat.map_eq_top_iff] at htop
    have hev : ∀ᶠ w in 𝓝 z, f w = 0 := analyticOrderAt_eq_top.mp htop
    have hPC : IsPreconnected ({(0 : ℂ)}ᶜ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 0).isPreconnected
    have hEq : Set.EqOn f 0 {(0 : ℂ)}ᶜ :=
      hAnalOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hPC hz0 hev
    exact hx₀ (by simpa using hEq hx₀ne)
  have hzero_div : ∀ z : ℂ, f z = 0 → z ≠ 0 → ∀ R : ℝ, ‖z‖ ≤ |R| →
      (1 : ℤ) ≤ MeromorphicOn.divisor f (closedBall 0 |R|) z := by
    intro z hzf hz0 R hzR
    have hmem : z ∈ closedBall (0 : ℂ) |R| := by
      simp only [mem_closedBall, dist_zero_right]; exact hzR
    have hA : AnalyticAt ℂ f z := hdiffOn.analyticAt (isOpen_compl_singleton.mem_nhds hz0)
    rw [MeromorphicOn.divisor_apply (hmeroOn _) hmem]
    have hnetop : meromorphicOrderAt f z ≠ ⊤ := hord_ne_top z hz0
    have hordne0 : meromorphicOrderAt f z ≠ 0 :=
      fun hh => (hA.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hh) hzf
    have hordnn : 0 ≤ meromorphicOrderAt f z := hA.meromorphicOrderAt_nonneg
    lift meromorphicOrderAt f z to ℤ using hnetop with m hm
    rw [WithTop.untop₀_coe]
    have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast hordnn
    have hmne : m ≠ 0 := by exact_mod_cast hordne0
    omega
  intro M C R₀
  set logtc : ℝ := Real.log ‖meromorphicTrailingCoeffAt f 0‖ with hlogtc
  set K : ℕ := ⌈max M 0⌉₊ + 1 with hKdef
  obtain ⟨S, hSsub, hScard⟩ := hinf.exists_subset_card_eq K
  set Cs : ℝ := ∑ z ∈ S, Real.log ‖z‖ with hCs
  set B : ℝ := 1 + ∑ z ∈ S, ‖z‖ with hB
  refine ⟨max R₀ (max B (Real.exp (C + Cs - logtc + 1))), le_max_left _ _, ?_⟩
  set R : ℝ := max R₀ (max B (Real.exp (C + Cs - logtc + 1))) with hRdef
  have hRB : B ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRexp : Real.exp (C + Cs - logtc + 1) ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hB1 : (1 : ℝ) ≤ B := by
    have : (0 : ℝ) ≤ ∑ z ∈ S, ‖z‖ := Finset.sum_nonneg (fun z _ => norm_nonneg z)
    simp only [hB]; linarith
  have hR1 : (1 : ℝ) ≤ R := le_trans hB1 hRB
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have habs : |R| = R := abs_of_pos hRpos
  have hlogRnn : (0 : ℝ) ≤ Real.log R := Real.log_nonneg hR1
  have hlogRbig : C + Cs - logtc + 1 ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos _) hRexp
    rwa [Real.log_exp] at this
  have hSprop : ∀ z ∈ S, f z = 0 ∧ z ≠ 0 ∧ ‖z‖ ≤ |R| := by
    intro z hzS
    have hzf : f z = 0 := hSsub hzS
    have hz0 : z ≠ 0 := by
      rintro rfl; rw [hdetC0] at hzf; exact one_ne_zero hzf
    have hznorm : ‖z‖ ≤ |R| := by
      rw [habs]
      have h1 : ‖z‖ ≤ ∑ w ∈ S, ‖w‖ := Finset.single_le_sum (fun w _ => norm_nonneg w) hzS
      have h2 : ∑ w ∈ S, ‖w‖ ≤ B := by simp only [hB]; linarith
      linarith [le_trans h1 h2, hRB]
    exact ⟨hzf, hz0, hznorm⟩
  set h : ℂ → ℝ := fun u => (MeromorphicOn.divisor f (closedBall 0 |R|) u : ℝ) *
      (Real.log R - Real.log ‖u‖) with hh_def
  have hhnn : ∀ u, 0 ≤ h u := by
    intro u
    by_cases hu : u ∈ closedBall (0 : ℂ) |R|
    · refine mul_nonneg (by exact_mod_cast hnn _ u) ?_
      have hnorm : ‖u‖ ≤ R := by
        simp only [mem_closedBall, dist_zero_right, habs] at hu; exact hu
      rcases eq_or_ne u 0 with rfl | hune
      · simp only [norm_zero, Real.log_zero, sub_zero]; exact hlogRnn
      · have := Real.log_le_log (norm_pos_iff.mpr hune) hnorm; linarith
    · have h0 : MeromorphicOn.divisor f (closedBall 0 |R|) u = 0 :=
        (MeromorphicOn.divisor f (closedBall 0 |R|)).apply_eq_zero_of_notMem hu
      simp only [hh_def, h0, Int.cast_zero, zero_mul, le_refl]
  have hhfin : (Function.support h).Finite := by
    apply Set.Finite.subset
      ((MeromorphicOn.divisor f (closedBall 0 |R|)).finiteSupport (isCompact_closedBall 0 |R|))
    intro u hu
    simp only [hh_def, Function.mem_support, ne_eq, mul_eq_zero, not_or] at hu
    simp only [Function.mem_support, ne_eq]
    intro hc; apply hu.1; rw [hc]; simp
  have hR0ne : R ≠ 0 := ne_of_gt hRpos
  have hjen := MeromorphicOn.circleAverage_log_norm hR0ne (hmeroOn (closedBall 0 |R|))
  rw [← countingFunction_finsum_eq_finsum_add hR0ne
    ((MeromorphicOn.divisor f (closedBall 0 |R|)).finiteSupport (isCompact_closedBall 0 |R|))] at hjen
  simp only [zero_sub, norm_neg] at hjen
  have hJenLower :
      (∑ z ∈ S, (Real.log R - Real.log ‖z‖)) + logtc
        ≤ circleAverage (fun s => Real.log ‖f s‖) 0 R := by
    rw [hjen]
    have hstep1 : (∑ z ∈ S, (Real.log R - Real.log ‖z‖)) ≤ ∑ z ∈ S, h z := by
      refine Finset.sum_le_sum (fun z hzS => ?_)
      obtain ⟨hzf, hz0, hznorm⟩ := hSprop z hzS
      have hdiv1 : (1 : ℤ) ≤ MeromorphicOn.divisor f (closedBall 0 |R|) z :=
        hzero_div z hzf hz0 R hznorm
      have hfac : (0 : ℝ) ≤ Real.log R - Real.log ‖z‖ := by
        have : Real.log ‖z‖ ≤ Real.log R :=
          Real.log_le_log (norm_pos_iff.mpr hz0) (by rw [← habs]; exact hznorm)
        linarith
      calc Real.log R - Real.log ‖z‖
          = (1 : ℝ) * (Real.log R - Real.log ‖z‖) := (one_mul _).symm
        _ ≤ (MeromorphicOn.divisor f (closedBall 0 |R|) z : ℝ) * (Real.log R - Real.log ‖z‖) := by
            apply mul_le_mul_of_nonneg_right _ hfac; exact_mod_cast hdiv1
    have hstep2 : (∑ z ∈ S, h z) ≤ ∑ᶠ u, h u :=
      finset_sum_le_finsum_of_nonneg h hhnn hhfin S
    have hchain : (∑ z ∈ S, (Real.log R - Real.log ‖z‖)) ≤ ∑ᶠ u, h u := le_trans hstep1 hstep2
    linarith
  have hcard : (M + 1 : ℝ) ≤ (S.card : ℝ) := by
    rw [hScard, hKdef]
    have hc : max M 0 ≤ (⌈max M 0⌉₊ : ℝ) := Nat.le_ceil _
    have : M ≤ (⌈max M 0⌉₊ : ℝ) := le_trans (le_max_left _ _) hc
    push_cast; linarith
  have hsumeq : (∑ z ∈ S, (Real.log R - Real.log ‖z‖)) = (S.card : ℝ) * Real.log R - Cs := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hCs]
  have hprod : (M + 1) * Real.log R ≤ (S.card : ℝ) * Real.log R :=
    mul_le_mul_of_nonneg_right hcard hlogRnn
  have hexpand : (M + 1) * Real.log R = M * Real.log R + Real.log R := by ring
  calc M * Real.log R + C
      < (S.card : ℝ) * Real.log R - Cs + logtc := by nlinarith [hprod, hexpand, hlogRbig]
    _ = (∑ z ∈ S, (Real.log R - Real.log ‖z‖)) + logtc := by rw [hsumeq]
    _ ≤ circleAverage (fun s => Real.log ‖f s‖) 0 R := hJenLower

/-- **Route B ≡ MZERO.1.**  For `det(Q̂₀)` (N=2, `0 < σᵢ`): the boundary-growth input `DetBoundaryGrowth`
(MZERO.10) is **logically equivalent** to `det` having infinitely many zeros (MZERO.1).  So Route B is a
Jensen reformulation of MZERO.1, not an independent closure of it. -/
theorem detC_boundaryGrowth_iff_infinite_zeros (sigma : Fin 2 → ℝ)
    (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ) (hσ : ∀ i, 0 < sigma i) :
    DetBoundaryGrowth (detC sigma rho_geo Qp Qpp)
      ↔ Set.Infinite {s : ℂ | detC sigma rho_geo Qp Qpp s = 0} := by
  constructor
  · intro hgrow
    exact detC_zeros_infinite_of_boundaryGrowth sigma rho_geo Qp Qpp (fun i => (hσ i).ne') hgrow
  · intro hinf
    exact detC_boundaryGrowth_of_infinite_zeros sigma rho_geo Qp Qpp hσ hinf

end FMSA.MixtureHSPoles
