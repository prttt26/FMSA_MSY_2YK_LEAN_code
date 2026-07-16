/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Jensen counting bound for finitely many zeros — PROVED, no axiom

Group MA (`MATH_AXIOMS.md`), task `MA.5`. The classical corollary of **Jensen's formula**
(Ahlfors Ch. 5 §3.1 / the trivial case of Nevanlinna's First Main Theorem): for `f` meromorphic
on all of `ℂ` with **no poles** (`divisor ≥ 0`) and **finitely many zeros counted by the divisor**
(finite divisor support), the circle average of `log‖f‖` grows at most log-linearly:
`circleAverage (log‖f·‖) 0 R ≤ M·log R + C` for all large `R`.

**History — this file briefly held a FALSE axiom (2026-07-15, same-day fixed).** The first
version hypothesized finiteness of the *literal* zero set `{s | f s = 0}` instead of the divisor
support. That statement is **false** under Lean's junk-value semantics: modify `sin` to take the
value `1` at every `nπ` — the result is still `MeromorphicOn ℂ univ` (meromorphy is a
`𝓝[≠]`-germ property, blind to isolated value changes), still has `divisor ≥ 0`, its literal
zero set is *empty*, yet `circleAverage log‖·‖` grows like `R`, not `log R`. The counting
hypothesis must be about *orders* (divisor support), not values. Caught while attempting the
proof below — a working example of why "just axiomatize it" is dangerous and prove-first is the
right discipline.

**Now proved outright** from Mathlib's Jensen formula (`MeromorphicOn.circleAverage_log_norm`,
`Mathlib/Analysis/Complex/JensenFormula.lean`): apply Jensen at each radius `R` large enough that
the closed ball contains the whole (finite) divisor support; the finsum collapses to a fixed
`Finset` sum; each term `Dᵤ·log(R·‖u‖⁻¹) ≤ Dᵤ·log R + Dᵤ·|log‖u‖|` (using `divisor ≥ 0`), giving
`M = Σ Dᵤ + D₀` and `C = Σ Dᵤ·|log‖u‖| + log‖trailing coeff‖`. `#print axioms` = the standard
three. This confirms the project's own assessment (`MixtureHSCounting.lean` `MZERO.9` notes) that
the step from Mathlib's Jensen to the counting bound is mechanical.

**Consumer.** Discharges the `hJensen` hypothesis of `infinite_zeros_of_growth` /
`detC_zeros_infinite_of_growth` (`YukawaDCF/MixtureHSCounting.lean`, `MZERO.11`) — with one
consumer-side bridge: `hJensen` is triggered by finiteness of the *literal* zero set of `detC`,
so the application needs "literal zeros finite → divisor support finite" for `detC`, which follows
from `detC`'s honest analyticity away from `s = 0` (`Q0_det_c_differentiableAt`: at analytic
points, positive order ⇔ value zero) plus at most one extra support point at the origin. That
bridge is `detC`-specific and left to the MZERO owner.
-/

open Filter MeromorphicAt MeasureTheory MeromorphicOn Metric Real Set Topology

noncomputable section

/-- **Jensen counting bound** (genuine theorem, no axiom). For `f` meromorphic on `ℂ` with no
poles (`divisor ≥ 0` on `univ`) and finite divisor support, `circleAverage (log‖f·‖) 0 R` is
eventually bounded by `M·log R + C`. Note the hypothesis is finiteness of the **divisor support**
(zeros counted by order) — finiteness of the literal zero set `{s | f s = 0}` would be too weak
(false, by junk-value modification; see the file docstring). -/
theorem circleAverage_log_norm_le_of_finite_zeros {f : ℂ → ℂ}
    (hmero : MeromorphicOn f Set.univ)
    (hdiv : 0 ≤ MeromorphicOn.divisor f Set.univ)
    (hfin : (MeromorphicOn.divisor f Set.univ).support.Finite) :
    ∃ M C R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      circleAverage (fun s => Real.log ‖f s‖) 0 R ≤ M * Real.log R + C := by
  classical
  set D := MeromorphicOn.divisor f Set.univ with hD
  set S : Finset ℂ := hfin.toFinset with hS
  have hDnn : ∀ u : ℂ, 0 ≤ D u := by
    intro u
    have h := Function.locallyFinsuppWithin.le_def.mp hdiv u
    simpa using h
  have hDnnR : ∀ u : ℂ, (0:ℝ) ≤ (D u : ℝ) := fun u => by exact_mod_cast hDnn u
  have hDS : ∀ u : ℂ, u ∉ S → D u = 0 := by
    intro u hu
    have : u ∉ Function.support D := by
      rw [hS] at hu
      simpa [Set.Finite.mem_toFinset] using hu
    simpa [Function.mem_support, not_not] using this
  refine ⟨(∑ u ∈ S, (D u : ℝ)) + (D 0 : ℝ),
    (∑ u ∈ S, (D u : ℝ) * |Real.log ‖u‖|) + Real.log ‖meromorphicTrailingCoeffAt f 0‖,
    1 + ∑ u ∈ S, ‖u‖, ?_⟩
  intro R hR
  have hnorm_sum_nn : 0 ≤ ∑ u ∈ S, ‖u‖ := Finset.sum_nonneg (fun u _ => norm_nonneg u)
  have hR1 : (1:ℝ) ≤ R := by linarith
  have hRpos : (0:ℝ) < R := by linarith
  have hRne : R ≠ 0 := hRpos.ne'
  have hRabs : |R| = R := abs_of_pos hRpos
  have hlogRnn : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hmem : ∀ u ∈ S, u ∈ closedBall (0:ℂ) |R| := by
    intro u hu
    rw [mem_closedBall, dist_zero_right, hRabs]
    have h1 : ‖u‖ ≤ ∑ v ∈ S, ‖v‖ := Finset.single_le_sum (fun v _ => norm_nonneg v) hu
    linarith
  have hmeroBall : MeromorphicOn f (closedBall (0:ℂ) |R|) := fun x _ => hmero x (mem_univ x)
  have hball_eq : ∀ u ∈ closedBall (0:ℂ) |R|,
      MeromorphicOn.divisor f (closedBall (0:ℂ) |R|) u = D u := by
    intro u hu
    rw [MeromorphicOn.divisor_apply hmeroBall hu, hD,
      MeromorphicOn.divisor_apply hmero (mem_univ u)]
  have hball_zero : ∀ u : ℂ, u ∉ S → MeromorphicOn.divisor f (closedBall (0:ℂ) |R|) u = 0 := by
    intro u hu
    by_cases hub : u ∈ closedBall (0:ℂ) |R|
    · rw [hball_eq u hub]; exact hDS u hu
    · by_contra hne
      exact hub ((MeromorphicOn.divisor f (closedBall (0:ℂ) |R|)).supportWithinDomain
        (Function.mem_support.mpr hne))
  have hsupp : Function.support
      (fun u => (MeromorphicOn.divisor f (closedBall (0:ℂ) |R|) u : ℝ) *
        Real.log (R * ‖(0:ℂ) - u‖⁻¹)) ⊆ ↑S := by
    intro u hu
    rw [Function.mem_support] at hu
    by_contra hnot
    rw [hball_zero u hnot] at hu
    simp at hu
  rw [MeromorphicOn.circleAverage_log_norm hRne hmeroBall]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hterm : ∀ u ∈ S,
      (MeromorphicOn.divisor f (closedBall (0:ℂ) |R|) u : ℝ) * Real.log (R * ‖(0:ℂ) - u‖⁻¹) ≤
        (D u : ℝ) * Real.log R + (D u : ℝ) * |Real.log ‖u‖| := by
    intro u hu
    rw [hball_eq u (hmem u hu)]
    have hnorm0u : ‖(0:ℂ) - u‖ = ‖u‖ := by rw [zero_sub, norm_neg]
    rw [hnorm0u]
    by_cases hu0 : u = 0
    · subst hu0
      simp only [norm_zero, inv_zero, mul_zero, Real.log_zero, mul_zero]
      have := hDnnR 0
      positivity
    · have hun : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
      rw [Real.log_mul hRne (inv_ne_zero hun.ne'), Real.log_inv]
      have hle : Real.log R + -Real.log ‖u‖ ≤ Real.log R + |Real.log ‖u‖| := by
        linarith [neg_le_abs (Real.log ‖u‖)]
      calc (D u : ℝ) * (Real.log R + -Real.log ‖u‖)
          ≤ (D u : ℝ) * (Real.log R + |Real.log ‖u‖|) :=
            mul_le_mul_of_nonneg_left hle (hDnnR u)
        _ = (D u : ℝ) * Real.log R + (D u : ℝ) * |Real.log ‖u‖| := by ring
  have hsum_le := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum_le
  have h0mem : (0:ℂ) ∈ closedBall (0:ℂ) |R| := by
    rw [mem_closedBall, dist_self]; positivity
  have h0eq : MeromorphicOn.divisor f (closedBall (0:ℂ) |R|) 0 = D 0 := hball_eq 0 h0mem
  rw [h0eq]
  refine le_trans (b := ((∑ u ∈ S, (D u : ℝ)) * Real.log R + ∑ u ∈ S, (D u : ℝ) * |Real.log ‖u‖|)
      + (D 0 : ℝ) * Real.log R + Real.log ‖meromorphicTrailingCoeffAt f 0‖)
    (by linarith [hsum_le]) (le_of_eq (by ring))

end
