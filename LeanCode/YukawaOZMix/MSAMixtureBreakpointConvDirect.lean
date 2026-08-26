/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.MSAMixtureBaxterConv

/-!
# BRK.16 — `baxterConvCore` breakpoints DIRECTLY from the convolution (axiom-reduction)

Goal (`proof_notes_breakpoints_MSA.md`, BRK.16): prove the physical-core breakpoint structure from
the convolution `baxterConvCore = (−Q'_ij + Σ_l ρ_l ∫ Q'_il(t+r) Q_jl(t) dt)/(2π r)` DIRECTLY, so
`baxterConvCore_smooth_off_unique_breakpoint` drops the sympy axiom `baxterConvCore_eq_matCoreUneq`
and becomes std-3.  This is legitimate because the breakpoint is *structural* (interior knot
`= |λ_ij|`, a support-edge geometric fact), independent of the coefficient VALUES — no closed-form
(hence no symbolic computation, hence no axiom) is needed.

## This file so far — BRK.16a (the factor smoothness, the buildable foundation)

`baxterQ`/`baxterQ'` are `ContDiffOn ℝ ⊤` on each of their open smooth pieces — the core
`(λ_ab, σ_ab)` and the tail `(σ_ab, ∞)` — each an entire polynomial/exponential formula.  (Below
`λ_ab` both are `0`.)  These feed the interval-split for the convolution smoothness (BRK.16b, the
load-bearing analytic core, still to come).
-/

open MSAMixture MSAMixtureCoreUneq MeasureTheory Set

namespace FMSA.ExactMSA.Breakpoint

variable {N : ℕ}

/-- **BRK.16a — `baxterQ` on the core piece** `(λ_ab, σ_ab)` equals its polynomial+exponential core
formula, hence `ContDiffOn ℝ ⊤`. -/
theorem baxterQ_contDiffOn_core (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (a b : Fin N) :
    ContDiffOn ℝ ⊤ (baxterQ z σ A qp Wt Ct a b) (Set.Ioo (edgeLo σ a b) (edgeHi σ a b)) := by
  have hg : ContDiffOn ℝ ⊤ (fun x => qp a b * (x - edgeLo σ a b - σ a)
      + A b / 2 * (x - edgeLo σ a b - σ a) ^ 2
      + Wt a b * Real.exp (-z * (x - edgeLo σ a b)) + Ct a b)
      (Set.Ioo (edgeLo σ a b) (edgeHi σ a b)) := by fun_prop
  refine hg.congr (fun x hx => ?_)
  unfold baxterQ
  rw [if_neg (not_lt.mpr (le_of_lt hx.1)), if_pos (le_of_lt hx.2)]

/-- **BRK.16a — `baxterQ` on the tail piece** `(σ_ab, ∞)` equals its two-exponential tail formula,
hence `ContDiffOn ℝ ⊤`. -/
theorem baxterQ_contDiffOn_tail (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (a b : Fin N) (hσ : ∀ i, 0 ≤ σ i) :
    ContDiffOn ℝ ⊤ (baxterQ z σ A qp Wt Ct a b) (Set.Ioi (edgeHi σ a b)) := by
  have hg : ContDiffOn ℝ ⊤ (fun x => Wt a b * Real.exp (-z * (x - edgeLo σ a b))
      + Ct a b * Real.exp (-z * (x - edgeHi σ a b))) (Set.Ioi (edgeHi σ a b)) := by fun_prop
  have hle : edgeLo σ a b ≤ edgeHi σ a b := by
    simp only [edgeLo, edgeHi]; linarith [hσ a, hσ b]
  refine hg.congr (fun x hx => ?_)
  have hxi : edgeHi σ a b < x := Set.mem_Ioi.mp hx
  unfold baxterQ
  rw [if_neg (by linarith : ¬ x < edgeLo σ a b), if_neg (not_le.mpr hxi)]

/-- **BRK.16a — `baxterQ'` on the core piece** `(λ_ab, σ_ab)`, `ContDiffOn ℝ ⊤`. -/
theorem baxterQ'_contDiffOn_core (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (a b : Fin N) :
    ContDiffOn ℝ ⊤ (baxterQ' z σ A qp Wt Ct a b) (Set.Ioo (edgeLo σ a b) (edgeHi σ a b)) := by
  have hg : ContDiffOn ℝ ⊤ (fun x => qp a b + A b * (x - edgeLo σ a b - σ a)
      - z * Wt a b * Real.exp (-z * (x - edgeLo σ a b)))
      (Set.Ioo (edgeLo σ a b) (edgeHi σ a b)) := by fun_prop
  refine hg.congr (fun x hx => ?_)
  unfold baxterQ'
  rw [if_neg (not_lt.mpr (le_of_lt hx.1)), if_pos (le_of_lt hx.2)]

/-- **BRK.16a — `baxterQ'` on the tail piece** `(σ_ab, ∞)`, `ContDiffOn ℝ ⊤`. -/
theorem baxterQ'_contDiffOn_tail (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (a b : Fin N) (hσ : ∀ i, 0 ≤ σ i) :
    ContDiffOn ℝ ⊤ (baxterQ' z σ A qp Wt Ct a b) (Set.Ioi (edgeHi σ a b)) := by
  have hg : ContDiffOn ℝ ⊤ (fun x => -z * Wt a b * Real.exp (-z * (x - edgeLo σ a b))
      - z * Ct a b * Real.exp (-z * (x - edgeHi σ a b))) (Set.Ioi (edgeHi σ a b)) := by fun_prop
  have hle : edgeLo σ a b ≤ edgeHi σ a b := by
    simp only [edgeLo, edgeHi]; linarith [hσ a, hσ b]
  refine hg.congr (fun x hx => ?_)
  have hxi : edgeHi σ a b < x := Set.mem_Ioi.mp hx
  unfold baxterQ'
  rw [if_neg (by linarith : ¬ x < edgeLo σ a b), if_neg (not_le.mpr hxi)]

/-! ### BRK.16b (item 1) — integrability of the convolution integrand -/

/-- **`baxterQ` is `Integrable`** (`z > 0`): `0` below `λ_ab`, continuous on the compact core
`[λ_ab, σ_ab]`, exponentially decaying on the tail `(σ_ab, ∞)` — the tail via
`integrableOn_exp_mul_Ioi`.  Exp-tailed analog of the compact-support PY-factor integrability. -/
theorem baxterQ_integrable (z : ℝ) (hz : 0 < z) (σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (a b : Fin N) (hσ : ∀ i, 0 ≤ σ i) :
    Integrable (baxterQ z σ A qp Wt Ct a b) := by
  have hle : edgeLo σ a b ≤ edgeHi σ a b := by simp only [edgeLo, edgeHi]; linarith [hσ a, hσ b]
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := edgeHi σ a b), integrableOn_union]
  refine ⟨?_, ?_⟩
  · have hset : Set.Iic (edgeHi σ a b)
        = Set.Iio (edgeLo σ a b) ∪ Set.Icc (edgeLo σ a b) (edgeHi σ a b) := by
      ext x; simp only [mem_Iic, mem_union, mem_Iio, mem_Icc]
      constructor
      · intro h
        by_cases h' : x < edgeLo σ a b
        · exact Or.inl h'
        · exact Or.inr ⟨not_lt.mp h', h⟩
      · rintro (h | ⟨_, h⟩)
        · exact le_trans h.le hle
        · exact h
    rw [hset, integrableOn_union]
    refine ⟨?_, ?_⟩
    · refine (integrableOn_zero).congr_fun ?_ measurableSet_Iio
      intro x hx; rw [Set.mem_Iio] at hx; simp [baxterQ, hx]
    · have hg : ContinuousOn (fun x => qp a b * (x - edgeLo σ a b - σ a)
          + A b / 2 * (x - edgeLo σ a b - σ a) ^ 2
          + Wt a b * Real.exp (-z * (x - edgeLo σ a b)) + Ct a b)
          (Icc (edgeLo σ a b) (edgeHi σ a b)) := by fun_prop
      refine (hg.congr (fun x hx => ?_)).integrableOn_compact isCompact_Icc
      unfold baxterQ; rw [if_neg (not_lt.mpr hx.1), if_pos hx.2]
  · have hexp : ∀ c : ℝ, IntegrableOn (fun x => Real.exp (-z * (x - c))) (Ioi (edgeHi σ a b)) := by
      intro c
      have heq : (fun x => Real.exp (-z * (x - c)))
          = (fun x => Real.exp (z * c) * Real.exp (-z * x)) := by
        funext x; rw [← Real.exp_add]; congr 1; ring
      rw [heq]; exact (integrableOn_exp_mul_Ioi (by linarith : -z < 0) _).const_mul _
    have htail : IntegrableOn (fun x => Wt a b * Real.exp (-z * (x - edgeLo σ a b))
        + Ct a b * Real.exp (-z * (x - edgeHi σ a b))) (Ioi (edgeHi σ a b)) :=
      ((hexp (edgeLo σ a b)).const_mul (Wt a b)).add ((hexp (edgeHi σ a b)).const_mul (Ct a b))
    refine htail.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hxi : edgeHi σ a b < x := hx
    unfold baxterQ; rw [if_neg (by linarith : ¬ x < edgeLo σ a b), if_neg (not_le.mpr hxi)]

/-- **`baxterQ'` is globally bounded** (`z > 0`): `0` below `λ_ab`; on the core the poly argument
`x − λ_ab − σ_a ∈ [−σ_a, 0]` is bounded and `e^{−z(x−λ)} ≤ 1`; on the tail both exponentials `≤ 1`.
Feeds the product-integrand integrability (`bdd · L¹`). -/
theorem baxterQ'_bounded (z : ℝ) (hz : 0 < z) (σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (a b : Fin N) (hσ : ∀ i, 0 ≤ σ i) :
    ∃ C, ∀ x, |baxterQ' z σ A qp Wt Ct a b x| ≤ C := by
  have hEH : edgeHi σ a b - edgeLo σ a b = σ a := by simp only [edgeLo, edgeHi]; ring
  have hnn : (0:ℝ) ≤ |qp a b| + |A b| * σ a + z * |Wt a b| + z * |Wt a b| + z * |Ct a b| := by
    have := hσ a
    positivity
  refine ⟨|qp a b| + |A b| * σ a + z * |Wt a b| + z * |Wt a b| + z * |Ct a b|, fun x => ?_⟩
  unfold baxterQ'
  split_ifs with h1 h2
  · rw [abs_zero]; exact hnn
  · have hxlo : edgeLo σ a b ≤ x := not_lt.mp h1
    have he1 : Real.exp (-z * (x - edgeLo σ a b)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hxlo])
    have he0 : (0:ℝ) ≤ Real.exp (-z * (x - edgeLo σ a b)) := (Real.exp_pos _).le
    have hpoly : |A b * (x - edgeLo σ a b - σ a)| ≤ |A b| * σ a := by
      rw [abs_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_le]; constructor <;> nlinarith [hxlo, h2, hEH, hσ a]
    have hexp : |z * Wt a b * Real.exp (-z * (x - edgeLo σ a b))| ≤ z * |Wt a b| := by
      rw [abs_mul, abs_mul, abs_of_pos hz, abs_of_nonneg he0]
      nlinarith [mul_nonneg hz.le (abs_nonneg (Wt a b)), abs_nonneg (Wt a b), he1, he0]
    have step1 : |qp a b + A b * (x - edgeLo σ a b - σ a)| ≤ |qp a b| + |A b| * σ a :=
      (abs_add_le _ _).trans (by gcongr)
    calc |qp a b + A b * (x - edgeLo σ a b - σ a)
            - z * Wt a b * Real.exp (-z * (x - edgeLo σ a b))|
        = |(qp a b + A b * (x - edgeLo σ a b - σ a))
            + -(z * Wt a b * Real.exp (-z * (x - edgeLo σ a b)))| := by ring_nf
      _ ≤ |qp a b + A b * (x - edgeLo σ a b - σ a)|
            + |z * Wt a b * Real.exp (-z * (x - edgeLo σ a b))| := by
          rw [← abs_neg (z * Wt a b * _)]; exact abs_add_le _ _
      _ ≤ (|qp a b| + |A b| * σ a) + z * |Wt a b| := add_le_add step1 hexp
      _ ≤ _ := by nlinarith [mul_nonneg hz.le (abs_nonneg (Wt a b)),
            mul_nonneg hz.le (abs_nonneg (Ct a b))]
  · have hxlo : edgeLo σ a b ≤ x := not_lt.mp h1
    have hxhi : edgeHi σ a b < x := not_le.mp h2
    have he1 : Real.exp (-z * (x - edgeLo σ a b)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hxlo])
    have he2 : Real.exp (-z * (x - edgeHi σ a b)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hxhi])
    have he0a : (0:ℝ) ≤ Real.exp (-z * (x - edgeLo σ a b)) := (Real.exp_pos _).le
    have he0b : (0:ℝ) ≤ Real.exp (-z * (x - edgeHi σ a b)) := (Real.exp_pos _).le
    have hA : |(-z * Wt a b) * Real.exp (-z * (x - edgeLo σ a b))| ≤ z * |Wt a b| := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos hz, abs_of_nonneg he0a]
      nlinarith [mul_nonneg hz.le (abs_nonneg (Wt a b)), he1, he0a]
    have hB : |z * Ct a b * Real.exp (-z * (x - edgeHi σ a b))| ≤ z * |Ct a b| := by
      rw [abs_mul, abs_mul, abs_of_pos hz, abs_of_nonneg he0b]
      nlinarith [mul_nonneg hz.le (abs_nonneg (Ct a b)), he2, he0b]
    calc |(-z * Wt a b) * Real.exp (-z * (x - edgeLo σ a b))
            - z * Ct a b * Real.exp (-z * (x - edgeHi σ a b))|
        ≤ |(-z * Wt a b) * Real.exp (-z * (x - edgeLo σ a b))|
            + |z * Ct a b * Real.exp (-z * (x - edgeHi σ a b))| := by
          rw [← abs_neg (z * Ct a b * _)]; exact abs_add_le _ _
      _ ≤ z * |Wt a b| + z * |Ct a b| := add_le_add hA hB
      _ ≤ _ := by nlinarith [abs_nonneg (qp a b), mul_nonneg (abs_nonneg (A b)) (hσ a),
            mul_nonneg hz.le (abs_nonneg (Wt a b))]

end FMSA.ExactMSA.Breakpoint
