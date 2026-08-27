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

/-- **`baxterQ'` is measurable** (piecewise, via `Measurable.ite`). -/
theorem baxterQ'_measurable (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ) (a b : Fin N) :
    Measurable (baxterQ' z σ A qp Wt Ct a b) := by
  unfold baxterQ'
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_ <;> fun_prop

/-- ⭐ **BRK.16b (item 1) — the convolution integrand is integrable.**  `t ↦ Q'_il(t+r)·Q_jl(t)` is
`Integrable` (`z>0`): `baxterQ'(·+r)` is bounded + measurable and `baxterQ_jl ∈ L¹`, so the product
is `bdd · L¹` (`Integrable.bdd_mul`).  This makes each `∫ Q'_il(t+r) Q_jl(t) dt` in `baxterConvCore`
well-defined — the prerequisite for the interval-form smoothness (item 2). -/
theorem baxterConvIntegrand_integrable (z : ℝ) (hz : 0 < z) (σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j l : Fin N) (r : ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    Integrable (fun t => baxterQ' z σ A qp Wt Ct i l (t + r) * baxterQ z σ A qp Wt Ct j l t) := by
  obtain ⟨C, hC⟩ := baxterQ'_bounded z hz σ A qp Wt Ct i l hσ
  exact (baxterQ_integrable z hz σ A qp Wt Ct j l hσ).bdd_mul
    ((baxterQ'_measurable z σ A qp Wt Ct i l).comp (measurable_id.add_const r)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hC (t + r)))

/-! ### BRK.16b (item 2, the diagonal half) — the `−Q'_ij` term matches `matCoreUneq`'s diagonal

`baxterConvCore = (−Q'_ij + Σ_l ρ_l ∫_l)/(2π r)` and `matCoreUneq = g/(2π r)` with each `g`-coeff
`= (diagonal −Q'_ij term) + Σ_l ρ_l·kernel_l` (`MSAMixtureCoreUneq.lean` docstring).  Because the
per-`l` kernels are σ_l-free, `baxterConvCore = matCoreUneq` splits into (a) the diagonal
`−Q'_ij(r) = gForm(diag coeffs)(r)` — proved below, no integral — and (b) the per-`l` convolution
`∫_l = gForm(kernel_l)(r)`, wrapped by `Finset.sum_congr`.  This lemma discharges (a): the whole
NON-integral content of the seam axiom, confirming the `cC0i/cC1i/cEmi` diagonal transcription. -/

/-- **BRK.16b (diagonal half) — `−Q'_ij(r)` equals `matCoreUneq`'s diagonal `g`-part.**  On the core
support `edgeLo σ i j ≤ r ≤ edgeHi σ i j` the negated derivative equals the diagonal (non-`∑`)
terms of `matCoreUneq`'s `g` read off `cC0i`/`cC1i`/`cEmi`: constant `−qp_ij + A_j·σ_ij`, `r`-slope
`−A_j`, and `e^{−zr}`-amplitude `z·Wt_ij·e^{−z(σ_i−σ_j)/2}` (`σ_ij = (σ_i+σ_j)/2`, `|λ_ij|` split).
This is the integral-free half of the seam `baxterConvCore = matCoreUneq`; the remaining content is
the per-`l` convolution `∫ Q'_il(t+r) Q_jl(t) dt`. -/
theorem neg_baxterQ'_eq_diag (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) (r : ℝ) (hlo : edgeLo σ i j ≤ r) (hhi : r ≤ edgeHi σ i j) :
    - baxterQ' z σ A qp Wt Ct i j r
      = (- qp i j + A j * ((σ i + σ j) / 2)) + (- A j) * r
        + (z * Wt i j * Real.exp (-z * (σ i - σ j) / 2)) * Real.exp (-z * r) := by
  unfold baxterQ'
  rw [if_neg (not_lt.mpr hlo), if_pos hhi]
  simp only [edgeLo]
  have hExp : Real.exp (-z * (r - (σ j - σ i) / 2))
      = Real.exp (-z * (σ i - σ j) / 2) * Real.exp (-z * r) := by
    rw [← Real.exp_add]; ring_nf
  rw [hExp]
  ring

/-! ### BRK.16b part (b) — the per-`l` convolution: support & interval structure

The per-`l` seam `∫ Q'_il(t+r) Q_jl(t) dt = gForm(kernel_l)(r)`.  The geometry: the integrand's
support is `[edgeLo σ j l, ∞)` (the `Q_jl` factor), and inside it the four factor-branch edges
order into a **3-region** split whose middle region flips at `r = |λ_ij|` — the source of the
inner/outer split. `Lj := edgeLo σ j l`, `Hj := edgeHi σ j l`, `Hi := edgeHi σ i l`.
* INNER `r < |λ_ij|`: `Lj < Hj < Hi−r` → regions `core·core`, `core'·tail`, `tail'·tail`.
* OUTER `r > |λ_ij|`: `Lj < Hi−r < Hj` → regions `core·core`, `tail'·core`, `tail'·tail`.
(`core'/tail'` = the `Q'_il(·+r)` branch; the tail·tail region is an improper `Ioi` integral.) -/

/-- **Support reduction.**  The convolution integrand `Q'_il(t+r)·Q_jl(t)` vanishes for
`t < edgeLo σ j l` (the `Q_jl` factor is `0` below its support edge), so `∫_ℝ = ∫` over
`[edgeLo σ j l, ∞)`.  Unconditional (only `z > 0`, `σ ≥ 0` for integrability). -/
theorem baxterConv_eq_setIntegral_Ici (z : ℝ) (hz : 0 < z) (σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j l : Fin N) (r : ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    (∫ (t : ℝ), baxterQ' z σ A qp Wt Ct i l (t + r) * baxterQ z σ A qp Wt Ct j l t)
      = ∫ t in Ici (edgeLo σ j l),
          baxterQ' z σ A qp Wt Ct i l (t + r) * baxterQ z σ A qp Wt Ct j l t := by
  have hint := baxterConvIntegrand_integrable z hz σ A qp Wt Ct i j l r hσ
  have hdisj : Disjoint (Iio (edgeLo σ j l)) (Ici (edgeLo σ j l)) := by
    rw [Set.disjoint_iff_inter_eq_empty, Iio_inter_Ici, Set.Ico_self]
  rw [← setIntegral_univ (μ := volume), ← Set.Iio_union_Ici (a := edgeLo σ j l),
    setIntegral_union hdisj measurableSet_Ici hint.integrableOn hint.integrableOn]
  have hzero : ∫ t in Iio (edgeLo σ j l),
      baxterQ' z σ A qp Wt Ct i l (t + r) * baxterQ z σ A qp Wt Ct j l t = 0 := by
    rw [setIntegral_congr_fun measurableSet_Iio (g := fun _ => 0) ?_, integral_zero]
    intro t ht
    show baxterQ' z σ A qp Wt Ct i l (t + r) * baxterQ z σ A qp Wt Ct j l t = 0
    have hb : baxterQ z σ A qp Wt Ct j l t = 0 := by
      unfold baxterQ; rw [if_pos (Set.mem_Iio.mp ht)]
    rw [hb, mul_zero]
  rw [hzero, zero_add]

/-- `|λ_ij| = (σ_i − σ_j)/2` in the orientation `σ_j ≤ σ_i` (`lamA = |edgeLo σ i j|`). -/
theorem lamA_eq_of_le (σ : Fin N → ℝ) (i j : Fin N) (hori : σ j ≤ σ i) :
    lamA σ i j = (σ i - σ j) / 2 := by
  unfold lamA edgeLo; rw [abs_of_nonpos (by linarith)]; ring

/-- `Lj < Hj` (from `σ_j > 0`): the `Q_jl` core interval `[edgeLo σ j l, edgeHi σ j l]` is
non-degenerate. -/
theorem edgeLo_lt_edgeHi (σ : Fin N → ℝ) (j l : Fin N) (hj : 0 < σ j) :
    edgeLo σ j l < edgeHi σ j l := by unfold edgeLo edgeHi; linarith

/-- `Lj < Hi − r` for `r < σ_ij = edgeHi σ i j`: `Q'_il`'s core-end is right of `Q_jl`'s
support-edge, so the `core·core` region is non-empty. -/
theorem edgeLo_lt_edgeHi_sub_r (σ : Fin N → ℝ) (i j l : Fin N) (r : ℝ) (hr : r < edgeHi σ i j) :
    edgeLo σ j l < edgeHi σ i l - r := by unfold edgeLo edgeHi at *; linarith

/-- INNER (`r < |λ_ij|`): `Hj < Hi − r` — the `Q_jl` tail starts before the `Q'_il` tail. -/
theorem edgeHi_lt_edgeHi_sub_r_inner (σ : Fin N → ℝ) (i j l : Fin N) (r : ℝ)
    (hori : σ j ≤ σ i) (hr : r < lamA σ i j) : edgeHi σ j l < edgeHi σ i l - r := by
  rw [lamA_eq_of_le σ i j hori] at hr; unfold edgeHi; linarith

/-- OUTER (`r > |λ_ij|`): `Hi − r < Hj` — the `Q'_il` tail starts before the `Q_jl` tail. -/
theorem edgeHi_sub_r_lt_edgeHi_outer (σ : Fin N → ℝ) (i j l : Fin N) (r : ℝ)
    (hori : σ j ≤ σ i) (hr : lamA σ i j < r) : edgeHi σ i l - r < edgeHi σ j l := by
  rw [lamA_eq_of_le σ i j hori] at hr; unfold edgeHi; linarith

/-- `Li − r < Lj`: `Q'_il`'s support-edge (shifted) is left of `Q_jl`'s support-edge (`r > 0`,
`σ_j ≤ σ_i`), so on `[Lj,∞)` the `Q'_il(·+r)` factor is already past its support edge. -/
theorem edgeLo_sub_r_lt_edgeLo (σ : Fin N → ℝ) (i j l : Fin N) (r : ℝ) (hori : σ j ≤ σ i)
    (hr0 : 0 < r) : edgeLo σ i l - r < edgeLo σ j l := by unfold edgeLo; linarith

/-- `∫` over `Icc a b` as an interval integral (`a ≤ b`). -/
theorem setIntegral_Icc_eq_uIcc (f : ℝ → ℝ) (a b : ℝ) (h : a ≤ b) :
    (∫ t in Icc a b, f t) = ∫ t in a..b, f t := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h]

/-- `∫` over `Ioc a b` as an interval integral (`a ≤ b`). -/
theorem setIntegral_Ioc_eq_uIcc (f : ℝ → ℝ) (a b : ℝ) (h : a ≤ b) :
    (∫ t in Ioc a b, f t) = ∫ t in a..b, f t := (intervalIntegral.integral_of_le h).symm

/-! ### BRK.16b part (b) — the interval-integral primitives (reusable, generic)

The 3-way split of `∫` over `[a,∞)`, and the elementary interval integrals the per-region evaluation
needs.  The convolution's exp terms are all `e^{−z(t−c)} = const·e^{−zt}`, atoms `tᵏe^{ct}`
(`k ≤ 2`) and pure `tᵏ` (`integral_pow`).  These are the fixed-exponential integrals (distinct from
MRS.5's `integral_poly_exp_conv`, which is the moving-endpoint convolution kernel). -/

/-- Generic 3-way split of `∫` over `[a,∞)`: two bounded pieces `[a,m1]`, `(m1,m2]`, and the tail
tail `(m2,∞)`, for `a ≤ m1 ≤ m2` (integrand integrable on `[a,∞)`). -/
theorem setIntegral_Ici_split3 (f : ℝ → ℝ) (a m1 m2 : ℝ) (h1 : a ≤ m1) (h2 : m1 ≤ m2)
    (hf : IntegrableOn f (Ici a)) :
    (∫ t in Ici a, f t)
      = (∫ t in Icc a m1, f t) + (∫ t in Ioc m1 m2, f t) + ∫ t in Ioi m2, f t := by
  have ha2 : a ≤ m2 := h1.trans h2
  have sIoi : Ioi m2 ⊆ Ici a := fun x hx => le_of_lt (lt_of_le_of_lt ha2 hx)
  have sIoc : Ioc m1 m2 ⊆ Ici a := fun x hx => h1.trans hx.1.le
  have hd1 : Disjoint (Icc a m2) (Ioi m2) :=
    Set.disjoint_left.mpr (fun x hx hx' => absurd hx.2 (not_le.mpr hx'))
  have hd2 : Disjoint (Icc a m1) (Ioc m1 m2) :=
    Set.disjoint_left.mpr (fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1))
  have e1 : (∫ t in Ici a, f t) = (∫ t in Icc a m2, f t) + ∫ t in Ioi m2, f t := by
    rw [← Icc_union_Ioi_eq_Ici ha2, setIntegral_union hd1 measurableSet_Ioi
        (hf.mono_set Icc_subset_Ici_self) (hf.mono_set sIoi)]
  have e2 : (∫ t in Icc a m2, f t) = (∫ t in Icc a m1, f t) + ∫ t in Ioc m1 m2, f t := by
    rw [← Icc_union_Ioc_eq_Icc h1 h2, setIntegral_union hd2 measurableSet_Ioc
        (hf.mono_set Icc_subset_Ici_self) (hf.mono_set sIoc)]
  rw [e1, e2]

/-- `∫_a^b e^{ct} = (e^{cb} − e^{ca})/c` (`c ≠ 0`). -/
theorem integral_exp_linear (a b c : ℝ) (hc : c ≠ 0) :
    ∫ t in a..b, Real.exp (c * t) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (c * t) / c) (Real.exp (c * t)) t := by
    intro t
    have h0 := ((Real.hasDerivAt_exp (c * t)).comp t ((hasDerivAt_id t).const_mul c)).div_const c
    have heq : Real.exp (c * t) * (c * 1) / c = Real.exp (c * t) := by
      rw [mul_one, mul_div_assoc, div_self hc, mul_one]
    rwa [heq] at h0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  ring

/-- `∫_a^b t·e^{ct}` (`c ≠ 0`), antiderivative `(ct−1)e^{ct}/c²`. -/
theorem integral_id_mul_exp (a b c : ℝ) (hc : c ≠ 0) :
    ∫ t in a..b, t * Real.exp (c * t)
      = ((c * b - 1) * Real.exp (c * b) - (c * a - 1) * Real.exp (c * a)) / c ^ 2 := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s => (c * s - 1) * Real.exp (c * s) / c ^ 2) (t * Real.exp (c * t)) t := by
    intro t
    have hu : HasDerivAt (fun s => c * s - 1) c t := by
      simpa using ((hasDerivAt_id t).const_mul c).sub_const 1
    have hv : HasDerivAt (fun s => Real.exp (c * s)) (c * Real.exp (c * t)) t := by
      have h := (Real.hasDerivAt_exp (c * t)).comp t ((hasDerivAt_id t).const_mul c)
      simp only [Function.comp_def, mul_one] at h
      rwa [mul_comm (Real.exp (c * t)) c] at h
    have h0 := (hu.mul hv).div_const (c ^ 2)
    have heq : (c * Real.exp (c * t) + (c * t - 1) * (c * Real.exp (c * t))) / c ^ 2
        = t * Real.exp (c * t) := by
      have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
      field_simp; ring
    rwa [heq] at h0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)]
  · ring
  · exact (continuous_id.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _

/-- `∫_a^b t²·e^{ct}` (`c ≠ 0`), antiderivative `(c²t²−2ct+2)e^{ct}/c³`. -/
theorem integral_sq_mul_exp (a b c : ℝ) (hc : c ≠ 0) :
    ∫ t in a..b, t ^ 2 * Real.exp (c * t)
      = ((c ^ 2 * b ^ 2 - 2 * c * b + 2) * Real.exp (c * b)
          - (c ^ 2 * a ^ 2 - 2 * c * a + 2) * Real.exp (c * a)) / c ^ 3 := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s => (c ^ 2 * s ^ 2 - 2 * c * s + 2) * Real.exp (c * s) / c ^ 3)
        (t ^ 2 * Real.exp (c * t)) t := by
    intro t
    have hu : HasDerivAt (fun s => c ^ 2 * s ^ 2 - 2 * c * s + 2)
        (c ^ 2 * (2 * t) - 2 * c) t := by
      have hs2 : HasDerivAt (fun s => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have hcs2 := hs2.const_mul (c ^ 2)
      have hlin : HasDerivAt (fun s => 2 * c * s) (2 * c) t := by
        simpa using (hasDerivAt_id t).const_mul (2 * c)
      exact (hcs2.sub hlin).add_const 2
    have hv : HasDerivAt (fun s => Real.exp (c * s)) (c * Real.exp (c * t)) t := by
      have h := (Real.hasDerivAt_exp (c * t)).comp t ((hasDerivAt_id t).const_mul c)
      simp only [Function.comp_def, mul_one] at h
      rwa [mul_comm (Real.exp (c * t)) c] at h
    have h0 := (hu.mul hv).div_const (c ^ 3)
    have heq : ((c ^ 2 * (2 * t) - 2 * c) * Real.exp (c * t)
        + (c ^ 2 * t ^ 2 - 2 * c * t + 2) * (c * Real.exp (c * t))) / c ^ 3
        = t ^ 2 * Real.exp (c * t) := by
      have hc3 : c ^ 3 ≠ 0 := pow_ne_zero 3 hc
      field_simp; ring
    rwa [heq] at h0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)]
  · ring
  · exact ((continuous_pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _

/-! ### BRK.16b part (b) — the four region-integrand closed forms

Each region of the convolution is a product of two explicit branch formulas; here is its closed form
as a function of the interval limits.  `Li := edgeLo σ i l`, `Hi := edgeHi σ i l`, `Lj/Hj` likewise.
The per-piece assembly (inner/outer) plugs the region limits into these and sums.  First the
`tail·tail` region — the improper `(c,∞)` tail, pure `exp·exp` collapsing to one `e^{−2zt}`. -/

/-- **Region `tail·tail`.**  `∫_c^∞ tail(Q'_il)(t+r)·tail(Q_jl)(t) dt`.  Both factors are pure
two-exponential tails, so the product is `K·e^{−2zt}` (one exponential); the improper integral is
`K·e^{−2zc}/(2z)` (`integral_exp_mul_Ioi`, `z > 0`).  `K` folds the four shift constants. -/
theorem integral_tailtail (z : ℝ) (hz : 0 < z) (Wil Ctil Wjl Ctjl Li Hi Lj Hj r c : ℝ) :
    (∫ t in Ioi c,
      (-z * Wil * Real.exp (-z * (t + r - Li)) - z * Ctil * Real.exp (-z * (t + r - Hi)))
      * (Wjl * Real.exp (-z * (t - Lj)) + Ctjl * Real.exp (-z * (t - Hj))))
    = (-z * (Wil * Wjl * Real.exp (-z * (r - Li - Lj))
          + Wil * Ctjl * Real.exp (-z * (r - Li - Hj))
          + Ctil * Wjl * Real.exp (-z * (r - Hi - Lj))
          + Ctil * Ctjl * Real.exp (-z * (r - Hi - Hj))))
      * (Real.exp (-2 * z * c) / (2 * z)) := by
  set K := -z * (Wil * Wjl * Real.exp (-z * (r - Li - Lj))
          + Wil * Ctjl * Real.exp (-z * (r - Li - Hj))
          + Ctil * Wjl * Real.exp (-z * (r - Hi - Lj))
          + Ctil * Ctjl * Real.exp (-z * (r - Hi - Hj))) with hK
  have hpt : ∀ t : ℝ,
      (-z * Wil * Real.exp (-z * (t + r - Li)) - z * Ctil * Real.exp (-z * (t + r - Hi)))
        * (Wjl * Real.exp (-z * (t - Lj)) + Ctjl * Real.exp (-z * (t - Hj)))
      = K * Real.exp (-2 * z * t) := by
    intro t
    have s1 : ∀ w : ℝ, Real.exp (-z * (t + r - w))
        = Real.exp (-z * t) * Real.exp (-z * r) * Real.exp (z * w) := fun w => by
      rw [show -z * (t + r - w) = -z * t + -z * r + z * w by ring, Real.exp_add, Real.exp_add]
    have s2 : ∀ w : ℝ, Real.exp (-z * (t - w)) = Real.exp (-z * t) * Real.exp (z * w) := fun w => by
      rw [show -z * (t - w) = -z * t + z * w by ring, Real.exp_add]
    have s3 : ∀ x y : ℝ, Real.exp (-z * (r - x - y))
        = Real.exp (-z * r) * Real.exp (z * x) * Real.exp (z * y) := fun x y => by
      rw [show -z * (r - x - y) = -z * r + z * x + z * y by ring, Real.exp_add, Real.exp_add]
    have s4 : Real.exp (-2 * z * t) = Real.exp (-z * t) * Real.exp (-z * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [hK]; simp only [s1, s2, s3, s4]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t),
    integral_const_mul, integral_exp_mul_Ioi (show -2 * z < 0 by linarith) c]
  rw [show -2 * z = -(2 * z) by ring]
  field_simp

/-! ### BRK.16b part (b) — the canonical bounded-region integral

Every BOUNDED region (`core·core`, `core'·tail`, `tail'·core`) expands — after rewriting each
`e^{−z(t−·)}` to the `e^{−zt}` atom — into `cubic + quadratic·e^{−zt} + K·e^{−2zt}`.  Its
antiderivative and FTC value are packaged once here; each region proof rewrites its branch product
into this canonical form (specific `cᵢ`/`dᵢ`/`K`) and applies `integral_canonical`. -/

/-- Antiderivative of `cubic + quadratic·e^{−zt} + K·e^{−2zt}` (`z ≠ 0` used at the value level). -/
noncomputable def canonAntider (z c0 c1 c2 c3 d0 d1 d2 K : ℝ) (t : ℝ) : ℝ :=
  c0 * t + c1 * t ^ 2 / 2 + c2 * t ^ 3 / 3 + c3 * t ^ 4 / 4
    + ((-d0 / z - d1 / z ^ 2 - 2 * d2 / z ^ 3) + (-d1 / z - 2 * d2 / z ^ 2) * t
        + (-d2 / z) * t ^ 2) * Real.exp (-z * t)
    + (-K / (2 * z)) * Real.exp (-2 * z * t)

/-- `canonAntider' = cubic + quadratic·e^{−zt} + K·e^{−2zt}` (the integrating-factor check). -/
theorem canonAntider_hasDerivAt (z c0 c1 c2 c3 d0 d1 d2 K : ℝ) (hz : 0 < z) (t : ℝ) :
    HasDerivAt (canonAntider z c0 c1 c2 c3 d0 d1 d2 K)
      (c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3
        + (d0 + d1 * t + d2 * t ^ 2) * Real.exp (-z * t) + K * Real.exp (-2 * z * t)) t := by
  have hz' : z ≠ 0 := ne_of_gt hz
  have hE : HasDerivAt (fun s => Real.exp (-z * s)) (-z * Real.exp (-z * t)) t := by
    have h := (Real.hasDerivAt_exp (-z * t)).comp t ((hasDerivAt_id t).const_mul (-z))
    simp only [Function.comp_def, mul_one] at h
    rwa [mul_comm (Real.exp (-z * t)) (-z)] at h
  have hE2 : HasDerivAt (fun s => Real.exp (-2 * z * s)) (-2 * z * Real.exp (-2 * z * t)) t := by
    have h := (Real.hasDerivAt_exp (-2 * z * t)).comp t ((hasDerivAt_id t).const_mul (-2 * z))
    simp only [Function.comp_def, mul_one] at h
    rwa [mul_comm (Real.exp (-2 * z * t)) (-2 * z)] at h
  have hpoly := ((((hasDerivAt_id t).const_mul c0).add
      (((hasDerivAt_pow 2 t).const_mul c1).div_const 2)).add
      (((hasDerivAt_pow 3 t).const_mul c2).div_const 3)).add
      (((hasDerivAt_pow 4 t).const_mul c3).div_const 4)
  have hquad := (((hasDerivAt_const t (-d0 / z - d1 / z ^ 2 - 2 * d2 / z ^ 3)).add
      ((hasDerivAt_id t).const_mul (-d1 / z - 2 * d2 / z ^ 2))).add
      ((hasDerivAt_pow 2 t).const_mul (-d2 / z)))
  have hsum := (hpoly.add (hquad.mul hE)).add (hE2.const_mul (-K / (2 * z)))
  refine hsum.congr_deriv ?_
  norm_num
  set E := Real.exp (-z * t)
  set F := Real.exp (-2 * z * t)
  field_simp
  ring

/-- **Canonical bounded-region integral.**  `∫_a^b (cubic + quadratic·e^{−zt} + K·e^{−2zt}) =
canonAntider b − canonAntider a` (FTC, `z > 0`). -/
theorem integral_canonical (a b z c0 c1 c2 c3 d0 d1 d2 K : ℝ) (hz : 0 < z) :
    (∫ t in a..b, c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3
        + (d0 + d1 * t + d2 * t ^ 2) * Real.exp (-z * t) + K * Real.exp (-2 * z * t))
      = canonAntider z c0 c1 c2 c3 d0 d1 d2 K b - canonAntider z c0 c1 c2 c3 d0 d1 d2 K a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => canonAntider_hasDerivAt z c0 c1 c2 c3 d0 d1 d2 K hz t)
    (Continuous.intervalIntegrable (by fun_prop) a b)]

/-! ### BRK.16b part (b) — branch-evaluation lemmas (which formula each factor takes per region)

On each region both factors sit in a definite branch; these rewrite `baxterQ`/`baxterQ'(·+r)` to
that branch's formula, so the region integrand is a plain product (fed to `integral_canonical` /
`integral_tailtail`).  The region membership + ordering lemmas discharge the branch conditions. -/

/-- `Q_jl(t)` on its core `[edgeLo σ j l, edgeHi σ j l]`. -/
theorem baxterQ_core_eq (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ) (j l : Fin N)
    (t : ℝ) (h1 : edgeLo σ j l ≤ t) (h2 : t ≤ edgeHi σ j l) :
    baxterQ z σ A qp Wt Ct j l t
      = qp j l * (t - edgeLo σ j l - σ j) + A l / 2 * (t - edgeLo σ j l - σ j) ^ 2
        + Wt j l * Real.exp (-z * (t - edgeLo σ j l)) + Ct j l := by
  unfold baxterQ; rw [if_neg (not_lt.mpr h1), if_pos h2]

/-- `Q_jl(t)` on its tail `(edgeHi σ j l, ∞)`. -/
theorem baxterQ_tail_eq (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ) (j l : Fin N)
    (t : ℝ) (hσ : ∀ i, 0 ≤ σ i) (h : edgeHi σ j l < t) :
    baxterQ z σ A qp Wt Ct j l t
      = Wt j l * Real.exp (-z * (t - edgeLo σ j l))
        + Ct j l * Real.exp (-z * (t - edgeHi σ j l)) := by
  have hle : edgeLo σ j l ≤ edgeHi σ j l := by simp only [edgeLo, edgeHi]; linarith [hσ j, hσ l]
  unfold baxterQ
  rw [if_neg (by linarith : ¬ t < edgeLo σ j l), if_neg (not_le.mpr h)]

/-- `Q'_il(t+r)` on its core `edgeLo σ i l ≤ t+r ≤ edgeHi σ i l`. -/
theorem baxterQ'_shift_core_eq (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i l : Fin N) (t r : ℝ) (h1 : edgeLo σ i l ≤ t + r) (h2 : t + r ≤ edgeHi σ i l) :
    baxterQ' z σ A qp Wt Ct i l (t + r)
      = qp i l + A l * (t + r - edgeLo σ i l - σ i)
        - z * Wt i l * Real.exp (-z * (t + r - edgeLo σ i l)) := by
  unfold baxterQ'; rw [if_neg (not_lt.mpr h1), if_pos h2]

/-- `Q'_il(t+r)` on its tail `edgeHi σ i l < t+r`. -/
theorem baxterQ'_shift_tail_eq (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i l : Fin N) (t r : ℝ) (hσ : ∀ i, 0 ≤ σ i) (h : edgeHi σ i l < t + r) :
    baxterQ' z σ A qp Wt Ct i l (t + r)
      = -z * Wt i l * Real.exp (-z * (t + r - edgeLo σ i l))
        - z * Ct i l * Real.exp (-z * (t + r - edgeHi σ i l)) := by
  have hle : edgeLo σ i l ≤ edgeHi σ i l := by simp only [edgeLo, edgeHi]; linarith [hσ i, hσ l]
  unfold baxterQ'
  rw [if_neg (by linarith : ¬ t + r < edgeLo σ i l), if_neg (not_le.mpr h)]

/-! ### BRK.16b part (b) — region pointwise-to-canonical identities

Each bounded region's branch product, rewritten into the canonical `cubic + quadratic·e^(−zt) +
K·e^(−2zt)` form fed to `integral_canonical`.  Coefficients are the validated
`scripts/verify_baxterconv_decomposition.py` output (LHS exps split to the `e^(zLi),e^(zLj),e^(−zr)`
atom basis, then `ring`). -/

set_option maxHeartbeats 800000 in
/-- **Region `core·core` (pointwise).**  `Q'_il(t+r)|core · Q_jl(t)|core` in canonical
`cubic + quadratic·e^(−zt) + K·e^(−2zt)` form (atoms `e^(zLi),e^(zLj),e^(−zr)`), the input to
`integral_canonical`.  Coefficients: `scripts/verify_baxterconv_decomposition.py`. -/
theorem region_corecore_pointwise (z r Li Lj si sj qi Al Wi qj Wj Cj t : ℝ) :
    (qi + Al * (t + r - Li - si) - z * Wi * Real.exp (-z * (t + r - Li)))
        * (qj * (t - Lj - sj) + Al / 2 * (t - Lj - sj) ^ 2
            + Wj * Real.exp (-z * (t - Lj)) + Cj)
      =
      (-Al^2*Li*Lj^2/2 - Al^2*Li*Lj*sj - Al^2*Li*sj^2/2 + Al^2*Lj^2*r/2 - Al^2*Lj^2*si/2
          + Al^2*Lj*r*sj - Al^2*Lj*si*sj + Al^2*r*sj^2/2 - Al^2*si*sj^2/2 - Al*Cj*Li + Al*Cj*r
          - Al*Cj*si + Al*Li*Lj*qj + Al*Li*qj*sj + Al*Lj^2*qi/2 + Al*Lj*qi*sj - Al*Lj*qj*r
          + Al*Lj*qj*si + Al*qi*sj^2/2 - Al*qj*r*sj + Al*qj*si*sj + Cj*qi - Lj*qi*qj - qi*qj*sj)
      + (
        (Al^2*Li*Lj + Al^2*Li*sj + Al^2*Lj^2/2 - Al^2*Lj*r + Al^2*Lj*si + Al^2*Lj*sj - Al^2*r*sj
            + Al^2*si*sj + Al^2*sj^2/2 + Al*Cj - Al*Li*qj - Al*Lj*qi - Al*Lj*qj - Al*qi*sj
            + Al*qj*r - Al*qj*si - Al*qj*sj + qi*qj)) * t
      + (
        (-Al^2*Li/2 - Al^2*Lj + Al^2*r/2 - Al^2*si/2 - Al^2*sj + Al*qi/2 + Al*qj)) * t ^ 2
      + (Al^2/2) * t ^ 3
      + ((
        (-Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Lj^2*Wi*z/2
            - Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Lj*Wi*sj*z
            - Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Wi*sj^2*z/2 - Al*(Real.exp (z*Lj))*Li*Wj
            + Al*(Real.exp (z*Lj))*Wj*r - Al*(Real.exp (z*Lj))*Wj*si
            - Cj*(Real.exp (z*Li))*(Real.exp (-z*r))*Wi*z
            + (Real.exp (z*Li))*(Real.exp (-z*r))*Lj*Wi*qj*z
            + (Real.exp (z*Li))*(Real.exp (-z*r))*Wi*qj*sj*z + (Real.exp (z*Lj))*Wj*qi))
        + (
          (Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Lj*Wi*z
              + Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Wi*sj*z + Al*(Real.exp (z*Lj))*Wj
              - (Real.exp (z*Li))*(Real.exp (-z*r))*Wi*qj*z)) * t
        + (-Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Wi*z/2) * t ^ 2) * Real.exp (-z * t)
      + (-(Real.exp (z*Li)) * (Real.exp (z*Lj)) * (Real.exp (-z*r)) * Wi * Wj * z)
        * Real.exp (-2 * z * t) := by
  have hI : Real.exp (-z * (t + r - Li))
      = Real.exp (-z * t) * Real.exp (-z * r) * Real.exp (z * Li) := by
    rw [show -z * (t + r - Li) = -z * t + -z * r + z * Li by ring,
      Real.exp_add, Real.exp_add]
  have hJ : Real.exp (-z * (t - Lj)) = Real.exp (-z * t) * Real.exp (z * Lj) := by
    rw [show -z * (t - Lj) = -z * t + z * Lj by ring, Real.exp_add]
  have hEE : Real.exp (-2 * z * t) = Real.exp (-z * t) * Real.exp (-z * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [hI, hJ, hEE]; ring

set_option maxHeartbeats 800000 in
/-- **Region `coretail` (pointwise)** — canonical `cubic + quadratic·e^(−zt) + K·e^(−2zt)` form
(coefficients: `scripts/verify_baxterconv_decomposition.py`). -/
theorem region_coretail_pointwise (z r Li Lj Hj si qi Al Wi Wj Cj t : ℝ) :
    (qi + Al * (t + r - Li - si) - z * Wi * Real.exp (-z * (t + r - Li)))
        * (Wj * Real.exp (-z * (t - Lj)) + Cj * Real.exp (-z * (t - Hj)))
      =
      (0)
      + (
        (0)) * t
      + (
        (0)) * t ^ 2
      + (0) * t ^ 3
      + ((
        (-Al*Cj*(Real.exp (z*Hj))*Li + Al*Cj*(Real.exp (z*Hj))*r - Al*Cj*(Real.exp (z*Hj))*si
            - Al*(Real.exp (z*Lj))*Li*Wj + Al*(Real.exp (z*Lj))*Wj*r
            - Al*(Real.exp (z*Lj))*Wj*si + Cj*(Real.exp (z*Hj))*qi + (Real.exp (z*Lj))*Wj*qi))
        + (
          (Al*Cj*(Real.exp (z*Hj)) + Al*(Real.exp (z*Lj))*Wj)) * t
        + (
          (0)) * t ^ 2) * Real.exp (-z * t)
      + (
        (-Cj*(Real.exp (z*Hj))*(Real.exp (z*Li))*(Real.exp (-z*r))*Wi*z
            - (Real.exp (z*Li))*(Real.exp (z*Lj))*(Real.exp (-z*r))*Wi*Wj*z))
        * Real.exp (-2 * z * t) := by
  have hI : Real.exp (-z * (t + r - Li))
      = Real.exp (-z * t) * Real.exp (-z * r) * Real.exp (z * Li) := by
    rw [show -z * (t + r - Li) = -z * t + -z * r + z * Li by ring,
      Real.exp_add, Real.exp_add]
  have hJ : Real.exp (-z * (t - Lj)) = Real.exp (-z * t) * Real.exp (z * Lj) := by
    rw [show -z * (t - Lj) = -z * t + z * Lj by ring, Real.exp_add]
  have hG : Real.exp (-z * (t - Hj)) = Real.exp (-z * t) * Real.exp (z * Hj) := by
    rw [show -z * (t - Hj) = -z * t + z * Hj by ring, Real.exp_add]
  have hEE : Real.exp (-2 * z * t) = Real.exp (-z * t) * Real.exp (-z * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [hI, hJ, hG, hEE]; ring

set_option maxHeartbeats 800000 in
/-- **Region `tailcore` (pointwise)** — canonical `cubic + quadratic·e^(−zt) + K·e^(−2zt)` form
(coefficients: `scripts/verify_baxterconv_decomposition.py`). -/
theorem region_tailcore_pointwise (z r Li Hi Lj sj qj Al Wi Ci Wj Cj t : ℝ) :
    (-z * Wi * Real.exp (-z * (t + r - Li)) - z * Ci * Real.exp (-z * (t + r - Hi)))
        * (qj * (t - Lj - sj) + Al / 2 * (t - Lj - sj) ^ 2 + Wj * Real.exp (-z * (t - Lj)) + Cj)
      =
      (0)
      + (
        (0)) * t
      + (
        (0)) * t ^ 2
      + (0) * t ^ 3
      + ((
        (-Al*Ci*(Real.exp (z*Hi))*(Real.exp (-z*r))*Lj^2*z/2
            - Al*Ci*(Real.exp (z*Hi))*(Real.exp (-z*r))*Lj*sj*z
            - Al*Ci*(Real.exp (z*Hi))*(Real.exp (-z*r))*sj^2*z/2
            - Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Lj^2*Wi*z/2
            - Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Lj*Wi*sj*z
            - Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Wi*sj^2*z/2
            - Ci*Cj*(Real.exp (z*Hi))*(Real.exp (-z*r))*z
            + Ci*(Real.exp (z*Hi))*(Real.exp (-z*r))*Lj*qj*z
            + Ci*(Real.exp (z*Hi))*(Real.exp (-z*r))*qj*sj*z
            - Cj*(Real.exp (z*Li))*(Real.exp (-z*r))*Wi*z
            + (Real.exp (z*Li))*(Real.exp (-z*r))*Lj*Wi*qj*z
            + (Real.exp (z*Li))*(Real.exp (-z*r))*Wi*qj*sj*z))
        + (
          (Al*Ci*(Real.exp (z*Hi))*(Real.exp (-z*r))*Lj*z
              + Al*Ci*(Real.exp (z*Hi))*(Real.exp (-z*r))*sj*z
              + Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Lj*Wi*z
              + Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Wi*sj*z
              - Ci*(Real.exp (z*Hi))*(Real.exp (-z*r))*qj*z
              - (Real.exp (z*Li))*(Real.exp (-z*r))*Wi*qj*z)) * t
        + (
          (-Al*Ci*(Real.exp (z*Hi))*(Real.exp (-z*r))*z/2
              - Al*(Real.exp (z*Li))*(Real.exp (-z*r))*Wi*z/2)) * t ^ 2) * Real.exp (-z * t)
      + (
        (-Ci*(Real.exp (z*Hi))*(Real.exp (z*Lj))*(Real.exp (-z*r))*Wj*z
            - (Real.exp (z*Li))*(Real.exp (z*Lj))*(Real.exp (-z*r))*Wi*Wj*z))
        * Real.exp (-2 * z * t) := by
  have hI : Real.exp (-z * (t + r - Li))
      = Real.exp (-z * t) * Real.exp (-z * r) * Real.exp (z * Li) := by
    rw [show -z * (t + r - Li) = -z * t + -z * r + z * Li by ring,
      Real.exp_add, Real.exp_add]
  have hIH : Real.exp (-z * (t + r - Hi))
      = Real.exp (-z * t) * Real.exp (-z * r) * Real.exp (z * Hi) := by
    rw [show -z * (t + r - Hi) = -z * t + -z * r + z * Hi by ring,
      Real.exp_add, Real.exp_add]
  have hJ : Real.exp (-z * (t - Lj)) = Real.exp (-z * t) * Real.exp (z * Lj) := by
    rw [show -z * (t - Lj) = -z * t + z * Lj by ring, Real.exp_add]
  have hEE : Real.exp (-2 * z * t) = Real.exp (-z * t) * Real.exp (-z * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [hI, hIH, hJ, hEE]; ring

end FMSA.ExactMSA.Breakpoint
