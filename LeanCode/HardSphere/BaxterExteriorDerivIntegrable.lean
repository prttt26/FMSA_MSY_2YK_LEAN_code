/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRenewalDiff
import LeanCode.HardSphere.BaxterExteriorRegularityGeneral

/-!
# `L¹` bound on the exterior derivative — step 6 of `OZFIX.25` (retires axiom 7b)

Goal: `IntegrableOn (baxterPsiSmoothDeriv …) (Ioi σ)`, i.e. the three summands of **(★DIFF)**

  `Ψ'(r) = baxterForcing'(r) + q0(0)·ψ̃(r) + ∫_σ^r q0'(r−t)·ψ̃(t)dt`

are each `L¹(σ,∞)`:

* **forcing term** — vanishes for `r > 2σ` (there `r−s ≥ r−σ > σ`, so `q0PolyDeriv_eq_zero_of_gt`
  kills the integrand), and is bounded on the remaining bounded piece;
* **`q0(0)·ψ̃`** — a constant times the already-proven `baxterPsiOuter_integrableOn`;
* **convolution term** — this is a genuine convolution `(ψ·1_{Ici σ}) ⋆ (q0'·1_{Icc 0 σ})`, so
  **Mathlib's Young inequality** `MeasureTheory.Integrable.integrable_convolution` applies directly;
  no hand-rolled Tonelli is needed.  The two support truncations are what make the identification
  work: `q0PolyDeriv u = 0` for `u > σ` handles `t < r−σ`, and the `Icc 0 σ` indicator kills the
  `t > r` region where `q0PolyDeriv (r−t)` (with negative argument) is *not* zero.
-/

open MeasureTheory Set Filter Topology
open scoped Convolution

namespace FMSA.HardSphere

noncomputable section

variable {eta sigma rho : ℝ}

/-! ### The two truncated factors -/

/-- `ψ` truncated to the exterior — the `L¹` left factor of the convolution. -/
def psiTrunc (eta sigma rho : ℝ) : ℝ → ℝ :=
  Set.indicator (Ici sigma) (baxterPsiOuter eta sigma rho)

/-- `q0'` truncated to the core — the `L¹` right factor.  The truncation is **essential**:
`q0PolyDeriv u ≠ 0` for `u < 0`, so without it the convolution would pick up `t > r`. -/
def q0DerivTrunc (eta sigma rho : ℝ) : ℝ → ℝ :=
  Set.indicator (Icc 0 sigma) (q0PolyDeriv eta sigma rho)

theorem psiTrunc_integrable (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    Integrable (psiTrunc eta sigma rho) := by
  have hIoi : IntegrableOn (baxterPsiOuter eta sigma rho) (Ioi sigma) :=
    baxterPsiOuter_integrableOn heta0 heta1 hsigma hrho heta_def
  have hIci : IntegrableOn (baxterPsiOuter eta sigma rho) (Ici sigma) := by
    rw [← Ioi_union_left, integrableOn_union]
    exact ⟨hIoi, by simp⟩
  rw [psiTrunc, integrable_indicator_iff measurableSet_Ici]
  exact hIci

/-- General pointwise bound `|q0PolyDeriv u| ≤ |ρq'| + |ρq''|·|u−σ|`. -/
theorem abs_q0PolyDeriv_le (eta sigma rho u : ℝ) :
    |q0PolyDeriv eta sigma rho u|
      ≤ |rho * q_prime_py eta sigma| + |rho * q_doubleprime_py eta| * |u - sigma| := by
  have h1 : |rho * q_prime_py eta sigma * (if u < sigma then (1:ℝ) else 0)|
      ≤ |rho * q_prime_py eta sigma| := by
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    split_ifs <;> simp
  have h2 : |rho * q_doubleprime_py eta * phi1_real sigma u|
      ≤ |rho * q_doubleprime_py eta| * |u - sigma| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_phi1_real_le sigma u) (abs_nonneg _)
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

/-- `|q0PolyDeriv| ≤ |ρq'| + |ρq''|·σ` on `Icc 0 σ`.  (`q0PolyDeriv` is *not* continuous there — the
`if u < σ` indicator jumps at `σ` — so integrability goes via bounded+measurable, not `ContinuousOn`.) -/
theorem abs_q0PolyDeriv_le_on_Icc (eta sigma rho : ℝ) (hsigma : 0 ≤ sigma) {u : ℝ}
    (hu : u ∈ Icc 0 sigma) :
    |q0PolyDeriv eta sigma rho u|
      ≤ |rho * q_prime_py eta sigma| + |rho * q_doubleprime_py eta| * sigma := by
  have h1 : |rho * q_prime_py eta sigma * (if u < sigma then (1:ℝ) else 0)|
      ≤ |rho * q_prime_py eta sigma| := by
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    split_ifs <;> simp
  have h2 : |rho * q_doubleprime_py eta * phi1_real sigma u|
      ≤ |rho * q_doubleprime_py eta| * sigma := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine le_trans (abs_phi1_real_le sigma u) ?_
    rw [abs_of_nonpos (by linarith [(mem_Icc.mp hu).2] : u - sigma ≤ 0)]
    linarith [(mem_Icc.mp hu).1]
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

theorem q0DerivTrunc_integrable (eta sigma rho : ℝ) (hsigma : 0 ≤ sigma) :
    Integrable (q0DerivTrunc eta sigma rho) := by
  rw [q0DerivTrunc, integrable_indicator_iff measurableSet_Icc]
  refine Measure.integrableOn_of_bounded (M := |rho * q_prime_py eta sigma|
      + |rho * q_doubleprime_py eta| * sigma) (by simp) ?_ ?_
  · exact (q0PolyDeriv_measurable eta sigma rho).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with u hu
    exact abs_q0PolyDeriv_le_on_Icc eta sigma rho hsigma hu

/-! ### The convolution term -/

/-- **The convolution identification.**  For `r ≥ σ`, the renewal-derivative integral
`∫_σ^r q0'(r−t)·ψ̃(t)dt` *is* the full-line convolution of the two truncated factors.

Both truncations do real work: `q0PolyDeriv u = 0` for `u > σ` lets us extend the lower limit from
`max(σ, r−σ)` down to `σ`, while the `Icc 0 σ` indicator kills `t > r` (where `q0PolyDeriv (r−t)`
has a *negative* argument and is **not** zero). -/
theorem renewalConv_eq_convolution (hsigma : 0 < sigma) {r : ℝ} (hr : sigma ≤ r) :
    (∫ t in sigma..r, q0PolyDeriv eta sigma rho (r - t) * baxterPsiExt eta sigma rho t)
      = (psiTrunc eta sigma rho ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          q0DerivTrunc eta sigma rho) r := by
  have hpt : ∀ t : ℝ, psiTrunc eta sigma rho t • q0DerivTrunc eta sigma rho (r - t)
      = Set.indicator (Icc sigma r)
        (fun t => q0PolyDeriv eta sigma rho (r - t) * baxterPsiExt eta sigma rho t) t := by
    intro t
    by_cases htl : sigma ≤ t
    · by_cases htr : t ≤ r
      · have hmem : t ∈ Icc sigma r := ⟨htl, htr⟩
        rw [Set.indicator_of_mem hmem, psiTrunc,
          Set.indicator_of_mem (Set.mem_Ici.mpr htl), q0DerivTrunc]
        by_cases hker : r - t ≤ sigma
        · rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨by linarith, hker⟩),
            baxterPsiExt_eq_of_ge htl, smul_eq_mul]
          exact mul_comm _ _
        · -- `r − t > σ`: BOTH sides vanish (`q0PolyDeriv` is 0 past the core)
          rw [Set.indicator_of_notMem (by intro hc; exact hker (mem_Icc.mp hc).2),
            q0PolyDeriv_eq_zero_of_gt sigma (not_le.mp hker), smul_zero, zero_mul]
      · have : r - t ∉ Icc (0:ℝ) sigma := by
          intro hc; exact absurd (mem_Icc.mp hc).1 (by linarith)
        rw [Set.indicator_of_notMem (by intro hc; exact htr (mem_Icc.mp hc).2),
          q0DerivTrunc, Set.indicator_of_notMem this, smul_zero]
    · rw [Set.indicator_of_notMem (by intro hc; exact htl (mem_Icc.mp hc).1),
        psiTrunc, Set.indicator_of_notMem (by simpa using htl), zero_smul]
  rw [convolution]
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [funext hpt, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr]

/-- **Young ⇒ the renewal-convolution term is `L¹`.** -/
theorem renewalConv_integrableOn (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    IntegrableOn
      (fun r => ∫ t in sigma..r, q0PolyDeriv eta sigma rho (r - t) * baxterPsiExt eta sigma rho t)
      (Ioi sigma) := by
  have hyoung : Integrable (psiTrunc eta sigma rho ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      q0DerivTrunc eta sigma rho) :=
    (psiTrunc_integrable heta0 heta1 hsigma hrho heta_def).integrable_convolution _
      (q0DerivTrunc_integrable eta sigma rho hsigma.le)
  refine (hyoung.integrableOn (s := Ioi sigma)).congr_fun (fun r hr => ?_) measurableSet_Ioi
  exact (renewalConv_eq_convolution hsigma (le_of_lt (mem_Ioi.mp hr))).symm

/-- The `q0(0)·ψ̃` summand — a constant times the proven exterior `L¹` bound. -/
theorem q0_mul_psiExt_integrableOn (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    IntegrableOn (fun r => q0_poly eta sigma rho 0 * baxterPsiExt eta sigma rho r) (Ioi sigma) := by
  have hpsi : IntegrableOn (baxterPsiExt eta sigma rho) (Ioi sigma) :=
    (baxterPsiOuter_integrableOn heta0 heta1 hsigma hrho heta_def).congr_fun
      (fun r hr => (baxterPsiExt_eq_of_ge (le_of_lt (mem_Ioi.mp hr))).symm) measurableSet_Ioi
  exact hpsi.const_mul (q0_poly eta sigma rho 0)

/-- The forcing-derivative summand vanishes past `2σ`. -/
theorem forcingDeriv_eq_zero_of_gt (hsigma : 0 < sigma) {r : ℝ} (hr : 2 * sigma < r) :
    (∫ s in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (r - s) * (-s)) = 0 := by
  have hz : (∫ s in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (r - s) * (-s))
      = ∫ _ in (0:ℝ)..sigma, (0:ℝ) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le hsigma.le] at hs
    show q0PolyDeriv eta sigma rho (r - s) * (-s) = 0
    rw [q0PolyDeriv_eq_zero_of_gt sigma (by linarith [(mem_Icc.mp hs).2]), zero_mul]
  rw [hz, intervalIntegral.integral_zero]

/-- The forcing-derivative summand is `L¹` on `(σ,∞)`.  It vanishes past `2σ`
(`forcingDeriv_eq_zero_of_gt`); on the bounded remainder it is measurable — it **is**
`deriv (baxterForcing …)` by `hasDerivAt_baxterForcing`, so `measurable_deriv` applies, sidestepping
the fact that the integrand itself jumps — and bounded by `(|ρq'|+|ρq''|σ)·σ²`. -/
theorem forcingDeriv_integrableOn (hsigma : 0 < sigma) :
    IntegrableOn (fun r => ∫ s in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (r - s) * (-s))
      (Ioi sigma) := by
  set B : ℝ := |rho * q_prime_py eta sigma| + |rho * q_doubleprime_py eta| * sigma with hBdef
  have hB0 : 0 ≤ B := by
    have h1 : 0 ≤ |rho * q_prime_py eta sigma| := abs_nonneg _
    have h2 : 0 ≤ |rho * q_doubleprime_py eta| * sigma :=
      mul_nonneg (abs_nonneg _) hsigma.le
    simp only [hBdef]; linarith
  have hmeas : AEStronglyMeasurable
      (fun r => ∫ s in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (r - s) * (-s)) volume := by
    have hEq : (fun r => ∫ s in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (r - s) * (-s))
        = deriv (baxterForcing eta sigma rho) :=
      funext fun r => ((hasDerivAt_baxterForcing eta sigma rho hsigma.le r).deriv).symm
    rw [hEq]
    exact (measurable_deriv (baxterForcing eta sigma rho)).aestronglyMeasurable
  have hsplit : Ioi sigma = Ioc sigma (2 * sigma) ∪ Ioi (2 * sigma) :=
    (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  rw [hsplit, integrableOn_union]
  refine ⟨Measure.integrableOn_of_bounded (M := B * sigma * sigma) (by simp) hmeas ?_, ?_⟩
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    have hr1 : sigma < r := (mem_Ioc.mp hr).1
    have hr2 : r ≤ 2 * sigma := (mem_Ioc.mp hr).2
    have hbd : ∀ x ∈ Set.uIoc (0:ℝ) sigma,
        ‖q0PolyDeriv eta sigma rho (r - x) * (-x)‖ ≤ B * sigma := by
      intro x hx
      rw [Set.uIoc_of_le hsigma.le] at hx
      have hx0 : 0 < x := (mem_Ioc.mp hx).1
      have hxs : x ≤ sigma := (mem_Ioc.mp hx).2
      have hker : |q0PolyDeriv eta sigma rho (r - x)| ≤ B := by
        refine le_trans (abs_q0PolyDeriv_le eta sigma rho (r - x)) ?_
        have habs : |r - x - sigma| ≤ sigma := by rw [abs_le]; constructor <;> linarith
        simp only [hBdef]
        linarith [mul_le_mul_of_nonneg_left habs (abs_nonneg (rho * q_doubleprime_py eta))]
      calc ‖q0PolyDeriv eta sigma rho (r - x) * (-x)‖
          = |q0PolyDeriv eta sigma rho (r - x)| * x := by
            rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hx0]
        _ ≤ B * sigma := mul_le_mul hker hxs hx0.le hB0
    have hfin := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    simp only [sub_zero, abs_of_nonneg hsigma.le] at hfin
    exact hfin
  · refine (integrableOn_zero (μ := volume) (s := Ioi (2 * sigma))).congr_fun (fun r hr => ?_)
      measurableSet_Ioi
    exact (forcingDeriv_eq_zero_of_gt hsigma (mem_Ioi.mp hr)).symm

/-- **The three (★DIFF) summands assemble: `Ψ'` is `L¹` on the exterior.** -/
theorem baxterPsiSmoothDeriv_integrableOn (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    IntegrableOn (baxterPsiSmoothDeriv eta sigma rho) (Ioi sigma) := by
  have h1 := forcingDeriv_integrableOn (eta := eta) (rho := rho) hsigma
  have h2 := q0_mul_psiExt_integrableOn heta0 heta1 hsigma hrho heta_def
  have h3 := renewalConv_integrableOn heta0 heta1 hsigma hrho heta_def
  exact h1.add (h2.add h3)

/-- **Axiom 7b PROVED** (`OZFIX.25` step 6) — the exterior derivative is `L¹`.

For *any* `C¹` representative `g` of `baxterPsiOuter/·`, `g + r·g' = (r·g)' = Ψ'` on the **open**
`Ioi σ`: there `y·g y = baxterPsiSmooth y` (by `hg_eq` + `baxterPsiSmooth_eq_of_ge`), both sides are
differentiable, and derivatives are unique.  So the claim reduces to
`baxterPsiSmoothDeriv_integrableOn`, independently of the representative. -/
theorem ozExterior_deriv_integrable_proved (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {g g' : ℝ → ℝ}
    (hderiv : ∀ r ∈ Set.Ici sigma, HasDerivAt g (g' r) r)
    (hg_eq : ∀ r, sigma ≤ r → g r = baxterPsiOuter eta sigma rho r / r) :
    IntegrableOn (fun r => g r + r * g' r) (Ioi sigma) := by
  refine (baxterPsiSmoothDeriv_integrableOn heta0 heta1 hsigma hrho heta_def).congr_fun
    (fun r hr => ?_) measurableSet_Ioi
  have hrσ : sigma < r := mem_Ioi.mp hr
  have hr0 : 0 < r := lt_trans hsigma hrσ
  -- `y ↦ y * g y` agrees with `baxterPsiSmooth` on the open set `Ioi σ ∋ r`
  have hev : (fun y : ℝ => y * g y) =ᶠ[nhds r] baxterPsiSmooth eta sigma rho := by
    filter_upwards [Ioi_mem_nhds hrσ] with y hy
    have hyσ : sigma ≤ y := le_of_lt (mem_Ioi.mp hy)
    have hy0 : y ≠ 0 := ne_of_gt (lt_trans hsigma (mem_Ioi.mp hy))
    rw [hg_eq y hyσ, baxterPsiSmooth_eq_of_ge hsigma hyσ]
    field_simp
  have hd1 : HasDerivAt (fun y : ℝ => y * g y) (1 * g r + r * g' r) r :=
    (hasDerivAt_id r).mul (hderiv r (le_of_lt hrσ))
  rw [one_mul] at hd1
  have hd2 : HasDerivAt (fun y : ℝ => y * g y) (baxterPsiSmoothDeriv eta sigma rho r) r :=
    (hasDerivAt_baxterPsiSmooth hsigma (le_of_lt hrσ)).congr_of_eventuallyEq hev
  exact hd2.unique hd1

end

end FMSA.HardSphere
