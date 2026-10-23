import LeanCode.YukawaOZMix.MSAMultiTailMixtureDerivative
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Actual ordered primitive as a finite-window shell integral, including
windows crossing contact. All derivative integrability is internal. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def rightCrossCorr (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j l : Fin N) (r : ℝ) : ℝ :=
  ∫ t : ℝ, qRight z σ A qp W C i l (t+r) * q z σ A qp W C j l t

theorem rightCrossCorr_lipschitz (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j l : Fin N) :
    ∃ L : NNReal, LipschitzWith L (rightCrossCorr z σ A qp W C i j l) := by
  obtain ⟨L, hL⟩ := qRight_lipschitz z hz σ A qp W C hσ i l
  let g := q z σ A qp W C j l
  have hg : Integrable (fun t => |g t|) := (q_integrable z hz σ A qp W C hσ j l).abs
  have hgn : 0 ≤ ∫ t : ℝ, |g t| := integral_nonneg (fun t => abs_nonneg _)
  refine ⟨L * Real.toNNReal (∫ t : ℝ, |g t|), LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  have hx := qRight_product_integrable z hz σ A qp W C hσ i j l x
  have hy := qRight_product_integrable z hz σ A qp W C hσ i j l y
  have hb : Integrable (fun t => ((L : ℝ)*dist x y)*|g t|) := hg.const_mul _
  have hnorm : ∀ t : ℝ,
      ‖qRight z σ A qp W C i l (t+x)*g t-qRight z σ A qp W C i l (t+y)*g t‖ ≤
        ((L : ℝ)*dist x y)*|g t| := by
    intro t
    have h := hL.dist_le_mul (t+x) (t+y)
    rw [dist_add_left] at h
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    simpa only [dist_eq_norm, Real.norm_eq_abs] using mul_le_mul_of_nonneg_right h (abs_nonneg (g t))
  unfold rightCrossCorr
  rw [dist_eq_norm, ← integral_sub hx hy]
  calc
    ‖∫ t : ℝ, qRight z σ A qp W C i l (t+x)*g t-qRight z σ A qp W C i l (t+y)*g t‖ ≤
        ∫ t : ℝ, ‖qRight z σ A qp W C i l (t+x)*g t-qRight z σ A qp W C i l (t+y)*g t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ((L : ℝ)*dist x y)*|g t| :=
      integral_mono (hx.sub hy).norm hb hnorm
    _ = ↑(L * Real.toNNReal (∫ t : ℝ, |g t|)) * dist x y := by
      rw [integral_const_mul, NNReal.coe_mul, Real.coe_toNNReal _ hgn]
      ring

def rightPrimitiveReal (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j : Fin N) (r : ℝ) : ℝ :=
  qRight z σ A qp W C i j r - ∑ l, ρ l * rightCrossCorr z σ A qp W C i j l r

theorem rightPrimitiveReal_lipschitz (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) :
    ∃ L : NNReal, LipschitzWith L (rightPrimitiveReal z ρ σ A qp W C i j) := by
  classical
  obtain ⟨L, hL⟩ := qRight_lipschitz z hz σ A qp W C hσ i j
  have hl : ∀ l, ∃ M : NNReal, LipschitzWith M (rightCrossCorr z σ A qp W C i j l) :=
    fun l => rightCrossCorr_lipschitz z hz σ A qp W C hσ i j l
  choose M hM using hl
  have hs := lipschitz_real_finite_sum Finset.univ
    (fun l r => ρ l * rightCrossCorr z σ A qp W C i j l r)
    (fun l => Real.nnabs (ρ l) * M l) (fun l _ => lipschitz_real_mul_const (hM l) _)
  exact ⟨_, hL.sub hs⟩

theorem rightPrimitiveReal_eq_ordered_positive (z : ι → ℝ) (ρ σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j : Fin N)
    (horder : σ j ≤ σ i) (r : ℝ) (hr : 0 < r) :
    rightPrimitiveReal z ρ σ A qp W C i j r = orderedPrimitiveReal z ρ σ A qp W C i j r := by
  unfold rightPrimitiveReal orderedPrimitiveReal
  rw [qRight_eq_q z σ A qp W C i j r (by unfold edgeLo; linarith)]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact qRight_product_eq_of_order z σ A qp W C i j l horder r hr t

theorem rightPrimitiveReal_hasDerivAt_positive (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (horder : σ j ≤ σ i)
    (r : ℝ) (hr : 0 < r) (hrR : r ≠ edgeHi σ i j) :
    HasDerivAt (rightPrimitiveReal z ρ σ A qp W C i j)
      (-2*π*r*correlation z ρ σ A qp W C i j r) r := by
  apply (orderedPrimitiveReal_hasDerivAt z hz ρ σ A qp W C hσ i j horder r hr hrR).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with x hx
  exact rightPrimitiveReal_eq_ordered_positive z ρ σ A qp W C i j horder x hx

/-- The actual shell integral on any finite positive window, including
windows crossing R_ij. No derivative integrability or contact premise. -/
theorem orderedPrimitiveReal_shell_window (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (horder : σ j ≤ σ i)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    orderedPrimitiveReal z ρ σ A qp W C i j a - orderedPrimitiveReal z ρ σ A qp W C i j b =
      2*π * ∫ r in a..b, r*correlation z ρ σ A qp W C i j r := by
  let P := rightPrimitiveReal z ρ σ A qp W C i j
  obtain ⟨L, hL⟩ := rightPrimitiveReal_lipschitz z hz ρ σ A qp W C hσ i j
  have hint : IntervalIntegrable (deriv P) volume a b :=
    (volume.integrableOn_of_bounded (s := uIcc a b) (isCompact_uIcc.measure_ne_top)
      (aestronglyMeasurable_deriv P volume)
      (Eventually.of_forall (fun x => norm_deriv_le_of_lipschitz hL))).intervalIntegrable
  have hd : ∀ x ∈ Ioo (min a b) (max a b) \ {edgeHi σ i j}, HasDerivAt P (deriv P x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans (lt_min ha hb) hx.1.1
    have hxR : x ≠ edgeHi σ i j := by simpa using hx.2
    exact (rightPrimitiveReal_hasDerivAt_positive z hz ρ σ A qp W C hσ i j horder x hx0 hxR).differentiableAt.hasDerivAt
  have hFTC := integral_eq_of_hasDerivAt_off_countable P (deriv P) (countable_singleton _)
    hL.continuous.continuousOn hd hint
  have he : (∫ x in a..b, deriv P x) = -2*π * ∫ x in a..b, x*correlation z ρ σ A qp W C i j x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (edgeHi σ i j)] with x hxR hx
    have hx0 : 0 < x := lt_trans (lt_min ha hb) hx.1
    rw [(rightPrimitiveReal_hasDerivAt_positive z hz ρ σ A qp W C hσ i j horder x hx0 hxR).deriv]
    ring
  dsimp only [P] at hFTC
  rw [he, rightPrimitiveReal_eq_ordered_positive z ρ σ A qp W C i j horder a ha,
    rightPrimitiveReal_eq_ordered_positive z ρ σ A qp W C i j horder b hb] at hFTC
  linarith

/-- Actual radius-weighted DCF is integrable on every nonnegative finite
window. Measurability and bounds follow from the actual Lipschitz primitive. -/
theorem orderedCorrelation_radius_intervalIntegrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (horder : σ j ≤ σ i)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun r => r*correlation z ρ σ A qp W C i j r) volume a b := by
  let P := rightPrimitiveReal z ρ σ A qp W C i j
  obtain ⟨L, hL⟩ := rightPrimitiveReal_lipschitz z hz ρ σ A qp W C hσ i j
  have hint : IntervalIntegrable (deriv P) volume a b :=
    (volume.integrableOn_of_bounded (s := uIcc a b) isCompact_uIcc.measure_ne_top
      (aestronglyMeasurable_deriv P volume)
      (Eventually.of_forall (fun x => norm_deriv_le_of_lipschitz hL))).intervalIntegrable
  apply (hint.div_const (-2*π)).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (volume.ae_ne (edgeHi σ i j))] with x hx hxR
  have hx0 : 0 < x := lt_of_le_of_lt (le_min ha hb) hx.1
  rw [(rightPrimitiveReal_hasDerivAt_positive z hz ρ σ A qp W C hσ i j horder x hx0 hxR).deriv]
  field_simp [pi_ne_zero]

end FMSA.ExactMSA.MultiTailMixture
