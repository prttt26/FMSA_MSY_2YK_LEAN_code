import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPPrimitive
import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPRegularity

/-! Spatial first-order identification uses the actual ordered radial BH
correlation. The compact quadratic correction is retained in Q1. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators ContDiff
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem bhCoefficient_neg_fixed_seed (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G0 : TailMatrix ι N) (i j : Fin N) (b : BasisIndex ι) :
    bhCoefficient z ρ σ (-D, G0) i j b =
      bhCoefficient z ρ σ (0, G0) i j b-coefficientSlope z ρ σ D G0 i j b := by
  have hw (u : ι) (a b : Fin N) : Wt (z u) ρ (G0 u) ((-D) u) a b =
      -Wt (z u) ρ (G0 u) (D u) a b := by
    simp [Wt, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  have hc (u : ι) (a b : Fin N) : Ct (z u) ρ σ (G0 u) ((-D) u) a b =
      -Ct (z u) ρ σ (G0 u) (D u) a b := by
    simp [Ct, Pi.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
  have hm (u : ι) (j : Fin N) : mixM (z u) ρ σ (G0 u) ((-D) u) j =
      -mixM (z u) ρ σ (G0 u) (D u) j := by
    simp only [mixM, hw, hc, mul_neg, ← neg_add, Finset.sum_neg_distrib]
  have hn (u : ι) (j : Fin N) : mixN (z u) ρ σ (G0 u) ((-D) u) j =
      -mixN (z u) ρ σ (G0 u) (D u) j := by
    simp only [mixN, hw, hc, mul_neg, ← neg_add, Finset.sum_neg_distrib]
  have ha (u : ι) (j : Fin N) : mixDA (z u) ρ σ (G0 u) ((-D) u) j =
      -mixDA (z u) ρ σ (G0 u) (D u) j := by
    simp only [mixDA, hm, hn, mul_neg, ← neg_add]
  have hq (u : ι) (a b : Fin N) : mixDqp (z u) ρ σ (G0 u) ((-D) u) a b =
      -mixDqp (z u) ρ σ (G0 u) (D u) a b := by
    simp only [mixDqp, hm, hn, mul_neg, ← neg_add]
  simp only [Pi.neg_apply] at ha hq
  rcases b with b | (u | u)
  · fin_cases b <;>
      simp [coefficientSlope, bhCoefficient, coefficient, amplitudeQp, amplitudeA,
        hq, ha,
        Finset.sum_neg_distrib] <;>
      simp [mixDqp, mixDA, mixM, mixN, Wt, Ct] <;> ring
  · simp [coefficientSlope, bhCoefficient, coefficient, W, Wt, Pi.neg_apply,
      mul_neg, Finset.sum_neg_distrib]
  · simp [coefficientSlope, bhCoefficient, coefficient, C, Ct, Pi.neg_apply,
      mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem bhCoefficient_fixed_seed_eq_base_add_slope (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G0 : TailMatrix ι N) (i j : Fin N) (b : BasisIndex ι) :
    bhCoefficient z ρ σ (D, G0) i j b =
      bhCoefficient z ρ σ (0, G0) i j b+coefficientSlope z ρ σ D G0 i j b := by
  unfold coefficientSlope
  ring

theorem linearizedPrimitiveReal_odd_polarization (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G0 : TailMatrix ι N) (i j : Fin N) (r : ℝ) :
    linearizedPrimitiveReal z ρ σ D G0 i j r =
      (primitiveBasisReal z ρ σ (D, G0) i j r-
        primitiveBasisReal z ρ σ (-D, G0) i j r)/2 := by
  simp only [primitiveBasisReal, linearizedPrimitiveReal,
    bhCoefficient_neg_fixed_seed z ρ σ D G0, bhCoefficient_fixed_seed_eq_base_add_slope z ρ σ D G0]
  simp only [add_mul, mul_add, sub_mul, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  ring

theorem linearizedCorrelation_odd_polarization (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G0 : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) :
    linearizedCorrelation z ρ σ D G0 i j r =
      (correlation z ρ σ (amplitudeA z ρ σ D G0) (amplitudeQp z ρ σ D G0)
        (W z ρ D G0) (C z ρ σ D G0) i j r-
      correlation z ρ σ (amplitudeA z ρ σ (-D) G0) (amplitudeQp z ρ σ (-D) G0)
        (W z ρ (-D) G0) (C z ρ σ (-D) G0) i j r)/2 := by
  rw [correlation_eq_basis z hz ρ σ hσ (D, G0),
    correlation_eq_basis z hz ρ σ hσ (-D, G0)]
  simp only [linearizedCorrelation, bhCoefficient_neg_fixed_seed z ρ σ D G0,
    bhCoefficient_fixed_seed_eq_base_add_slope z ρ σ D G0]
  simp only [add_mul, mul_add, sub_mul, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  ring

theorem linearizedPrimitiveReal_hasDerivAt_ordered (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G0 : TailMatrix ι N)
    (i j : Fin N) (horder : σ j ≤ σ i) (r : ℝ) (hr : 0 < r)
    (hrR : r ≠ edgeHi σ i j) :
    HasDerivAt (linearizedPrimitiveReal z ρ σ D G0 i j)
      (-2*π*r*linearizedCorrelation z ρ σ D G0 i j r) r := by
  have hd (E : TailMatrix ι N) := baxterPrimitive_re_hasDerivAt z hz ρ σ
    (amplitudeA z ρ σ E G0) (amplitudeQp z ρ σ E G0)
    (W z ρ E G0) (C z ρ σ E G0) hσ i j horder r hr hrR
  have hb (E : TailMatrix ι N) : (fun x =>
      (baxterPrimitive z ρ σ (amplitudeA z ρ σ E G0) (amplitudeQp z ρ σ E G0)
        (W z ρ E G0) (C z ρ σ E G0) i j x).re) =
      primitiveBasisReal z ρ σ (E, G0) i j := by
    funext x
    rw [baxterPrimitive_eq_basis z hz ρ σ hσ (E, G0), Complex.ofReal_re]
  have hp := (hd D).sub (hd (-D)) |>.div_const 2
  simp only [hb] at hp
  convert! hp using 1
  · funext x
    exact linearizedPrimitiveReal_odd_polarization z ρ σ D G0 i j x
  · rw [linearizedCorrelation_odd_polarization z hz ρ σ hσ D G0]
    ring

theorem dpOddW_continuousAt_positive_off_contact (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : 0 < r) (hrR : r ≠ edgeHi σ i j) :
    ContinuousAt (dpOddW z ρ σ K i j) r := by
  have hn : -r ≠ edgeHi σ i j := by unfold edgeHi; linarith [hσ i, hσ j]
  exact (dpW_continuousAt_off_contact z hz ρ σ (fun i => (hσ i).le) K i j r hrR).sub
    ((dpW_continuousAt_off_contact z hz ρ σ (fun i => (hσ i).le) K i j (-r) hn).comp
      (f := fun x : ℝ => -x) continuousAt_id.neg)

theorem dpPrimitive_hasDerivAt_positive_off_contact (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : 0 < r) (hrR : r ≠ edgeHi σ i j) :
    HasDerivAt (dpPrimitive z ρ σ K i j) (-dpOddW z ρ σ K i j r) r := by
  have hi := dpOddW_integrable z hz ρ σ (fun i => (hσ i).le) K i j
  have he : dpPrimitive z ρ σ K i j = fun x =>
      (∫ t in Ioi (0 : ℝ), dpOddW z ρ σ K i j t)-
        (∫ t in (0 : ℝ)..x, dpOddW z ρ σ K i j t) := by
    funext x
    unfold dpPrimitive
    have he := intervalIntegral.integral_Ioi_sub_Ioi' (a := 0) (b := x)
      hi.integrableOn hi.integrableOn
    linarith
  rw [he]
  have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := r)
    hi.intervalIntegrable hi.aestronglyMeasurable.stronglyMeasurableAtFilter
    (dpOddW_continuousAt_positive_off_contact z hz ρ σ hσ K i j r hr hrR)
  convert! (hasDerivAt_const r (∫ t in Ioi (0 : ℝ), dpOddW z ρ σ K i j t)).sub hd using 1
  simp only [zero_sub]

/-- Full core and exterior first-order DCF identification, for the actual
ordered radial BH representative. No independent core identity is assumed. -/
theorem linearizedCorrelation_eq_dpCorrelation_ordered (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) (horder : σ j ≤ σ i)
    (r : ℝ) (hr : 0 < r) (hrR : r ≠ edgeHi σ i j) :
    linearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j r =
      dpCorrelation z ρ σ K i j r := by
  have hrL : r ≠ edgeLo σ i j := by unfold edgeLo; linarith
  have he : dpPrimitive z ρ σ K i j =ᶠ[𝓝 r]
      linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j := by
    filter_upwards [eventually_ne_nhds hrL] with x hx
    exact (linearizedPrimitiveReal_eq_dpPrimitive_off_edge z ρ σ K hz hv hρ hσ hK i j x hx).symm
  have ha := linearizedPrimitiveReal_hasDerivAt_ordered z hz ρ σ (fun i => (hσ i).le)
    (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j horder r hr hrR
  have hd := dpPrimitive_hasDerivAt_positive_off_contact z hz ρ σ hσ K i j r hr hrR
  have hv := (ha.congr_of_eventuallyEq he).unique hd
  unfold dpCorrelation
  unfold dpOddW at hv
  have hden : 2*π*r ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hr.ne'
  apply (eq_div_iff hden).mpr
  nlinarith only [hv]

theorem linearizedCorrelation_ae_eq_dpCorrelation_ordered (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) (horder : σ j ≤ σ i) :
    linearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j =ᵐ[volume.restrict (Ioi 0)]
      dpCorrelation z ρ σ K i j := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (volume.ae_ne (edgeHi σ i j))] with r hr hrR
  exact linearizedCorrelation_eq_dpCorrelation_ordered z ρ σ K hz hv hρ hσ hK i j horder r hr hrR

/-- The actual smooth BH root germ realizes the independent DP first-order
radial correlation at every ordered positive radius off contact. -/
theorem exists_contDiffAt_root_with_dpCorrelation_ordered (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) :
    ∃ ψ : ℝ → TailMatrix ι N × TailMatrix ι N,
      ψ 0 = (0, baseSeed z ρ σ) ∧
      (∀ᶠ τ in 𝓝 0, IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2) ∧
      ContDiffAt ℝ ∞ ψ 0 ∧
      ∀ i j, σ j ≤ σ i → ∀ r, 0 < r → r ≠ edgeHi σ i j →
        HasDerivAt (fun τ => correlation z ρ σ
          (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
          (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) i j r)
          (dpCorrelation z ρ σ K i j r) 0 := by
  obtain ⟨ψ, h0, hroot, hc, _, hd⟩ := exists_contDiffAt_root_with_linearizedCorrelation z ρ σ K hz hv hρ hσ
  refine ⟨ψ, h0, hroot, hc, fun i j ho r hr hrR => ?_⟩
  rw [← linearizedCorrelation_eq_dpCorrelation_ordered z ρ σ K hz hv hρ hσ hK i j ho r hr hrR]
  exact hd i j r ho hr

end FMSA.ExactMSA.MultiTailMixture
