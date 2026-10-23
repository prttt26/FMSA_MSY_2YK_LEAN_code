import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairSpectralOZ

/-! Actual canonical HS-DCF continuity for the radial Fourier-to-OZ transfer.
The convolution smoothing is proved by dominated convergence; no independent
injectivity or physical-reference axiom is introduced. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def hsPairZeroPrime (z : ι → ℝ) (ρ σ : Fin N → ℝ) (i j : Fin N) : ℝ → ℝ :=
  qPrime z σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ))
    (amplitudeQp z ρ σ 0 (baseSeed z ρ σ)) (W z ρ 0 (baseSeed z ρ σ))
    (C z ρ σ 0 (baseSeed z ρ σ)) i j

theorem hsPairZeroPrime_eq_polynomial (z : ι → ℝ) (ρ σ : Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    hsPairZeroPrime z ρ σ i j r =
      if r < edgeLo σ i j then 0 else if r ≤ edgeHi σ i j then
        Q0phys ρ σ i j+Qppphys ρ σ j j*(r-edgeHi σ i j) else 0 := by
  simp only [hsPairZeroPrime, qPrime, amplitudeA_zero, amplitudeQp_zero, W, C, Wt, Ct,
    Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero]

theorem hsPairZeroPrime_continuousAt_off_edges (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (i j : Fin N) (r : ℝ) (hrL : r ≠ edgeLo σ i j) (hrR : r ≠ edgeHi σ i j) :
    ContinuousAt (hsPairZeroPrime z ρ σ i j) r := by
  rcases lt_or_gt_of_ne hrL with hl | hl
  · have he : hsPairZeroPrime z ρ σ i j =ᶠ[𝓝 r] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds hl] with x hx
      rw [hsPairZeroPrime_eq_polynomial, if_pos hx]
    exact continuousAt_const.congr_of_eventuallyEq he
  · rcases lt_or_gt_of_ne hrR with hh | hh
    · have he : hsPairZeroPrime z ρ σ i j =ᶠ[𝓝 r]
          fun x => Q0phys ρ σ i j+Qppphys ρ σ j j*(x-edgeHi σ i j) := by
        filter_upwards [eventually_gt_nhds hl, eventually_lt_nhds hh] with x hxl hxh
        rw [hsPairZeroPrime_eq_polynomial, if_neg (not_lt.mpr hxl.le), if_pos hxh.le]
      exact (by fun_prop : ContinuousAt
        (fun x => Q0phys ρ σ i j+Qppphys ρ σ j j*(x-edgeHi σ i j)) r).congr_of_eventuallyEq he
    · have he : hsPairZeroPrime z ρ σ i j =ᶠ[𝓝 r] fun _ => 0 := by
        filter_upwards [eventually_gt_nhds hl, eventually_gt_nhds hh] with x hxl hxh
        rw [hsPairZeroPrime_eq_polynomial, if_neg (not_lt.mpr hxl.le), if_neg (not_le.mpr hxh)]
      exact continuousAt_const.congr_of_eventuallyEq he

theorem hsPairZeroPrime_convolution_continuous (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (i j l : Fin N) :
    Continuous (fun r => ∫ t : ℝ, hsPairZeroPrime z ρ σ i l (t+r)*
      q z σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ))
        (amplitudeQp z ρ σ 0 (baseSeed z ρ σ)) (W z ρ 0 (baseSeed z ρ σ))
        (C z ρ σ 0 (baseSeed z ρ σ)) j l t) := by
  let Q := q z σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ))
    (amplitudeQp z ρ σ 0 (baseSeed z ρ σ)) (W z ρ 0 (baseSeed z ρ σ))
    (C z ρ σ 0 (baseSeed z ρ σ)) j l
  apply continuous_iff_continuousAt.mpr
  intro r
  apply continuousAt_of_dominated
    (bound := fun t => hsPrimeBound ρ σ i l*|Q t|)
  · apply Eventually.of_forall
    intro x
    exact (convolution_integrable z hz σ _ _ _ _ hσ i j l x).aestronglyMeasurable
  · apply Eventually.of_forall
    intro x
    apply Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (qPrime_zero_abs_le z ρ σ hσ i l (t+x)) (abs_nonneg _)
  · exact (q_integrable z hz σ _ _ _ _ hσ j l).abs.const_mul _
  · filter_upwards [volume.ae_ne (edgeLo σ i l-r), volume.ae_ne (edgeHi σ i l-r)] with t htL htR
    have hl : t+r ≠ edgeLo σ i l := by intro h; apply htL; linarith
    have hh : t+r ≠ edgeHi σ i l := by intro h; apply htR; linarith
    exact ((hsPairZeroPrime_continuousAt_off_edges z ρ σ i l (t+r) hl hh).comp
      (continuous_const.add continuous_id).continuousAt).mul continuousAt_const

theorem hsPairZeroCorrelation_continuousAt_ordered (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (horder : σ j ≤ σ i)
    (r : ℝ) (hr : 0 < r) (hrR : r ≠ edgeHi σ i j) :
    ContinuousAt (correlation z ρ σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ))
      (amplitudeQp z ρ σ 0 (baseSeed z ρ σ)) (W z ρ 0 (baseSeed z ρ σ))
      (C z ρ σ 0 (baseSeed z ρ σ)) i j) r := by
  have hrL : r ≠ edgeLo σ i j := by unfold edgeLo; linarith
  have hp := (hsPairZeroPrime_continuousAt_off_edges z ρ σ i j r hrL hrR).neg
  have hc := (continuous_finsetSum Finset.univ (fun l _ =>
    (hsPairZeroPrime_convolution_continuous z hz ρ σ hσ i j l).const_mul (ρ l))).continuousAt (x := r)
  exact (hp.add hc).div (continuousAt_const.mul continuousAt_id) (by positivity)

theorem rdfActualHS_continuousAt_positive_off_contact (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (r : ℝ)
    (hr : 0 < r) (hrR : r ≠ edgeHi σ i j) : ContinuousAt (rdfActualHS z ρ σ i j) r := by
  unfold rdfActualHS orderedRadialCorrelation
  split_ifs with ho
  · exact hsPairZeroCorrelation_continuousAt_ordered z hz ρ σ hσ i j ho r hr hrR
  · apply hsPairZeroCorrelation_continuousAt_ordered z hz ρ σ hσ j i (not_le.mp ho).le r hr
    simpa only [edgeHi, add_comm] using hrR

theorem rdfActualHS_odd_ae_continuous (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) :
    ∀ᵐ v, ContinuousAt (oddRadialMoment (rdfActualHS z ρ σ i j)) v :=
  oddRadialMoment_ae_continuous_off_contact _ (edgeHi σ i j)
    (rdfActualHS_continuousAt_positive_off_contact z hz ρ σ hσ i j)

end FMSA.ExactMSA.MultiTailMixture
