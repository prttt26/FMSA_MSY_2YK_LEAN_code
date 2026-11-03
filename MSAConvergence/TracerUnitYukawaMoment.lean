import MSAConvergence.TracerUnitYukawaPairing
import MSAConvergence.ActualGCanonicalIdentification

/-! The spatial unit-strength exterior Yukawa test measures the positive
h moment up to a fixed hard-core correction. -/
noncomputable section
open MeasureTheory Set Real FMSA.HardSphere FMSA.ExactMSA
open FMSA.Convergence.YukawaTestMoments FMSA.Convergence.RadialCovarianceBounds
open FMSA.Convergence.TracerTailSpectralBound FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.ActualGCanonicalIdentification
namespace FMSA.Convergence.TracerUnitYukawaMoment

/-- Exact unit-tail spatial pairing. The only correction is a fixed core
integral; the test itself vanishes in the core. -/
theorem unit_tail_spatial_pair_eq_moment_plus_core
    (s edge : ℝ) (_hs : 0 < s) (hedge : 0 < edge)
    (f : ℝ → ℝ)
    (hi : IntegrableOn (fun r : ℝ => r*f r*exp (-s*r)) (Ioi 0))
    (hcore : ∀ r : ℝ, 0 < r → r < edge → f r = -1) :
    (∫ r : ℝ, r^2*f |r| *cMSAtail 1 s edge |r|) =
      2*exp (s*edge)*
        ((∫ r in Ioi (0 : ℝ), r*f r*exp (-s*r))+
          (∫ r in (0 : ℝ)..edge, r*exp (-s*r))) := by
  have heven : (fun r : ℝ => r^2*f |r| *cMSAtail 1 s edge |r|) =
      (fun r : ℝ => r^2*f r*cMSAtail 1 s edge r) ∘ abs := by
    funext r
    simp only [Function.comp_apply,sq_abs]
  rw [heven]
  change (∫ r : ℝ, (fun t : ℝ => t^2*f t*cMSAtail 1 s edge t) |r|) = _
  rw [integral_comp_abs (f := fun t : ℝ => t^2*f t*cMSAtail 1 s edge t)]
  have houter :
      (∫ r in Ioi (0 : ℝ), r^2*f r*cMSAtail 1 s edge r) =
      ∫ r in Ioi edge, r*f r*exp (-s*(r-edge)) := by
    rw [← integral_indicator measurableSet_Ioi,
      ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    apply ae_of_all
    intro r
    by_cases hr : edge < r
    · have hr0 : 0 < r := hedge.trans hr
      simp only [indicator_of_mem (mem_Ioi.mpr hr0),
        indicator_of_mem (mem_Ioi.mpr hr),cMSAtail,if_pos hr]
      field_simp [hr0.ne']
    · by_cases hr0 : 0 < r
      · simp [indicator_of_mem (mem_Ioi.mpr hr0),cMSAtail,hr]
      · simp [indicator_of_notMem (show r ∉ Ioi (0:ℝ) from hr0),
          indicator_of_notMem (show r ∉ Ioi edge from fun h => hr0 (hedge.trans h))]
  have hshift (r : ℝ) : r*f r*exp (-s*(r-edge)) =
      exp (s*edge)*(r*f r*exp (-s*r)) := by
    have hexp : exp (-s*(r-edge))=exp (s*edge)*exp (-s*r) := by
      rw [← exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  have houter' : (∫ r in Ioi (0 : ℝ), r^2*f r*cMSAtail 1 s edge r) =
      exp (s*edge)*(∫ r in Ioi edge, r*f r*exp (-s*r)) := by
    rw [houter]
    simp_rw [hshift]
    rw [integral_const_mul]
  have hcoreint : (∫ r in (0 : ℝ)..edge, r*f r*exp (-s*r)) =
      -(∫ r in (0 : ℝ)..edge, r*exp (-s*r)) := by
    calc
      _ = ∫ r in (0 : ℝ)..edge, -(r*exp (-s*r)) := by
        apply intervalIntegral.integral_congr_ae'
        · filter_upwards [volume.ae_ne edge] with r hr hrI
          have hr0 : 0 < r := hrI.1
          have hre : r < edge := lt_of_le_of_ne hrI.2 hr
          rw [hcore r hr0 hre]
          ring
        · filter_upwards [] with r hrI
          exact False.elim (by rcases hrI with ⟨h1,h2⟩; linarith)
      _ = _ := by rw [intervalIntegral.integral_neg]
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hi hedge.le
  rw [hcoreint] at hsplit
  rw [houter']
  linear_combination -2*exp (s*edge)*hsplit


variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual unit-tail spectral h pairing equals twice the ORIGINAL
second BH amplitude plus an explicitly fixed hard-core correction. -/
theorem actual_unit_yukawa_spectral_pair_eq_G_plus_fixed
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hσ : ∀ a, 0 < sigma a)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ v : ℂ, 0 ≤ v.re → IsUnit (causalFactor z rho sigma D G v))
    (u : T) (i j : Fin N) :
    (∫ w : ℝ, w^2*
      radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w)*
      radial_fourier (cMSAtail 1 (z u) (edgeHi sigma i j)) (2*Real.pi*w)) =
    2*G u i j + 2*exp ((z u)*edgeHi sigma i j)*
      ((∫ r in (0 : ℝ)..edgeHi sigma i j, r*exp (-(z u)*r))-(z u)⁻¹^2) := by
  let edge := edgeHi sigma i j
  let H := nonlinearH z rho sigma D G i j
  let ψ := cMSAtail 1 (z u) edge
  have hedge : 0 < edge := by dsimp [edge,edgeHi]; linarith [hσ i,hσ j]
  have hi0 := actual_weighted_h_integrable z hz rho sigma (fun a => (hσ a).le)
    hv D G hcanon i j
  have hi : IntegrableOn (fun r : ℝ => r*H r*exp (-(z u)*r)) (Ioi 0) := by
    refine hi0.mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (by nlinarith [hz u,show 0 < r from hr])
  have hcore : ∀ r : ℝ, 0 < r → r < edge → H r = -1 := by
    intro r hr hre
    exact nonlinearH_hardcore z rho sigma D G i j r hr hre
  obtain ⟨hpairi,hparseval⟩ := radial_spectral_pairing H ψ
    (actual_odd_h_integrable z hz rho sigma (fun a => (hσ a).le) hv D G hcanon i j)
    (tail_odd_integrable (z u) edge 1 (hz u) hedge)
    (actual_odd_h_memLp_two z hz rho sigma hσ hv D G hcanon i j)
    (tail_odd_memLp_two (z u) edge 1 (hz u) hedge)
  have hspatial := unit_tail_spatial_pair_eq_moment_plus_core
    (z u) edge (hz u) hedge H hi hcore
  have hmoment := actual_h_moment_at_rate z hz rho sigma hσ hv
    K D G hroot hcanon u i j
  have hexp : exp ((z u)*edge)*exp (-(z u)*edge) = 1 := by
    rw [← exp_add]
    convert exp_zero using 2
    ring
  rw [hparseval,hspatial,hmoment]
  dsimp only [edge] at hexp ⊢
  linear_combination (2*G u i j)*hexp

end FMSA.Convergence.TracerUnitYukawaMoment
/-- info: 'FMSA.Convergence.TracerUnitYukawaMoment.unit_tail_spatial_pair_eq_moment_plus_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaMoment.unit_tail_spatial_pair_eq_moment_plus_core
/-- info: 'FMSA.Convergence.TracerUnitYukawaMoment.actual_unit_yukawa_spectral_pair_eq_G_plus_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaMoment.actual_unit_yukawa_spectral_pair_eq_G_plus_fixed
