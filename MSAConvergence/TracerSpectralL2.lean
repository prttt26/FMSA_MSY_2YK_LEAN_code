import MSAConvergence.TracerActualRowEnergy
import MSAConvergence.TracerCoreTrialField
/-! Honest L2 control of the frequency-weighted radial Fourier transform
from odd-field L1/L2 and the genuine radial Parseval theorem. -/
open MeasureTheory Real FourierTransform FMSA.HardSphere
open FMSA.Convergence.TracerTailSpectralBound
open FMSA.Convergence.RadialCovarianceBounds FMSA.Convergence.TracerCoreTrialField
open FMSA.Convergence.TracerBaseCField
open FMSA.ExactMSA.MultiTailMixture MSAMixture
noncomputable section
namespace FMSA.Convergence.TracerSpectralL2

/-- Odd radial L1 makes the weighted radial Fourier transform continuous. -/
theorem continuous_weighted_radial_fourier (f : ℝ → ℝ) (hi : Integrable (oddRadialMoment f)) :
    Continuous (fun w : ℝ => w*radial_fourier f (2*Real.pi*w)) := by
  have hc : Continuous (fun w : ℝ => 𝓕 (oddRadialMoment f) w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  have he : (fun w : ℝ => w*radial_fourier f (2*Real.pi*w)) =
      (fun w : ℝ => -(𝓕 (oddRadialMoment f) w).im) := by
    funext w
    rw [odd_radial_integral_fourier f hi w]
    simp only [Complex.neg_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im]
    ring
  rw [he]
  exact (Complex.continuous_im.comp hc).neg

/-- Genuine radial Parseval gives frequency-weighted spectral L2. -/
theorem weighted_radial_fourier_memLp_two (f : ℝ → ℝ)
    (hi : Integrable (oddRadialMoment f))
    (h₂ : MemLp (oddRadialMoment f) 2 volume) :
    MemLp (fun w : ℝ => w*radial_fourier f (2*Real.pi*w)) 2 volume := by
  have hs := (radial_spectral_pairing f f hi hi h₂ h₂).1
  have hm : AEStronglyMeasurable
      (fun w : ℝ => w*radial_fourier f (2*Real.pi*w)) volume :=
    (continuous_weighted_radial_fourier f hi).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  have he : (fun w : ℝ => (w*radial_fourier f (2*Real.pi*w))^2) =
      (fun w : ℝ => w^2*radial_fourier f (2*Real.pi*w)*
        radial_fourier f (2*Real.pi*w)) := by
    funext w; ring
  rw [he]
  exact hs

/-- The fixed hard-core trial is a concrete weighted spectral L2 field. -/
theorem core_weighted_spectral_memLp_two (R : ℝ) (hR : 0 < R) :
    MemLp (fun w : ℝ => w*radial_fourier (coreValue R) (2*Real.pi*w)) 2 volume :=
  weighted_radial_fourier_memLp_two (coreValue R)
    (core_odd_L1_L2 R hR).1 (core_odd_L1_L2 R hR).2

variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual finite exterior tail has frequency-weighted spectral L2. -/
theorem tail_field_weighted_spectral_memLp_two (z : T → ℝ)
    (hz : ∀ u, 0 < z u) (sigma : ℝ) (hs : 0 < sigma)
    (K : T → ℝ) :
    MemLp (fun w : ℝ => w*radial_fourier (tailField z sigma K) (2*Real.pi*w))
      2 volume := by
  obtain ⟨hi,h₂⟩ := tail_field_odd_L1_L2 z hz sigma hs K
  exact weighted_radial_fourier_memLp_two _ hi h₂

/-- The actual ordered direct correlation field has weighted spectral L2. -/
theorem actual_c_weighted_spectral_memLp_two (z : T → ℝ)
    (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hs : ∀ i, 0 < sigma i) (K D G : TailMatrix T N)
    (hroot : IsRoot z rho sigma K D G) (i j : Fin N) :
    MemLp (fun w : ℝ => w*radial_fourier
      (orderedRadialCorrelation z rho sigma K D G i j) (2*Real.pi*w))
      2 volume := by
  obtain ⟨hi,h₂⟩ := actual_odd_c_L1_L2 z hz rho sigma hs K D G hroot i j
  exact weighted_radial_fourier_memLp_two _ hi h₂

/-- The actual canonical total-correlation field has weighted spectral L2. -/
theorem actual_h_weighted_spectral_memLp_two (z : T → ℝ)
    (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hs : ∀ i, 0 < sigma i) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (D G : TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma D G) s))
    (i j : Fin N) :
    MemLp (fun w : ℝ => w*radial_fourier
      (nonlinearH z rho sigma D G i j) (2*Real.pi*w))
      2 volume := by
  have hi := actual_odd_h_integrable z hz rho sigma (fun i => (hs i).le)
    hv D G hcanon i j
  have h₂ := actual_odd_h_memLp_two z hz rho sigma hs hv D G hcanon i j
  exact weighted_radial_fourier_memLp_two _ hi h₂

end FMSA.Convergence.TracerSpectralL2
/-- info: 'FMSA.Convergence.TracerSpectralL2.continuous_weighted_radial_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerSpectralL2.continuous_weighted_radial_fourier
/-- info: 'FMSA.Convergence.TracerSpectralL2.weighted_radial_fourier_memLp_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerSpectralL2.weighted_radial_fourier_memLp_two
/-- info: 'FMSA.Convergence.TracerSpectralL2.core_weighted_spectral_memLp_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerSpectralL2.core_weighted_spectral_memLp_two
/-- info: 'FMSA.Convergence.TracerSpectralL2.tail_field_weighted_spectral_memLp_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerSpectralL2.tail_field_weighted_spectral_memLp_two
/-- info: 'FMSA.Convergence.TracerSpectralL2.actual_c_weighted_spectral_memLp_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerSpectralL2.actual_c_weighted_spectral_memLp_two
/-- info: 'FMSA.Convergence.TracerSpectralL2.actual_h_weighted_spectral_memLp_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerSpectralL2.actual_h_weighted_spectral_memLp_two
