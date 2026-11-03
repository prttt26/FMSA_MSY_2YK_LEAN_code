import MSAConvergence.ActualGCanonicalIdentification
import MSAConvergence.CovariancePairingBounds
import MSAConvergence.YukawaTestMoments

/-! Uniform bounds for the ORIGINAL second BH amplitudes of general
canonical reciprocal mixtures, retaining zero-density weights. No strength bound is needed. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.WeightedMixtureAmplitudeBounds
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.ExactMSA.Breakpoint MSAMixture
open FMSA.Convergence.CanonicalInverseCovariance FMSA.Convergence.ActualStructureCovariance
open FMSA.Convergence.RadialCovarianceBounds FMSA.Convergence.CovariancePairingBounds
open FMSA.Convergence.YukawaConvolutionTest FMSA.Convergence.YukawaTestMoments
open FMSA.Convergence.ActualGCanonicalIdentification
variable {N : ℕ} {T : Type*} [Fintype T]

/-- A fixed density-WEIGHTED original second-amplitude entry is uniformly
bounded over all canonical reciprocal roots. Zero densities are retained;
no division by a density and no K/D/G bound is supplied. -/
theorem second_entry_weighted_uniform_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (R : ℝ) (hR : 0 < R) (hRσ : ∀ i, R < σ i)
    (u : T) (i j : Fin N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) → sqrt (ρ i)*sqrt (ρ j)*|G u i j| ≤ C := by
  let s := z u
  let M := exteriorCoefficient s R
  let d := sqrt (ρ i)*sqrt (ρ j)
  let Q := ∫ r : ℝ, coreCorrection s R r
  let C₀ := ∫ t : ℝ, exponential s t
  let B := |C₀*((N : ℝ)+1)*(∫ w : ℝ, testWeight R w)|
  have hM : 0 < M := exterior_coefficient_pos s R (hz u) hR
  have hd : 0 ≤ d := mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  have hC₀ : 0 ≤ C₀ := integral_nonneg (fun t => (exp_pos _).le)
  have hB : 0 ≤ B := abs_nonneg _
  let L := (B+d*|Q|)/(2*M)
  have hL : 0 ≤ L := div_nonneg (add_nonneg hB (mul_nonneg hd (abs_nonneg _)))
    (mul_pos (by norm_num) hM).le
  let C := exp (s*edgeHi σ i j)*(L+d*s⁻¹^2)
  have hC : 0 ≤ C := mul_nonneg (exp_pos _).le (add_nonneg hL (mul_nonneg hd (sq_nonneg _)))
  refine ⟨C,hC,?_⟩
  intro K D G hK hroot hcanon
  let H := nonlinearH z ρ σ D G i j
  let I := ∫ r in Ioi (0 : ℝ), r*H r*exp (-s*r)
  have hcontact : R < edgeHi σ i j := by unfold edgeHi; linarith [hRσ i,hRσ j]
  have hcore : ∀ r : ℝ, 0 < r → r < R → H r= -1 := fun r hr ht =>
    nonlinearH_hardcore z ρ σ D G i j r hr (ht.trans hcontact)
  have hmoment := core_pairing_eq_yukawa_moment s R (hz u) hR H
    (actual_odd_h_integrable z hz ρ σ (fun i => (hσ i).le) hv D G hcanon i j) hcore
  have hpair := actual_dominated_radial_pairing_bound z hz ρ σ hρ hσ hv R hR hRσ
    (radialTest s R) (radial_test_L1_L2 s R (hz u) hR).1
    (radial_test_L1_L2 s R (hz u) hR).2 C₀ hC₀
    (radial_test_fourier_bound s R (hz u) hR) K D G hK hroot hcanon i j
  change d*|(∫ r : ℝ, r^2*H |r| *radialTest s R |r|)| ≤ _ at hpair
  rw [hmoment] at hpair
  have hp : d*|2*M*I-Q| ≤ B := hpair.trans (le_abs_self _)
  have htriangle : |2*M*I| ≤ |2*M*I-Q|+|Q| := by
    calc
      _ = |(2*M*I-Q)+Q| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hnorm : (2*M)*(d*|I|) ≤ B+d*|Q| := by
    have h := mul_le_mul_of_nonneg_left htriangle hd
    rw [abs_mul,abs_of_pos (mul_pos (by norm_num) hM)] at h
    nlinarith [hp]
  have hI : d*|I| ≤ L := (le_div_iff₀ (mul_pos (by norm_num) hM)).mpr
    (by simpa only [mul_comm] using hnorm)
  have hid : I= -s⁻¹^2+exp (-s*edgeHi σ i j)*G u i j :=
    actual_h_moment_at_rate z hz ρ σ hσ hv K D G hroot hcanon u i j
  have hsmall : exp (-s*edgeHi σ i j)*(d*|G u i j|) ≤ L+d*s⁻¹^2 := by
    have htriangle : |I+s⁻¹^2| ≤ |I|+s⁻¹^2 := by
      have h := abs_add_le I (s⁻¹^2)
      rw [abs_of_nonneg (sq_nonneg (s⁻¹))] at h
      exact h
    have he : exp (-s*edgeHi σ i j)*|G u i j|=|I+s⁻¹^2| := by
      calc
        _ = |exp (-s*edgeHi σ i j)*G u i j| := by rw [abs_mul,abs_of_pos (exp_pos _)]
        _ = |I+s⁻¹^2| := by congr 1; rw [hid]; ring
    have h := mul_le_mul_of_nonneg_left htriangle hd
    rw [← he] at h
    nlinarith [hI]
  have hexp : exp (s*edgeHi σ i j)*exp (-s*edgeHi σ i j)=1 := by
    rw [← exp_add]
    convert exp_zero using 2; ring
  calc
    _ = exp (s*edgeHi σ i j)*(exp (-s*edgeHi σ i j)*(d*|G u i j|)) := by rw [← mul_assoc,hexp,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (exp_pos _).le


end FMSA.Convergence.WeightedMixtureAmplitudeBounds
/-- info: 'FMSA.Convergence.WeightedMixtureAmplitudeBounds.second_entry_weighted_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.WeightedMixtureAmplitudeBounds.second_entry_weighted_uniform_bound
