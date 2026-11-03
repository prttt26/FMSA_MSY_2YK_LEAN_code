import MSAConvergence.ActualGCanonicalIdentification
import MSAConvergence.CovariancePairingBounds
import MSAConvergence.YukawaTestMoments

/-! Uniform bounds for the ORIGINAL second BH amplitudes of general
positive-density canonical reciprocal mixtures. No strength bound is needed. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.MixtureSecondAmplitudeBounds
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.ExactMSA.Breakpoint MSAMixture
open FMSA.Convergence.CanonicalInverseCovariance FMSA.Convergence.ActualStructureCovariance
open FMSA.Convergence.RadialCovarianceBounds FMSA.Convergence.CovariancePairingBounds
open FMSA.Convergence.YukawaConvolutionTest FMSA.Convergence.YukawaTestMoments
open FMSA.Convergence.ActualGCanonicalIdentification
variable {N : ℕ} {T : Type*} [Fintype T]

/-- A fixed original second-amplitude entry is bounded uniformly over ALL
canonical reciprocal roots. The constant contains no K, D or G. -/
theorem second_entry_uniform_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (R : ℝ) (hR : 0 < R) (hRσ : ∀ i, R < σ i)
    (u : T) (i j : Fin N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) → |G u i j| ≤ C := by
  let s := z u
  let M := exteriorCoefficient s R
  let d := sqrt (ρ i)*sqrt (ρ j)
  let Q := ∫ r : ℝ, coreCorrection s R r
  let C₀ := ∫ t : ℝ, exponential s t
  let B := |C₀*((N : ℝ)+1)*(∫ w : ℝ, testWeight R w)|
  have hM : 0 < M := exterior_coefficient_pos s R (hz u) hR
  have hd : 0 < d := mul_pos (sqrt_pos.mpr (hρ i)) (sqrt_pos.mpr (hρ j))
  have hC₀ : 0 ≤ C₀ := integral_nonneg (fun t => (exp_pos _).le)
  have hB : 0 ≤ B := abs_nonneg _
  let L := (B/d+|Q|)/(2*M)
  have hL : 0 ≤ L := div_nonneg (add_nonneg (div_nonneg hB hd.le) (abs_nonneg _))
    (mul_pos (by norm_num) hM).le
  let C := exp (s*edgeHi σ i j)*(L+s⁻¹^2)
  have hC : 0 ≤ C := mul_nonneg (exp_pos _).le (add_nonneg hL (sq_nonneg _))
  refine ⟨C,hC,?_⟩
  intro K D G hK hroot hcanon
  let H := nonlinearH z ρ σ D G i j
  let I := ∫ r in Ioi (0 : ℝ), r*H r*exp (-s*r)
  have hcontact : R < edgeHi σ i j := by unfold edgeHi; linarith [hRσ i,hRσ j]
  have hcore : ∀ r : ℝ, 0 < r → r < R → H r= -1 := fun r hr ht =>
    nonlinearH_hardcore z ρ σ D G i j r hr (ht.trans hcontact)
  have hmoment := core_pairing_eq_yukawa_moment s R (hz u) hR H
    (actual_odd_h_integrable z hz ρ σ (fun i => (hσ i).le) hv D G hcanon i j) hcore
  have hpair := actual_dominated_radial_pairing_bound z hz ρ σ (fun i => (hρ i).le) hσ hv R hR hRσ
    (radialTest s R) (radial_test_L1_L2 s R (hz u) hR).1
    (radial_test_L1_L2 s R (hz u) hR).2 C₀ hC₀
    (radial_test_fourier_bound s R (hz u) hR) K D G hK hroot hcanon i j
  change d*|(∫ r : ℝ, r^2*H |r| *radialTest s R |r|)| ≤ _ at hpair
  rw [hmoment] at hpair
  have hp : d*|2*M*I-Q| ≤ B := hpair.trans (le_abs_self _)
  have hb : |2*M*I-Q| ≤ B/d := (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hp)
  have hnorm : |2*M*I| ≤ B/d+|Q| := by
    calc
      _ = |(2*M*I-Q)+Q| := by ring_nf
      _ ≤ |2*M*I-Q|+|Q| := abs_add_le _ _
      _ ≤ _ := add_le_add hb le_rfl
  rw [abs_mul,abs_of_pos (mul_pos (by norm_num) hM)] at hnorm
  have hI : |I| ≤ L := (le_div_iff₀ (mul_pos (by norm_num) hM)).mpr
    (by simpa only [mul_comm] using hnorm)
  have hid : I= -s⁻¹^2+exp (-s*edgeHi σ i j)*G u i j :=
    actual_h_moment_at_rate z hz ρ σ hσ hv K D G hroot hcanon u i j
  have hsmall : exp (-s*edgeHi σ i j)*|G u i j| ≤ L+s⁻¹^2 := by
    calc
      _ = |exp (-s*edgeHi σ i j)*G u i j| := by rw [abs_mul,abs_of_pos (exp_pos _)]
      _ = |I+s⁻¹^2| := by congr 1; rw [hid]; ring
      _ ≤ |I|+|s⁻¹^2| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg (sq_nonneg s⁻¹)]; exact add_le_add hI le_rfl
  have hexp : exp (s*edgeHi σ i j)*exp (-s*edgeHi σ i j)=1 := by
    rw [← exp_add]
    convert exp_zero using 2; ring
  calc
    _ = exp (s*edgeHi σ i j)*(exp (-s*edgeHi σ i j)*|G u i j|) := by rw [← mul_assoc,hexp,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (exp_pos _).le

/-- The ORIGINAL full second-amplitude Pi norm is bounded over ALL canonical
reciprocal roots at fixed positive densities/diameters. No K bound is supplied. -/
theorem second_amplitudes_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) → ‖G‖ ≤ C := by
  classical
  have hsmall : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i : Fin N, r < σ i :=
    Filter.eventually_all.mpr (fun i => Iio_mem_nhds (hσ i))
  have hpositive : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨R,hR,hRσ⟩ := (hpositive.and (hsmall.filter_mono nhdsWithin_le_nhds)).exists
  choose C hC hb using second_entry_uniform_bound z hz ρ σ hρ hσ hv R hR hRσ
  let B := ∑ u, ∑ i, ∑ j, C u i j
  have hsum : 0 ≤ B := Finset.sum_nonneg (fun u _ =>
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC u i j)))
  refine ⟨B,hsum,?_⟩
  intro K D G hK hroot hcanon
  apply (pi_norm_le_iff_of_nonneg hsum).mpr
  intro u
  apply (pi_norm_le_iff_of_nonneg hsum).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hsum).mpr
  intro j
  exact (hb u i j K D G hK hroot hcanon).trans
    ((Finset.single_le_sum (fun j _ => hC u i j) (Finset.mem_univ j)).trans
      ((Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hC u i j)) (Finset.mem_univ i)).trans
        (Finset.single_le_sum (fun u _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC u i j)))
          (Finset.mem_univ u))))

end FMSA.Convergence.MixtureSecondAmplitudeBounds
/-- info: 'FMSA.Convergence.MixtureSecondAmplitudeBounds.second_entry_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureSecondAmplitudeBounds.second_entry_uniform_bound
/-- info: 'FMSA.Convergence.MixtureSecondAmplitudeBounds.second_amplitudes_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureSecondAmplitudeBounds.second_amplitudes_uniformly_bounded
