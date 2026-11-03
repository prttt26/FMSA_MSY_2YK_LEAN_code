import MSAConvergence.TracerStructureContinuity

/-! Uniform exterior-tail covariance forcing integral from the physical
compact-spectrum trace budget and actual finite Yukawa tail field. -/
noncomputable section
open MeasureTheory Real Set FMSA.HardSphere FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.TracerTailForcingBound FMSA.Convergence.TracerSpectralL2
open FMSA.Convergence.TracerCovarianceQuadraticTrace FMSA.Convergence.TracerStructureContinuity
open FMSA.Convergence.RadialCovarianceBounds FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters
open scoped BigOperators ComplexOrder
namespace FMSA.Convergence.TracerTailCovarianceBudget
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual finite-tail spectral vector varies continuously with real
frequency, including its zero mode after multiplication by frequency. -/
theorem tail_trial_vector_continuous (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ a, 0 < sigma a)
    (K : TailMatrix T N) (i a : Fin N) :
    Continuous (fun w : ℝ => tailTrialVector z rho sigma K i a w) := by
  have hR : 0 < edgeHi sigma i a := by dsimp [edgeHi]; linarith [hs i,hs a]
  have hi := (FMSA.Convergence.TracerTailSpectralBound.tail_field_odd_L1_L2
    z hz (edgeHi sigma i a) hR (fun u => K u i a)).1
  have hc := continuous_weighted_radial_fourier
    (FMSA.Convergence.TracerTailSpectralBound.tailField z (edgeHi sigma i a)
      (fun u => K u i a)) hi
  change Continuous (fun w : ℝ => (Real.sqrt (rho a) : ℂ) *
    ((w*radial_fourier
      (FMSA.Convergence.TracerTailSpectralBound.tailField z (edgeHi sigma i a)
        (fun u => K u i a)) (2*Real.pi*w) : ℝ) : ℂ))
  exact continuous_const.mul (Complex.continuous_ofReal.comp hc)

/-- The actual covariance-weighted finite Yukawa tail trial has a uniform
integral bound over canonical roots with bounded couplings. -/
theorem actual_tail_covariance_forcing_integral_uniform (z : T → ℝ)
    (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hρ : ∀ a, 0 ≤ rho a) (hs : ∀ a, 0 < sigma a)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (R : ℝ) (hR : 0 < R) (hRσ : ∀ a, R < sigma a)
    (B : ℝ) (i : Fin N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u a b, K u a b = K u b a) →
      IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
      ‖∫ w : ℝ, ∑ a : Fin N, ∑ b : Fin N,
        star (tailTrialVector z rho sigma K i a w) *
        (MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)) a b *
        tailTrialVector z rho sigma K i b w‖ ≤ M := by
  obtain ⟨C,hC,hvec⟩ := tail_trial_square_sum_uniformly_dominated
    z hz rho sigma hρ hs R hR B i
  let A : ℝ := (N:ℝ)*C
  let M : ℝ := max 0 (A*((N:ℝ)*(∫ w : ℝ, testWeight R w)))
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) hC
  have hM : 0 ≤ M := le_max_left _ _
  refine ⟨M,hM,?_⟩
  intro K D G hB hK hroot hcanon
  let S : ℝ → Matrix (Fin N) (Fin N) ℂ := fun w =>
    MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)
  let t : Fin N → ℝ → ℂ := fun a w => tailTrialVector z rho sigma K i a w
  let q : ℝ → ℂ := fun w => ∑ a : Fin N, ∑ b : Fin N,
    star (t a w)*S w a b*t b w
  have hSc : Continuous S :=
    (actual_structure_matrix_continuous z hz rho sigma hρ hs hv K D G hroot hK hcanon).comp
      (show Continuous (fun w : ℝ => 2*Real.pi*w) by fun_prop)
  have htc (a : Fin N) : Continuous (t a) :=
    tail_trial_vector_continuous z hz rho sigma hs K i a
  have hqc : Continuous q := by
    dsimp only [q]
    apply continuous_finsetSum
    intro a _
    apply continuous_finsetSum
    intro b _
    have he : Continuous (fun w : ℝ => S w a b) :=
      (continuous_apply b).comp ((continuous_apply a).comp hSc)
    exact ((htc a).star.mul he).mul (htc b)
  have htrace := actual_structure_weighted_trace_bound z hz rho sigma hρ hs hv
    R hR hRσ K D G hK hroot hcanon
  have hpoint (w : ℝ) : ‖q w‖ ≤
      A*(testWeight R w*(S w).trace.re) := by
    have hF : IsUnit (physicalFactor z rho sigma D G (2*Real.pi*w)) :=
      FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit
        z rho sigma hρ (D,G) (2*Real.pi*w) (hcanon _ (by simp))
    have hpos : (S w).PosDef :=
      MatrixOZPairing.actual_structure_matrix_posDef z hz rho sigma K D G
        hρ hs hv hroot hK (2*Real.pi*w) hF
    exact posdef_quadratic_norm_le_weighted_trace (S w) hpos
      (fun a => t a w) C (testWeight R w) (hvec K hB w)
  have hqi : Integrable q := by
    apply (htrace.1.const_mul A).mono' hqc.aestronglyMeasurable
    exact ae_of_all _ hpoint
  calc
    ‖∫ w : ℝ, q w‖ ≤ ∫ w : ℝ, ‖q w‖ := norm_integral_le_integral_norm _
    _ ≤ A*(∫ w : ℝ, testWeight R w*(S w).trace.re) := by
      rw [← integral_const_mul]
      exact integral_mono hqi.norm (htrace.1.const_mul A) hpoint
    _ ≤ A*((N:ℝ)*(∫ w : ℝ, testWeight R w)) :=
      mul_le_mul_of_nonneg_left htrace.2 hA
    _ ≤ M := le_max_right _ _

end FMSA.Convergence.TracerTailCovarianceBudget
/-- info: 'FMSA.Convergence.TracerTailCovarianceBudget.tail_trial_vector_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailCovarianceBudget.tail_trial_vector_continuous
/-- info: 'FMSA.Convergence.TracerTailCovarianceBudget.actual_tail_covariance_forcing_integral_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailCovarianceBudget.actual_tail_covariance_forcing_integral_uniform
