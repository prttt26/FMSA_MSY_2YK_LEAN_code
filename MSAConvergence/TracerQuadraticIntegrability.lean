import MSAConvergence.TracerActualPointwiseForcing
import MSAConvergence.TracerTailCovarianceBudget
import MSAConvergence.TracerCoreForcingBound

/-! Actual physical quadratic forcing functions are integrable. -/
noncomputable section
open Matrix MeasureTheory Real Set FMSA.HardSphere FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.TracerCoreForcingBound FMSA.Convergence.TracerTailForcingBound
open FMSA.Convergence.TracerTailCovarianceBudget FMSA.Convergence.TracerStructureContinuity
open FMSA.Convergence.TracerCovarianceQuadraticTrace FMSA.Convergence.RadialCovarianceBounds
open FMSA.Convergence.TracerForcingIntegrability FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters
open scoped BigOperators ComplexOrder
namespace FMSA.Convergence.TracerQuadraticIntegrability
variable {N : ℕ} {T : Type*} [Fintype T]

def coreQuadratic (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K D G : TailMatrix T N) (i : Fin N) (w : ℝ) : ℂ :=
  ∑ a : Fin N, ∑ b : Fin N,
    star (coreTrialVector rho sigma i a w) *
      (MatrixOZPairing.radialDenominator z rho sigma K D G (2*Real.pi*w)) a b *
        coreTrialVector rho sigma i b w

def tailQuadratic (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K D G : TailMatrix T N) (i : Fin N) (w : ℝ) : ℂ :=
  ∑ a : Fin N, ∑ b : Fin N,
    star (tailTrialVector z rho sigma K i a w) *
      (MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)) a b *
        tailTrialVector z rho sigma K i b w

/-- Expand the physical hard-core matrix quadratic as a dot product. -/
theorem core_quadratic_dotProduct (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K D G : TailMatrix T N) (i : Fin N) (w : ℝ) :
    let v : Fin N → ℂ := fun a => coreTrialVector rho sigma i a w
    (star v ⬝ᵥ
      (MatrixOZPairing.radialDenominator z rho sigma K D G (2*Real.pi*w) *ᵥ v)) =
      coreQuadratic z rho sigma K D G i w := by
  change (∑ a : Fin N, star (coreTrialVector rho sigma i a w) *
    (∑ b : Fin N,
      (MatrixOZPairing.radialDenominator z rho sigma K D G (2*Real.pi*w)) a b *
        coreTrialVector rho sigma i b w)) = _
  simp only [coreQuadratic,Finset.mul_sum,mul_assoc]

/-- Expand the physical tail covariance quadratic as a dot product. -/
theorem tail_quadratic_dotProduct (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K D G : TailMatrix T N) (i : Fin N) (w : ℝ) :
    let t : Fin N → ℂ := fun a => tailTrialVector z rho sigma K i a w
    (star t ⬝ᵥ
      (MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w) *ᵥ t)) =
      tailQuadratic z rho sigma K D G i w := by
  change (∑ a : Fin N, star (tailTrialVector z rho sigma K i a w) *
    (∑ b : Fin N,
      (MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)) a b *
        tailTrialVector z rho sigma K i b w)) = _
  simp only [tailQuadratic,Finset.mul_sum,mul_assoc]

/-- The genuine hard-core inverse-Gram forcing is L1 on the real frequency axis. -/
theorem actual_core_quadratic_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hs : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (B : ℝ) (K D G : TailMatrix T N) (hB : ‖K‖ ≤ B)
    (hK : ∀ u a b, K u a b = K u b a)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s))
    (i : Fin N) : Integrable (coreQuadratic z rho sigma K D G i) := by
  exact actual_core_inverse_trial_integrable z hz rho sigma hρ hs hv B
    K D G hB hK hroot hcanon i

/-- The genuine exterior-tail covariance forcing is L1, including zero
frequency, by the compact physical covariance trace budget. -/
theorem actual_tail_quadratic_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hs : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (R : ℝ) (hR : 0 < R) (hRσ : ∀ a, R < sigma a)
    (B : ℝ) (K D G : TailMatrix T N) (hB : ‖K‖ ≤ B)
    (hK : ∀ u a b, K u a b = K u b a)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s))
    (i : Fin N) : Integrable (tailQuadratic z rho sigma K D G i) := by
  obtain ⟨C,hC,hvec⟩ := tail_trial_square_sum_uniformly_dominated
    z hz rho sigma hρ hs R hR B i
  let A : ℝ := (N:ℝ)*C
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) hC
  let S : ℝ → Matrix (Fin N) (Fin N) ℂ := fun w =>
    MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)
  let t : Fin N → ℝ → ℂ := fun a w => tailTrialVector z rho sigma K i a w
  have hSc : Continuous S :=
    (actual_structure_matrix_continuous z hz rho sigma hρ hs hv K D G hroot hK hcanon).comp
      (show Continuous (fun w : ℝ => 2*Real.pi*w) by fun_prop)
  have htc (a : Fin N) : Continuous (t a) :=
    tail_trial_vector_continuous z hz rho sigma hs K i a
  have hqc : Continuous (tailQuadratic z rho sigma K D G i) := by
    change Continuous (fun w : ℝ => ∑ a : Fin N, ∑ b : Fin N,
      star (t a w)*S w a b*t b w)
    apply continuous_finsetSum
    intro a _
    apply continuous_finsetSum
    intro b _
    have he : Continuous (fun w : ℝ => S w a b) :=
      (continuous_apply b).comp ((continuous_apply a).comp hSc)
    exact ((htc a).star.mul he).mul (htc b)
  have htrace := actual_structure_weighted_trace_bound z hz rho sigma hρ hs hv
    R hR hRσ K D G hK hroot hcanon
  have hpoint (w : ℝ) : ‖tailQuadratic z rho sigma K D G i w‖ ≤
      A*(testWeight R w*(S w).trace.re) := by
    have hF : IsUnit (physicalFactor z rho sigma D G (2*Real.pi*w)) :=
      FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit
        z rho sigma hρ (D,G) (2*Real.pi*w) (hcanon _ (by simp))
    have hpos : (S w).PosDef :=
      MatrixOZPairing.actual_structure_matrix_posDef z hz rho sigma K D G
        hρ hs hv hroot hK (2*Real.pi*w) hF
    exact posdef_quadratic_norm_le_weighted_trace (S w) hpos
      (fun a => t a w) C (testWeight R w) (hvec K hB w)
  apply (htrace.1.const_mul A).mono' hqc.aestronglyMeasurable
  exact ae_of_all _ hpoint

end FMSA.Convergence.TracerQuadraticIntegrability
/-- info: 'FMSA.Convergence.TracerQuadraticIntegrability.core_quadratic_dotProduct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerQuadraticIntegrability.core_quadratic_dotProduct
/-- info: 'FMSA.Convergence.TracerQuadraticIntegrability.tail_quadratic_dotProduct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerQuadraticIntegrability.tail_quadratic_dotProduct
/-- info: 'FMSA.Convergence.TracerQuadraticIntegrability.actual_core_quadratic_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerQuadraticIntegrability.actual_core_quadratic_integrable
/-- info: 'FMSA.Convergence.TracerQuadraticIntegrability.actual_tail_quadratic_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerQuadraticIntegrability.actual_tail_quadratic_integrable
