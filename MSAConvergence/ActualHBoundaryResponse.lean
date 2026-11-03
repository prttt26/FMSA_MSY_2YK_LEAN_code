import MSAConvergence.ActualHRadialL2
import MSAConvergence.ActualHLaplaceJets
import MSAConvergence.ActualSourceBoundary

/-! Genuine actual h tangent Laplace response directly on the Fourier
boundary. The amplitude-independent background has already been cancelled. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators

namespace FMSA.Convergence.ActualHBoundaryResponse
open FMSA.Paper FMSA.Paper.JacobianExterior FMSA.ExactMSA.MultiTailMixture
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.ActualRDFTangent FMSA.Convergence.ActualHLaplaceJets
open FMSA.Convergence.ActualExcessTangentDecay FMSA.Convergence.ActualExcessDecay
open FMSA.Convergence.ActualExcessSourceTangent FMSA.Convergence.ActualSourceBoundary

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Actual contact-phase transfer on the full closed right half-plane,
including zero, from the genuine tangent integrals. No far-right formula
is evaluated outside its proved domain and no limit is required here. -/
theorem actual_h_tangent_boundary_phase
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hs : 0 ≤ s.re) :
    (∀ i j, IntegrableOn (fun r : ℝ => ((r*hVariation z rho sigma p v i j r : ℝ) : ℂ)*Complex.exp (-s*r)) (Ioi 0)) ∧
    rdfMatrixLaplace (fun r => Matrix.of (fun i j => r*hVariation z rho sigma p v i j r)) s =
      rdfPhase sigma s*rdfMatrixLaplace (fun r => Matrix.of (fun i j => excessVariation z rho sigma p v i j r)) s*rdfPhase sigma s := by
  have hdx := (actual_excess_tangent_boundary_laplace z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon s hs).1
  have he (i j : Fin N) : causalVariation z rho sigma p v i j = excessVariation z rho sigma p v i j :=
    (funext (excessVariation_eq_causalVariation z rho sigma p v i j)).symm
  have hshift (i j : Fin N) := hVariation_laplace_shift z rho sigma p v i j
    (by unfold edgeHi; linarith [hsigma i, hsigma j]) s (by simpa only [he] using hdx i j)
  refine ⟨(fun i j => (hshift i j).1), ?_⟩
  rw [← additive_contact_phase_sandwich]
  ext i j
  simpa only [rdfMatrixLaplace, Matrix.of_apply, he] using (hshift i j).2

/-- Honest actual h tangent boundary response to its already cancelled
linearized forcing, with the finite inverse and exact species order.
This includes zero frequency without J/L divisions by the frequency. -/
theorem actual_h_tangent_boundary_forcing_response
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hs : 0 ≤ s.re) :
    rdfMatrixLaplace (fun r => Matrix.of (fun i j => r*hVariation z rho sigma p v i j r)) s =
      rdfPhase sigma s*(rdfMatrixLaplace (excessTangentForcing z rho sigma p v) s*
        (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹)*rdfPhase sigma s := by
  rw [(actual_h_tangent_boundary_phase z hz rho sigma hsigma hv p v hcanon s hs).2,
    (actual_excess_tangent_boundary_laplace z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon s hs).2]

/-- Actual forcing transform on the closed right half-plane, including
zero. Both convolution inputs and the cancelled source derivative have
proved real weighted L1. -/
theorem actual_forcing_laplace_closed_right
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hs : 0 ≤ s.re) :
    (∀ i j, IntegrableOn (fun t : ℝ => (excessTangentForcing z rho sigma p v t i j : ℂ)*Complex.exp (-s*t)) (Ioi 0)) ∧
    rdfMatrixLaplace (excessTangentForcing z rho sigma p v) s =
      rdfMatrixLaplace (fun t => Matrix.of (fun i j => excessSourceVariation z rho sigma p v i j t)) s+
      rdfMatrixLaplace (nonlinearRDFExcess z rho sigma p.1 p.2) s*
        rdfMatrixLaplace (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) s := by
  obtain ⟨epsilon, _D, he, _hD, hX⟩ := actual_excess_canonical_integrable z hz rho sigma hsigma hv p hcanon
  have hXi (i j : Fin N) := (hX i j).2.2.1 s.re (by linarith)
  have hvi (i j m : Fin N) := complexCausalLaplace_weighted_convolution
    (kernelVariation z rho sigma p v m j) (fun t => nonlinearRDFExcess z rho sigma p.1 p.2 t i m)
    (kernel_variation_continuous z rho sigma p v m j)
    ((nonlinearRDFExcess_continuous z rho sigma p.1 p.2).matrix_elem i m) s
    (actual_kernel_variation_real_damped_integrable z hz rho sigma p v s.re hs m j) (hXi i m)
  have hSi (i j : Fin N) := FMSA.complex_laplace_integrable _
    (excess_source_variation_continuous z rho sigma p v i j).continuousOn s
    (actual_source_variation_real_damped_integrable z hz rho sigma hsigma hv p v s.re hs i j)
  have hw (i j : Fin N) : (fun t : ℝ => (excessTangentForcing z rho sigma p v t i j : ℂ)*Complex.exp (-s*t)) =
      fun t : ℝ => (excessSourceVariation z rho sigma p v i j t : ℂ)*Complex.exp (-s*t)+
        ∑ m, (causalIntervalConv (kernelVariation z rho sigma p v m j)
          (fun u => nonlinearRDFExcess z rho sigma p.1 p.2 u i m) t : ℂ)*Complex.exp (-s*t) := by
    funext t
    simp only [excessTangentForcing, Matrix.of_apply, Complex.ofReal_add, Complex.ofReal_sum, add_mul, Finset.sum_mul]
  constructor
  · intro i j
    rw [hw]
    exact (hSi i j).add (integrable_finsetSum _ (fun m _ => (hvi i j m).1))
  · have hentry (i j : Fin N) : FMSA.causalComplexLaplace (fun t => excessTangentForcing z rho sigma p v t i j) s =
        FMSA.causalComplexLaplace (excessSourceVariation z rho sigma p v i j) s+
        ∑ m, FMSA.causalComplexLaplace (fun t => nonlinearRDFExcess z rho sigma p.1 p.2 t i m) s*
          FMSA.causalComplexLaplace (kernelVariation z rho sigma p v m j) s := by
      unfold FMSA.causalComplexLaplace
      rw [hw, integral_add (hSi i j) (integrable_finsetSum _ (fun m _ => (hvi i j m).1)),
        integral_finsetSum _ (fun m _ => (hvi i j m).1)]
      congr 1
      exact Finset.sum_congr rfl (fun m _ => (hvi i j m).2)
    ext i j
    simpa only [rdfMatrixLaplace, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply] using hentry i j

/-- The actual forcing has its finite J/actual-q response away from zero
on the FULL closed right half-plane. The affine background terms cancel
algebraically AFTER the actual cancelled source integrals are established. -/
theorem actual_forcing_finite_boundary_response
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) :
    rdfMatrixLaplace (excessTangentForcing z rho sigma p v) s =
      (2*(π : ℂ))⁻¹ • jVariation z rho sigma p v s+
        ((2*(π : ℂ))⁻¹ • nonlinearComplexJ z rho sigma p.1 p.2 s)*
          (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹*
            rdfMatrixLaplace (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) s := by
  let Q := rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s
  let U := (1-Q)⁻¹
  let B := nonlinearComplexBackground sigma s
  let J := (2*(π : ℂ))⁻¹ • nonlinearComplexJ z rho sigma p.1 p.2 s
  have hAU : (1-Q)*U = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hcanon s hre))
  obtain ⟨epsilon, he, hx⟩ := actual_excess_canonical_laplace z hz rho sigma hsigma hv p hcanon
  have hX : rdfMatrixLaplace (nonlinearRDFExcess z rho sigma p.1 p.2) s = J*U-B := by
    rw [(hx s (by linarith)).2, actual_source_laplace_closed_right z hz rho sigma hsigma hv p s hs hre]
    change (J-B+B*Q)*U = J*U-B
    calc
      _ = J*U-B*((1-Q)*U) := by noncomm_ring
      _ = _ := by rw [hAU, Matrix.mul_one]
  rw [(actual_forcing_laplace_closed_right z hz rho sigma hsigma hv p v hcanon s hre).2,
    actual_source_variation_laplace_closed_right z hz rho sigma hsigma hv p v s hs hre, hX]
  change ((2*(π : ℂ))⁻¹ • jVariation z rho sigma p v s+B*
      rdfMatrixLaplace (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) s)+
    (J*U-B)*rdfMatrixLaplace (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) s = _
  rw [Matrix.sub_mul]
  abel

/-- Genuine finite actual h Frechet tangent response directly on every
nonzero point of the closed right half-plane, with exact contact phases.
The separate forcing-response theorem already covers zero without divisions. -/
theorem actual_h_tangent_finite_boundary_response
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) :
    rdfMatrixLaplace (fun r => Matrix.of (fun i j => r*hVariation z rho sigma p v i j r)) s =
      rdfPhase sigma s*((((2*(π : ℂ))⁻¹ • jVariation z rho sigma p v s)+
        ((2*(π : ℂ))⁻¹ • nonlinearComplexJ z rho sigma p.1 p.2 s)*
          (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹*
            rdfMatrixLaplace (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) s)*
              (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹)*rdfPhase sigma s := by
  rw [actual_h_tangent_boundary_forcing_response z hz rho sigma hsigma hv p v hcanon s hre,
    actual_forcing_finite_boundary_response z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon s hs hre]

/-- Pure finite J/L form of the genuine actual h tangent transform at
all nonzero closed-right-half-plane frequencies. Every kernel/tangent
symbol is identified with its honest actual integral before substitution. -/
theorem actual_h_tangent_JL_boundary_response
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) :
    rdfMatrixLaplace (fun r => Matrix.of (fun i j => r*hVariation z rho sigma p v i j r)) s =
      rdfPhase sigma s*((((2*(π : ℂ))⁻¹ • jVariation z rho sigma p v s)+
        ((2*(π : ℂ))⁻¹ • nonlinearComplexJ z rho sigma p.1 p.2 s)*
          (1-finiteKernelSymbol z rho sigma p s)⁻¹*finiteKernelVariationSymbol z rho sigma p v s)*
            (1-finiteKernelSymbol z rho sigma p s)⁻¹)*rdfPhase sigma s := by
  have h := actual_h_tangent_finite_boundary_response z hz rho sigma hsigma hv p v hcanon s hs hre
  rw [← finite_kernel_symbol_eq_laplace z hz rho sigma (fun i => (hsigma i).le) p s hs hre,
    ← finite_kernel_variation_symbol_eq_laplace z hz rho sigma (fun i => (hsigma i).le) p v s hs hre] at h
  exact h

end FMSA.Convergence.ActualHBoundaryResponse

/-- info: 'FMSA.Convergence.ActualHBoundaryResponse.actual_h_tangent_boundary_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHBoundaryResponse.actual_h_tangent_boundary_phase

/-- info: 'FMSA.Convergence.ActualHBoundaryResponse.actual_h_tangent_boundary_forcing_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHBoundaryResponse.actual_h_tangent_boundary_forcing_response

/-- info: 'FMSA.Convergence.ActualHBoundaryResponse.actual_forcing_laplace_closed_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHBoundaryResponse.actual_forcing_laplace_closed_right

/-- info: 'FMSA.Convergence.ActualHBoundaryResponse.actual_forcing_finite_boundary_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHBoundaryResponse.actual_forcing_finite_boundary_response

/-- info: 'FMSA.Convergence.ActualHBoundaryResponse.actual_h_tangent_finite_boundary_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHBoundaryResponse.actual_h_tangent_finite_boundary_response

/-- info: 'FMSA.Convergence.ActualHBoundaryResponse.actual_h_tangent_JL_boundary_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHBoundaryResponse.actual_h_tangent_JL_boundary_response
