import MSAConvergence.ActualSourceBoundary

/-! Full fixed-base canonicity is open in the genuine amplitude space.
The perturbation is a change in actual coefficients, not a small base kernel. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.CanonicalNeighborhood
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture
open FMSA.Convergence.ActualSourceBoundary FMSA.Convergence.ActualLaplaceJets
open FMSA.Convergence.CanonicalKernelEstimates
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Actual fixed row-density basis L1 mass, independent of amplitudes/frequency. -/
def kernelBasisMass (z : T → ℝ) (rho sigma : Fin N → ℝ) (b : BasisIndex T) (i : Fin N) : ℝ :=
  ∫ r in Ioi (0 : ℝ), |rho i*recenteredBasis z sigma b i r|

/-- An actual finite coefficient-distance budget in the existing amplitude norm. -/
def kernelCoefficientDistance (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p q : TailMatrix T N × TailMatrix T N) : ℝ :=
  ∑ i, ∑ j, ∑ b : BasisIndex T,
    |bhCoefficient z rho sigma p i j b-bhCoefficient z rho sigma q i j b| *kernelBasisMass z rho sigma b i

/-- The fixed actual basis mass has a genuine finite L1 integral. -/
theorem kernel_basis_mass_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (b : BasisIndex T) (i : Fin N) :
    IntegrableOn (fun r : ℝ => |rho i*recenteredBasis z sigma b i r|) (Ioi 0) := by
  have he := (kernel_basis_laplace_closed_right z hz rho sigma 0 (by simp) b i).norm
  change Integrable (fun r : ℝ => |rho i*recenteredBasis z sigma b i r|) (volume.restrict (Ioi 0))
  simpa only [neg_zero, zero_mul, Complex.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs] using he

/-- Actual L1 basis masses are nonnegative. -/
theorem kernel_basis_mass_nonneg (z : T → ℝ) (rho sigma : Fin N → ℝ) (b : BasisIndex T) (i : Fin N) :
    0 ≤ kernelBasisMass z rho sigma b i := integral_nonneg (fun _ => abs_nonneg _)

/-- Actual basis Laplace symbols are uniformly bounded on the WHOLE closed
right half-plane, including its frequency origin. -/
theorem kernel_basis_laplace_uniform_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (b : BasisIndex T) (i : Fin N) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖FMSA.causalComplexLaplace (fun r => rho i*recenteredBasis z sigma b i r) s‖ ≤
      kernelBasisMass z rho sigma b i := by
  unfold FMSA.causalComplexLaplace kernelBasisMass
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae
    (kernel_basis_laplace_closed_right z hz rho sigma s hs b i).norm
    (kernel_basis_mass_integrable z hz rho sigma b i)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change 0 < r at hr
  simp only [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.norm_eq_abs]
  have hphase : exp (-s.re*r) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  simpa only [mul_one, abs_mul] using
    mul_le_mul_of_nonneg_left hphase (mul_nonneg (abs_nonneg (rho i)) (abs_nonneg (recenteredBasis z sigma b i r)))

/-- The actual whole-kernel integral is a finite coefficient/basis sum,
with every fixed basis integral supplied before exchanging the sum. -/
theorem kernel_laplace_coefficient_sum (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (p : TailMatrix T N × TailMatrix T N)
    (s : ℂ) (hs : 0 ≤ s.re) (i j : Fin N) :
    rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j =
      ∑ b : BasisIndex T, (bhCoefficient z rho sigma p i j b : ℂ)*
        FMSA.causalComplexLaplace (fun r => rho i*recenteredBasis z sigma b i r) s := by
  rw [kernel_laplace_basis, finite_complex_integral _ _ _
    (fun b => kernel_basis_laplace_closed_right z hz rho sigma s hs b i)]
  rfl

/-- Actual kernel changes are bounded entrywise by genuine finite L1 basis
masses, uniformly for every complex frequency with nonnegative real part. -/
theorem kernel_laplace_entry_difference_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (p q : TailMatrix T N × TailMatrix T N)
    (s : ℂ) (hs : 0 ≤ s.re) (i j : Fin N) :
    ‖rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j-
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma q.1 q.2) s i j‖ ≤
      ∑ b : BasisIndex T, |bhCoefficient z rho sigma p i j b-bhCoefficient z rho sigma q i j b| *
        kernelBasisMass z rho sigma b i := by
  rw [kernel_laplace_coefficient_sum z hz rho sigma p s hs i j,
    kernel_laplace_coefficient_sum z hz rho sigma q s hs i j, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (kernel_basis_laplace_uniform_bound z hz rho sigma b i s hs) (abs_nonneg _)

/-- Genuine actual kernel-symbol changes have a finite uniform norm-sum
bound, retaining arbitrary density signs in this off-root analytic statement. -/
theorem kernel_laplace_difference_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (p q : TailMatrix T N × TailMatrix T N)
    (s : ℂ) (hs : 0 ≤ s.re) :
    complexNormSum (rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s-
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma q.1 q.2) s) ≤
      kernelCoefficientDistance z rho sigma p q := by
  unfold complexNormSum kernelCoefficientDistance
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
    kernel_laplace_entry_difference_bound z hz rho sigma p q s hs i j))

/-- The actual distance budget is continuous in the genuine amplitude norm. -/
theorem kernel_coefficient_distance_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (q : TailMatrix T N × TailMatrix T N) : Continuous (fun p => kernelCoefficientDistance z rho sigma p q) := by
  unfold kernelCoefficientDistance
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro b _
  exact ((bhCoefficient_contDiff z rho sigma i j b).continuous.sub continuous_const).abs.mul continuous_const

/-- The coefficient-distance budget vanishes at its actual base point. -/
theorem kernel_coefficient_distance_self (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) : kernelCoefficientDistance z rho sigma p p = 0 := by
  simp [kernelCoefficientDistance]

/-- The genuine distance budget is nonnegative. -/
theorem kernel_coefficient_distance_nonneg (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p q : TailMatrix T N × TailMatrix T N) : 0 ≤ kernelCoefficientDistance z rho sigma p q := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun b _ =>
    mul_nonneg (abs_nonneg _) (kernel_basis_mass_nonneg z rho sigma b i))))

/-- Pure finite-matrix inverse perturbation; the base kernel need not be small. -/
theorem unit_of_inverse_perturbation (Q P : Matrix (Fin N) (Fin N) ℂ)
    (hu : IsUnit (1-Q)) (hsmall : complexNormSum ((1-Q)⁻¹*(P-Q)) < 1) : IsUnit (1-P) := by
  have he : IsUnit (1-(1-Q)⁻¹*(P-Q)) := complex_matrix_one_sub_isUnit_of_normSum _ hsmall
  have hprod : (1-Q)*(1-(1-Q)⁻¹*(P-Q)) = 1-P := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mul]
    noncomm_ring
  rw [← hprod]
  exact hu.mul he

/-- Full closed-right-half-plane canonicity is a genuine neighbourhood property
of the actual amplitude family. Nearby canonicity is PROVED, not assumed. -/
theorem actual_canonicity_eventually (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∀ᶠ q : TailMatrix T N × TailMatrix T N in 𝓝 p,
      ∀ s : ℂ, 0 ≤ s.re → IsUnit
        (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma q.1 q.2) s) := by
  obtain ⟨delta, R, B, C, hd, hdz, hR, hB, hC, hcont, hb⟩ :=
    actual_canonical_resolvent_control z hz rho sigma hsigma p hcanon
  have hc : Continuous (fun q => (C+1)*kernelCoefficientDistance z rho sigma q p) :=
    (kernel_coefficient_distance_continuous z rho sigma p).const_mul (C+1)
  have he : ∀ᶠ q in 𝓝 p, (C+1)*kernelCoefficientDistance z rho sigma q p < 1 :=
    hc.continuousAt.eventually_lt continuousAt_const (by rw [kernel_coefficient_distance_self, mul_zero]; norm_num)
  filter_upwards [he] with q hq
  intro s hs
  have hbase := hb s (by linarith : -delta ≤ s.re)
  apply unit_of_inverse_perturbation _ _ (hcanon s hs)
  calc
    _ ≤ complexNormSum ((1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹)*
        complexNormSum (rdfMatrixLaplace (nonlinearCausalKernel z rho sigma q.1 q.2) s-
          rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s) := complexNormSum_mul_le _ _
    _ ≤ C*kernelCoefficientDistance z rho sigma q p :=
      mul_le_mul hbase.2.1 (kernel_laplace_difference_bound z hz rho sigma q p s hs)
        (complexNormSum_nonneg _) hC
    _ ≤ (C+1)*kernelCoefficientDistance z rho sigma q p :=
      mul_le_mul_of_nonneg_right (by linarith) (kernel_coefficient_distance_nonneg z rho sigma q p)
    _ < 1 := hq

/-- Actual full canonical amplitudes as a subset of the original parameter space. -/
def canonicalAmplitudes (z : T → ℝ) (rho sigma : Fin N → ℝ) : Set (TailMatrix T N × TailMatrix T N) :=
  {p | ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)}

/-- The true full canonical amplitude set is open, including its Fourier boundary. -/
theorem canonical_amplitudes_isOpen (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) :
    IsOpen (canonicalAmplitudes z rho sigma) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  exact actual_canonicity_eventually z hz rho sigma hsigma p hp

end FMSA.Convergence.CanonicalNeighborhood

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.kernel_basis_mass_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.kernel_basis_mass_integrable

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.kernel_basis_mass_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.kernel_basis_mass_nonneg

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.kernel_basis_laplace_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.kernel_basis_laplace_uniform_bound

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.kernel_laplace_coefficient_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.kernel_laplace_coefficient_sum

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.kernel_laplace_entry_difference_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.kernel_laplace_entry_difference_bound

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.kernel_laplace_difference_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.kernel_laplace_difference_bound

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.kernel_coefficient_distance_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.kernel_coefficient_distance_continuous

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.kernel_coefficient_distance_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.kernel_coefficient_distance_self

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.kernel_coefficient_distance_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.kernel_coefficient_distance_nonneg

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.unit_of_inverse_perturbation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.unit_of_inverse_perturbation

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.actual_canonicity_eventually' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.actual_canonicity_eventually

/-- info: 'FMSA.Convergence.CanonicalNeighborhood.canonical_amplitudes_isOpen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalNeighborhood.canonical_amplitudes_isOpen
