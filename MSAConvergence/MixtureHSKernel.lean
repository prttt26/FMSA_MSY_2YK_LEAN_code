import MSAConvergence.MixtureHSAxis
import MSAConvergence.MaximalMSAConvergence

/-! Actual general-mixture HS axis units, including the honest frequency
origin. Empty-tail presentation only fixes an irrelevant kernel dictionary. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.MixtureHSKernel
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.MatrixQ0
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture
open FMSA.Convergence.MixtureHSEnergy FMSA.Convergence.MixtureHSAxis
open FMSA.Convergence.LowDensityCanonicalSeed FMSA.Convergence.CanonicalNeighborhood
variable {N : ℕ}

def emptyRates : Fin 0 → ℝ := fun i => Fin.elim0 i

theorem empty_rates_pos : ∀ i, 0 < emptyRates i := fun i => Fin.elim0 i

def seedKernel (rho sigma : Fin N → ℝ) : ℝ → Matrix (Fin N) (Fin N) ℝ :=
  nonlinearCausalKernel emptyRates rho sigma 0 0

def seedSymbol (rho sigma : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  rdfMatrixLaplace (seedKernel rho sigma) s

def seedFactor (rho sigma : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ := 1-seedSymbol rho sigma s

def seedDet (rho sigma : Fin N → ℝ) (s : ℂ) : ℂ := (seedFactor rho sigma s).det

/-- This presentation is EXACTLY the actual HS seed kernel for every tail
rate set and G value, not an alternative reference model. -/
theorem seed_kernel_eq_actual {T : Type*} [Fintype T] (z : T → ℝ)
    (rho sigma : Fin N → ℝ) (G : TailMatrix T N) :
    seedKernel rho sigma = nonlinearCausalKernel z rho sigma 0 G :=
  hs_kernel_independent_tails emptyRates z rho sigma 0 G

/-- The physical A coefficient has the collective-energy moment form. -/
theorem hs_A_physical (rho sigma : Fin N → ℝ) (hv : vacMix rho sigma ≠ 0) (j : Fin N) :
    hsA rho sigma (Real.pi/vacMix rho sigma) j = Qppphys rho sigma j j := by
  unfold hsA secondMoment Qppphys xi2
  field_simp [hv]

/-- The physical Qp coefficient has the SAME moment form, unequal diameters
and arbitrary nonnegative densities included. -/
theorem hs_qp_physical (rho sigma : Fin N → ℝ) (hv : vacMix rho sigma ≠ 0) (i j : Fin N) :
    hsQp rho sigma (Real.pi/vacMix rho sigma) i j = Q0phys rho sigma i j := by
  unfold hsQp
  rw [hs_A_physical rho sigma hv]
  unfold Q0phys Qppphys
  field_simp [hv]
  ring

/-- Honest HS symbol away from zero is the row-density physical core formula.
This equality is established through the actual integral before axis units. -/
theorem seed_symbol_nonzero_formula (rho sigma : Fin N → ℝ) (hv : vacMix rho sigma ≠ 0)
    (hsigma : ∀ i, 0 ≤ sigma i) (s : ℂ) (hs : s ≠ 0) (hsre : 0 ≤ s.re) :
    seedSymbol rho sigma s = Matrix.diagonal (fun i => (rho i : ℂ))*bareHS rho sigma (Real.pi/vacMix rho sigma) s := by
  ext i j
  rw [Matrix.diagonal_mul]
  change FMSA.causalComplexLaplace
    (fun r => rho i*nonlinearRecenteredQ emptyRates rho sigma 0 0 i j r) s =
      (rho i : ℂ)*bareHS rho sigma (Real.pi/vacMix rho sigma) s i j
  dsimp only [bareHS]
  have hrec := nonlinearRecenteredQ_actual_complex_laplace emptyRates rho sigma 0 0 empty_rates_pos hsigma s hs hsre i j
  have hA : amplitudeA emptyRates rho sigma 0 0 = fun j => Qppphys rho sigma j j := by
    funext j
    exact amplitudeA_zero emptyRates rho sigma 0 j
  have hQ : amplitudeQp emptyRates rho sigma 0 0 = Q0phys rho sigma := by
    funext i j
    exact amplitudeQp_zero emptyRates rho sigma 0 i j
  rw [hA,hQ] at hrec
  rw [causal_laplace_real_const_mul,hrec]
  have hfree : QhatComplex emptyRates sigma (fun j => Qppphys rho sigma j j) (Q0phys rho sigma)
      (W emptyRates rho 0 0) (C emptyRates rho sigma 0 0) s i j =
      Complex.exp (-s*(edgeLo sigma i j : ℂ))*(phi1 s (sigma i)*(Q0phys rho sigma i j : ℂ)+
        phi2 s (sigma i)*(Qppphys rho sigma j j : ℂ)) := by
    unfold QhatComplex phi1 phi2
    simp
  rw [hfree]
  have hexp : Complex.exp (s*(edgeLo sigma i j : ℂ))*Complex.exp (-s*(edgeLo sigma i j : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    _ = (rho i : ℂ)*(Complex.exp (s*(edgeLo sigma i j : ℂ))*Complex.exp (-s*(edgeLo sigma i j : ℂ)))*
        (phi1 s (sigma i)*(Q0phys rho sigma i j : ℂ)+phi2 s (sigma i)*(Qppphys rho sigma j j : ℂ)) := by ring
    _ = _ := by
      rw [hexp,mul_one]
      simp only [hs_A_physical rho sigma hv,hs_qp_physical rho sigma hv]
      ring

/-- True integral origin of the compact linear basis, not phi1(0). -/
theorem linear_basis_laplace_zero (sigma : Fin N → ℝ) (i : Fin N) (hsigma : 0 ≤ sigma i) :
    FMSA.causalComplexLaplace (recenteredBasis emptyRates sigma (.inl 0) i) 0 =
      -((sigma i : ℂ)^2/2) := by
  let f := recenteredBasis emptyRates sigma (.inl 0) i
  have hn (r : ℝ) : f r ≤ 0 := by
    simp only [f,recenteredBasis,basisQp,basisA,basisW,basisC,Fin.isValue,if_true,
      show (0 : Fin 2) ≠ 1 by decide,if_false,zero_div,zero_mul,one_mul,add_zero]
    exact sub_nonpos.mpr (min_le_right _ _)
  have hm : (∫ r in Ioi (0 : ℝ), |f r|) = sigma i^2/2 := by
    simpa only [kernelBasisMass,one_mul,f] using hs_linear_basis_mass emptyRates empty_rates_pos sigma i hsigma
  simp_rw [abs_of_nonpos (hn _),integral_neg] at hm
  have hi : (∫ r in Ioi (0 : ℝ), f r) = -sigma i^2/2 := by linarith
  change (∫ r in Ioi (0 : ℝ), (f r : ℂ)*Complex.exp (-(0 : ℂ)*r)) = _
  simp only [neg_zero,zero_mul,Complex.exp_zero,mul_one,integral_complex_ofReal]
  rw [hi]
  push_cast
  ring

/-- True integral origin of the compact quadratic basis, not phi2(0). -/
theorem quadratic_basis_laplace_zero (sigma : Fin N → ℝ) (i : Fin N) (hsigma : 0 ≤ sigma i) :
    FMSA.causalComplexLaplace (recenteredBasis emptyRates sigma (.inl 1) i) 0 =
      (sigma i : ℂ)^3/6 := by
  let f := recenteredBasis emptyRates sigma (.inl 1) i
  have hp (r : ℝ) : 0 ≤ f r := by
    simp only [f,recenteredBasis,basisQp,basisA,basisW,basisC,Fin.isValue,if_true,
      show (1 : Fin 2) ≠ 0 by decide,if_false,zero_mul,add_zero,zero_add]
    positivity
  have hi : (∫ r in Ioi (0 : ℝ), f r) = sigma i^3/6 := by
    have h := hs_quadratic_basis_mass emptyRates empty_rates_pos sigma i hsigma
    simpa only [kernelBasisMass,one_mul,abs_of_nonneg (hp _),f] using h
  change (∫ r in Ioi (0 : ℝ), (f r : ℂ)*Complex.exp (-(0 : ℂ)*r)) = _
  simp only [neg_zero,zero_mul,Complex.exp_zero,mul_one,integral_complex_ofReal]
  rw [hi]
  push_cast
  rfl

/-- HS static symbol is derived from honest compact polynomial integrals. -/
theorem seed_symbol_zero_formula (rho sigma : Fin N → ℝ) (hv : vacMix rho sigma ≠ 0)
    (hsigma : ∀ i, 0 ≤ sigma i) :
    seedSymbol rho sigma 0 = Matrix.diagonal (fun i => (rho i : ℂ))*staticCore rho sigma (Real.pi/vacMix rho sigma) := by
  ext i j
  change rdfMatrixLaplace (nonlinearCausalKernel emptyRates rho sigma 0 0) 0 i j = _
  rw [hs_kernel_symbol emptyRates empty_rates_pos rho sigma 0 0 (by simp) i j,
    linear_basis_laplace_zero sigma i (hsigma i),quadratic_basis_laplace_zero sigma i (hsigma i)]
  simp only [Matrix.diagonal_mul,static_core_eq_polynomial_moments,hs_A_physical rho sigma hv,hs_qp_physical rho sigma hv]
  push_cast
  ring

/-- ACTUAL general-mixture HS factor is invertible at EVERY Fourier-axis
frequency, including zero and all tracers; no no-spinodal axiom is consumed. -/
theorem seed_factor_axis_isUnit (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : 0 < vacMix rho sigma) (k : ℝ) :
    IsUnit (seedFactor rho sigma (Complex.I*(k : ℂ))) := by
  by_cases hk : k = 0
  · simp only [hk,Complex.ofReal_zero,mul_zero,seedFactor]
    rw [seed_symbol_zero_formula rho sigma hv.ne' hsigma]
    exact static_row_factor_isUnit rho sigma hrho hsigma _ (div_nonneg Real.pi_pos.le hv.le)
  · unfold seedFactor
    rw [seed_symbol_nonzero_formula rho sigma hv.ne' hsigma _
      (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)) (by simp)]
    exact row_factor_axis_isUnit rho sigma hrho _ k hk

/-- No imaginary-axis point is missed by the real-wave-number parametrization. -/
theorem seed_factor_imaginary_isUnit (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : 0 < vacMix rho sigma) (s : ℂ) (hs : s.re = 0) :
    IsUnit (seedFactor rho sigma s) := by
  have he : s = Complex.I*(s.im : ℂ) := by apply Complex.ext <;> simp [hs]
  rw [he]
  exact seed_factor_axis_isUnit rho sigma hrho hsigma hv s.im

end FMSA.Convergence.MixtureHSKernel

/-- info: 'FMSA.Convergence.MixtureHSKernel.empty_rates_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSKernel.empty_rates_pos

/-- info: 'FMSA.Convergence.MixtureHSKernel.seed_kernel_eq_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSKernel.seed_kernel_eq_actual

/-- info: 'FMSA.Convergence.MixtureHSKernel.hs_A_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSKernel.hs_A_physical

/-- info: 'FMSA.Convergence.MixtureHSKernel.hs_qp_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSKernel.hs_qp_physical

/-- info: 'FMSA.Convergence.MixtureHSKernel.seed_symbol_nonzero_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSKernel.seed_symbol_nonzero_formula

/-- info: 'FMSA.Convergence.MixtureHSKernel.linear_basis_laplace_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSKernel.linear_basis_laplace_zero

/-- info: 'FMSA.Convergence.MixtureHSKernel.quadratic_basis_laplace_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSKernel.quadratic_basis_laplace_zero

/-- info: 'FMSA.Convergence.MixtureHSKernel.seed_symbol_zero_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSKernel.seed_symbol_zero_formula

/-- info: 'FMSA.Convergence.MixtureHSKernel.seed_factor_axis_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSKernel.seed_factor_axis_isUnit

/-- info: 'FMSA.Convergence.MixtureHSKernel.seed_factor_imaginary_isUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSKernel.seed_factor_imaginary_isUnit

