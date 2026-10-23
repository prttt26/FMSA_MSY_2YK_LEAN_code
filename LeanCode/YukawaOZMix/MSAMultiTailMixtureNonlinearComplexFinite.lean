import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearComplexKernel

/-! The same finite real coefficient certificate controls complex transforms.
Rates may coincide and species may have zero density. -/
noncomputable section
open MeasureTheory Set Real Filter Topology Polynomial
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def nonlinearComplexReciprocityResidual (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  nonlinearComplexJ z ρ σ Dt G s-(nonlinearComplexJ z ρ σ Dt G s).transpose+
    s⁻¹ • ((nonlinearComplexJ z ρ σ Dt G s).transpose*Matrix.diagonal (fun i => (ρ i : ℂ))*
      nonlinearComplexL z ρ σ Dt G s-
      (nonlinearComplexL z ρ σ Dt G s).transpose*Matrix.diagonal (fun i => (ρ i : ℂ))*
      nonlinearComplexJ z ρ σ Dt G s)

theorem nonlinearRatePolynomial_complex_eval (z : ι → ℝ) (s : ℂ) :
    (nonlinearRatePolynomial z).eval₂ (algebraMap ℝ ℂ) s=∏ u, (s+(z u : ℂ)) := by
  simp only [nonlinearRatePolynomial, Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Complex.coe_algebraMap]

theorem nonlinearRatePolynomialExcept_complex_eval (z : ι → ℝ) (s : ℂ) (u : ι) :
    (s+(z u : ℂ))*(nonlinearRatePolynomialExcept z u).eval₂ (algebraMap ℝ ℂ) s=
      (nonlinearRatePolynomial z).eval₂ (algebraMap ℝ ℂ) s := by
  simp only [nonlinearRatePolynomialExcept, Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Complex.coe_algebraMap, nonlinearRatePolynomial_complex_eval]
  exact Finset.mul_prod_erase (f := fun v => s+(z v : ℂ)) Finset.univ (Finset.mem_univ u)

theorem nonlinear_complex_rate_nonzero (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (s : ℂ) (hs : 0 ≤ s.re) (u : ι) : s+(z u : ℂ) ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at he
  linarith [hz u]

theorem nonlinearRationalDenominator_complex_eval_ne_zero (z : ι → ℝ)
    (hz : ∀ u, 0 < z u) (s : ℂ) (hs : s ≠ 0) (hsre : 0 ≤ s.re) :
    (nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s ≠ 0 := by
  simp only [nonlinearRationalDenominator, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, nonlinearRatePolynomial_complex_eval]
  exact mul_ne_zero (pow_ne_zero _ hs) (Finset.prod_ne_zero_iff.mpr
    (fun u _ => nonlinear_complex_rate_nonzero z hz s hsre u))

theorem nonlinearJNumerator_complex_eval (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (s : ℂ)
    (hs : s ≠ 0) (hsre : 0 ≤ s.re) (i j : Fin N) :
    (nonlinearJNumerator z ρ σ Dt G i j).eval₂ (algebraMap ℝ ℂ) s=
      (nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s*nonlinearComplexJ z ρ σ Dt G s i j := by
  have ht (u : ι) : (z u : ℂ)*(C z ρ σ Dt G u i j : ℂ)*s^2*
      (nonlinearRatePolynomialExcept z u).eval₂ (algebraMap ℝ ℂ) s=
      s^2*(nonlinearRatePolynomial z).eval₂ (algebraMap ℝ ℂ) s*
        ((z u : ℂ)*(C z ρ σ Dt G u i j : ℂ)/(s+(z u : ℂ))) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (nonlinear_complex_rate_nonzero z hz s hsre u)).mpr
    linear_combination (z u : ℂ)*(C z ρ σ Dt G u i j : ℂ)*s^2*
      nonlinearRatePolynomialExcept_complex_eval z s u
  simp only [nonlinearJNumerator, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_finset_sum,
    Complex.coe_algebraMap, Complex.ofReal_mul, nonlinearRationalDenominator,
    nonlinearComplexJ, Matrix.of_apply, ht]
  rw [← Finset.mul_sum]
  field_simp [hs]
  <;> ring

theorem nonlinearLNumerator_complex_eval (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (s : ℂ)
    (hs : s ≠ 0) (hsre : 0 ≤ s.re) (i j : Fin N) :
    (nonlinearLNumerator z ρ σ Dt G i j).eval₂ (algebraMap ℝ ℂ) s=
      (nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s*nonlinearComplexL z ρ σ Dt G s i j := by
  have ht (u : ι) : (z u : ℂ)*(W z ρ Dt G u i j : ℂ)*s^2*
      (nonlinearRatePolynomialExcept z u).eval₂ (algebraMap ℝ ℂ) s=
      s^2*(nonlinearRatePolynomial z).eval₂ (algebraMap ℝ ℂ) s*
        ((z u : ℂ)*(W z ρ Dt G u i j : ℂ)/(s+(z u : ℂ))) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (nonlinear_complex_rate_nonzero z hz s hsre u)).mpr
    linear_combination (z u : ℂ)*(W z ρ Dt G u i j : ℂ)*s^2*
      nonlinearRatePolynomialExcept_complex_eval z s u
  simp only [nonlinearLNumerator, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_finset_sum,
    Complex.coe_algebraMap, Complex.ofReal_mul, Complex.ofReal_sub, nonlinearRationalDenominator,
    nonlinearComplexL, Matrix.of_apply, ht]
  rw [← Finset.mul_sum]
  field_simp [hs]
  <;> ring

theorem nonlinearComplexReciprocityResidual_entry (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (s : ℂ) (i j : Fin N) :
    nonlinearComplexReciprocityResidual z ρ σ Dt G s i j=
      nonlinearComplexJ z ρ σ Dt G s i j-nonlinearComplexJ z ρ σ Dt G s j i+
      (∑ m, (ρ m : ℂ)*(nonlinearComplexJ z ρ σ Dt G s m i*nonlinearComplexL z ρ σ Dt G s m j-
        nonlinearComplexL z ρ σ Dt G s m i*nonlinearComplexJ z ρ σ Dt G s m j))/s := by
  simp only [nonlinearComplexReciprocityResidual, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, inv_mul_eq_div, Matrix.transpose_apply,
    Matrix.mul_apply (M := (nonlinearComplexJ z ρ σ Dt G s).transpose*Matrix.diagonal (fun i => (ρ i : ℂ))),
    Matrix.mul_apply (M := (nonlinearComplexL z ρ σ Dt G s).transpose*Matrix.diagonal (fun i => (ρ i : ℂ)))]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  congr 1
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem nonlinearReciprocityPolynomial_complex_eval (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (s : ℂ)
    (hs : s ≠ 0) (hsre : 0 ≤ s.re) (i j : Fin N) :
    (nonlinearReciprocityPolynomial z ρ σ Dt G i j).eval₂ (algebraMap ℝ ℂ) s=
      s*((nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s)^2*
        nonlinearComplexReciprocityResidual z ρ σ Dt G s i j := by
  simp only [nonlinearReciprocityPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_finset_sum,
    Complex.coe_algebraMap, nonlinearJNumerator_complex_eval z ρ σ Dt G hz s hs hsre,
    nonlinearLNumerator_complex_eval z ρ σ Dt G hz s hs hsre,
    nonlinearComplexReciprocityResidual_entry, mul_add, Finset.mul_sum]
  have he : (∑ m, (ρ m : ℂ)*((nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s*
      nonlinearComplexJ z ρ σ Dt G s m i*((nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s*
      nonlinearComplexL z ρ σ Dt G s m j)-(nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s*
      nonlinearComplexL z ρ σ Dt G s m i*((nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s*
      nonlinearComplexJ z ρ σ Dt G s m j)))=
      ((nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s)^2*∑ m, (ρ m : ℂ)*
        (nonlinearComplexJ z ρ σ Dt G s m i*nonlinearComplexL z ρ σ Dt G s m j-
        nonlinearComplexL z ρ σ Dt G s m i*nonlinearComplexJ z ρ σ Dt G s m j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [he]
  field_simp [hs]
  <;> ring

theorem nonlinear_finite_certificate_complex_residual_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u)
    (hcert : NonlinearFiniteReciprocityCertificate z ρ σ Dt G)
    (s : ℂ) (hs : s ≠ 0) (hsre : 0 ≤ s.re) :
    nonlinearComplexReciprocityResidual z ρ σ Dt G s=0 := by
  ext i j
  have he := nonlinearReciprocityPolynomial_complex_eval z ρ σ Dt G hz s hs hsre i j
  rw [nonlinear_finite_certificate_polynomial_zero z ρ σ Dt G hcert, Polynomial.eval₂_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero hs (pow_ne_zero _
    (nonlinearRationalDenominator_complex_eval_ne_zero z hz s hs hsre)))

end FMSA.ExactMSA.MultiTailMixture
