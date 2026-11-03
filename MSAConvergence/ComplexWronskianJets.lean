import MSAConvergence.NormalizedWronskianJets

/-! Genuine complex-frequency amplitude derivatives of the actual finite
Wronskian defects. All clearing identities are established off-root. -/
noncomputable section
open Real Polynomial
open scoped BigOperators ContDiff

namespace FMSA.Convergence.ComplexWronskianJets
open FMSA.Convergence.PolynomialJets FMSA.Convergence.WronskianJets
open FMSA.Convergence.NormalizedWronskianJets
open FMSA.Paper.JacobianExterior FMSA.ExactMSA.MultiTailMixture FMSA.MatrixQ0 MSAMixture

section General
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The genuine real amplitude derivative commutes with evaluation of a
uniformly bounded real polynomial family at any complex frequency. -/
theorem variation_complex_eval_fderiv (D : ℕ) (f : P → Polynomial ℝ) (p v : P)
    (hb : ∀ a, (f a).natDegree ≤ D)
    (hd : ∀ n ∈ Finset.range (D + 1), DifferentiableAt ℝ (fun a => (f a).coeff n) p)
    (s : ℂ) :
    (variation D f p v).eval₂ (algebraMap ℝ ℂ) s =
      fderiv ℝ (fun a => (f a).eval₂ (algebraMap ℝ ℂ) s) p v := by
  have he : (fun a => (f a).eval₂ (algebraMap ℝ ℂ) s) =
      fun a => ∑ n ∈ Finset.range (D + 1), ((f a).coeff n : ℂ) * s^n := by
    funext a
    exact Polynomial.eval₂_eq_sum_range' (algebraMap ℝ ℂ) (by have := hb a; omega) s
  have hc (n : ℕ) (hn : n ∈ Finset.range (D + 1)) :
      HasFDerivAt (fun a => ((f a).coeff n : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ (fun a => (f a).coeff n) p)) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (hd n hn).hasFDerivAt
  rw [he, fderiv_fun_sum (fun n hn => (hc n hn).differentiableAt.mul_const _)]
  simp only [variation, Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial,
    Complex.coe_algebraMap, sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [((hc n hn).mul_const (s^n)).fderiv]
  simp [mul_comm]

/-- Complex evaluation is genuinely smooth in the real amplitudes. -/
theorem coeffSmooth_complex_eval_contDiff (D : ℕ) (f : P → Polynomial ℝ)
    (hb : ∀ a, (f a).natDegree ≤ D) (hf : CoeffSmooth f) (s : ℂ) :
    ContDiff ℝ ∞ (fun a => (f a).eval₂ (algebraMap ℝ ℂ) s) := by
  have he : (fun a => (f a).eval₂ (algebraMap ℝ ℂ) s) =
      fun a => ∑ n ∈ Finset.range (D + 1), ((f a).coeff n : ℂ) * s^n := by
    funext a
    exact Polynomial.eval₂_eq_sum_range' (algebraMap ℝ ℂ) (by have := hb a; omega) s
  rw [he]
  exact ContDiff.sum fun n _ => (Complex.ofRealCLM.contDiff.comp (hf n)).mul contDiff_const
/-- Smooth real coefficients remain smooth under the bounded real-linear
embedding into complex values. -/
@[fun_prop]
theorem complex_ofReal_contDiff (f : P → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun a => (f a : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

end General

variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual complete U/V tangent certificate annihilates every complex
cleared-polynomial evaluation, with genuine derivatives proved to exist. -/
theorem actual_kernel_complex_polynomial_eval_fderiv_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hk : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) (s : ℂ) :
    fderiv ℝ (fun a => (nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j).eval₂ (algebraMap ℝ ℂ) s) p v = 0 ∧
    fderiv ℝ (fun a => (nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).eval₂ (algebraMap ℝ ℂ) s) p v = 0 := by
  have h0 := actual_kernel_tangent_polynomials_zero z rho sigma K hK hz hv t p v hroot hk i j
  constructor
  · rw [← variation_complex_eval_fderiv (2 * (nonlinearDistinctRates z).card + 5)
      (fun a : TailMatrix T N × TailMatrix T N => nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j) p v
      (fun a => nonlinearDistinctUPolynomial_degree_le z rho sigma a.1 a.2 i j)
      (fun n _ => ((actual_distinct_wronskian_coeffSmooth z rho sigma).1 i j n).differentiable (by simp) p) s]
    change (tangentU z rho sigma p v i j).eval₂ (algebraMap ℝ ℂ) s = 0
    rw [h0.1, Polynomial.eval₂_zero]
  · rw [← variation_complex_eval_fderiv (2 * (nonlinearDistinctRates z).card + 4)
      (fun a : TailMatrix T N × TailMatrix T N => nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j) p v
      (fun a => nonlinearDistinctVPolynomial_degree_le z rho sigma a.1 a.2 i j)
      (fun n _ => ((actual_distinct_wronskian_coeffSmooth z rho sigma).2 i j n).differentiable (by simp) p) s]
    change (tangentV z rho sigma p v i j).eval₂ (algebraMap ℝ ℂ) s = 0
    rw [h0.2, Polynomial.eval₂_zero]

/-- The distinct-rate denominator evaluates without dropping any rate value. -/
theorem distinctRatePolynomial_complex_eval (z : T → ℝ) (s : ℂ) :
    (nonlinearDistinctRatePolynomial z).eval₂ (algebraMap ℝ ℂ) s =
      ∏ r ∈ nonlinearDistinctRates z, (s + (r : ℂ)) := by
  simp only [nonlinearDistinctRatePolynomial, Polynomial.eval₂_finsetProd,
    Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, Complex.coe_algebraMap]

/-- The fixed distinct factorization remains exact over complex frequencies. -/
theorem distinctRateExcept_complex_eval (z : T → ℝ) (s : ℂ) (u : T) :
    (s + (z u : ℂ)) * (nonlinearDistinctRatePolynomialExcept z (z u)).eval₂ (algebraMap ℝ ℂ) s =
      (nonlinearDistinctRatePolynomial z).eval₂ (algebraMap ℝ ℂ) s := by
  have h := congrArg (fun q : Polynomial ℝ => q.eval₂ (algebraMap ℝ ℂ) s)
    (nonlinearDistinctRatePolynomial_factor z (z u) (nonlinearDistinctRates_mem z u))
  simpa only [Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Complex.coe_algebraMap] using h

/-- Positive rates exclude all distinct denominator zeros in the closed
right half-plane away from the origin, including repeated original labels. -/
theorem distinctDenominator_complex_eval_ne_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (s : ℂ) (hs : s ≠ 0) (hsre : 0 ≤ s.re) :
    (nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) s ≠ 0 := by
  classical
  simp only [nonlinearDistinctDenominator, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, distinctRatePolynomial_complex_eval]
  apply mul_ne_zero (pow_ne_zero _ hs)
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hr
  exact nonlinear_complex_rate_nonzero z hz s hsre u

/-- Off-root complex clearing for the actual distinct J numerator. -/
theorem distinctJNumerator_complex_eval (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (Dt G : TailMatrix T N) (hz : ∀ u, 0 < z u) (s : ℂ)
    (hs : s ≠ 0) (hsre : 0 ≤ s.re) (i j : Fin N) :
    (nonlinearDistinctJNumerator z rho sigma Dt G i j).eval₂ (algebraMap ℝ ℂ) s =
      (nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) s * nonlinearComplexJ z rho sigma Dt G s i j := by
  classical
  have ht (u : T) : (z u : ℂ) * (C z rho sigma Dt G u i j : ℂ) * s^2 *
      (nonlinearDistinctRatePolynomialExcept z (z u)).eval₂ (algebraMap ℝ ℂ) s =
      s^2 * (nonlinearDistinctRatePolynomial z).eval₂ (algebraMap ℝ ℂ) s *
        ((z u : ℂ) * (C z rho sigma Dt G u i j : ℂ) / (s + (z u : ℂ))) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (nonlinear_complex_rate_nonzero z hz s hsre u)).mpr
    linear_combination (z u : ℂ) * (C z rho sigma Dt G u i j : ℂ) * s^2 *
      distinctRateExcept_complex_eval z s u
  simp only [nonlinearDistinctJNumerator, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum,
    Complex.coe_algebraMap, Complex.ofReal_mul, nonlinearDistinctDenominator,
    nonlinearComplexJ, Matrix.of_apply, ht]
  rw [← Finset.mul_sum]
  field_simp [hs]

/-- Off-root complex clearing for the actual distinct L numerator. -/
theorem distinctLNumerator_complex_eval (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (Dt G : TailMatrix T N) (hz : ∀ u, 0 < z u) (s : ℂ)
    (hs : s ≠ 0) (hsre : 0 ≤ s.re) (i j : Fin N) :
    (nonlinearDistinctLNumerator z rho sigma Dt G i j).eval₂ (algebraMap ℝ ℂ) s =
      (nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) s * nonlinearComplexL z rho sigma Dt G s i j := by
  classical
  have ht (u : T) : (z u : ℂ) * (W z rho Dt G u i j : ℂ) * s^2 *
      (nonlinearDistinctRatePolynomialExcept z (z u)).eval₂ (algebraMap ℝ ℂ) s =
      s^2 * (nonlinearDistinctRatePolynomial z).eval₂ (algebraMap ℝ ℂ) s *
        ((z u : ℂ) * (W z rho Dt G u i j : ℂ) / (s + (z u : ℂ))) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (nonlinear_complex_rate_nonzero z hz s hsre u)).mpr
    linear_combination (z u : ℂ) * (W z rho Dt G u i j : ℂ) * s^2 *
      distinctRateExcept_complex_eval z s u
  simp only [nonlinearDistinctLNumerator, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum,
    Complex.coe_algebraMap, Complex.ofReal_mul, Complex.ofReal_sub, nonlinearDistinctDenominator,
    nonlinearComplexL, Matrix.of_apply, ht]
  rw [← Finset.mul_sum]
  field_simp [hs]

/-- Exact complex U clearing, before imposing any root equation. -/
theorem distinctUPolynomial_complex_eval (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (Dt G : TailMatrix T N) (hz : ∀ u, 0 < z u) (s : ℂ)
    (hs : s ≠ 0) (hsre : s.re=0) (i j : Fin N) :
    (nonlinearDistinctUPolynomial z rho sigma Dt G i j).eval₂ (algebraMap ℝ ℂ) s=
      s*(nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) s*
        (nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) (-s)*
        nonlinearWronskianU (nonlinearComplexJ z rho sigma Dt G s) (nonlinearComplexL z rho sigma Dt G s)
          (nonlinearComplexJ z rho sigma Dt G (-s)) (nonlinearComplexL z rho sigma Dt G (-s))
          (fun i => (rho i : ℂ)) s i j := by
  have hp : 0 ≤ s.re := by rw [hsre]
  have hm : 0 ≤ (-s).re := by simp [hsre]
  simp only [nonlinearDistinctUPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_neg, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_finsetSum, Complex.coe_algebraMap, polynomial_complex_eval_neg_comp,
    distinctJNumerator_complex_eval z rho sigma Dt G hz s hs hp,
    distinctLNumerator_complex_eval z rho sigma Dt G hz s hs hp,
    distinctJNumerator_complex_eval z rho sigma Dt G hz (-s) (neg_ne_zero.mpr hs) hm,
    distinctLNumerator_complex_eval z rho sigma Dt G hz (-s) (neg_ne_zero.mpr hs) hm,
    nonlinearWronskianU_entry]
  let D := (nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) s
  let M := (nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) (-s)
  have he : (∑ m, (rho m : ℂ)*(M*nonlinearComplexJ z rho sigma Dt G (-s) i m*
      (D*nonlinearComplexJ z rho sigma Dt G s j m)-D*nonlinearComplexL z rho sigma Dt G s i m*
      (M*nonlinearComplexL z rho sigma Dt G (-s) j m)))=
      D*M*∑ m, (rho m : ℂ)*(nonlinearComplexJ z rho sigma Dt G (-s) i m*
        nonlinearComplexJ z rho sigma Dt G s j m-nonlinearComplexL z rho sigma Dt G s i m*
        nonlinearComplexL z rho sigma Dt G (-s) j m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _; ring
  rw [he]
  field_simp [hs]
  ring

/-- Exact complex V clearing, before imposing any root equation. -/
theorem distinctVPolynomial_complex_eval (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (Dt G : TailMatrix T N) (hz : ∀ u, 0 < z u) (s : ℂ)
    (hs : s ≠ 0) (hsre : s.re=0) (i j : Fin N) :
    (nonlinearDistinctVPolynomial z rho sigma Dt G i j).eval₂ (algebraMap ℝ ℂ) s=
      s*(nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) s*
        (nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) (-s)*
        nonlinearWronskianV (nonlinearComplexJ z rho sigma Dt G s) (nonlinearComplexL z rho sigma Dt G s)
          (nonlinearComplexL z rho sigma Dt G (-s)) (fun i => (rho i : ℂ)) s i j := by
  have hp : 0 ≤ s.re := by rw [hsre]
  have hm : 0 ≤ (-s).re := by simp [hsre]
  simp only [nonlinearDistinctVPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_finsetSum, Complex.coe_algebraMap, polynomial_complex_eval_neg_comp,
    distinctJNumerator_complex_eval z rho sigma Dt G hz s hs hp,
    distinctLNumerator_complex_eval z rho sigma Dt G hz (-s) (neg_ne_zero.mpr hs) hm,
    nonlinearWronskianV_entry]
  let D := (nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) s
  let M := (nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) (-s)
  have he : (∑ m, (rho m : ℂ)*(D*nonlinearComplexJ z rho sigma Dt G s i m*
      (M*nonlinearComplexL z rho sigma Dt G (-s) j m)-M*nonlinearComplexL z rho sigma Dt G (-s) i m*
      (D*nonlinearComplexJ z rho sigma Dt G s j m)))=
      D*M*∑ m, (rho m : ℂ)*(nonlinearComplexJ z rho sigma Dt G s i m*
        nonlinearComplexL z rho sigma Dt G (-s) j m-nonlinearComplexL z rho sigma Dt G (-s) i m*
        nonlinearComplexJ z rho sigma Dt G s j m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _; ring
  rw [he]
  field_simp [hs]
  ring


/-- Actual complex J is smooth in the real BH amplitudes, at every fixed s. -/
@[fun_prop]
theorem complexJ_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (s : ℂ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 s i j) := by
  simp only [nonlinearComplexJ, Matrix.of_apply]
  fun_prop

/-- Actual complex L is smooth in the real BH amplitudes, including all
actual W/C and lower-value contributions. -/
@[fun_prop]
theorem complexL_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (s : ℂ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexL z rho sigma a.1 a.2 s i j) := by
  simp only [nonlinearComplexL, nonlinearLowerQValue, Matrix.of_apply]
  fun_prop

def actualWronskianU (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  nonlinearWronskianU (nonlinearComplexJ z rho sigma p.1 p.2 s) (nonlinearComplexL z rho sigma p.1 p.2 s)
    (nonlinearComplexJ z rho sigma p.1 p.2 (-s)) (nonlinearComplexL z rho sigma p.1 p.2 (-s))
    (fun i => (rho i : ℂ)) s

def actualWronskianV (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  nonlinearWronskianV (nonlinearComplexJ z rho sigma p.1 p.2 s) (nonlinearComplexL z rho sigma p.1 p.2 s)
    (nonlinearComplexL z rho sigma p.1 p.2 (-s)) (fun i => (rho i : ℂ)) s

/-- Actual rational Wronskian U has a genuine real amplitude derivative. -/
@[fun_prop]
theorem actualWronskianU_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (s : ℂ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => actualWronskianU z rho sigma a s i j) := by
  simp only [actualWronskianU, nonlinearWronskianU_entry]
  fun_prop

/-- Actual rational Wronskian V has a genuine real amplitude derivative. -/
@[fun_prop]
theorem actualWronskianV_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (s : ℂ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => actualWronskianV z rho sigma a s i j) := by
  simp only [actualWronskianV, nonlinearWronskianV_entry]
  fun_prop

/-- Genuine variations of both existing rational complex Wronskian defects
vanish at every nonzero imaginary frequency along every actual BH kernel.
The clearing factor is amplitude-independent and proved nonzero internally. -/
theorem actual_kernel_complex_wronskian_fderiv_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hk : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re = 0) :
    fderiv ℝ (fun a => actualWronskianU z rho sigma a s i j) p v = 0 ∧
    fderiv ℝ (fun a => actualWronskianV z rho sigma a s i j) p v = 0 := by
  let c := s * (nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) s *
    (nonlinearDistinctDenominator z).eval₂ (algebraMap ℝ ℂ) (-s)
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero hs
    (distinctDenominator_complex_eval_ne_zero z hz s hs (by rw [hsre])))
    (distinctDenominator_complex_eval_ne_zero z hz (-s) (neg_ne_zero.mpr hs) (by simp [hsre]))
  have hu : (fun a : TailMatrix T N × TailMatrix T N =>
        (nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j).eval₂ (algebraMap ℝ ℂ) s) =
      fun a => c * actualWronskianU z rho sigma a s i j := by
    funext a
    exact distinctUPolynomial_complex_eval z rho sigma a.1 a.2 hz s hs hsre i j
  have hw : (fun a : TailMatrix T N × TailMatrix T N =>
        (nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).eval₂ (algebraMap ℝ ℂ) s) =
      fun a => c * actualWronskianV z rho sigma a s i j := by
    funext a
    exact distinctVPolynomial_complex_eval z rho sigma a.1 a.2 hz s hs hsre i j
  have h0 := actual_kernel_complex_polynomial_eval_fderiv_zero z rho sigma K hK hz hv t p v hroot hk i j s
  have hdu : fderiv ℝ (fun a => (nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j).eval₂ (algebraMap ℝ ℂ) s) p v =
      c * fderiv ℝ (fun a => actualWronskianU z rho sigma a s i j) p v := by
    rw [hu]
    exact congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ => L v)
      ((((actualWronskianU_entry_contDiff z rho sigma s i j).differentiable (by simp) p).hasFDerivAt.const_mul c).fderiv)
  have hdv : fderiv ℝ (fun a => (nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).eval₂ (algebraMap ℝ ℂ) s) p v =
      c * fderiv ℝ (fun a => actualWronskianV z rho sigma a s i j) p v := by
    rw [hw]
    exact congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ => L v)
      ((((actualWronskianV_entry_contDiff z rho sigma s i j).differentiable (by simp) p).hasFDerivAt.const_mul c).fderiv)
  exact ⟨(mul_eq_zero.mp (hdu.symm.trans h0.1)).resolve_left hc,
    (mul_eq_zero.mp (hdv.symm.trans h0.2)).resolve_left hc⟩

/-- The actual Fourier Q/source relation's off-root defect, with all contact
phases and the actual spectral Baxter C retained. -/
def actualSourceDefect (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  let s : ℂ := Complex.I * k
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  (1 - nonlinearActualFourierQ z rho sigma p.1 p.2 k * R) *
      (rdfPhase sigma (-s) * (nonlinearComplexJ z rho sigma p.1 p.2 (-s)).transpose * rdfPhase sigma (-s)) -
    (1 - nonlinearActualFourierQ z rho sigma p.1 p.2 (-k) * R) *
      (rdfPhase sigma s * (nonlinearComplexJ z rho sigma p.1 p.2 s).transpose * rdfPhase sigma s) -
    s • nonlinearActualFourierC z rho sigma p.1 p.2 k

/-- The existing all-amplitude contact-phase algebra identifies the ACTUAL
Fourier source defect with the two ACTUAL rational complex Wronskians. -/
theorem actualSourceDefect_factorization (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ) (hk : k ≠ 0) :
    actualSourceDefect z rho sigma p k =
      rdfPhase sigma (-(Complex.I * k)) * actualWronskianU z rho sigma p (Complex.I * k) * rdfPhase sigma (Complex.I * k) +
      rdfPhase sigma (Complex.I * k) * actualWronskianV z rho sigma p (Complex.I * k) * rdfPhase sigma (Complex.I * k) := by
  classical
  have hs : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  have he := nonlinear_phase_wronskian_residual sigma
    (nonlinearComplexJ z rho sigma p.1 p.2 (Complex.I * k))
    (nonlinearComplexL z rho sigma p.1 p.2 (Complex.I * k))
    (nonlinearComplexJ z rho sigma p.1 p.2 (-(Complex.I * k)))
    (nonlinearComplexL z rho sigma p.1 p.2 (-(Complex.I * k)))
    (fun i => (rho i : ℂ)) (Complex.I * k) hs
  unfold actualSourceDefect
  rw [nonlinearActualFourierC_eq_Q_product]
  simp_rw [nonlinearActualFourierQ_eq_phaseQ z rho sigma p.1 p.2 hz hsigma k hk,
    nonlinearActualFourierQ_eq_phaseQ z rho sigma p.1 p.2 hz hsigma (-k) (neg_ne_zero.mpr hk)]
  simpa only [actualWronskianU, actualWronskianV, Complex.ofReal_neg, mul_neg, neg_neg] using he

/-- Diagonal contact phases make the fixed linear combination explicit in
each actual species entry. -/
theorem actualSourceDefect_entry (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    actualSourceDefect z rho sigma p k i j =
      rdfPhase sigma (-(Complex.I * k)) i i * actualWronskianU z rho sigma p (Complex.I * k) i j *
        rdfPhase sigma (Complex.I * k) j j +
      rdfPhase sigma (Complex.I * k) i i * actualWronskianV z rho sigma p (Complex.I * k) i j *
        rdfPhase sigma (Complex.I * k) j j := by
  rw [actualSourceDefect_factorization z rho sigma hz hsigma p k hk]
  simp [rdfPhase, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Actual source-defect entries have genuine amplitude derivatives at every
nonzero real wave number, with fixed physical transforms used off-root. -/
theorem actualSourceDefect_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => actualSourceDefect z rho sigma a k i j) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => actualSourceDefect z rho sigma a k i j) =
      fun a => rdfPhase sigma (-(Complex.I * k)) i i * actualWronskianU z rho sigma a (Complex.I * k) i j *
        rdfPhase sigma (Complex.I * k) j j +
      rdfPhase sigma (Complex.I * k) i i * actualWronskianV z rho sigma a (Complex.I * k) i j *
        rdfPhase sigma (Complex.I * k) j j := by
    funext a
    exact actualSourceDefect_entry z rho sigma hz hsigma a k hk i j
  rw [he]
  exact ((contDiff_const.mul (actualWronskianU_entry_contDiff z rho sigma (Complex.I * k) i j)).mul contDiff_const).add
    ((contDiff_const.mul (actualWronskianV_entry_contDiff z rho sigma (Complex.I * k) i j)).mul contDiff_const)

/-- The genuine actual Fourier Q/source-defect derivative vanishes along
any actual fixed-coupling BH kernel vector. This is a source Wronskian
identity; it does not postulate or prove Fourier/L2 control of the actual h. -/
theorem actual_kernel_sourceDefect_fderiv_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hkern : amplitudeJacobian z rho sigma K t p v = 0)
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    fderiv ℝ (fun a => actualSourceDefect z rho sigma a k i j) p v = 0 := by
  have hs : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  have h0 := actual_kernel_complex_wronskian_fderiv_zero z rho sigma K hK hz hv t p v hroot hkern i j
    (Complex.I * k) hs (by simp)
  have he : (fun a : TailMatrix T N × TailMatrix T N => actualSourceDefect z rho sigma a k i j) =
      fun a => rdfPhase sigma (-(Complex.I * k)) i i * actualWronskianU z rho sigma a (Complex.I * k) i j *
        rdfPhase sigma (Complex.I * k) j j +
      rdfPhase sigma (Complex.I * k) i i * actualWronskianV z rho sigma a (Complex.I * k) i j *
        rdfPhase sigma (Complex.I * k) j j := by
    funext a
    exact actualSourceDefect_entry z rho sigma hz hsigma a k hk i j
  rw [he]
  have hu := (((actualWronskianU_entry_contDiff z rho sigma (Complex.I * k) i j).differentiable
    (by simp) p).hasFDerivAt.const_mul (rdfPhase sigma (-(Complex.I * k)) i i)).mul_const
      (rdfPhase sigma (Complex.I * k) j j)
  have hw := (((actualWronskianV_entry_contDiff z rho sigma (Complex.I * k) i j).differentiable
    (by simp) p).hasFDerivAt.const_mul (rdfPhase sigma (Complex.I * k) i i)).mul_const
      (rdfPhase sigma (Complex.I * k) j j)
  have hd := congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ => L v) (hu.fun_add hw).fderiv
  simpa [h0.1, h0.2] using hd

/-- Actual Fourier Q is genuinely smooth in amplitudes at nonzero frequency;
the all-amplitude phase representation supplies the derivative existence. -/
theorem actualFourierQ_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierQ z rho sigma a.1 a.2 k i j) := by
  classical
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierQ z rho sigma a.1 a.2 k i j) =
      fun a => nonlinearPhaseQ sigma (nonlinearComplexJ z rho sigma a.1 a.2 (Complex.I * k))
        (nonlinearComplexL z rho sigma a.1 a.2 (Complex.I * k)) (Complex.I * k) i j := by
    funext a
    rw [nonlinearActualFourierQ_eq_phaseQ z rho sigma a.1 a.2 hz hsigma k hk]
  rw [he]
  simp only [nonlinearPhaseQ_entry]
  fun_prop

/-- The actual spectral Baxter C has genuine amplitude entry derivatives,
without imposing the BH root equations in a neighborhood. -/
theorem actualFourierC_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k i j) := by
  classical
  have hq (i j : Fin N) := actualFourierQ_entry_contDiff z rho sigma hz hsigma k hk i j
  have hm (i j : Fin N) := actualFourierQ_entry_contDiff z rho sigma hz hsigma (-k) (neg_ne_zero.mpr hk) i j
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k i j) =
      fun a => nonlinearActualFourierQ z rho sigma a.1 a.2 k i j +
        nonlinearActualFourierQ z rho sigma a.1 a.2 (-k) j i -
        ∑ m, nonlinearActualFourierQ z rho sigma a.1 a.2 k i m * (rho m : ℂ) *
          nonlinearActualFourierQ z rho sigma a.1 a.2 (-k) j m := by
    funext a
    rw [nonlinearActualFourierC_eq_Q_product]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply,
      Matrix.mul_apply (M := nonlinearActualFourierQ z rho sigma a.1 a.2 k * Matrix.diagonal (fun l => (rho l : ℂ))),
      Matrix.mul_diagonal]
  rw [he]
  exact ((hq i j).add (hm j i)).sub (ContDiff.sum fun m _ => ((hq i m).mul contDiff_const).mul (hm j m))

/-- The sum of the two ACTUAL source defects is the fixed-frequency multiple
of the spectral Baxter C transpose defect, at arbitrary amplitudes. -/
theorem actualSourceDefect_sum (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ) :
    actualSourceDefect z rho sigma p k + actualSourceDefect z rho sigma p (-k) =
      (Complex.I * k) • ((nonlinearActualFourierC z rho sigma p.1 p.2 k).transpose -
        nonlinearActualFourierC z rho sigma p.1 p.2 k) := by
  classical
  rw [← nonlinearActualFourierC_neg_transpose]
  simp only [actualSourceDefect, Complex.ofReal_neg, mul_neg, neg_neg]
  module

/-- The actual spectral Baxter C variation is symmetric at each nonzero real
wave number along every actual BH Jacobian kernel direction. This is not
an assumed differentiation of the root-only spectral reciprocity theorem. -/
theorem actual_kernel_fourierC_fderiv_symmetric
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hkern : amplitudeJacobian z rho sigma K t p v = 0)
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    fderiv ℝ (fun a => nonlinearActualFourierC z rho sigma a.1 a.2 k i j) p v =
      fderiv ℝ (fun a => nonlinearActualFourierC z rho sigma a.1 a.2 k j i) p v := by
  have hs : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
        actualSourceDefect z rho sigma a k i j + actualSourceDefect z rho sigma a (-k) i j) =
      fun a => (Complex.I * k) * (nonlinearActualFourierC z rho sigma a.1 a.2 k j i -
        nonlinearActualFourierC z rho sigma a.1 a.2 k i j) := by
    funext a
    have h := congrFun (congrFun (actualSourceDefect_sum z rho sigma a k) i) j
    simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
      Matrix.transpose_apply] using h
  have hp := ((actualSourceDefect_entry_contDiff z rho sigma hz hsigma k hk i j).differentiable
    (by simp) p).hasFDerivAt
  have hm := ((actualSourceDefect_entry_contDiff z rho sigma hz hsigma (-k) (neg_ne_zero.mpr hk) i j).differentiable
    (by simp) p).hasFDerivAt
  have hleft := congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ => L v) (hp.fun_add hm).fderiv
  have hl0 : fderiv ℝ (fun a => actualSourceDefect z rho sigma a k i j +
      actualSourceDefect z rho sigma a (-k) i j) p v = 0 := by
    simpa only [add_apply,
      actual_kernel_sourceDefect_fderiv_zero z rho sigma K hK hz hsigma hv t p v hroot hkern k hk i j,
      actual_kernel_sourceDefect_fderiv_zero z rho sigma K hK hz hsigma hv t p v hroot hkern (-k) (neg_ne_zero.mpr hk) i j,
      add_zero] using hleft
  have hcij := ((actualFourierC_entry_contDiff z rho sigma hz hsigma k hk i j).differentiable
    (by simp) p).hasFDerivAt
  have hcji := ((actualFourierC_entry_contDiff z rho sigma hz hsigma k hk j i).differentiable
    (by simp) p).hasFDerivAt
  have hright := congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ => L v)
    ((hcji.fun_sub hcij).const_mul (Complex.I * k)).fderiv
  rw [he] at hl0
  have hz0 : (Complex.I * k) *
      (fderiv ℝ (fun a => nonlinearActualFourierC z rho sigma a.1 a.2 k j i) p v -
        fderiv ℝ (fun a => nonlinearActualFourierC z rho sigma a.1 a.2 k i j) p v) = 0 := by
    simpa only [smul_apply, smul_eq_mul, sub_apply] using hright.symm.trans hl0
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hz0).resolve_left hs)).symm

end FMSA.Convergence.ComplexWronskianJets

/-- info: 'FMSA.Convergence.ComplexWronskianJets.variation_complex_eval_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.variation_complex_eval_fderiv

/-- info: 'FMSA.Convergence.ComplexWronskianJets.coeffSmooth_complex_eval_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.coeffSmooth_complex_eval_contDiff

/-- info: 'FMSA.Convergence.ComplexWronskianJets.complex_ofReal_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.complex_ofReal_contDiff

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actual_kernel_complex_polynomial_eval_fderiv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actual_kernel_complex_polynomial_eval_fderiv_zero

/-- info: 'FMSA.Convergence.ComplexWronskianJets.distinctRatePolynomial_complex_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.distinctRatePolynomial_complex_eval

/-- info: 'FMSA.Convergence.ComplexWronskianJets.distinctRateExcept_complex_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.distinctRateExcept_complex_eval

/-- info: 'FMSA.Convergence.ComplexWronskianJets.distinctDenominator_complex_eval_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.distinctDenominator_complex_eval_ne_zero

/-- info: 'FMSA.Convergence.ComplexWronskianJets.distinctJNumerator_complex_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.distinctJNumerator_complex_eval

/-- info: 'FMSA.Convergence.ComplexWronskianJets.distinctLNumerator_complex_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.distinctLNumerator_complex_eval

/-- info: 'FMSA.Convergence.ComplexWronskianJets.distinctUPolynomial_complex_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.distinctUPolynomial_complex_eval

/-- info: 'FMSA.Convergence.ComplexWronskianJets.distinctVPolynomial_complex_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.distinctVPolynomial_complex_eval

/-- info: 'FMSA.Convergence.ComplexWronskianJets.complexJ_entry_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.complexJ_entry_contDiff

/-- info: 'FMSA.Convergence.ComplexWronskianJets.complexL_entry_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.complexL_entry_contDiff

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actualWronskianU_entry_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actualWronskianU_entry_contDiff

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actualWronskianV_entry_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actualWronskianV_entry_contDiff

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actual_kernel_complex_wronskian_fderiv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actual_kernel_complex_wronskian_fderiv_zero

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actualSourceDefect_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actualSourceDefect_factorization

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actualSourceDefect_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actualSourceDefect_entry

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actualSourceDefect_entry_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actualSourceDefect_entry_contDiff

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actual_kernel_sourceDefect_fderiv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actual_kernel_sourceDefect_fderiv_zero

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actualFourierQ_entry_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actualFourierQ_entry_contDiff

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actualFourierC_entry_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actualFourierC_entry_contDiff

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actualSourceDefect_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actualSourceDefect_sum

/-- info: 'FMSA.Convergence.ComplexWronskianJets.actual_kernel_fourierC_fderiv_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexWronskianJets.actual_kernel_fourierC_fderiv_symmetric
