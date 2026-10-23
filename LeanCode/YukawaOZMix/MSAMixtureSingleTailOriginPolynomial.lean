import LeanCode.YukawaOZMix.MSAMixtureLegacyFourier

/-! Leading coefficients of the original single-tail Wronskian numerator. -/
noncomputable section
open Polynomial Real MSAMixture
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def legacyCubic (a b c d : ℝ) : Polynomial ℝ := Polynomial.C a+Polynomial.C b*X+Polynomial.C c*X^2+Polynomial.C d*X^3

def legacyQuadratic (a b c : ℝ) : Polynomial ℝ := Polynomial.C a+Polynomial.C b*X+Polynomial.C c*X^2

private theorem pair_coeff6 (a b c d e f g h i j x y z v : ℝ) :
    ((legacyQuadratic a b c).comp (-X)*legacyQuadratic d e f -
      legacyCubic g h i j*(legacyCubic x y z v).comp (-X)).coeff 6 = j*v := by
  simp only [legacyQuadratic, legacyCubic, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.pow_comp]
  conv_lhs => arg 1; ring_nf
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow, Polynomial.coeff_X_pow_mul,
    Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  norm_num <;> ring

private theorem linear_coeff6 (a b c d e f g h z : ℝ) :
    (-legacyCubic a b c d*X*(X^2*(X+Polynomial.C z)).comp (-X)+
      (legacyCubic e f g h).comp (-X)*X*(X^2*(X+Polynomial.C z))).coeff 6 = c+g-z*(d+h) := by
  simp only [legacyCubic, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.pow_comp]
  conv_lhs => arg 1; ring_nf
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow, Polynomial.coeff_X_pow_mul,
    Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  norm_num <;> ring

private theorem cubic_expansion (A d q z W : ℝ) :
    (Polynomial.C A+Polynomial.C d*X+Polynomial.C q*X^2)*(X+Polynomial.C z)-Polynomial.C (z*W)*X^2 =
      legacyCubic (z*A) (A+z*d) (d+z*q-z*W) q := by
  simp only [legacyCubic, map_add, map_sub, map_mul]
  ring

private theorem quadratic_expansion (A qp z Ct : ℝ) :
    (Polynomial.C A+Polynomial.C qp*X)*(X+Polynomial.C z)+Polynomial.C (z*Ct)*X^2 =
      legacyQuadratic (z*A) (A+z*qp) (qp+z*Ct) := by
  simp only [legacyQuadratic, map_add, map_mul]
  ring

theorem legacySingle_LNumerator (z : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    nonlinearLNumerator (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) i j =
      legacyCubic (z*AVec z ρ σ Gt Dt j)
        (AVec z ρ σ Gt Dt j+z*(qpMat z ρ σ Gt Dt i j-σ i*AVec z ρ σ Gt Dt j))
        (qpMat z ρ σ Gt Dt i j-σ i*AVec z ρ σ Gt Dt j+
          z*nonlinearLowerQValue (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) i j-
          z*Wt z ρ Gt Dt i j)
        (nonlinearLowerQValue (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) i j) := by
  simp only [nonlinearLNumerator, amplitudeA_single, amplitudeQp_single, W_single,
    nonlinearRatePolynomial, nonlinearRatePolynomialExcept, Finset.univ_unique,
    Finset.prod_singleton, Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty]
  simpa only [mul_one] using cubic_expansion _ _ _ z (Wt z ρ Gt Dt i j)

theorem legacySingle_JNumerator (z : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    nonlinearJNumerator (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) i j =
      legacyQuadratic (z*AVec z ρ σ Gt Dt j)
        (AVec z ρ σ Gt Dt j+z*qpMat z ρ σ Gt Dt i j)
        (qpMat z ρ σ Gt Dt i j+z*Ct z ρ σ Gt Dt i j) := by
  simp only [nonlinearJNumerator, amplitudeA_single, amplitudeQp_single, C_single,
    nonlinearRatePolynomial, nonlinearRatePolynomialExcept, Finset.univ_unique,
    Finset.prod_singleton, Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty]
  simpa only [mul_one] using quadratic_expansion _ _ z (Ct z ρ σ Gt Dt i j)

theorem legacySingle_U_coeff6 (z : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    (nonlinearWronskianUPolynomial (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) i j).coeff 6 =
      (qpMat z ρ σ Gt Dt i j-σ i*AVec z ρ σ Gt Dt j-z*Wt z ρ Gt Dt i j)+
      (qpMat z ρ σ Gt Dt j i-σ j*AVec z ρ σ Gt Dt i-z*Wt z ρ Gt Dt j i)+
      ∑ m, ρ m*nonlinearLowerQValue (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) i m*
        nonlinearLowerQValue (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) j m := by
  simp only [nonlinearWronskianUPolynomial, nonlinearRationalDenominator,
    nonlinearRatePolynomial, Finset.univ_unique, Finset.prod_singleton,
    legacySingle_LNumerator, legacySingle_JNumerator]
  rw [Polynomial.coeff_add, linear_coeff6]
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, pair_coeff6]
  rw [show (∑ m, ρ m*(nonlinearLowerQValue (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) i m*
    nonlinearLowerQValue (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) j m)) =
    ∑ m, ρ m*nonlinearLowerQValue (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) i m*
      nonlinearLowerQValue (fun _ : Unit => z) ρ σ (fun _ => Dt) (fun _ => Gt) j m by
    apply Finset.sum_congr rfl; intro m _; ring]
  ring

end FMSA.ExactMSA.MultiTailMixture
