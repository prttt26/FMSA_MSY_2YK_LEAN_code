import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearWronskianAlgebra

/-! Exact finite coefficient conditions for both nonlinear Wronskian residuals.
They are admissibility checks on BH coefficients, not supplied OZ premises. -/
noncomputable section
open MeasureTheory Set Real Filter Topology Polynomial
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def nonlinearWronskianUPolynomial (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : Polynomial ℝ :=
  -nonlinearLNumerator z ρ σ Dt G i j*X*(nonlinearRationalDenominator z).comp (-X)+
    (nonlinearLNumerator z ρ σ Dt G j i).comp (-X)*X*nonlinearRationalDenominator z+
    ∑ m, Polynomial.C (ρ m)*((nonlinearJNumerator z ρ σ Dt G i m).comp (-X)*
      nonlinearJNumerator z ρ σ Dt G j m-nonlinearLNumerator z ρ σ Dt G i m*
      (nonlinearLNumerator z ρ σ Dt G j m).comp (-X))

def nonlinearWronskianVPolynomial (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : Polynomial ℝ :=
  (nonlinearJNumerator z ρ σ Dt G i j-nonlinearJNumerator z ρ σ Dt G j i)*X*
    (nonlinearRationalDenominator z).comp (-X)+
    ∑ m, Polynomial.C (ρ m)*(nonlinearJNumerator z ρ σ Dt G i m*
      (nonlinearLNumerator z ρ σ Dt G j m).comp (-X)-
      (nonlinearLNumerator z ρ σ Dt G i m).comp (-X)*nonlinearJNumerator z ρ σ Dt G j m)

def NonlinearFiniteWronskianCertificate (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) : Prop :=
  (∀ i j, ∀ n ∈ Finset.range ((nonlinearWronskianUPolynomial z ρ σ Dt G i j).natDegree+1),
    (nonlinearWronskianUPolynomial z ρ σ Dt G i j).coeff n=0) ∧
  (∀ i j, ∀ n ∈ Finset.range ((nonlinearWronskianVPolynomial z ρ σ Dt G i j).natDegree+1),
    (nonlinearWronskianVPolynomial z ρ σ Dt G i j).coeff n=0)

theorem finite_polynomial_zero_of_coefficients (p : Polynomial ℝ)
    (h : ∀ n ∈ Finset.range (p.natDegree+1), p.coeff n=0) : p=0 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  by_cases hn : n<p.natDegree+1
  · exact h n (Finset.mem_range.mpr hn)
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem nonlinearWronskianU_entry (J L Jm Lm : Matrix (Fin N) (Fin N) ℂ)
    (d : Fin N → ℂ) (s : ℂ) (i j : Fin N) :
    nonlinearWronskianU J L Jm Lm d s i j=
      -L i j+Lm j i+(∑ m, d m*(Jm i m*J j m-L i m*Lm j m))/s := by
  simp only [nonlinearWronskianU, Matrix.add_apply, Matrix.neg_apply,
    Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, inv_mul_eq_div,
    Matrix.mul_apply (M := Jm*Matrix.diagonal d), Matrix.mul_apply (M := L*Matrix.diagonal d)]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  congr 1
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _; ring

theorem nonlinearWronskianV_entry (J L Lm : Matrix (Fin N) (Fin N) ℂ)
    (d : Fin N → ℂ) (s : ℂ) (i j : Fin N) :
    nonlinearWronskianV J L Lm d s i j=
      J i j-J j i+(∑ m, d m*(J i m*Lm j m-Lm i m*J j m))/s := by
  simp only [nonlinearWronskianV, Matrix.add_apply, Matrix.sub_apply,
    Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, inv_mul_eq_div,
    Matrix.mul_apply (M := J*Matrix.diagonal d), Matrix.mul_apply (M := Lm*Matrix.diagonal d)]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  congr 1
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _; ring

theorem polynomial_complex_eval_neg_comp (p : Polynomial ℝ) (s : ℂ) :
    (p.comp (-X)).eval₂ (algebraMap ℝ ℂ) s=p.eval₂ (algebraMap ℝ ℂ) (-s) := by
  rw [Polynomial.eval₂_comp]
  simp

theorem nonlinearWronskianUPolynomial_complex_eval (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (s : ℂ)
    (hs : s ≠ 0) (hsre : s.re=0) (i j : Fin N) :
    (nonlinearWronskianUPolynomial z ρ σ Dt G i j).eval₂ (algebraMap ℝ ℂ) s=
      s*(nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s*
        (nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) (-s)*
        nonlinearWronskianU (nonlinearComplexJ z ρ σ Dt G s) (nonlinearComplexL z ρ σ Dt G s)
          (nonlinearComplexJ z ρ σ Dt G (-s)) (nonlinearComplexL z ρ σ Dt G (-s))
          (fun i => (ρ i : ℂ)) s i j := by
  have hp : 0 ≤ s.re := by rw [hsre]
  have hm : 0 ≤ (-s).re := by simp [hsre]
  simp only [nonlinearWronskianUPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_neg, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_finset_sum, Complex.coe_algebraMap, polynomial_complex_eval_neg_comp,
    nonlinearJNumerator_complex_eval z ρ σ Dt G hz s hs hp,
    nonlinearLNumerator_complex_eval z ρ σ Dt G hz s hs hp,
    nonlinearJNumerator_complex_eval z ρ σ Dt G hz (-s) (neg_ne_zero.mpr hs) hm,
    nonlinearLNumerator_complex_eval z ρ σ Dt G hz (-s) (neg_ne_zero.mpr hs) hm,
    nonlinearWronskianU_entry]
  let D := (nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s
  let M := (nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) (-s)
  have he : (∑ m, (ρ m : ℂ)*(M*nonlinearComplexJ z ρ σ Dt G (-s) i m*
      (D*nonlinearComplexJ z ρ σ Dt G s j m)-D*nonlinearComplexL z ρ σ Dt G s i m*
      (M*nonlinearComplexL z ρ σ Dt G (-s) j m)))=
      D*M*∑ m, (ρ m : ℂ)*(nonlinearComplexJ z ρ σ Dt G (-s) i m*
        nonlinearComplexJ z ρ σ Dt G s j m-nonlinearComplexL z ρ σ Dt G s i m*
        nonlinearComplexL z ρ σ Dt G (-s) j m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _; ring
  rw [he]
  field_simp [hs]
  <;> ring

theorem nonlinearWronskianVPolynomial_complex_eval (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (s : ℂ)
    (hs : s ≠ 0) (hsre : s.re=0) (i j : Fin N) :
    (nonlinearWronskianVPolynomial z ρ σ Dt G i j).eval₂ (algebraMap ℝ ℂ) s=
      s*(nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s*
        (nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) (-s)*
        nonlinearWronskianV (nonlinearComplexJ z ρ σ Dt G s) (nonlinearComplexL z ρ σ Dt G s)
          (nonlinearComplexL z ρ σ Dt G (-s)) (fun i => (ρ i : ℂ)) s i j := by
  have hp : 0 ≤ s.re := by rw [hsre]
  have hm : 0 ≤ (-s).re := by simp [hsre]
  simp only [nonlinearWronskianVPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_neg, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_finset_sum, Complex.coe_algebraMap, polynomial_complex_eval_neg_comp,
    nonlinearJNumerator_complex_eval z ρ σ Dt G hz s hs hp,
    nonlinearLNumerator_complex_eval z ρ σ Dt G hz s hs hp,
    nonlinearLNumerator_complex_eval z ρ σ Dt G hz (-s) (neg_ne_zero.mpr hs) hm,
    nonlinearWronskianV_entry]
  let D := (nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s
  let M := (nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) (-s)
  have he : (∑ m, (ρ m : ℂ)*(D*nonlinearComplexJ z ρ σ Dt G s i m*
      (M*nonlinearComplexL z ρ σ Dt G (-s) j m)-M*nonlinearComplexL z ρ σ Dt G (-s) i m*
      (D*nonlinearComplexJ z ρ σ Dt G s j m)))=
      D*M*∑ m, (ρ m : ℂ)*(nonlinearComplexJ z ρ σ Dt G s i m*
        nonlinearComplexL z ρ σ Dt G (-s) j m-nonlinearComplexL z ρ σ Dt G (-s) i m*
        nonlinearComplexJ z ρ σ Dt G s j m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _; ring
  rw [he]
  field_simp [hs]
  <;> ring

theorem nonlinear_finite_wronskian_residuals_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u)
    (hc : NonlinearFiniteWronskianCertificate z ρ σ Dt G)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re=0) :
    nonlinearWronskianU (nonlinearComplexJ z ρ σ Dt G s) (nonlinearComplexL z ρ σ Dt G s)
      (nonlinearComplexJ z ρ σ Dt G (-s)) (nonlinearComplexL z ρ σ Dt G (-s))
      (fun i => (ρ i : ℂ)) s=0 ∧
    nonlinearWronskianV (nonlinearComplexJ z ρ σ Dt G s) (nonlinearComplexL z ρ σ Dt G s)
      (nonlinearComplexL z ρ σ Dt G (-s)) (fun i => (ρ i : ℂ)) s=0 := by
  have hd := nonlinearRationalDenominator_complex_eval_ne_zero z hz s hs (by rw [hsre])
  have hm := nonlinearRationalDenominator_complex_eval_ne_zero z hz (-s) (neg_ne_zero.mpr hs) (by simp [hsre])
  have hn : s*(nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) s*
      (nonlinearRationalDenominator z).eval₂ (algebraMap ℝ ℂ) (-s) ≠ 0 := mul_ne_zero (mul_ne_zero hs hd) hm
  constructor
  · ext i j
    have he := nonlinearWronskianUPolynomial_complex_eval z ρ σ Dt G hz s hs hsre i j
    rw [finite_polynomial_zero_of_coefficients _ (hc.1 i j), Polynomial.eval₂_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hn
  · ext i j
    have he := nonlinearWronskianVPolynomial_complex_eval z ρ σ Dt G hz s hs hsre i j
    rw [finite_polynomial_zero_of_coefficients _ (hc.2 i j), Polynomial.eval₂_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hn

end FMSA.ExactMSA.MultiTailMixture
