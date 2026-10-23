import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearReciprocity
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-! Finite polynomial coefficient certificate for nonlinear Laplace reciprocity.
No distinctness of rates is required: every labelled factor is retained. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def nonlinearRatePolynomial (z : ι → ℝ) : Polynomial ℝ := ∏ u, (X+Polynomial.C (z u))
def nonlinearRatePolynomialExcept (z : ι → ℝ) (u : ι) : Polynomial ℝ :=
  ∏ v ∈ Finset.univ.erase u, (X+Polynomial.C (z v))
def nonlinearRationalDenominator (z : ι → ℝ) : Polynomial ℝ := X^2*nonlinearRatePolynomial z

def nonlinearJNumerator (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) : Polynomial ℝ :=
  (Polynomial.C (amplitudeA z ρ σ Dt G j)+Polynomial.C (amplitudeQp z ρ σ Dt G i j)*X)*
    nonlinearRatePolynomial z+
  ∑ u, Polynomial.C (z u*C z ρ σ Dt G u i j)*X^2*nonlinearRatePolynomialExcept z u

def nonlinearLNumerator (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) : Polynomial ℝ :=
  (Polynomial.C (amplitudeA z ρ σ Dt G j)+
    Polynomial.C (amplitudeQp z ρ σ Dt G i j-σ i*amplitudeA z ρ σ Dt G j)*X+
    Polynomial.C (nonlinearLowerQValue z ρ σ Dt G i j)*X^2)*nonlinearRatePolynomial z-
  ∑ u, Polynomial.C (z u*W z ρ Dt G u i j)*X^2*nonlinearRatePolynomialExcept z u

theorem nonlinearRatePolynomial_eval (z : ι → ℝ) (s : ℝ) :
    (nonlinearRatePolynomial z).eval s=∏ u, (s+z u) := by
  simp only [nonlinearRatePolynomial, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]

theorem nonlinearRatePolynomialExcept_eval (z : ι → ℝ) (s : ℝ) (u : ι) :
    (s+z u)*(nonlinearRatePolynomialExcept z u).eval s=(nonlinearRatePolynomial z).eval s := by
  simp only [nonlinearRatePolynomialExcept, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, nonlinearRatePolynomial_eval]
  exact Finset.mul_prod_erase (f := fun v => s+z v) Finset.univ (Finset.mem_univ u)

theorem nonlinearRationalDenominator_eval_pos (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (s : ℝ) (hs : 0 < s) : 0 < (nonlinearRationalDenominator z).eval s := by
  simp only [nonlinearRationalDenominator, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, nonlinearRatePolynomial_eval]
  exact mul_pos (sq_pos_of_pos hs) (Finset.prod_pos (fun u _ => add_pos hs (hz u)))

theorem nonlinearJNumerator_eval (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (s : ℝ) (hs : 0 < s) (i j : Fin N) :
    (nonlinearJNumerator z ρ σ Dt G i j).eval s=
      (nonlinearRationalDenominator z).eval s*nonlinearRationalJ z ρ σ Dt G s i j := by
  have ht (u : ι) : z u*C z ρ σ Dt G u i j*s^2*(nonlinearRatePolynomialExcept z u).eval s=
      s^2*(nonlinearRatePolynomial z).eval s*(z u*C z ρ σ Dt G u i j/(s+z u)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (add_pos hs (hz u)).ne').mpr
    linear_combination z u*C z ρ σ Dt G u i j*s^2*nonlinearRatePolynomialExcept_eval z s u
  simp only [nonlinearJNumerator, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_finset_sum,
    nonlinearRationalDenominator, nonlinearRationalJ, Matrix.of_apply, ht]
  rw [← Finset.mul_sum]
  field_simp [hs.ne']
  <;> ring

theorem nonlinearLNumerator_eval (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (s : ℝ) (hs : 0 < s) (i j : Fin N) :
    (nonlinearLNumerator z ρ σ Dt G i j).eval s=
      (nonlinearRationalDenominator z).eval s*nonlinearRationalL z ρ σ Dt G s i j := by
  have ht (u : ι) : z u*W z ρ Dt G u i j*s^2*(nonlinearRatePolynomialExcept z u).eval s=
      s^2*(nonlinearRatePolynomial z).eval s*(z u*W z ρ Dt G u i j/(s+z u)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (add_pos hs (hz u)).ne').mpr
    linear_combination z u*W z ρ Dt G u i j*s^2*nonlinearRatePolynomialExcept_eval z s u
  simp only [nonlinearLNumerator, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_finset_sum,
    nonlinearRationalDenominator, nonlinearRationalL, Matrix.of_apply, ht]
  rw [← Finset.mul_sum]
  field_simp [hs.ne']
  <;> ring

def nonlinearReciprocityPolynomial (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : Polynomial ℝ :=
  (nonlinearJNumerator z ρ σ Dt G i j-nonlinearJNumerator z ρ σ Dt G j i)*X*
    nonlinearRationalDenominator z+
  ∑ m, Polynomial.C (ρ m)*(nonlinearJNumerator z ρ σ Dt G m i*nonlinearLNumerator z ρ σ Dt G m j-
    nonlinearLNumerator z ρ σ Dt G m i*nonlinearJNumerator z ρ σ Dt G m j)

theorem nonlinearReciprocityResidual_entry (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (s : ℝ) (i j : Fin N) :
    nonlinearRationalReciprocityResidual z ρ σ Dt G s i j=
      nonlinearRationalJ z ρ σ Dt G s i j-nonlinearRationalJ z ρ σ Dt G s j i+
      (∑ m, ρ m*(nonlinearRationalJ z ρ σ Dt G s m i*nonlinearRationalL z ρ σ Dt G s m j-
        nonlinearRationalL z ρ σ Dt G s m i*nonlinearRationalJ z ρ σ Dt G s m j))/s := by
  simp only [nonlinearRationalReciprocityResidual, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, inv_mul_eq_div, Matrix.transpose_apply,
    Matrix.mul_apply (M := (nonlinearRationalJ z ρ σ Dt G s).transpose*Matrix.diagonal ρ),
    Matrix.mul_apply (M := (nonlinearRationalL z ρ σ Dt G s).transpose*Matrix.diagonal ρ)]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  congr 1
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem nonlinearReciprocityPolynomial_eval (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (s : ℝ) (hs : 0 < s) (i j : Fin N) :
    (nonlinearReciprocityPolynomial z ρ σ Dt G i j).eval s=
      s*((nonlinearRationalDenominator z).eval s)^2*nonlinearRationalReciprocityResidual z ρ σ Dt G s i j := by
  simp only [nonlinearReciprocityPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finset_sum,
    nonlinearJNumerator_eval z ρ σ Dt G hz s hs, nonlinearLNumerator_eval z ρ σ Dt G hz s hs,
    nonlinearReciprocityResidual_entry, mul_add, Finset.mul_sum]
  have he : (∑ m, ρ m*((nonlinearRationalDenominator z).eval s*nonlinearRationalJ z ρ σ Dt G s m i*
      ((nonlinearRationalDenominator z).eval s*nonlinearRationalL z ρ σ Dt G s m j)-
      (nonlinearRationalDenominator z).eval s*nonlinearRationalL z ρ σ Dt G s m i*
      ((nonlinearRationalDenominator z).eval s*nonlinearRationalJ z ρ σ Dt G s m j)))=
      ((nonlinearRationalDenominator z).eval s)^2*∑ m, ρ m*(nonlinearRationalJ z ρ σ Dt G s m i*
        nonlinearRationalL z ρ σ Dt G s m j-nonlinearRationalL z ρ σ Dt G s m i*nonlinearRationalJ z ρ σ Dt G s m j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [he]
  field_simp [hs.ne']
  <;> ring

/-- Finite exact coefficient check; evaluating a few floats is not this premise. -/
def NonlinearFiniteReciprocityCertificate (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) : Prop :=
  ∀ i j, ∀ n ∈ Finset.range ((nonlinearReciprocityPolynomial z ρ σ Dt G i j).natDegree+1),
    (nonlinearReciprocityPolynomial z ρ σ Dt G i j).coeff n=0

theorem nonlinear_finite_certificate_polynomial_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hcert : NonlinearFiniteReciprocityCertificate z ρ σ Dt G)
    (i j : Fin N) : nonlinearReciprocityPolynomial z ρ σ Dt G i j=0 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  by_cases hn : n<(nonlinearReciprocityPolynomial z ρ σ Dt G i j).natDegree+1
  · exact hcert i j n (Finset.mem_range.mpr hn)
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem nonlinear_finite_certificate_residual_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u)
    (hcert : NonlinearFiniteReciprocityCertificate z ρ σ Dt G) (s : ℝ) (hs : 0 < s) :
    nonlinearRationalReciprocityResidual z ρ σ Dt G s=0 := by
  ext i j
  have he := nonlinearReciprocityPolynomial_eval z ρ σ Dt G hz s hs i j
  rw [nonlinear_finite_certificate_polynomial_zero z ρ σ Dt G hcert, Polynomial.eval_zero] at he
  have hd := nonlinearRationalDenominator_eval_pos z hz s hs
  exact (mul_eq_zero.mp he.symm).resolve_left (by positivity)

theorem nonlinear_finite_certificate_actual_laplace_reciprocity (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hcert : NonlinearFiniteReciprocityCertificate z ρ σ Dt G) (s : ℝ) (hs : 0 < s) :
    (realMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s).transpose=
      realMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s :=
  (nonlinear_actual_laplace_reciprocity_iff z ρ σ Dt G hz hσ hv δ hδ hδz hb s hs).mp
    (nonlinear_finite_certificate_residual_zero z ρ σ Dt G hz hcert s hs)

theorem nonlinear_finite_certificate_iff_all_positive_residuals (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) :
    NonlinearFiniteReciprocityCertificate z ρ σ Dt G ↔
      ∀ s, 0 < s → nonlinearRationalReciprocityResidual z ρ σ Dt G s=0 := by
  constructor
  · exact fun h s hs => nonlinear_finite_certificate_residual_zero z ρ σ Dt G hz h s hs
  · intro h i j n _
    have hp : nonlinearReciprocityPolynomial z ρ σ Dt G i j=0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.Ioi_infinite (0 : ℝ)).mono
      intro s hs
      change (nonlinearReciprocityPolynomial z ρ σ Dt G i j).eval s=0
      rw [nonlinearReciprocityPolynomial_eval z ρ σ Dt G hz s hs,
        h s hs, Matrix.zero_apply, mul_zero]
    rw [hp, Polynomial.coeff_zero]

theorem nonlinear_failed_finite_certificate_excludes_pair_reciprocity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u)
    (hσ : ∀ i, 0 < σ i) (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ)
    (hδz : ∀ u, δ < z u) (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hfail : ¬NonlinearFiniteReciprocityCertificate z ρ σ Dt G) :
    ¬∀ i j r, 0 < r → nonlinearG z ρ σ Dt G i j r=nonlinearG z ρ σ Dt G j i r := by
  rw [nonlinear_finite_certificate_iff_all_positive_residuals z ρ σ Dt G hz] at hfail
  push_neg at hfail
  obtain ⟨s, hs, hres⟩ := hfail
  exact nonlinear_nonzero_residual_excludes_pair_reciprocity z ρ σ Dt G hz hσ hv δ hδ hδz hb s hs hres

end FMSA.ExactMSA.MultiTailMixture
