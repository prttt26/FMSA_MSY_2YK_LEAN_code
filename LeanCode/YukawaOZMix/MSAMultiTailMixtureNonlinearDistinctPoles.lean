import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearPolePolynomial
import Mathlib.Tactic.ComputeDegree

/-! Common denominator over rate values, rather than tail labels.
Repeated rates retain all physical contributions in the numerators and
contribute just one denominator factor. -/
noncomputable section
open Real Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def nonlinearDistinctRates (z : ι → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image z

def nonlinearDistinctRatePolynomial (z : ι → ℝ) : Polynomial ℝ :=
  ∏ r ∈ nonlinearDistinctRates z, (X + Polynomial.C r)

def nonlinearDistinctRatePolynomialExcept (z : ι → ℝ) (r : ℝ) : Polynomial ℝ := by
  classical
  exact ∏ t ∈ (nonlinearDistinctRates z).erase r, (X + Polynomial.C t)

def nonlinearDistinctDenominator (z : ι → ℝ) : Polynomial ℝ :=
  X^2 * nonlinearDistinctRatePolynomial z

def nonlinearDistinctJNumerator (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : Polynomial ℝ :=
  (Polynomial.C (amplitudeA z ρ σ Dt G j) +
    Polynomial.C (amplitudeQp z ρ σ Dt G i j) * X) * nonlinearDistinctRatePolynomial z +
  ∑ u, Polynomial.C (z u * C z ρ σ Dt G u i j) * X^2 *
    nonlinearDistinctRatePolynomialExcept z (z u)

def nonlinearDistinctLNumerator (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : Polynomial ℝ :=
  (Polynomial.C (amplitudeA z ρ σ Dt G j) +
    Polynomial.C (amplitudeQp z ρ σ Dt G i j - σ i * amplitudeA z ρ σ Dt G j) * X +
    Polynomial.C (nonlinearLowerQValue z ρ σ Dt G i j) * X^2) *
      nonlinearDistinctRatePolynomial z -
  ∑ u, Polynomial.C (z u * W z ρ Dt G u i j) * X^2 *
    nonlinearDistinctRatePolynomialExcept z (z u)

theorem nonlinearDistinctRates_mem (z : ι → ℝ) (u : ι) :
    z u ∈ nonlinearDistinctRates z := by
  classical
  exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩

theorem nonlinearDistinctRates_positive (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (r : ℝ) (hr : r ∈ nonlinearDistinctRates z) : 0 < r := by
  classical
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hr
  exact hz u

theorem nonlinearDistinctRatePolynomial_factor (z : ι → ℝ) (r : ℝ)
    (hr : r ∈ nonlinearDistinctRates z) :
    (X + Polynomial.C r) * nonlinearDistinctRatePolynomialExcept z r =
      nonlinearDistinctRatePolynomial z := by
  classical
  exact Finset.mul_prod_erase (f := fun t => X + Polynomial.C t) _ hr

theorem nonlinearDistinctRatePolynomial_monic (z : ι → ℝ) :
    (nonlinearDistinctRatePolynomial z).Monic := by
  exact Polynomial.monic_prod_of_monic _ _ (fun r _ => Polynomial.monic_X_add_C r)

theorem nonlinearDistinctRatePolynomial_degree (z : ι → ℝ) :
    (nonlinearDistinctRatePolynomial z).natDegree = (nonlinearDistinctRates z).card := by
  rw [nonlinearDistinctRatePolynomial, Polynomial.natDegree_prod_of_monic _ _
    (fun r _ => Polynomial.monic_X_add_C r)]
  simp

theorem nonlinearDistinctRatePolynomialExcept_degree (z : ι → ℝ) (r : ℝ)
    (hr : r ∈ nonlinearDistinctRates z) :
    (nonlinearDistinctRatePolynomialExcept z r).natDegree =
      (nonlinearDistinctRates z).card - 1 := by
  classical
  rw [nonlinearDistinctRatePolynomialExcept, Polynomial.natDegree_prod_of_monic _ _
    (fun r _ => Polynomial.monic_X_add_C r)]
  simp [Finset.card_erase_of_mem hr]

theorem nonlinearDistinctRatePolynomial_eval (z : ι → ℝ) (s : ℝ) :
    (nonlinearDistinctRatePolynomial z).eval s = ∏ r ∈ nonlinearDistinctRates z, (s+r) := by
  simp only [nonlinearDistinctRatePolynomial, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

theorem nonlinearDistinctRatePolynomial_eval_neg_rate (z : ι → ℝ)
    (r : ℝ) (hr : r ∈ nonlinearDistinctRates z) :
    (nonlinearDistinctRatePolynomial z).eval (-r) = 0 := by
  rw [nonlinearDistinctRatePolynomial_eval]
  exact Finset.prod_eq_zero hr (by simp)

theorem nonlinearDistinctRatePolynomialExcept_eval_other_neg_rate
    (z : ι → ℝ) (r t : ℝ) (hr : r ∈ nonlinearDistinctRates z) (hrt : r ≠ t) :
    (nonlinearDistinctRatePolynomialExcept z t).eval (-r) = 0 := by
  classical
  simp only [nonlinearDistinctRatePolynomialExcept, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hrt, hr⟩) (by simp)

theorem nonlinearDistinctDenominator_eval_ne_zero (z : ι → ℝ) (s : ℝ)
    (hs : s ≠ 0) (hsp : ∀ u, s + z u ≠ 0) :
    (nonlinearDistinctDenominator z).eval s ≠ 0 := by
  simp only [nonlinearDistinctDenominator, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, nonlinearDistinctRatePolynomial_eval]
  apply mul_ne_zero (pow_ne_zero _ hs)
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  classical
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hr
  exact hsp u

theorem nonlinearDistinctJNumerator_eval (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (s : ℝ) (hs : s ≠ 0)
    (hsp : ∀ u, s + z u ≠ 0) (i j : Fin N) :
    (nonlinearDistinctJNumerator z ρ σ Dt G i j).eval s =
      (nonlinearDistinctDenominator z).eval s * nonlinearRationalJ z ρ σ Dt G s i j := by
  have hf (u : ι) := congrArg (Polynomial.eval s)
    (nonlinearDistinctRatePolynomial_factor z (z u) (nonlinearDistinctRates_mem z u))
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C] at hf
  have ht (u : ι) : z u*C z ρ σ Dt G u i j*s^2*
      (nonlinearDistinctRatePolynomialExcept z (z u)).eval s =
      s^2*(nonlinearDistinctRatePolynomial z).eval s*
        (z u*C z ρ σ Dt G u i j/(s+z u)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (hsp u)).mpr
    linear_combination z u*C z ρ σ Dt G u i j*s^2*hf u
  simp only [nonlinearDistinctJNumerator, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_finset_sum,
    nonlinearDistinctDenominator, nonlinearRationalJ, Matrix.of_apply, ht]
  rw [← Finset.mul_sum]
  field_simp [hs] <;> ring

theorem nonlinearDistinctLNumerator_eval (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (s : ℝ) (hs : s ≠ 0)
    (hsp : ∀ u, s + z u ≠ 0) (i j : Fin N) :
    (nonlinearDistinctLNumerator z ρ σ Dt G i j).eval s =
      (nonlinearDistinctDenominator z).eval s * nonlinearRationalL z ρ σ Dt G s i j := by
  have hf (u : ι) := congrArg (Polynomial.eval s)
    (nonlinearDistinctRatePolynomial_factor z (z u) (nonlinearDistinctRates_mem z u))
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C] at hf
  have ht (u : ι) : z u*W z ρ Dt G u i j*s^2*
      (nonlinearDistinctRatePolynomialExcept z (z u)).eval s =
      s^2*(nonlinearDistinctRatePolynomial z).eval s*
        (z u*W z ρ Dt G u i j/(s+z u)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (hsp u)).mpr
    linear_combination z u*W z ρ Dt G u i j*s^2*hf u
  simp only [nonlinearDistinctLNumerator, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
    Polynomial.eval_finset_sum, nonlinearDistinctDenominator, nonlinearRationalL,
    Matrix.of_apply, ht]
  rw [← Finset.mul_sum]
  field_simp [hs] <;> ring

theorem nonlinearDistinctDenominator_degree (z : ι → ℝ) :
    (nonlinearDistinctDenominator z).natDegree = (nonlinearDistinctRates z).card + 2 := by
  rw [nonlinearDistinctDenominator, Polynomial.natDegree_mul
    (pow_ne_zero _ Polynomial.X_ne_zero) (nonlinearDistinctRatePolynomial_monic z).ne_zero,
    Polynomial.natDegree_X_pow, nonlinearDistinctRatePolynomial_degree]
  omega

theorem nonlinearDistinctJNumerator_degree_le (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    (nonlinearDistinctJNumerator z ρ σ Dt G i j).natDegree ≤
      (nonlinearDistinctRates z).card + 1 := by
  have hlin : (Polynomial.C (amplitudeA z ρ σ Dt G j) +
      Polynomial.C (amplitudeQp z ρ σ Dt G i j) * X).natDegree ≤ 1 := by
    compute_degree
  have hf : ((Polynomial.C (amplitudeA z ρ σ Dt G j) +
      Polynomial.C (amplitudeQp z ρ σ Dt G i j) * X) *
      nonlinearDistinctRatePolynomial z).natDegree ≤ (nonlinearDistinctRates z).card + 1 := by
    apply Polynomial.natDegree_mul_le.trans
    rw [nonlinearDistinctRatePolynomial_degree]
    omega
  have ht (u : ι) : (Polynomial.C (z u * C z ρ σ Dt G u i j) * X^2 *
      nonlinearDistinctRatePolynomialExcept z (z u)).natDegree ≤
        (nonlinearDistinctRates z).card + 1 := by
    have hp : (Polynomial.C (z u * C z ρ σ Dt G u i j) * X^2).natDegree ≤ 2 := by
      compute_degree
    have hc : 1 ≤ (nonlinearDistinctRates z).card :=
      Finset.card_pos.mpr ⟨z u, nonlinearDistinctRates_mem z u⟩
    apply Polynomial.natDegree_mul_le.trans
    rw [nonlinearDistinctRatePolynomialExcept_degree z (z u) (nonlinearDistinctRates_mem z u)]
    omega
  apply le_trans (Polynomial.natDegree_add_le _ _)
  exact max_le hf (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun u _ => ht u))

theorem nonlinearDistinctLNumerator_degree_le (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    (nonlinearDistinctLNumerator z ρ σ Dt G i j).natDegree ≤
      (nonlinearDistinctRates z).card + 2 := by
  have hlin : (Polynomial.C (amplitudeA z ρ σ Dt G j) +
      Polynomial.C (amplitudeQp z ρ σ Dt G i j - σ i * amplitudeA z ρ σ Dt G j) * X +
      Polynomial.C (nonlinearLowerQValue z ρ σ Dt G i j) * X^2).natDegree ≤ 2 := by
    compute_degree
  have hf : ((Polynomial.C (amplitudeA z ρ σ Dt G j) +
      Polynomial.C (amplitudeQp z ρ σ Dt G i j - σ i * amplitudeA z ρ σ Dt G j) * X +
      Polynomial.C (nonlinearLowerQValue z ρ σ Dt G i j) * X^2) *
      nonlinearDistinctRatePolynomial z).natDegree ≤ (nonlinearDistinctRates z).card + 2 := by
    apply Polynomial.natDegree_mul_le.trans
    rw [nonlinearDistinctRatePolynomial_degree]
    omega
  have ht (u : ι) : (Polynomial.C (z u * W z ρ Dt G u i j) * X^2 *
      nonlinearDistinctRatePolynomialExcept z (z u)).natDegree ≤
        (nonlinearDistinctRates z).card + 2 := by
    have hp : (Polynomial.C (z u * W z ρ Dt G u i j) * X^2).natDegree ≤ 2 := by
      compute_degree
    apply Polynomial.natDegree_mul_le.trans
    rw [nonlinearDistinctRatePolynomialExcept_degree z (z u) (nonlinearDistinctRates_mem z u)]
    omega
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  exact max_le hf (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun u _ => ht u))

end FMSA.ExactMSA.MultiTailMixture
