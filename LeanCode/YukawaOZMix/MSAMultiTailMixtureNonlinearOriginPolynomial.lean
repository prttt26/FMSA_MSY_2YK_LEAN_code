import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearDistinctPoles
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearOriginExpansion

/-! Actual minimal J/L numerators agree with their origin jets modulo X^7.
The identities hold as polynomials, without a convergence assumption. -/
noncomputable section
open Polynomial Real
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def originTaylor4 (a : ℕ → ℝ) : Polynomial ℝ :=
  Polynomial.C (a 0)-Polynomial.C (a 1)*X+Polynomial.C (a 2)*X^2-
    Polynomial.C (a 3)*X^3+Polynomial.C (a 4)*X^4

theorem originTaylor4_resolvent (z a : ℝ) (hz : z ≠ 0) :
    (X+Polynomial.C z)*originTaylor4 (fun p => a/z^p) =
      Polynomial.C (z*a)+Polynomial.C (a/z^4)*X^5 := by
  apply Polynomial.funext
  intro s
  simp only [originTaylor4, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  field_simp [hz]
  ring

theorem originTaylor4_sum (a : ι → ℕ → ℝ) :
    (∑ u, originTaylor4 (a u)) = originTaylor4 (fun p => ∑ u, a u p) := by
  simp only [originTaylor4, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    map_sum, Finset.sum_mul]

theorem nonlinearDistinct_tail_polynomial_origin (z : ι → ℝ) (a : ι → ℝ)
    (hz : ∀ u, z u ≠ 0) :
    (∑ u, Polynomial.C (z u*a u)*nonlinearDistinctRatePolynomialExcept z (z u)) =
      nonlinearDistinctRatePolynomial z*originTaylor4 (fun p => ∑ u, a u/(z u)^p) -
      X^5*(∑ u, Polynomial.C (a u/(z u)^4)*nonlinearDistinctRatePolynomialExcept z (z u)) := by
  classical
  have ht (u : ι) : Polynomial.C (z u*a u)*nonlinearDistinctRatePolynomialExcept z (z u) =
      nonlinearDistinctRatePolynomial z*originTaylor4 (fun p => a u/(z u)^p) -
      X^5*(Polynomial.C (a u/(z u)^4)*nonlinearDistinctRatePolynomialExcept z (z u)) := by
    have he := congrArg (fun p : Polynomial ℝ => p*nonlinearDistinctRatePolynomialExcept z (z u))
      (originTaylor4_resolvent (z u) (a u) (hz u))
    rw [← nonlinearDistinctRatePolynomial_factor z (z u) (nonlinearDistinctRates_mem z u)]
    linear_combination -he
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, originTaylor4_sum]

def originJJet (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) : Polynomial ℝ :=
  Polynomial.C (amplitudeA z ρ σ Dt G j) + Polynomial.C (amplitudeQp z ρ σ Dt G i j)*X +
    X^2*originTaylor4 (fun p => nonlinearOriginCmoment z ρ σ Dt G p i j)

def originLJet (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) : Polynomial ℝ :=
  Polynomial.C (amplitudeA z ρ σ Dt G j) +
    Polynomial.C (amplitudeQp z ρ σ Dt G i j-σ i*amplitudeA z ρ σ Dt G j)*X +
    Polynomial.C (nonlinearLowerQValue z ρ σ Dt G i j)*X^2 -
    X^2*originTaylor4 (fun p => nonlinearOriginWmoment z ρ Dt G p i j)

def originCRemainderPolynomial (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : Polynomial ℝ :=
  ∑ u, Polynomial.C (C z ρ σ Dt G u i j/(z u)^4)*
    nonlinearDistinctRatePolynomialExcept z (z u)

def originWRemainderPolynomial (z : ι → ℝ) (ρ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : Polynomial ℝ :=
  ∑ u, Polynomial.C (W z ρ Dt G u i j/(z u)^4)*
    nonlinearDistinctRatePolynomialExcept z (z u)

theorem nonlinearDistinctJNumerator_origin_polynomial
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (i j : Fin N) :
    nonlinearDistinctJNumerator z ρ σ Dt G i j =
      nonlinearDistinctRatePolynomial z*originJJet z ρ σ Dt G i j -
      X^7*originCRemainderPolynomial z ρ σ Dt G i j := by
  classical
  have ht := nonlinearDistinct_tail_polynomial_origin z (fun u => C z ρ σ Dt G u i j) hz
  unfold nonlinearDistinctJNumerator originJJet originCRemainderPolynomial nonlinearOriginCmoment
  have he : (∑ u, Polynomial.C (z u*C z ρ σ Dt G u i j)*X^2*
      nonlinearDistinctRatePolynomialExcept z (z u)) =
      X^2*(∑ u, Polynomial.C (z u*C z ρ σ Dt G u i j)*
        nonlinearDistinctRatePolynomialExcept z (z u)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [he, ht]
  ring

theorem nonlinearDistinctLNumerator_origin_polynomial
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (i j : Fin N) :
    nonlinearDistinctLNumerator z ρ σ Dt G i j =
      nonlinearDistinctRatePolynomial z*originLJet z ρ σ Dt G i j +
      X^7*originWRemainderPolynomial z ρ Dt G i j := by
  classical
  have ht := nonlinearDistinct_tail_polynomial_origin z (fun u => W z ρ Dt G u i j) hz
  unfold nonlinearDistinctLNumerator originLJet originWRemainderPolynomial nonlinearOriginWmoment
  have he : (∑ u, Polynomial.C (z u*W z ρ Dt G u i j)*X^2*
      nonlinearDistinctRatePolynomialExcept z (z u)) =
      X^2*(∑ u, Polynomial.C (z u*W z ρ Dt G u i j)*
        nonlinearDistinctRatePolynomialExcept z (z u)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [he, ht]
  ring

end FMSA.ExactMSA.MultiTailMixture
