import MSAConvergence.PolynomialJets
import Mathlib.Analysis.Polynomial.Basic

/-! Finite polynomials cannot equal a strictly decaying exponential
 times another polynomial on the positive axis, unless both vanish. -/
noncomputable section
open Filter Topology Real Polynomial
open scoped BigOperators
namespace FMSA.Convergence.PolynomialExponentialSeparation

/-- Every fixed power times a strictly decaying exponential tends to zero. -/
theorem power_exp_neg_tendsto_zero (n : ℕ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => x^n*exp (-a*x)) atTop (𝓝 0) := by
  have hs : Tendsto (fun x : ℝ => a*x) atTop atTop :=
    (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).const_mul_atTop ha
  have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hs
  have he : (fun x : ℝ => x^n*exp (-a*x)) =
      fun x => (a⁻¹)^n*((a*x)^n*exp (-(a*x))) := by
    funext x
    simp only [mul_pow, neg_mul]
    have hc : (a⁻¹)^n*a^n = 1 := by rw [← mul_pow, inv_mul_cancel₀ ha.ne', one_pow]
    calc
      _ = ((a⁻¹)^n*a^n)*x^n*exp (-(a*x)) := by rw [hc, one_mul]
      _ = _ := by ring
  rw [he]
  simpa only [mul_zero, Function.comp_def] using h.const_mul ((a⁻¹)^n)

/-- Actual finite polynomial evaluation is dominated by every positive
exponential decay rate, with no norm on the polynomial coefficient space. -/
theorem polynomial_exp_neg_tendsto_zero (P : Polynomial ℝ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => P.eval x*exp (-a*x)) atTop (𝓝 0) := by
  have he : (fun x : ℝ => P.eval x*exp (-a*x)) =
      fun x => ∑ n ∈ Finset.range (P.natDegree+1), P.coeff n*(x^n*exp (-a*x)) := by
    funext x
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [he]
  simpa only [mul_zero, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.range (P.natDegree+1))
      (fun n _ => (power_exp_neg_tendsto_zero n a ha).const_mul (P.coeff n))

/-- A real polynomial whose actual evaluation tends to zero at infinity
is zero, by the proved leading-coefficient limit characterization. -/
theorem polynomial_zero_of_eval_tendsto_zero (P : Polynomial ℝ)
    (h : Tendsto (fun x : ℝ => P.eval x) atTop (𝓝 0)) : P = 0 :=
  Polynomial.leadingCoeff_eq_zero.mp ((P.tendsto_nhds_iff).mp h).1

/-- Positive-axis polynomial/exponential separation. Strict positive
diameter is essential; no assertion is made for zero decay rate. -/
theorem polynomial_exp_separation (P Q : Polynomial ℝ) (a : ℝ) (ha : 0 < a)
    (h : ∀ x : ℝ, 0 < x → P.eval x = exp (-a*x)*Q.eval x) : P = 0 ∧ Q = 0 := by
  have he : (fun x : ℝ => Q.eval x*exp (-a*x)) =ᶠ[atTop] fun x => P.eval x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [h x hx]
    ring
  have hp := polynomial_zero_of_eval_tendsto_zero P ((polynomial_exp_neg_tendsto_zero Q a ha).congr' he)
  refine ⟨hp, ?_⟩
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℝ)).mono
  intro x hx
  simp only [Set.mem_setOf_eq, Polynomial.eval_zero]
  have hh := h x hx
  rw [hp, Polynomial.eval_zero] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left (exp_pos _).ne'

end FMSA.Convergence.PolynomialExponentialSeparation

/-- info: 'FMSA.Convergence.PolynomialExponentialSeparation.power_exp_neg_tendsto_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialExponentialSeparation.power_exp_neg_tendsto_zero

/-- info: 'FMSA.Convergence.PolynomialExponentialSeparation.polynomial_exp_neg_tendsto_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialExponentialSeparation.polynomial_exp_neg_tendsto_zero

/-- info: 'FMSA.Convergence.PolynomialExponentialSeparation.polynomial_zero_of_eval_tendsto_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialExponentialSeparation.polynomial_zero_of_eval_tendsto_zero

/-- info: 'FMSA.Convergence.PolynomialExponentialSeparation.polynomial_exp_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialExponentialSeparation.polynomial_exp_separation
