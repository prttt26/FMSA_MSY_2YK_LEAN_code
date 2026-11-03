import MSAConvergence.ResidualJets

/-! Coefficientwise actual Frechet variations of uniformly bounded-degree
polynomial families, without choosing a norm on the infinite polynomial ring. -/
noncomputable section
open Polynomial
open scoped BigOperators ContDiff

namespace FMSA.Convergence.PolynomialJets

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A finite polynomial with the genuine amplitude derivatives of its
coefficients. The degree cutoff will be discharged by a uniform bound. -/
def variation (D : ℕ) (f : P → Polynomial ℝ) (p v : P) : Polynomial ℝ :=
  ∑ n ∈ Finset.range (D + 1), Polynomial.monomial n (fderiv ℝ (fun a => (f a).coeff n) p v)

/-- The cutoff only suppresses coefficients beyond D. -/
theorem variation_coeff_cutoff (D : ℕ) (f : P → Polynomial ℝ) (p v : P) (n : ℕ) :
    (variation D f p v).coeff n =
      if n < D + 1 then fderiv ℝ (fun a => (f a).coeff n) p v else 0 := by
  classical
  simp [variation, Polynomial.coeff_monomial]

/-- The cutoff imposes the expected degree bound, independently of the family. -/
theorem variation_degree (D : ℕ) (f : P → Polynomial ℝ) (p v : P) :
    (variation D f p v).natDegree ≤ D := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [variation_coeff_cutoff, if_neg (by omega)]

/-- A uniform degree bound makes every coefficient the actual derivative,
including coefficients beyond the chosen cutoff. -/
theorem variation_coeff (D : ℕ) (f : P → Polynomial ℝ) (p v : P)
    (hb : ∀ a, (f a).natDegree ≤ D) (n : ℕ) :
    (variation D f p v).coeff n = fderiv ℝ (fun a => (f a).coeff n) p v := by
  rw [variation_coeff_cutoff]
  split_ifs with hn
  · rfl
  · have he : (fun a => (f a).coeff n) = fun _ : P => (0 : ℝ) := by
      funext a
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hb a; omega)
    rw [he, fderiv_const_apply]
    rfl

/-- The coefficient construction commutes with real evaluation whenever
actual coefficient derivatives exist; no derivative of a default value is used. -/
theorem variation_eval_fderiv (D : ℕ) (f : P → Polynomial ℝ) (p v : P)
    (hb : ∀ a, (f a).natDegree ≤ D)
    (hd : ∀ n ∈ Finset.range (D + 1), DifferentiableAt ℝ (fun a => (f a).coeff n) p)
    (s : ℝ) :
    (variation D f p v).eval s = fderiv ℝ (fun a => (f a).eval s) p v := by
  have he : (fun a => (f a).eval s) =
      fun a => ∑ n ∈ Finset.range (D + 1), (f a).coeff n * s^n := by
    funext a
    exact Polynomial.eval_eq_sum_range' (by have := hb a; omega) s
  rw [he, fderiv_fun_sum (fun n hn => (hd n hn).mul_const _)]
  simp only [variation, Polynomial.eval_finsetSum, Polynomial.eval_monomial, sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [((hd n hn).hasFDerivAt.mul_const (s^n)).fderiv]
  simp [mul_comm]

/-- Scalar coefficient smoothness does not require a norm on polynomials. -/
def CoeffSmooth (f : P → Polynomial ℝ) : Prop :=
  ∀ n, ContDiff ℝ ∞ (fun a => (f a).coeff n)

/-- Constant polynomial families have smooth coefficients. -/
theorem coeffSmooth_const (q : Polynomial ℝ) : CoeffSmooth (fun _ : P => q) := by
  intro n
  exact contDiff_const

/-- A smooth scalar coefficient defines a smooth constant-polynomial family. -/
theorem coeffSmooth_C (f : P → ℝ) (hf : ContDiff ℝ ∞ f) :
    CoeffSmooth (fun a => Polynomial.C (f a)) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using hf
  · simpa only [Polynomial.coeff_C, if_neg hn] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : P => (0 : ℝ)))

/-- Coefficient smoothness is closed under addition. -/
theorem coeffSmooth_add (f g : P → Polynomial ℝ) (hf : CoeffSmooth f) (hg : CoeffSmooth g) :
    CoeffSmooth (fun a => f a + g a) := by
  intro n
  simpa only [Polynomial.coeff_add] using (hf n).add (hg n)

/-- Coefficient smoothness is closed under negation. -/
theorem coeffSmooth_neg (f : P → Polynomial ℝ) (hf : CoeffSmooth f) :
    CoeffSmooth (fun a => -f a) := by
  intro n
  simpa only [Polynomial.coeff_neg] using (hf n).neg

/-- The coefficient of a product is a fixed finite convolution. -/
theorem coeffSmooth_mul (f g : P → Polynomial ℝ) (hf : CoeffSmooth f) (hg : CoeffSmooth g) :
    CoeffSmooth (fun a => f a * g a) := by
  intro n
  simp only [Polynomial.coeff_mul]
  exact ContDiff.sum fun ij _ => (hf ij.1).mul (hg ij.2)

/-- Fixed finite sums of smooth coefficient families remain smooth. -/
theorem coeffSmooth_sum {I : Type*} (s : Finset I) (f : I → P → Polynomial ℝ)
    (hf : ∀ i ∈ s, CoeffSmooth (f i)) : CoeffSmooth (fun a => ∑ i ∈ s, f i a) := by
  intro n
  simp only [Polynomial.finsetSum_coeff]
  exact ContDiff.sum fun i hi => hf i hi n

/-- Fixed polynomial substitution is a finite linear operation on a family
with a uniform degree bound; this includes frequency reflection. -/
theorem coeffSmooth_comp (D : ℕ) (f : P → Polynomial ℝ)
    (hb : ∀ a, (f a).natDegree ≤ D) (hf : CoeffSmooth f) (q : Polynomial ℝ) :
    CoeffSmooth (fun a => (f a).comp q) := by
  intro n
  have he : (fun a => ((f a).comp q).coeff n) =
      fun a => ∑ k ∈ Finset.range (D + 1), (f a).coeff k * (q^k).coeff n := by
    funext a
    conv_lhs => rw [(f a).as_sum_range_C_mul_X_pow' (n := D + 1) (by have := hb a; omega)]
    simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  rw [he]
  exact ContDiff.sum fun k _ => (hf k).mul contDiff_const

/-- Uniformly finite coefficient smoothness supplies genuine smoothness of
every real evaluation, rather than only a formal derivative value. -/
theorem coeffSmooth_eval_contDiff (D : ℕ) (f : P → Polynomial ℝ)
    (hb : ∀ a, (f a).natDegree ≤ D) (hf : CoeffSmooth f) (s : ℝ) :
    ContDiff ℝ ∞ (fun a => (f a).eval s) := by
  have he : (fun a => (f a).eval s) =
      fun a => ∑ n ∈ Finset.range (D + 1), (f a).coeff n * s^n := by
    funext a
    exact Polynomial.eval_eq_sum_range' (by have := hb a; omega) s
  rw [he]
  exact ContDiff.sum fun n _ => (hf n).mul contDiff_const

end FMSA.Convergence.PolynomialJets

/-- info: 'FMSA.Convergence.PolynomialJets.variation_coeff_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.variation_coeff_cutoff

/-- info: 'FMSA.Convergence.PolynomialJets.variation_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.variation_degree

/-- info: 'FMSA.Convergence.PolynomialJets.variation_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.variation_coeff

/-- info: 'FMSA.Convergence.PolynomialJets.variation_eval_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.variation_eval_fderiv

/-- info: 'FMSA.Convergence.PolynomialJets.coeffSmooth_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.coeffSmooth_const

/-- info: 'FMSA.Convergence.PolynomialJets.coeffSmooth_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.coeffSmooth_C

/-- info: 'FMSA.Convergence.PolynomialJets.coeffSmooth_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.coeffSmooth_add

/-- info: 'FMSA.Convergence.PolynomialJets.coeffSmooth_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.coeffSmooth_neg

/-- info: 'FMSA.Convergence.PolynomialJets.coeffSmooth_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.coeffSmooth_mul

/-- info: 'FMSA.Convergence.PolynomialJets.coeffSmooth_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.coeffSmooth_sum

/-- info: 'FMSA.Convergence.PolynomialJets.coeffSmooth_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.coeffSmooth_comp

/-- info: 'FMSA.Convergence.PolynomialJets.coeffSmooth_eval_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PolynomialJets.coeffSmooth_eval_contDiff
