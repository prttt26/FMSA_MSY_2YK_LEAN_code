import MSAConvergence.DistinctPoleJets
import MSAConvergence.PolynomialJets

/-! Actual coefficientwise Wronskian tangent polynomials and their finite
reflected-rate factors. Root-only identities are never differentiated. -/
noncomputable section
open Real Polynomial
open scoped BigOperators ContDiff

namespace FMSA.Convergence.WronskianJets
open FMSA.Paper.JacobianExterior FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.PolynomialJets FMSA.Convergence.DistinctPoleJets

variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual distinct J numerator has smooth amplitude coefficients. -/
theorem actual_JNumerator_coeffSmooth (z : T → ℝ) (rho sigma : Fin N → ℝ) (i j : Fin N) :
    CoeffSmooth (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearDistinctJNumerator z rho sigma a.1 a.2 i j) := by
  unfold nonlinearDistinctJNumerator
  apply coeffSmooth_add
  · apply coeffSmooth_mul
    · apply coeffSmooth_add
      · exact coeffSmooth_C _ (amplitudeA_contDiff z rho sigma j)
      · exact coeffSmooth_mul _ _ (coeffSmooth_C _ (amplitudeQp_contDiff z rho sigma i j))
          (coeffSmooth_const X)
    · exact coeffSmooth_const _
  · apply coeffSmooth_sum
    intro u _
    apply coeffSmooth_mul
    · exact coeffSmooth_mul _ _ (coeffSmooth_C _ (contDiff_const.mul (C_contDiff z rho sigma u i j)))
        (coeffSmooth_const _)
    · exact coeffSmooth_const _

/-- The actual distinct L numerator has smooth amplitude coefficients. -/
theorem actual_LNumerator_coeffSmooth (z : T → ℝ) (rho sigma : Fin N → ℝ) (i j : Fin N) :
    CoeffSmooth (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearDistinctLNumerator z rho sigma a.1 a.2 i j) := by
  have hl : ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearLowerQValue z rho sigma a.1 a.2 i j) := by
    unfold nonlinearLowerQValue
    fun_prop
  unfold nonlinearDistinctLNumerator
  simp only [sub_eq_add_neg]
  apply coeffSmooth_add
  · apply coeffSmooth_mul
    · apply coeffSmooth_add
      · apply coeffSmooth_add
        · exact coeffSmooth_C _ (amplitudeA_contDiff z rho sigma j)
        · exact coeffSmooth_mul _ _ (coeffSmooth_C _
            ((amplitudeQp_contDiff z rho sigma i j).add
              (contDiff_const.mul (amplitudeA_contDiff z rho sigma j)).neg)) (coeffSmooth_const _)
      · exact coeffSmooth_mul _ _ (coeffSmooth_C _ hl) (coeffSmooth_const _)
    · exact coeffSmooth_const _
  · apply coeffSmooth_neg
    apply coeffSmooth_sum
    intro u _
    apply coeffSmooth_mul
    · exact coeffSmooth_mul _ _ (coeffSmooth_C _ (contDiff_const.mul (W_contDiff z rho u i j)))
        (coeffSmooth_const _)
    · exact coeffSmooth_const _

/-- Both actual Wronskian numerator families have genuine smooth coefficient
maps. Frequency reflection is a fixed finite operation. -/
theorem actual_distinct_wronskian_coeffSmooth (z : T → ℝ) (rho sigma : Fin N → ℝ) :
    (∀ i j, CoeffSmooth (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j)) ∧
    (∀ i j, CoeffSmooth (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j)) := by
  let A := TailMatrix T N × TailMatrix T N
  have hm {f g : A → Polynomial ℝ} (hf : CoeffSmooth f) (hg : CoeffSmooth g) :=
    coeffSmooth_mul f g hf hg
  have ha {f g : A → Polynomial ℝ} (hf : CoeffSmooth f) (hg : CoeffSmooth g) :=
    coeffSmooth_add f g hf hg
  have hn {f : A → Polynomial ℝ} (hf : CoeffSmooth f) := coeffSmooth_neg f hf
  have hJ (i j : Fin N) := actual_JNumerator_coeffSmooth z rho sigma i j
  have hL (i j : Fin N) := actual_LNumerator_coeffSmooth z rho sigma i j
  have hJm (i j : Fin N) := coeffSmooth_comp ((nonlinearDistinctRates z).card + 1)
    (fun a : A => nonlinearDistinctJNumerator z rho sigma a.1 a.2 i j)
    (fun a => nonlinearDistinctJNumerator_degree_le z rho sigma a.1 a.2 i j) (hJ i j) (-X)
  have hLm (i j : Fin N) := coeffSmooth_comp ((nonlinearDistinctRates z).card + 2)
    (fun a : A => nonlinearDistinctLNumerator z rho sigma a.1 a.2 i j)
    (fun a => nonlinearDistinctLNumerator_degree_le z rho sigma a.1 a.2 i j) (hL i j) (-X)
  constructor
  · intro i j
    unfold nonlinearDistinctUPolynomial
    simp only [sub_eq_add_neg]
    exact ha (ha (hm (hm (hn (hL i j)) (coeffSmooth_const X)) (coeffSmooth_const _))
        (hm (hm (hLm j i) (coeffSmooth_const X)) (coeffSmooth_const _)))
      (coeffSmooth_sum _ _ (fun m _ => hm (coeffSmooth_const _) (ha
        (hm (hJm i m) (hJ j m)) (hn (hm (hL i m) (hLm j m))))))
  · intro i j
    unfold nonlinearDistinctVPolynomial
    simp only [sub_eq_add_neg]
    exact ha (hm (hm (ha (hJ i j) (hn (hJ j i))) (coeffSmooth_const X)) (coeffSmooth_const _))
      (coeffSmooth_sum _ _ (fun m _ => hm (coeffSmooth_const _) (ha
        (hm (hJ i m) (hLm j m)) (hn (hm (hLm i m) (hJ j m))))))

/-- Every real U/V evaluation is genuinely smooth in the original amplitudes,
with no root, kernel, positivity or caller-supplied regularity assumption. -/
theorem actual_distinct_eval_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (i j : Fin N) (s : ℝ) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      (nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j).eval s) ∧
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      (nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).eval s) := by
  exact ⟨coeffSmooth_eval_contDiff (2 * (nonlinearDistinctRates z).card + 5)
      (fun a : TailMatrix T N × TailMatrix T N => nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j)
      (fun a => nonlinearDistinctUPolynomial_degree_le z rho sigma a.1 a.2 i j)
      ((actual_distinct_wronskian_coeffSmooth z rho sigma).1 i j) s,
    coeffSmooth_eval_contDiff (2 * (nonlinearDistinctRates z).card + 4)
      (fun a : TailMatrix T N × TailMatrix T N => nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j)
      (fun a => nonlinearDistinctVPolynomial_degree_le z rho sigma a.1 a.2 i j)
      ((actual_distinct_wronskian_coeffSmooth z rho sigma).2 i j) s⟩

/-- The actual U tangent polynomial, with a uniform proven cutoff. -/
def tangentU (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) : Polynomial ℝ :=
  variation (2 * (nonlinearDistinctRates z).card + 5)
    (fun a => nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j) p v

/-- The actual V tangent polynomial, with its sharper uniform cutoff. -/
def tangentV (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) : Polynomial ℝ :=
  variation (2 * (nonlinearDistinctRates z).card + 4)
    (fun a => nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j) p v

/-- Both tangent polynomials obey the original uniform degree bounds. -/
theorem tangent_degrees (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    (tangentU z rho sigma p v i j).natDegree ≤ 2 * (nonlinearDistinctRates z).card + 5 ∧
    (tangentV z rho sigma p v i j).natDegree ≤ 2 * (nonlinearDistinctRates z).card + 4 := by
  exact ⟨variation_degree _ _ _ _, variation_degree _ _ _ _⟩

/-- Every coefficient is the actual Frechet amplitude derivative; the cutoff
has removed only identically zero higher coefficient functions. -/
theorem tangent_coefficients (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (n : ℕ) :
    (tangentU z rho sigma p v i j).coeff n =
      fderiv ℝ (fun a => (nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j).coeff n) p v ∧
    (tangentV z rho sigma p v i j).coeff n =
      fderiv ℝ (fun a => (nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).coeff n) p v := by
  exact ⟨variation_coeff _ _ p v (fun a => nonlinearDistinctUPolynomial_degree_le z rho sigma a.1 a.2 i j) n,
    variation_coeff _ _ p v (fun a => nonlinearDistinctVPolynomial_degree_le z rho sigma a.1 a.2 i j) n⟩

/-- Actual coefficient differentiation commutes with every real evaluation,
with coefficient derivative existence discharged internally. -/
theorem tangent_eval_fderiv (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (s : ℝ) :
    (tangentU z rho sigma p v i j).eval s =
      fderiv ℝ (fun a => (nonlinearDistinctUPolynomial z rho sigma a.1 a.2 i j).eval s) p v ∧
    (tangentV z rho sigma p v i j).eval s =
      fderiv ℝ (fun a => (nonlinearDistinctVPolynomial z rho sigma a.1 a.2 i j).eval s) p v := by
  exact ⟨variation_eval_fderiv _ _ p v
      (fun a => nonlinearDistinctUPolynomial_degree_le z rho sigma a.1 a.2 i j)
      (fun n _ => ((actual_distinct_wronskian_coeffSmooth z rho sigma).1 i j n).differentiable
        (by simp) p) s,
    variation_eval_fderiv _ _ p v
      (fun a => nonlinearDistinctVPolynomial_degree_le z rho sigma a.1 a.2 i j)
      (fun n _ => ((actual_distinct_wronskian_coeffSmooth z rho sigma).2 i j n).differentiable
        (by simp) p) s⟩

/-- The actual tangent polynomials vanish at both signs of every distinct
positive rate, including repeated original tail labels. -/
theorem actual_kernel_tangent_rate_zeros
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hz : ∀ u, 0 < z u) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hv : amplitudeJacobian z rho sigma K t p v = 0)
    (r : ℝ) (hr : r ∈ nonlinearDistinctRates z) (i j : Fin N) :
    (tangentU z rho sigma p v i j).eval r = 0 ∧
    (tangentU z rho sigma p v i j).eval (-r) = 0 ∧
    (tangentV z rho sigma p v i j).eval r = 0 ∧
    (tangentV z rho sigma p v i j).eval (-r) = 0 := by
  have h := actual_kernel_distinct_wronskian_rates_fderiv_zero
    z rho sigma K hK hz t p v hroot hv r hr i j
  exact ⟨(tangent_eval_fderiv z rho sigma p v i j r).1.trans h.1,
    (tangent_eval_fderiv z rho sigma p v i j (-r)).1.trans h.2.1,
    (tangent_eval_fderiv z rho sigma p v i j r).2.trans h.2.2.1,
    (tangent_eval_fderiv z rho sigma p v i j (-r)).2.trans h.2.2.2⟩

/-- The full fixed reflected-rate polynomial divides both actual tangent
numerators. No distinctness or root-curve hypothesis is supplied. -/
theorem actual_kernel_tangent_pole_factor
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hz : ∀ u, 0 < z u) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    nonlinearDistinctPoleFactor z ∣ tangentU z rho sigma p v i j ∧
    nonlinearDistinctPoleFactor z ∣ tangentV z rho sigma p v i j := by
  classical
  constructor <;> apply nonlinearDistinctPoleFactor_dvd_of_roots
  · intro r hr
    rcases Finset.mem_union.mp hr with hp | hn
    · exact (actual_kernel_tangent_rate_zeros z rho sigma K hK hz t p v hroot hv r hp i j).1
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
      exact (actual_kernel_tangent_rate_zeros z rho sigma K hK hz t p v hroot hv s hs i j).2.1
  · intro r hr
    rcases Finset.mem_union.mp hr with hp | hn
    · exact (actual_kernel_tangent_rate_zeros z rho sigma K hK hz t p v hroot hv r hp i j).2.2.1
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
      exact (actual_kernel_tangent_rate_zeros z rho sigma K hK hz t p v hroot hv s hs i j).2.2.2

/-- After removing the proven reflected factors, only degree-five U and
degree-four V tangent remainders remain, independently of the tail count. -/
theorem actual_kernel_tangent_fixed_degree_remainders
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hz : ∀ u, 0 < z u) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hv : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    (∃ q : Polynomial ℝ, tangentU z rho sigma p v i j = nonlinearDistinctPoleFactor z * q ∧
      q.natDegree ≤ 5) ∧
    (∃ q : Polynomial ℝ, tangentV z rho sigma p v i j = nonlinearDistinctPoleFactor z * q ∧
      q.natDegree ≤ 4) := by
  have hdeg := tangent_degrees z rho sigma p v i j
  obtain ⟨⟨qu, hu⟩, ⟨qv, hqv⟩⟩ := actual_kernel_tangent_pole_factor z rho sigma K hK hz t p v hroot hv i j
  constructor
  · refine ⟨qu, hu, polynomial_factor_degree_bound _ _ 5 (nonlinearDistinctPoleFactor_monic z).ne_zero ?_⟩
    rw [← hu, nonlinearDistinctPoleFactor_degree z hz]
    exact hdeg.1
  · refine ⟨qv, hqv, polynomial_factor_degree_bound _ _ 4 (nonlinearDistinctPoleFactor_monic z).ne_zero ?_⟩
    rw [← hqv, nonlinearDistinctPoleFactor_degree z hz]
    exact hdeg.2

end FMSA.Convergence.WronskianJets

/-- info: 'FMSA.Convergence.WronskianJets.actual_JNumerator_coeffSmooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.WronskianJets.actual_JNumerator_coeffSmooth

/-- info: 'FMSA.Convergence.WronskianJets.actual_LNumerator_coeffSmooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.WronskianJets.actual_LNumerator_coeffSmooth

/-- info: 'FMSA.Convergence.WronskianJets.actual_distinct_wronskian_coeffSmooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.WronskianJets.actual_distinct_wronskian_coeffSmooth

/-- info: 'FMSA.Convergence.WronskianJets.actual_distinct_eval_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.WronskianJets.actual_distinct_eval_contDiff

/-- info: 'FMSA.Convergence.WronskianJets.tangent_degrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.WronskianJets.tangent_degrees

/-- info: 'FMSA.Convergence.WronskianJets.tangent_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.WronskianJets.tangent_coefficients

/-- info: 'FMSA.Convergence.WronskianJets.tangent_eval_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.WronskianJets.tangent_eval_fderiv

/-- info: 'FMSA.Convergence.WronskianJets.actual_kernel_tangent_rate_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.WronskianJets.actual_kernel_tangent_rate_zeros

/-- info: 'FMSA.Convergence.WronskianJets.actual_kernel_tangent_pole_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.WronskianJets.actual_kernel_tangent_pole_factor

/-- info: 'FMSA.Convergence.WronskianJets.actual_kernel_tangent_fixed_degree_remainders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.WronskianJets.actual_kernel_tangent_fixed_degree_remainders
