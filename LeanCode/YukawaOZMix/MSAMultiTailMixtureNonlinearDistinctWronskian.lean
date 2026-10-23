import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearDistinctResidues

/-! Wronskian numerators with one factor per distinct rate value. -/
noncomputable section
open Real Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def nonlinearDistinctUPolynomial (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : Polynomial ℝ :=
  -nonlinearDistinctLNumerator z ρ σ Dt G i j * X *
    (nonlinearDistinctDenominator z).comp (-X) +
  (nonlinearDistinctLNumerator z ρ σ Dt G j i).comp (-X) * X *
    nonlinearDistinctDenominator z +
  ∑ m, Polynomial.C (ρ m) *
    ((nonlinearDistinctJNumerator z ρ σ Dt G i m).comp (-X) *
      nonlinearDistinctJNumerator z ρ σ Dt G j m -
    nonlinearDistinctLNumerator z ρ σ Dt G i m *
      (nonlinearDistinctLNumerator z ρ σ Dt G j m).comp (-X))

def nonlinearDistinctVPolynomial (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : Polynomial ℝ :=
  (nonlinearDistinctJNumerator z ρ σ Dt G i j -
    nonlinearDistinctJNumerator z ρ σ Dt G j i) * X *
      (nonlinearDistinctDenominator z).comp (-X) +
  ∑ m, Polynomial.C (ρ m) *
    (nonlinearDistinctJNumerator z ρ σ Dt G i m *
      (nonlinearDistinctLNumerator z ρ σ Dt G j m).comp (-X) -
    (nonlinearDistinctLNumerator z ρ σ Dt G i m).comp (-X) *
      nonlinearDistinctJNumerator z ρ σ Dt G j m)

theorem collected_residues_cleared_values_zero
    (C W J L : Matrix (Fin N) (Fin N) ℝ) (ρ : Fin N → ℝ) (r p d : ℝ)
    (hu : r • W.transpose - C*Matrix.diagonal ρ*J.transpose -
      L*Matrix.diagonal ρ*W.transpose = 0)
    (hum : r • W - J*Matrix.diagonal ρ*C.transpose -
      W*Matrix.diagonal ρ*L.transpose = 0)
    (hv : J*Matrix.diagonal ρ*W.transpose - W*Matrix.diagonal ρ*J.transpose = 0)
    (hvm : r • (C-C.transpose) + L*Matrix.diagonal ρ*C.transpose -
      C*Matrix.diagonal ρ*L.transpose = 0) (i j : Fin N) :
    -p*W j i*r*d + ∑ m, ρ m*(p*C i m*(d*J j m) - d*L i m*(-p*W j m)) = 0 ∧
    -d*L i j*(-r)*0 - (-p*W i j)*(-r)*d +
      ∑ m, ρ m*(d*J i m*(p*C j m) - (-p*W i m)*(d*L j m)) = 0 ∧
    ∑ m, ρ m*(d*J i m*(-p*W j m) - (-p*W i m)*(d*J j m)) = 0 ∧
    (p*C i j-p*C j i)*(-r)*d +
      ∑ m, ρ m*(p*C i m*(d*L j m) - d*L i m*(p*C j m)) = 0 := by
  have h1 := congrFun (congrFun hu i) j
  have h2 := congrFun (congrFun hum i) j
  have h3 := congrFun (congrFun hv i) j
  have h4 := congrFun (congrFun hvm i) j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.transpose_apply, Matrix.zero_apply,
    Matrix.mul_apply (M := C*Matrix.diagonal ρ),
    Matrix.mul_apply (M := W*Matrix.diagonal ρ),
    Matrix.mul_apply (M := J*Matrix.diagonal ρ),
    Matrix.mul_apply (M := L*Matrix.diagonal ρ), Matrix.mul_diagonal] at h1 h2 h3 h4
  constructor
  · linear_combination (norm := skip) (-p*d)*h1
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    ring_nf
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_eq_zero
    intro m _
    ring
  constructor
  · linear_combination (norm := skip) (-p*d)*h2
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    ring_nf
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_eq_zero
    intro m _
    ring
  constructor
  · linear_combination (norm := skip) (-p*d)*h3
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    ring_nf
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_eq_zero
    intro m _
    ring
  · linear_combination (norm := skip) (-p*d)*h4
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    ring_nf
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_eq_zero
    intro m _
    ring

theorem nonlinearRoot_distinct_wronskian_zero_at_all_rates
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j = K u j i)
    (r : ℝ) (hr : r ∈ nonlinearDistinctRates z) (i j : Fin N) :
    (nonlinearDistinctUPolynomial z ρ σ Dt G i j).eval r = 0 ∧
    (nonlinearDistinctUPolynomial z ρ σ Dt G i j).eval (-r) = 0 ∧
    (nonlinearDistinctVPolynomial z ρ σ Dt G i j).eval r = 0 ∧
    (nonlinearDistinctVPolynomial z ρ σ Dt G i j).eval (-r) = 0 := by
  have hrp := nonlinearDistinctRates_positive z hz r hr
  have hsp (u : ι) : r + z u ≠ 0 := (add_pos hrp (hz u)).ne'
  have h := nonlinearRoot_collected_yukawa_residues_zero z ρ σ K Dt G hz hroot hK r
  have he := collected_residues_cleared_values_zero
    (nonlinearRateFibreMatrix z (C z ρ σ Dt G) r)
    (nonlinearRateFibreMatrix z (W z ρ Dt G) r)
    (nonlinearRationalJ z ρ σ Dt G r) (nonlinearRationalL z ρ σ Dt G r) ρ r
    (r^3*(nonlinearDistinctRatePolynomialExcept z r).eval (-r))
    ((nonlinearDistinctDenominator z).eval r) h.1 h.2.1 h.2.2.1 h.2.2.2 i j
  have hd : (nonlinearDistinctDenominator z).eval (-r) = 0 := by
    simp [nonlinearDistinctDenominator, nonlinearDistinctRatePolynomial_eval_neg_rate z r hr]
  have hc (p : Polynomial ℝ) (s : ℝ) : (p.comp (-X)).eval s = p.eval (-s) := by
    rw [Polynomial.eval_comp]
    simp
  simp only [nonlinearDistinctUPolynomial, nonlinearDistinctVPolynomial,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finset_sum, hc, neg_neg,
    nonlinearDistinctJNumerator_eval z ρ σ Dt G r hrp.ne' hsp,
    nonlinearDistinctLNumerator_eval z ρ σ Dt G r hrp.ne' hsp,
    nonlinearDistinctJNumerator_eval_neg_rate z ρ σ Dt G r hr,
    nonlinearDistinctLNumerator_eval_neg_rate z ρ σ Dt G r hr, hd,
    mul_zero, zero_mul, zero_add, add_zero, sub_zero] at he ⊢
  simpa only [zero_sub, neg_mul, neg_neg] using he

end FMSA.ExactMSA.MultiTailMixture
