import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearPoleCancellation
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearWronskianFinite

/-! Automatic zeros of the actual finite Wronskian polynomials at every
positive and reflected Yukawa rate. Repeated labels are allowed. Point zeros
alone do not assert the full coefficient certificate or root multiplicities. -/
noncomputable section
open Real Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nonlinearRatePolynomial_eval_neg_rate (z : ι → ℝ) (u : ι) :
    (nonlinearRatePolynomial z).eval (-z u)=0 := by
  rw [nonlinearRatePolynomial_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ u) (by simp)

theorem nonlinearRatePolynomialExcept_eval_other_neg_rate (z : ι → ℝ)
    (u v : ι) (huv : u ≠ v) :
    (nonlinearRatePolynomialExcept z v).eval (-z u)=0 := by
  simp only [nonlinearRatePolynomialExcept, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨huv, Finset.mem_univ u⟩) (by simp)

theorem nonlinearJNumerator_eval_neg_rate (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (u : ι) (i j : Fin N) :
    (nonlinearJNumerator z ρ σ Dt G i j).eval (-z u)=
      (z u)^3*(nonlinearRatePolynomialExcept z u).eval (-z u)*C z ρ σ Dt G u i j := by
  simp only [nonlinearJNumerator, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_finset_sum,
    nonlinearRatePolynomial_eval_neg_rate, mul_zero, zero_add]
  rw [Finset.sum_eq_single u]
  · ring
  · intro v _ hvu
    rw [nonlinearRatePolynomialExcept_eval_other_neg_rate z u v (Ne.symm hvu), mul_zero]
  · simp

theorem nonlinearLNumerator_eval_neg_rate (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (u : ι) (i j : Fin N) :
    (nonlinearLNumerator z ρ σ Dt G i j).eval (-z u)=
      -((z u)^3*(nonlinearRatePolynomialExcept z u).eval (-z u))*W z ρ Dt G u i j := by
  simp only [nonlinearLNumerator, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_finset_sum,
    nonlinearRatePolynomial_eval_neg_rate, mul_zero, zero_sub]
  rw [Finset.sum_eq_single u]
  · ring
  · intro v _ hvu
    rw [nonlinearRatePolynomialExcept_eval_other_neg_rate z u v (Ne.symm hvu), mul_zero]
  · simp

/-- A necessary part of finite admissibility now follows directly from the
actual root. No independent Wronskian or RDF reciprocity premise is used. -/
theorem nonlinearRoot_wronskian_polynomials_zero_at_all_rates
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j=K u j i) (u : ι) (i j : Fin N) :
    (nonlinearWronskianUPolynomial z ρ σ Dt G i j).eval (z u)=0 ∧
    (nonlinearWronskianUPolynomial z ρ σ Dt G i j).eval (-z u)=0 ∧
    (nonlinearWronskianVPolynomial z ρ σ Dt G i j).eval (z u)=0 ∧
    (nonlinearWronskianVPolynomial z ρ σ Dt G i j).eval (-z u)=0 := by
  have h := nonlinearRoot_yukawa_residue_matrices_zero z ρ σ K Dt G hz hroot hK u
  dsimp only at h
  have hu := congrFun (congrFun h.1 i) j
  have hum := congrFun (congrFun h.2.1 i) j
  have hv := congrFun (congrFun h.2.2.1 i) j
  have hvm := congrFun (congrFun h.2.2.2 i) j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.transpose_apply, Matrix.of_apply,
    Matrix.mul_apply (M := Matrix.of (C z ρ σ Dt G u)*Matrix.diagonal ρ),
    Matrix.mul_apply (M := Matrix.of (W z ρ Dt G u)*Matrix.diagonal ρ),
    Matrix.mul_apply (M := nonlinearRationalJ z ρ σ Dt G (z u)*Matrix.diagonal ρ),
    Matrix.mul_apply (M := nonlinearRationalL z ρ σ Dt G (z u)*Matrix.diagonal ρ),
    Matrix.mul_diagonal, Matrix.zero_apply] at hu hum hv hvm
  have hd : (nonlinearRationalDenominator z).eval (-z u)=0 := by
    simp [nonlinearRationalDenominator, nonlinearRatePolynomial_eval_neg_rate]
  have heval (p : Polynomial ℝ) (s : ℝ) : (p.comp (-X)).eval s=p.eval (-s) := by
    rw [Polynomial.eval_comp]
    simp
  simp only [nonlinearWronskianUPolynomial, nonlinearWronskianVPolynomial,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finset_sum, heval, neg_neg,
    nonlinearJNumerator_eval z ρ σ Dt G hz (z u) (hz u),
    nonlinearLNumerator_eval z ρ σ Dt G hz (z u) (hz u),
    nonlinearJNumerator_eval_neg_rate, nonlinearLNumerator_eval_neg_rate,
    hd, mul_zero, zero_mul, zero_add, add_zero, sub_zero]
  let d := (nonlinearRationalDenominator z).eval (z u)
  let p := (z u)^3*(nonlinearRatePolynomialExcept z u).eval (-z u)
  simp only [nonlinearRationalJ, nonlinearRationalL, Matrix.of_apply] at hu hum hv hvm ⊢
  change _=0 ∧ _=0 ∧ _=0 ∧ _=0
  constructor
  · linear_combination (norm := skip) (-p*d)*hu
    dsimp only [p, d]
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    ring_nf
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_eq_zero
    intro m _
    first
    | (ring; done)
    | ring_nf
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_eq_zero
      intro t _
      ring
  constructor
  · linear_combination (norm := skip) (-p*d)*hum
    dsimp only [p, d]
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    ring_nf
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_eq_zero
    intro m _
    first
    | (ring; done)
    | ring_nf
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_eq_zero
      intro t _
      ring
  constructor
  · linear_combination (norm := skip) (-p*d)*hv
    dsimp only [p, d]
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    ring_nf
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_eq_zero
    intro m _
    first
    | (ring; done)
    | ring_nf
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_eq_zero
      intro t _
      ring
  · linear_combination (norm := skip) (-p*d)*hvm
    dsimp only [p, d]
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    ring_nf
    try simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_eq_zero
    intro m _
    first
    | (ring; done)
    | ring_nf
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_eq_zero
      intro t _
      ring

end FMSA.ExactMSA.MultiTailMixture
