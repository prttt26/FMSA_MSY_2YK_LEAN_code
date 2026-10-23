import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearNormalizedDegree
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearNormalizedFactors

/-! Automatic finite Wronskian admissibility of actual finite-mixture BH roots. -/
noncomputable section
open Polynomial MSAMixture FMSA.MatrixQ0
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem nonlinearRoot_intrinsicNormalizedDefect_zero
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hv : vacMix ρ σ ≠ 0)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i) :
    intrinsicNormalizedDefect z ρ σ Dt G = 0 := by
  obtain ⟨F,hF⟩ := nonlinearRoot_intrinsicNormalizedDefect_factor z ρ σ K Dt G hz hv hroot hK
  let p := intrinsicRatePairPolynomial z*nonlinearDistinctPoleFactor z
  have hp0 : p.coeff 0 ≠ 0 := by
    change (intrinsicRatePairPolynomial z*nonlinearDistinctPoleFactor z).coeff 0 ≠ 0
    rw [Polynomial.mul_coeff_zero]
    exact mul_ne_zero (intrinsicRatePairPolynomial_coeff_zero_ne_zero z hz)
      (by simpa only [Polynomial.coeff_zero_eq_eval_zero] using
        nonlinearDistinctPoleFactor_eval_zero_ne_zero z hz)
  have hq : intrinsicRatePairPolynomial z ≠ 0 := by
    intro he
    have hh := intrinsicRatePairPolynomial_coeff_zero_ne_zero z hz
    simp [he] at hh
  have hpdeg : p.natDegree = 4*(nonlinearDistinctRates z).card := by
    rw [Polynomial.natDegree_mul hq (nonlinearDistinctPoleFactor_monic z).ne_zero,
      intrinsicRatePairPolynomial_degree, nonlinearDistinctPoleFactor_degree z hz]
    omega
  have hd := intrinsicNormalizedDefect_degree z ρ σ Dt G (fun u => ne_of_gt (hz u)) hv
  have ho := intrinsicNormalizedDefect_origin_zero z ρ σ Dt G (fun u => ne_of_gt (hz u))
  have hs : (polyMatrixCoeff 1 (intrinsicNormalizedDefect z ρ σ Dt G)).transpose =
      -polyMatrixCoeff 1 (intrinsicNormalizedDefect z ρ σ Dt G) := by
    have hh := congrArg (polyMatrixCoeff 1) (intrinsicNormalizedDefect_skew z ρ σ Dt G)
    apply Matrix.ext
    intro i j
    have hij := congrFun (congrFun hh i) j
    simpa [polyMatrixCoeff, Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply, Polynomial.coeff_neg] using hij
  have hfzero : F = 0 := by
    apply polynomial_matrix_factor_completion (1 : Matrix (Fin N) (Fin N) ℝ) p F hp0
    · intro i j
      rw [← hpdeg] at hd
      simpa only [hF, Matrix.smul_apply, smul_eq_mul] using hd.1 i j
    · intro i j
      simpa only [hF, Matrix.smul_apply, smul_eq_mul, hpdeg] using hd.2 i j
    · simpa only [hF, polyMatrixCoeff] using ho.1
    · simpa only [hF, polyMatrixCoeff] using ho.2
    · simpa only [hF, polyMatrixCoeff] using hs
  rw [hF,hfzero,smul_zero]

theorem nonlinearRoot_distinct_wronskian_polynomials_zero
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hv : vacMix ρ σ ≠ 0)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i) :
    (∀ i j, nonlinearDistinctUPolynomial z ρ σ Dt G i j = 0) ∧
    (∀ i j, nonlinearDistinctVPolynomial z ρ σ Dt G i j = 0) := by
  have hn := nonlinearRoot_intrinsicNormalizedDefect_zero z ρ σ K Dt G hz hv hroot hK
  have ht := intrinsicNormalizedDefect_transport z ρ σ Dt G (fun u => ne_of_gt (hz u)) hv
  rw [hn,smul_zero] at ht
  have hE := polynomial_matrix_congruence_cancel _ _
    (intrinsicNormalizationMatrix_det_ne_zero ρ σ) ht.symm
  have hq : intrinsicRatePairPolynomial z ≠ 0 := by
    intro he
    have hh := intrinsicRatePairPolynomial_coeff_zero_ne_zero z hz
    simp [he] at hh
  have hW : intrinsicWronskianMatrix z ρ σ Dt G = 0 := by
    apply Matrix.ext
    intro i j
    have hh := congrFun (congrFun hE i) j
    exact (mul_eq_zero.mp hh).resolve_left hq
  constructor
  · intro i j
    exact congrFun (congrFun hW (Sum.inl i)) (Sum.inr j)
  · intro i j
    exact congrFun (congrFun hW (Sum.inr i)) (Sum.inr j)

theorem nonlinearRoot_automatic_finite_wronskian [DecidableEq ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hv : vacMix ρ σ ≠ 0)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i) :
    NonlinearFiniteWronskianCertificate z ρ σ Dt G := by
  classical
  apply nonlinearRoot_fixed_origin_certificate_implies_finite_wronskian z ρ σ K Dt G hz hroot hK
  apply (nonlinearRoot_fixed_origin_certificate_iff_distinct_polynomials_zero z ρ σ K Dt G hz hroot hK).mpr
  exact nonlinearRoot_distinct_wronskian_polynomials_zero z ρ σ K Dt G hz hv hroot hK

end FMSA.ExactMSA.MultiTailMixture
