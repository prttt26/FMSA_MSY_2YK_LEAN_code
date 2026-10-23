import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearNormalizedTransport

/-! Finite reflected factors survive normalization without density cancellation. -/
noncomputable section
open Polynomial MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem intrinsicRatePairPolynomial_coeff_zero_ne_zero (z : ι → ℝ) (hz : ∀ u, 0 < z u) :
    (intrinsicRatePairPolynomial z).coeff 0 ≠ 0 := by
  have hp : (nonlinearDistinctRatePolynomial z).eval 0 ≠ 0 := by
    rw [nonlinearDistinctRatePolynomial_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro r hr
    have hh := nonlinearDistinctRates_positive z hz r hr
    simpa using ne_of_gt hh
  simpa only [intrinsicRatePairPolynomial, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
    neg_zero] using mul_ne_zero hp hp

theorem nonlinearDistinctReflectedRates_neg_mem (z : ι → ℝ) (r : ℝ)
    (hr : r ∈ nonlinearDistinctReflectedRates z) : -r ∈ nonlinearDistinctReflectedRates z := by
  classical
  rcases Finset.mem_union.mp hr with hp | hm
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r,hp,rfl⟩)
  · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_union_left _ (by simpa using ht)

theorem nonlinearDistinctPoleFactor_eval_at_member (z : ι → ℝ) (r : ℝ)
    (hr : r ∈ nonlinearDistinctReflectedRates z) : (nonlinearDistinctPoleFactor z).eval r = 0 := by
  classical
  simp only [nonlinearDistinctPoleFactor, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hr (by simp)

theorem nonlinearDistinctPoleFactor_dvd_reflection (z : ι → ℝ) (p : Polynomial ℝ)
    (h : nonlinearDistinctPoleFactor z ∣ p) :
    nonlinearDistinctPoleFactor z ∣ p.comp (-X) := by
  obtain ⟨q,rfl⟩ := h
  apply nonlinearDistinctPoleFactor_dvd_of_roots
  intro r hr
  simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_mul]
  rw [nonlinearDistinctPoleFactor_eval_at_member z (-r)
    (nonlinearDistinctReflectedRates_neg_mem z r hr), zero_mul]

theorem nonlinearRoot_intrinsicWronskian_factor
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j = K u j i) :
    ∃ W : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ),
      intrinsicWronskianMatrix z ρ σ Dt G = nonlinearDistinctPoleFactor z • W := by
  classical
  have hd (i j : Fin N ⊕ Fin N) :
      nonlinearDistinctPoleFactor z ∣ intrinsicWronskianMatrix z ρ σ Dt G i j := by
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        exact dvd_neg.mpr (nonlinearDistinctPoleFactor_dvd_reflection z _
          (nonlinearRoot_distinct_wronskian_pole_factor_dvd z ρ σ K Dt G hz hroot hK i j).2)
      | inr j => exact (nonlinearRoot_distinct_wronskian_pole_factor_dvd z ρ σ K Dt G hz hroot hK i j).1
    | inr i =>
      cases j with
      | inl j => exact dvd_neg.mpr (nonlinearRoot_distinct_wronskian_pole_factor_dvd z ρ σ K Dt G hz hroot hK j i).1
      | inr j => exact (nonlinearRoot_distinct_wronskian_pole_factor_dvd z ρ σ K Dt G hz hroot hK i j).2
  refine ⟨fun i j => Classical.choose (hd i j), ?_⟩
  apply Matrix.ext
  intro i j
  exact Classical.choose_spec (hd i j)

theorem nonlinearRoot_intrinsicNormalizedDefect_factor
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hv : vacMix ρ σ ≠ 0)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i) :
    ∃ F : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ),
      intrinsicNormalizedDefect z ρ σ Dt G =
        (intrinsicRatePairPolynomial z*nonlinearDistinctPoleFactor z) • F := by
  classical
  obtain ⟨W,hW⟩ := nonlinearRoot_intrinsicWronskian_factor z ρ σ K Dt G hz hroot hK
  have ht := intrinsicNormalizedDefect_transport z ρ σ Dt G (fun u => ne_of_gt (hz u)) hv
  rw [hW, smul_smul, Matrix.mul_smul, Matrix.smul_mul] at ht
  have hp0 : (intrinsicRatePairPolynomial z*nonlinearDistinctPoleFactor z).coeff 0 ≠ 0 := by
    rw [Polynomial.mul_coeff_zero]
    exact mul_ne_zero (intrinsicRatePairPolynomial_coeff_zero_ne_zero z hz)
      (by simpa only [Polynomial.coeff_zero_eq_eval_zero] using
        nonlinearDistinctPoleFactor_eval_zero_ne_zero z hz)
  have hd (i j : Fin N ⊕ Fin N) :
      intrinsicRatePairPolynomial z*nonlinearDistinctPoleFactor z ∣
        intrinsicNormalizedDefect z ρ σ Dt G i j := by
    apply polynomial_cancel_origin_power_dvd _ _ 10 hp0
    refine ⟨(intrinsicNormalizationMatrix ρ σ*W*(intrinsicNormalizationMatrix ρ σ).transpose) i j, ?_⟩
    exact congrFun (congrFun ht i) j
  refine ⟨fun i j => Classical.choose (hd i j), ?_⟩
  apply Matrix.ext
  intro i j
  exact Classical.choose_spec (hd i j)

end FMSA.ExactMSA.MultiTailMixture
