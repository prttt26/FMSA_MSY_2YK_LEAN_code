import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearNormalizedTransport

/-! Infinity bounds on the reduced normalization, including its lower defect block. -/
noncomputable section
open Polynomial MSAMixture FMSA.MatrixQ0
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem polynomial_comp_neg_X_degree (p : Polynomial ℝ) :
    (p.comp (-X)).natDegree = p.natDegree := by
  have h := polynomial_comp_neg_X_degree_le p
  have hh := polynomial_comp_neg_X_degree_le (p.comp (-X))
  simp only [Polynomial.comp_assoc, Polynomial.neg_comp, Polynomial.X_comp,
    neg_neg, Polynomial.comp_X] at hh
  exact le_antisymm h hh

theorem intrinsicRatePairPolynomial_degree (z : ι → ℝ) :
    (intrinsicRatePairPolynomial z).natDegree = 2*(nonlinearDistinctRates z).card := by
  have hp := (nonlinearDistinctRatePolynomial_monic z).ne_zero
  have hpm : (nonlinearDistinctRatePolynomial z).comp (-X) ≠ 0 := by
    intro h
    have hh := congrArg (fun p : Polynomial ℝ => p.comp (-X)) h
    simp only [Polynomial.comp_assoc, Polynomial.neg_comp, Polynomial.X_comp,
      neg_neg, Polynomial.comp_X, Polynomial.zero_comp] at hh
    exact hp hh
  rw [intrinsicRatePairPolynomial, Polynomial.natDegree_mul hp hpm,
    polynomial_comp_neg_X_degree, nonlinearDistinctRatePolynomial_degree]
  omega

theorem intrinsicDPolynomial_degree (ρ σ : Fin N → ℝ) :
    PolyMatrixDegreeLE (intrinsicDPolynomial ρ σ) 2 := by
  apply polyMatrix_degree_add
  · apply polyMatrix_degree_add
    · exact fun i j => (polyMatrix_degree_term 0 _ i j).trans (by omega)
    · exact fun i j => (polyMatrix_degree_term 1 _ i j).trans (by omega)
  · exact polyMatrix_degree_term 2 _

theorem intrinsicDPolynomial_lower_off_degree (ρ σ : Fin N → ℝ) (i j : Fin N) :
    (intrinsicDPolynomial ρ σ (Sum.inr i) (Sum.inl j)).natDegree ≤ 1 := by
  have hz : polyMatrixTerm 2 (originIntrinsicD1 ρ σ) (Sum.inr i) (Sum.inl j) = 0 := by
    simp [polyMatrixTerm, originIntrinsicD1, originKernelMatrix, originLift,
      originJetD1, Matrix.fromBlocks]
  simp only [intrinsicDPolynomial, polyOriginD, Matrix.add_apply, hz, add_zero]
  exact Polynomial.natDegree_add_le _ _ |>.trans
    (max_le ((polyMatrix_degree_term 0 _ _ _).trans (by omega)) (polyMatrix_degree_term 1 _ _ _))

theorem intrinsicHNumerator_degree (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    PolyMatrixDegreeLE (intrinsicHNumerator z ρ σ Dt G) (2*(nonlinearDistinctRates z).card+2) := by
  have hp := nonlinearDistinctRatePolynomial_degree z
  have hpm := polynomial_comp_neg_X_degree (nonlinearDistinctRatePolynomial z)
  intro i j
  cases i <;> cases j
  all_goals
    rename_i i j
    simp only [intrinsicHNumerator, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_neg, polynomial_comp_neg_X_degree, hp]
    have hj := nonlinearDistinctJNumerator_degree_le z ρ σ Dt G i j
    have hl := nonlinearDistinctLNumerator_degree_le z ρ σ Dt G i j
    omega

theorem intrinsicHNumerator_lower_off_degree
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (i j : Fin N) :
    (intrinsicHNumerator z ρ σ Dt G (Sum.inr i) (Sum.inl j)).natDegree ≤
      2*(nonlinearDistinctRates z).card+1 := by
  simp only [intrinsicHNumerator, Matrix.fromBlocks_apply₂₁]
  have h := nonlinearDistinctJNumerator_degree_le z ρ σ Dt G i j
  have hp := nonlinearDistinctRatePolynomial_degree z
  have hm := Polynomial.natDegree_mul_le (p := nonlinearDistinctJNumerator z ρ σ Dt G i j)
    (q := (nonlinearDistinctRatePolynomial z).comp (-X))
  rw [polynomial_comp_neg_X_degree, hp] at hm
  omega

theorem intrinsicNormalizedNumerator_degree
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    PolyMatrixDegreeLE (intrinsicNormalizedNumerator z ρ σ Dt G)
      (2*(nonlinearDistinctRates z).card+5) ∧
    ∀ i j, (intrinsicNormalizedNumerator z ρ σ Dt G (Sum.inr i) (Sum.inl j)).natDegree ≤
      2*(nonlinearDistinctRates z).card+4 := by
  have hq : (intrinsicRatePairPolynomial z).natDegree ≤ 2*(nonlinearDistinctRates z).card :=
    le_of_eq (intrinsicRatePairPolynomial_degree z)
  have hd := intrinsicDPolynomial_degree ρ σ
  have hh := intrinsicHNumerator_degree z ρ σ Dt G
  have hx : (X^3 : Polynomial ℝ).natDegree ≤ 3 := by simp
  have ht := polyMatrix_degree_mul
    (polyMatrix_degree_mul hd (polyMatrix_degree_term 0 (originDensityMatrix ρ))) hh
  have h1 := polyMatrix_degree_smul hx (polyMatrix_degree_smul hq hd)
  have h2 := polyMatrix_degree_smul hx hh
  constructor
  · exact polyMatrix_degree_add (polyMatrix_degree_add
      (fun i j => (h1 i j).trans (by omega)) (fun i j => (h2 i j).trans (by omega)))
      (fun i j => (ht i j).trans (by omega))
  · intro i j
    have ha := Polynomial.natDegree_mul_le (p := (X^3 : Polynomial ℝ))
      (q := intrinsicRatePairPolynomial z*intrinsicDPolynomial ρ σ (Sum.inr i) (Sum.inl j))
    have hb := Polynomial.natDegree_mul_le (p := intrinsicRatePairPolynomial z)
      (q := intrinsicDPolynomial ρ σ (Sum.inr i) (Sum.inl j))
    have hc := intrinsicDPolynomial_lower_off_degree ρ σ i j
    have he := intrinsicHNumerator_lower_off_degree z ρ σ Dt G i j
    have hf := Polynomial.natDegree_mul_le (p := (X^3 : Polynomial ℝ))
      (q := intrinsicHNumerator z ρ σ Dt G (Sum.inr i) (Sum.inl j))
    simp only [intrinsicNormalizedNumerator, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    apply Polynomial.natDegree_add_le _ _ |>.trans
    apply max_le
    · apply Polynomial.natDegree_add_le _ _ |>.trans
      exact max_le (by omega) (by omega)
    · exact (ht (Sum.inr i) (Sum.inl j)).trans (by omega)

theorem intrinsicNormalizedReducedNumerator_degree
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0) :
    PolyMatrixDegreeLE (intrinsicNormalizedReducedNumerator z ρ σ Dt G)
      (2*(nonlinearDistinctRates z).card) ∧
    ∀ i j, intrinsicNormalizedReducedNumerator z ρ σ Dt G (Sum.inr i) (Sum.inl j) = 0 ∨
      (intrinsicNormalizedReducedNumerator z ρ σ Dt G (Sum.inr i) (Sum.inl j)).natDegree+1 ≤
        2*(nonlinearDistinctRates z).card := by
  have hd := intrinsicNormalizedNumerator_degree z ρ σ Dt G
  have he := intrinsicNormalizedNumerator_origin_factor z ρ σ Dt G hz hv
  rw [he] at hd
  have hx : (X^5 : Polynomial ℝ) ≠ 0 := by simp
  have hxd : (X^5 : Polynomial ℝ).natDegree = 5 := by simp
  constructor
  · intro i j
    apply polynomial_factor_degree_bound (X^5) _ (2*(nonlinearDistinctRates z).card) hx
    simpa only [hxd, Nat.add_comm, Matrix.smul_apply, smul_eq_mul] using hd.1 i j
  · intro i j
    by_cases h : intrinsicNormalizedReducedNumerator z ρ σ Dt G (Sum.inr i) (Sum.inl j) = 0
    · exact Or.inl h
    · right
      have hh := hd.2 i j
      change ((X^5 : Polynomial ℝ)*_).natDegree ≤ _ at hh
      rw [Polynomial.natDegree_mul hx h,hxd] at hh
      omega

theorem polynomialMatrix_omega_lower
    (M : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ)) (i j : Fin N) :
    (M*polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ))+
      polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ))*M.transpose)
      (Sum.inr i) (Sum.inr j) = M (Sum.inr i) (Sum.inl j)-M (Sum.inr j) (Sum.inl i) := by
  rw [polyMatrixTerm_omega]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  simp [completionOmega, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.transpose_apply, sub_eq_add_neg]

theorem intrinsicNormalizedDefect_degree
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0) :
    PolyMatrixDegreeLE (intrinsicNormalizedDefect z ρ σ Dt G)
      (4*(nonlinearDistinctRates z).card+1) ∧
    ∀ i j, (intrinsicNormalizedDefect z ρ σ Dt G (Sum.inr i) (Sum.inr j)).natDegree ≤
      4*(nonlinearDistinctRates z).card := by
  have hm := intrinsicNormalizedReducedNumerator_degree z ρ σ Dt G hz hv
  have hp := polyMatrix_degree_term 0 (originDensityMatrix ρ)
  have ho := polyMatrix_degree_term 0 (completionOmega (n := Fin N) (R := ℝ))
  have hmt := polyMatrix_degree_transpose hm.1
  have hquad := polyMatrix_degree_mul (polyMatrix_degree_mul (polyMatrix_degree_mul hm.1 hp) ho) hmt
  have hq : (X*intrinsicRatePairPolynomial z).natDegree ≤ 1+2*(nonlinearDistinctRates z).card := by
    apply Polynomial.natDegree_mul_le.trans
    simp [intrinsicRatePairPolynomial_degree]
  have hlinear := polyMatrix_degree_smul hq
    (polyMatrix_degree_add (by simpa using polyMatrix_degree_mul hm.1 ho)
      (by simpa using polyMatrix_degree_mul ho hmt))
  constructor
  · exact polyMatrix_degree_add (fun i j => (hlinear i j).trans (by omega))
      (fun i j => (hquad i j).trans (by omega))
  · intro i j
    unfold intrinsicNormalizedDefect intrinsicClearedDefect
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have he := polynomialMatrix_omega_lower (intrinsicNormalizedReducedNumerator z ρ σ Dt G) i j
    simp only [Matrix.add_apply] at he
    rw [he]
    apply Polynomial.natDegree_add_le _ _ |>.trans
    apply max_le
    · have hh (a b : Fin N) :
          ((X*intrinsicRatePairPolynomial z)*intrinsicNormalizedReducedNumerator z ρ σ Dt G
            (Sum.inr a) (Sum.inl b)).natDegree ≤ 4*(nonlinearDistinctRates z).card := by
        rcases hm.2 a b with he | hd
        · simp [he]
        · exact Polynomial.natDegree_mul_le.trans (by omega)
      rw [mul_sub]
      exact Polynomial.natDegree_sub_le _ _ |>.trans (max_le (hh i j) (hh j i))
    · exact (hquad (Sum.inr i) (Sum.inr j)).trans (by omega)

end FMSA.ExactMSA.MultiTailMixture
