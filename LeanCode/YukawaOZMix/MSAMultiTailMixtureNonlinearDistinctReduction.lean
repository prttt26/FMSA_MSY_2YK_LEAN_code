import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearDistinctWronskian

/-! The finite pole factors cancel from actual BH-root Wronskians.
The remaining degrees are bounded independently of the number of tails. -/
noncomputable section
open Real Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def nonlinearDistinctReflectedRates (z : ι → ℝ) : Finset ℝ := by
  classical
  exact nonlinearDistinctRates z ∪ (nonlinearDistinctRates z).image Neg.neg

def nonlinearDistinctPoleFactor (z : ι → ℝ) : Polynomial ℝ :=
  ∏ r ∈ nonlinearDistinctReflectedRates z, (X - Polynomial.C r)

theorem nonlinearDistinctReflectedRates_card (z : ι → ℝ) (hz : ∀ u, 0 < z u) :
    (nonlinearDistinctReflectedRates z).card = 2 * (nonlinearDistinctRates z).card := by
  classical
  have hd : Disjoint (nonlinearDistinctRates z)
      ((nonlinearDistinctRates z).image Neg.neg) := by
    apply Finset.disjoint_left.mpr
    intro r hr hn
    obtain ⟨t, ht, htr⟩ := Finset.mem_image.mp hn
    have hpr := nonlinearDistinctRates_positive z hz r hr
    have hpt := nonlinearDistinctRates_positive z hz t ht
    linarith
  rw [nonlinearDistinctReflectedRates, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ neg_injective]
  omega

theorem nonlinearDistinctReflectedRates_ne_zero (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (r : ℝ) (hr : r ∈ nonlinearDistinctReflectedRates z) : r ≠ 0 := by
  classical
  rcases Finset.mem_union.mp hr with hp | hn
  · exact (nonlinearDistinctRates_positive z hz r hp).ne'
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact neg_ne_zero.mpr (nonlinearDistinctRates_positive z hz t ht).ne'

theorem nonlinearDistinctPoleFactor_monic (z : ι → ℝ) :
    (nonlinearDistinctPoleFactor z).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun r _ => Polynomial.monic_X_sub_C r)

theorem nonlinearDistinctPoleFactor_degree (z : ι → ℝ) (hz : ∀ u, 0 < z u) :
    (nonlinearDistinctPoleFactor z).natDegree = 2 * (nonlinearDistinctRates z).card := by
  rw [nonlinearDistinctPoleFactor, Polynomial.natDegree_prod_of_monic _ _
    (fun r _ => Polynomial.monic_X_sub_C r)]
  simpa using nonlinearDistinctReflectedRates_card z hz

theorem nonlinearDistinctPoleFactor_eval_zero_ne_zero (z : ι → ℝ)
    (hz : ∀ u, 0 < z u) : (nonlinearDistinctPoleFactor z).eval 0 ≠ 0 := by
  simp only [nonlinearDistinctPoleFactor, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  exact neg_ne_zero.mpr (nonlinearDistinctReflectedRates_ne_zero z hz r hr)

theorem nonlinearDistinctPoleFactor_dvd_of_roots (z : ι → ℝ) (p : Polynomial ℝ)
    (hp : ∀ r ∈ nonlinearDistinctReflectedRates z, p.eval r = 0) :
    nonlinearDistinctPoleFactor z ∣ p := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro a _ b _ hab
    exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id hab
  · intro r hr
    exact Polynomial.dvd_iff_isRoot.mpr (hp r hr)

theorem nonlinearRoot_distinct_wronskian_pole_factor_dvd
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) :
    nonlinearDistinctPoleFactor z ∣ nonlinearDistinctUPolynomial z ρ σ Dt G i j ∧
    nonlinearDistinctPoleFactor z ∣ nonlinearDistinctVPolynomial z ρ σ Dt G i j := by
  classical
  constructor <;> apply nonlinearDistinctPoleFactor_dvd_of_roots
  · intro r hr
    rcases Finset.mem_union.mp hr with hp | hn
    · exact (nonlinearRoot_distinct_wronskian_zero_at_all_rates
        z ρ σ K Dt G hz hroot hK r hp i j).1
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
      exact (nonlinearRoot_distinct_wronskian_zero_at_all_rates
        z ρ σ K Dt G hz hroot hK t ht i j).2.1
  · intro r hr
    rcases Finset.mem_union.mp hr with hp | hn
    · exact (nonlinearRoot_distinct_wronskian_zero_at_all_rates
        z ρ σ K Dt G hz hroot hK r hp i j).2.2.1
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
      exact (nonlinearRoot_distinct_wronskian_zero_at_all_rates
        z ρ σ K Dt G hz hroot hK t ht i j).2.2.2

theorem polynomial_comp_neg_X_degree_le (p : Polynomial ℝ) :
    (p.comp (-X)).natDegree ≤ p.natDegree := by
  simpa using (Polynomial.natDegree_comp_le (p := p) (q := -X))

theorem nonlinearDistinctUPolynomial_degree_le (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    (nonlinearDistinctUPolynomial z ρ σ Dt G i j).natDegree ≤
      2 * (nonlinearDistinctRates z).card + 5 := by
  classical
  let m := (nonlinearDistinctRates z).card
  have hJ (a b : Fin N) := nonlinearDistinctJNumerator_degree_le z ρ σ Dt G a b
  have hL (a b : Fin N) := nonlinearDistinctLNumerator_degree_le z ρ σ Dt G a b
  have hD := nonlinearDistinctDenominator_degree z
  have hDc : ((nonlinearDistinctDenominator z).comp (-X)).natDegree ≤ m+2 :=
    (polynomial_comp_neg_X_degree_le _).trans (le_of_eq hD)
  have hJc (a b : Fin N) :
      ((nonlinearDistinctJNumerator z ρ σ Dt G a b).comp (-X)).natDegree ≤ m+1 :=
    (polynomial_comp_neg_X_degree_le _).trans (hJ a b)
  have hLc (a b : Fin N) :
      ((nonlinearDistinctLNumerator z ρ σ Dt G a b).comp (-X)).natDegree ≤ m+2 :=
    (polynomial_comp_neg_X_degree_le _).trans (hL a b)
  have hm {p q : Polynomial ℝ} {a b : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
      (p*q).natDegree ≤ a+b := (Polynomial.natDegree_mul_le).trans (Nat.add_le_add hp hq)
  have hn {p : Polynomial ℝ} {a : ℕ} (hp : p.natDegree ≤ a) : (-p).natDegree ≤ a := by
    simpa using hp
  unfold nonlinearDistinctUPolynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (hm (hm (hn (hL i j)) (show (X : Polynomial ℝ).natDegree ≤ 1 by simp)) hDc).trans (by omega)
    · exact (hm (hm (hLc j i) (show (X : Polynomial ℝ).natDegree ≤ 1 by simp)) (le_of_eq hD)).trans (by omega)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro a _
    have hs : ((nonlinearDistinctJNumerator z ρ σ Dt G i a).comp (-X) *
        nonlinearDistinctJNumerator z ρ σ Dt G j a -
        nonlinearDistinctLNumerator z ρ σ Dt G i a *
        (nonlinearDistinctLNumerator z ρ σ Dt G j a).comp (-X)).natDegree ≤ 2*m+4 :=
      (Polynomial.natDegree_sub_le _ _).trans
        (max_le ((hm (hJc i a) (hJ j a)).trans (by omega))
          ((hm (hL i a) (hLc j a)).trans (by omega)))
    exact (hm (show (Polynomial.C (ρ a)).natDegree ≤ 0 by simp) hs).trans (by omega)

theorem nonlinearDistinctVPolynomial_degree_le (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    (nonlinearDistinctVPolynomial z ρ σ Dt G i j).natDegree ≤
      2 * (nonlinearDistinctRates z).card + 4 := by
  classical
  let m := (nonlinearDistinctRates z).card
  have hJ (a b : Fin N) := nonlinearDistinctJNumerator_degree_le z ρ σ Dt G a b
  have hL (a b : Fin N) := nonlinearDistinctLNumerator_degree_le z ρ σ Dt G a b
  have hD := nonlinearDistinctDenominator_degree z
  have hDc : ((nonlinearDistinctDenominator z).comp (-X)).natDegree ≤ m+2 :=
    (polynomial_comp_neg_X_degree_le _).trans (le_of_eq hD)
  have hLc (a b : Fin N) :
      ((nonlinearDistinctLNumerator z ρ σ Dt G a b).comp (-X)).natDegree ≤ m+2 :=
    (polynomial_comp_neg_X_degree_le _).trans (hL a b)
  have hm {p q : Polynomial ℝ} {a b : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
      (p*q).natDegree ≤ a+b := (Polynomial.natDegree_mul_le).trans (Nat.add_le_add hp hq)
  unfold nonlinearDistinctVPolynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · have hs := (Polynomial.natDegree_sub_le _ _).trans (max_le (hJ i j) (hJ j i))
    exact (hm (hm hs (show (X : Polynomial ℝ).natDegree ≤ 1 by simp)) hDc).trans (by omega)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro a _
    have hs : (nonlinearDistinctJNumerator z ρ σ Dt G i a *
        (nonlinearDistinctLNumerator z ρ σ Dt G j a).comp (-X) -
        (nonlinearDistinctLNumerator z ρ σ Dt G i a).comp (-X) *
        nonlinearDistinctJNumerator z ρ σ Dt G j a).natDegree ≤ 2*m+3 :=
      (Polynomial.natDegree_sub_le _ _).trans
        (max_le ((hm (hJ i a) (hLc j a)).trans (by omega))
          ((hm (hLc i a) (hJ j a)).trans (by omega)))
    exact (hm (show (Polynomial.C (ρ a)).natDegree ≤ 0 by simp) hs).trans (by omega)

theorem nonlinearDistinctPoleFactor_fixed_degree_quotient (z : ι → ℝ)
    (hz : ∀ u, 0 < z u) (p : Polynomial ℝ) (b : ℕ)
    (hdiv : nonlinearDistinctPoleFactor z ∣ p)
    (hdeg : p.natDegree ≤ 2*(nonlinearDistinctRates z).card+b) :
    ∃ q : Polynomial ℝ, p = nonlinearDistinctPoleFactor z*q ∧ q.natDegree ≤ b := by
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨q, hq, ?_⟩
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [hq, Polynomial.natDegree_mul
      (nonlinearDistinctPoleFactor_monic z).ne_zero hq0,
      nonlinearDistinctPoleFactor_degree z hz] at hdeg
    omega

theorem nonlinearRoot_distinct_wronskian_fixed_degree_remainders
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) :
    (∃ u : Polynomial ℝ,
      nonlinearDistinctUPolynomial z ρ σ Dt G i j = nonlinearDistinctPoleFactor z*u ∧
        u.natDegree ≤ 5) ∧
    (∃ v : Polynomial ℝ,
      nonlinearDistinctVPolynomial z ρ σ Dt G i j = nonlinearDistinctPoleFactor z*v ∧
        v.natDegree ≤ 4) := by
  have hd := nonlinearRoot_distinct_wronskian_pole_factor_dvd
    z ρ σ K Dt G hz hroot hK i j
  exact ⟨nonlinearDistinctPoleFactor_fixed_degree_quotient z hz _ 5 hd.1
      (nonlinearDistinctUPolynomial_degree_le z ρ σ Dt G i j),
    nonlinearDistinctPoleFactor_fixed_degree_quotient z hz _ 4 hd.2
      (nonlinearDistinctVPolynomial_degree_le z ρ σ Dt G i j)⟩

end FMSA.ExactMSA.MultiTailMixture
