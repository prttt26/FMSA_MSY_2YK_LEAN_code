import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearDistinctReduction

/-! A tail-count independent certificate and its connection to the existing
labelled Wronskian certificate. These coefficient checks remain hypotheses;
this module does not assert that a general BH root automatically passes them. -/
noncomputable section
open Real Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def nonlinearDistinctUQuotient (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : Polynomial ℝ :=
  nonlinearDistinctUPolynomial z ρ σ Dt G i j /ₘ nonlinearDistinctPoleFactor z

def nonlinearDistinctVQuotient (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : Polynomial ℝ :=
  nonlinearDistinctVPolynomial z ρ σ Dt G i j /ₘ nonlinearDistinctPoleFactor z

def NonlinearFixedOriginWronskianCertificate (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) : Prop :=
  (∀ i j, ∀ n ∈ Finset.range 6, (nonlinearDistinctUQuotient z ρ σ Dt G i j).coeff n = 0) ∧
  (∀ i j, ∀ n ∈ Finset.range 5, (nonlinearDistinctVQuotient z ρ σ Dt G i j).coeff n = 0)

theorem nonlinearRoot_distinct_quotient_degrees
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) :
    (nonlinearDistinctUQuotient z ρ σ Dt G i j).natDegree ≤ 5 ∧
    (nonlinearDistinctVQuotient z ρ σ Dt G i j).natDegree ≤ 4 := by
  obtain ⟨⟨u, hu, hdu⟩, ⟨v, hv, hdv⟩⟩ :=
    nonlinearRoot_distinct_wronskian_fixed_degree_remainders z ρ σ K Dt G hz hroot hK i j
  unfold nonlinearDistinctUQuotient nonlinearDistinctVQuotient
  rw [hu, hv, Polynomial.mul_divByMonic_cancel_left _ (nonlinearDistinctPoleFactor_monic z),
    Polynomial.mul_divByMonic_cancel_left _ (nonlinearDistinctPoleFactor_monic z)]
  exact ⟨hdu, hdv⟩

theorem nonlinearRoot_fixed_origin_certificate_iff_distinct_polynomials_zero
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j = K u j i) :
    NonlinearFixedOriginWronskianCertificate z ρ σ Dt G ↔
      (∀ i j, nonlinearDistinctUPolynomial z ρ σ Dt G i j = 0) ∧
      (∀ i j, nonlinearDistinctVPolynomial z ρ σ Dt G i j = 0) := by
  constructor
  · intro hc
    constructor
    · intro i j
      obtain ⟨u, hu, hdu⟩ :=
        (nonlinearRoot_distinct_wronskian_fixed_degree_remainders z ρ σ K Dt G hz hroot hK i j).1
      have he : nonlinearDistinctUQuotient z ρ σ Dt G i j = u := by
        unfold nonlinearDistinctUQuotient
        rw [hu, Polynomial.mul_divByMonic_cancel_left _ (nonlinearDistinctPoleFactor_monic z)]
      have h0 : u = 0 := finite_polynomial_zero_of_coefficients u (by
        intro n hn
        rw [← he]
        exact hc.1 i j n (Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hn
          omega)))
      simp [hu, h0]
    · intro i j
      obtain ⟨v, hv, hdv⟩ :=
        (nonlinearRoot_distinct_wronskian_fixed_degree_remainders z ρ σ K Dt G hz hroot hK i j).2
      have he : nonlinearDistinctVQuotient z ρ σ Dt G i j = v := by
        unfold nonlinearDistinctVQuotient
        rw [hv, Polynomial.mul_divByMonic_cancel_left _ (nonlinearDistinctPoleFactor_monic z)]
      have h0 : v = 0 := finite_polynomial_zero_of_coefficients v (by
        intro n hn
        rw [← he]
        exact hc.2 i j n (Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hn
          omega)))
      simp [hv, h0]
  · intro hc
    constructor
    · intro i j n _
      simp [nonlinearDistinctUQuotient, hc.1 i j]
    · intro i j n _
      simp [nonlinearDistinctVQuotient, hc.2 i j]

theorem nonlinearDistinctJNumerator_cross_identity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (i j : Fin N) :
    nonlinearDistinctDenominator z * nonlinearJNumerator z ρ σ Dt G i j =
      nonlinearRationalDenominator z * nonlinearDistinctJNumerator z ρ σ Dt G i j := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℝ)).mono
  intro s hs
  have hsp (u : ι) : s+z u ≠ 0 := (add_pos hs (hz u)).ne'
  simp only [Set.mem_setOf_eq, Polynomial.eval_mul,
    nonlinearJNumerator_eval z ρ σ Dt G hz s hs,
    nonlinearDistinctJNumerator_eval z ρ σ Dt G s hs.ne' hsp]
  ring

theorem nonlinearDistinctLNumerator_cross_identity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (i j : Fin N) :
    nonlinearDistinctDenominator z * nonlinearLNumerator z ρ σ Dt G i j =
      nonlinearRationalDenominator z * nonlinearDistinctLNumerator z ρ σ Dt G i j := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℝ)).mono
  intro s hs
  have hsp (u : ι) : s+z u ≠ 0 := (add_pos hs (hz u)).ne'
  simp only [Set.mem_setOf_eq, Polynomial.eval_mul,
    nonlinearLNumerator_eval z ρ σ Dt G hz s hs,
    nonlinearDistinctLNumerator_eval z ρ σ Dt G s hs.ne' hsp]
  ring

theorem wronskian_cross_denominators
    {R : Type*} [CommRing R] (d dm e em s : R) (ρ : Fin N → R)
    (J L Jm Lm j l jm lm : Fin N → Fin N → R)
    (hJ : ∀ a b, d*J a b = e*j a b) (hL : ∀ a b, d*L a b = e*l a b)
    (hJm : ∀ a b, dm*Jm a b = em*jm a b)
    (hLm : ∀ a b, dm*Lm a b = em*lm a b) (a b : Fin N) :
    d*dm*(-L a b*s*em + Lm b a*s*e +
      ∑ m, ρ m*(Jm a m*J b m-L a m*Lm b m)) =
      e*em*(-l a b*s*dm + lm b a*s*d +
        ∑ m, ρ m*(jm a m*j b m-l a m*lm b m)) ∧
    d*dm*((J a b-J b a)*s*em +
      ∑ m, ρ m*(J a m*Lm b m-Lm a m*J b m)) =
      e*em*((j a b-j b a)*s*dm +
        ∑ m, ρ m*(j a m*lm b m-lm a m*j b m)) := by
  have hu : d*dm*(∑ m, ρ m*(Jm a m*J b m-L a m*Lm b m)) =
      e*em*(∑ m, ρ m*(jm a m*j b m-l a m*lm b m)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    calc
      _ = ρ m*((dm*Jm a m)*(d*J b m)-(d*L a m)*(dm*Lm b m)) := by ring
      _ = ρ m*((em*jm a m)*(e*j b m)-(e*l a m)*(em*lm b m)) := by
        rw [hJm, hJ, hL, hLm]
      _ = _ := by ring
  have hv : d*dm*(∑ m, ρ m*(J a m*Lm b m-Lm a m*J b m)) =
      e*em*(∑ m, ρ m*(j a m*lm b m-lm a m*j b m)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    calc
      _ = ρ m*((d*J a m)*(dm*Lm b m)-(dm*Lm a m)*(d*J b m)) := by ring
      _ = ρ m*((e*j a m)*(em*lm b m)-(em*lm a m)*(e*j b m)) := by
        rw [hJ, hLm, hLm, hJ]
      _ = _ := by ring
  constructor
  · calc
      _ = -(d*L a b)*s*(dm*em)+(dm*Lm b a)*s*(d*e) +
          d*dm*(∑ m, ρ m*(Jm a m*J b m-L a m*Lm b m)) := by ring
      _ = -(e*l a b)*s*(dm*em)+(em*lm b a)*s*(d*e) +
          e*em*(∑ m, ρ m*(jm a m*j b m-l a m*lm b m)) := by rw [hL, hLm, hu]
      _ = _ := by ring
  · calc
      _ = (d*J a b-d*J b a)*s*(dm*em) +
          d*dm*(∑ m, ρ m*(J a m*Lm b m-Lm a m*J b m)) := by ring
      _ = (e*j a b-e*j b a)*s*(dm*em) +
          e*em*(∑ m, ρ m*(j a m*lm b m-lm a m*j b m)) := by rw [hJ, hJ, hv]
      _ = _ := by ring

theorem nonlinearDistinctWronskian_cross_identity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (i j : Fin N) :
    nonlinearDistinctDenominator z * (nonlinearDistinctDenominator z).comp (-X) *
        nonlinearWronskianUPolynomial z ρ σ Dt G i j =
      nonlinearRationalDenominator z * (nonlinearRationalDenominator z).comp (-X) *
        nonlinearDistinctUPolynomial z ρ σ Dt G i j ∧
    nonlinearDistinctDenominator z * (nonlinearDistinctDenominator z).comp (-X) *
        nonlinearWronskianVPolynomial z ρ σ Dt G i j =
      nonlinearRationalDenominator z * (nonlinearRationalDenominator z).comp (-X) *
        nonlinearDistinctVPolynomial z ρ σ Dt G i j := by
  have hJ := nonlinearDistinctJNumerator_cross_identity z ρ σ Dt G hz
  have hL := nonlinearDistinctLNumerator_cross_identity z ρ σ Dt G hz
  have hJm (a b : Fin N) :
      (nonlinearDistinctDenominator z).comp (-X) *
        (nonlinearJNumerator z ρ σ Dt G a b).comp (-X) =
      (nonlinearRationalDenominator z).comp (-X) *
        (nonlinearDistinctJNumerator z ρ σ Dt G a b).comp (-X) := by
    simpa only [Polynomial.mul_comp] using
      congrArg (fun p : Polynomial ℝ => p.comp (-X)) (hJ a b)
  have hLm (a b : Fin N) :
      (nonlinearDistinctDenominator z).comp (-X) *
        (nonlinearLNumerator z ρ σ Dt G a b).comp (-X) =
      (nonlinearRationalDenominator z).comp (-X) *
        (nonlinearDistinctLNumerator z ρ σ Dt G a b).comp (-X) := by
    simpa only [Polynomial.mul_comp] using
      congrArg (fun p : Polynomial ℝ => p.comp (-X)) (hL a b)
  exact wronskian_cross_denominators
    (nonlinearDistinctDenominator z) ((nonlinearDistinctDenominator z).comp (-X))
    (nonlinearRationalDenominator z) ((nonlinearRationalDenominator z).comp (-X)) X
    (fun m => Polynomial.C (ρ m))
    (nonlinearJNumerator z ρ σ Dt G) (nonlinearLNumerator z ρ σ Dt G)
    (fun a b => (nonlinearJNumerator z ρ σ Dt G a b).comp (-X))
    (fun a b => (nonlinearLNumerator z ρ σ Dt G a b).comp (-X))
    (nonlinearDistinctJNumerator z ρ σ Dt G) (nonlinearDistinctLNumerator z ρ σ Dt G)
    (fun a b => (nonlinearDistinctJNumerator z ρ σ Dt G a b).comp (-X))
    (fun a b => (nonlinearDistinctLNumerator z ρ σ Dt G a b).comp (-X))
    hJ hL hJm hLm i j

theorem nonlinearDistinctDenominator_reflected_ne_zero (z : ι → ℝ) :
    nonlinearDistinctDenominator z * (nonlinearDistinctDenominator z).comp (-X) ≠ 0 := by
  have hd : nonlinearDistinctDenominator z ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero)
      (nonlinearDistinctRatePolynomial_monic z).ne_zero
  have hm : (nonlinearDistinctDenominator z).comp (-X) ≠ 0 := by
    intro he
    have hh := congrArg (fun p : Polynomial ℝ => p.comp (-X)) he
    simp only [Polynomial.comp_assoc, Polynomial.neg_comp, Polynomial.X_comp,
      neg_neg, Polynomial.comp_X, Polynomial.zero_comp] at hh
    exact hd hh
  exact mul_ne_zero hd hm

theorem nonlinearRoot_fixed_origin_certificate_implies_finite_wronskian
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j = K u j i)
    (hc : NonlinearFixedOriginWronskianCertificate z ρ σ Dt G) :
    NonlinearFiniteWronskianCertificate z ρ σ Dt G := by
  have hzpoly := (nonlinearRoot_fixed_origin_certificate_iff_distinct_polynomials_zero
    z ρ σ K Dt G hz hroot hK).mp hc
  have hn := nonlinearDistinctDenominator_reflected_ne_zero z
  constructor
  · intro i j n _
    have he := (nonlinearDistinctWronskian_cross_identity z ρ σ Dt G hz i j).1
    rw [hzpoly.1 i j, mul_zero] at he
    have hp := (mul_eq_zero.mp he).resolve_left hn
    simp [hp]
  · intro i j n _
    have he := (nonlinearDistinctWronskian_cross_identity z ρ σ Dt G hz i j).2
    rw [hzpoly.2 i j, mul_zero] at he
    have hp := (mul_eq_zero.mp he).resolve_left hn
    simp [hp]

theorem nonlinearRationalDenominator_reflected_ne_zero (z : ι → ℝ)
    (hz : ∀ u, 0 < z u) :
    nonlinearRationalDenominator z * (nonlinearRationalDenominator z).comp (-X) ≠ 0 := by
  have hd : nonlinearRationalDenominator z ≠ 0 := by
    intro he
    have hp := nonlinearRationalDenominator_eval_pos z hz 1 (by norm_num)
    rw [he, Polynomial.eval_zero] at hp
    exact (lt_irrefl 0) hp
  have hm : (nonlinearRationalDenominator z).comp (-X) ≠ 0 := by
    intro he
    have hh := congrArg (fun p : Polynomial ℝ => p.comp (-X)) he
    simp only [Polynomial.comp_assoc, Polynomial.neg_comp, Polynomial.X_comp,
      neg_neg, Polynomial.comp_X, Polynomial.zero_comp] at hh
    exact hd hh
  exact mul_ne_zero hd hm

theorem nonlinearRoot_fixed_origin_certificate_iff_finite_wronskian
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j = K u j i) :
    NonlinearFixedOriginWronskianCertificate z ρ σ Dt G ↔
      NonlinearFiniteWronskianCertificate z ρ σ Dt G := by
  constructor
  · exact nonlinearRoot_fixed_origin_certificate_implies_finite_wronskian
      z ρ σ K Dt G hz hroot hK
  · intro hc
    apply (nonlinearRoot_fixed_origin_certificate_iff_distinct_polynomials_zero
      z ρ σ K Dt G hz hroot hK).mpr
    have hn := nonlinearRationalDenominator_reflected_ne_zero z hz
    constructor
    · intro i j
      have he := (nonlinearDistinctWronskian_cross_identity z ρ σ Dt G hz i j).1
      rw [finite_polynomial_zero_of_coefficients _ (hc.1 i j), mul_zero] at he
      exact (mul_eq_zero.mp he.symm).resolve_left hn
    · intro i j
      have he := (nonlinearDistinctWronskian_cross_identity z ρ σ Dt G hz i j).2
      rw [finite_polynomial_zero_of_coefficients _ (hc.2 i j), mul_zero] at he
      exact (mul_eq_zero.mp he.symm).resolve_left hn

end FMSA.ExactMSA.MultiTailMixture
