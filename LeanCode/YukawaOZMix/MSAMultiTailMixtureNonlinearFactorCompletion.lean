import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearMatrixPolynomial
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearDistinctCertificate

/-! After finite factors cancel, an origin-zero polynomial defect of degree
at most one vanishes by its Lagrangian first coefficient and lower-block bound. -/
noncomputable section
open Polynomial
namespace FMSA.ExactMSA.MultiTailMixture
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem polynomial_factor_degree_bound (p q : Polynomial ℝ) (b : ℕ)
    (hp : p ≠ 0) (h : (p*q).natDegree ≤ p.natDegree+b) : q.natDegree ≤ b := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [Polynomial.natDegree_mul hp hq] at h
    omega

theorem polynomial_matrix_factor_completion
    (P : Matrix n n ℝ) (p : Polynomial ℝ)
    (F : Matrix (n ⊕ n) (n ⊕ n) (Polynomial ℝ))
    (hp0 : p.coeff 0 ≠ 0)
    (hdeg : ∀ i j, (p*F i j).natDegree ≤ p.natDegree+1)
    (hbottom : ∀ i j, (p*F (Sum.inr i) (Sum.inr j)).natDegree ≤ p.natDegree)
    (hzero : (p • F).map (fun f => f.coeff 0) = 0)
    (hU : completionU P * (p • F).map (fun f => f.coeff 1) = 0)
    (hskew : ((p • F).map (fun f => f.coeff 1)).transpose =
      -((p • F).map (fun f => f.coeff 1))) : F = 0 := by
  have hp : p ≠ 0 := by intro h; simp [h] at hp0
  have hd (i j : n ⊕ n) : (F i j).natDegree ≤ 1 :=
    polynomial_factor_degree_bound p (F i j) 1 hp (hdeg i j)
  have hb (i j : n) : (F (Sum.inr i) (Sum.inr j)).natDegree ≤ 0 :=
    polynomial_factor_degree_bound p (F (Sum.inr i) (Sum.inr j)) 0 hp (by
      simpa only [Nat.add_zero] using hbottom i j)
  have hz (i j : n ⊕ n) : (F i j).coeff 0 = 0 := by
    have h := congrFun (congrFun hzero i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Polynomial.mul_coeff_zero, Matrix.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left hp0
  have hc : (p • F).map (fun f => f.coeff 1) =
      p.coeff 0 • F.map (fun f => f.coeff 1) := by
    apply Matrix.ext
    intro i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Polynomial.mul_coeff_one, hz]
  have hU1 : completionU P * F.map (fun f => f.coeff 1) = 0 := by
    rw [hc, Matrix.mul_smul] at hU
    exact (smul_eq_zero.mp hU).resolve_left hp0
  have hskew1 : (F.map (fun f => f.coeff 1)).transpose =
      -(F.map (fun f => f.coeff 1)) := by
    rw [hc, Matrix.transpose_smul, ← smul_neg] at hskew
    exact smul_right_injective _ hp0 hskew
  have h22 : (F.map (fun f => f.coeff 1)).toBlocks₂₂ = 0 := by
    ext i j
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hb i j; omega)
  have h1 := completion_skew_origin_zero P (F.map (fun f => f.coeff 1)) hU1 hskew1 h22
  apply Matrix.ext
  intro i j
  apply Polynomial.ext
  intro d
  simp only [Matrix.zero_apply, Polynomial.coeff_zero]
  rcases d with _ | d
  · exact hz i j
  · rcases d with _ | d
    · exact congrFun (congrFun h1 i) j
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hd i j; omega)

end FMSA.ExactMSA.MultiTailMixture
