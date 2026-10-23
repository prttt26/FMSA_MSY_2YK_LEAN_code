import LeanCode.YukawaOZMix.MSABHierarchy
import LeanCode.YukawaOZ.MSABlumHoyeSystem
import LeanCode.YukawaOZ.MSABaxterKSpace

/-! Actual BH jets and one-sided renewal source numerators. These are distinct
from Fourier-OZ B. No finite representation of an unknown RDF is assumed. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FMSA.ExactMSA.BSource

abbrev jet (f : ℝ → ℝ) (n : ℕ) : ℝ := iteratedDeriv n f 0 / (n.factorial : ℝ)

theorem normalized_mul (f g : ℝ → ℝ) (n : ℕ)
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0) :
    jet (fun t => f t * g t) n =
      ∑ j ∈ Finset.range (n + 1), jet f j * jet g (n - j) := by
  unfold jet
  rw [iteratedDeriv_fun_mul hf hg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hc : (n.choose j : ℝ) * (j.factorial : ℝ) * ((n - j).factorial : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hnf : ((n - j).factorial : ℝ) ≠ 0 := by positivity
  have hnn : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination (iteratedDeriv j f 0 * iteratedDeriv (n - j) g 0) * hc

def lowerProduct (D G : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n - 1), D (j + 1) * G (n - (j + 1))

theorem convolution_split (D G : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range (n + 1), D j * G (n - j)) =
      D 0 * G n + D n * G 0 + lowerProduct D G n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp [lowerProduct, Nat.succ_sub_succ_eq_sub, Nat.add_sub_add_right]
  ring

theorem bhFRest_affine (xi z G G0 : ℝ) :
    bhFRest xi z G = bhFRest xi z G0 +
      (bhFRest xi z (G0 + 1) - bhFRest xi z G0) * (G - G0) := by
  simp only [bhFRest, Mtil, Ntil, tailtil, gam]
  ring

theorem bhPRest_affine (xi z G G0 : ℝ) :
    bhPRest xi z G = bhPRest xi z G0 +
      (bhPRest xi z (G0 + 1) - bhPRest xi z G0) * (G - G0) := by
  unfold bhPRest Mtil Ntil gam
  ring

theorem solve_D_order (D F : ℕ → ℝ) (n : ℕ) (a : ℝ)
    (hn : 0 < n) (hD0 : D 0 = 0) (hF0 : F 0 ≠ 0)
    (heq : (∑ j ∈ Finset.range (n + 1), D j * F (n - j)) =
      if n = 1 then a else 0) :
    D n = ((if n = 1 then a else 0) - lowerProduct D F n) / F 0 := by
  rw [convolution_split D F n hn, hD0, zero_mul, zero_add] at heq
  apply (eq_div_iff hF0).mpr
  linarith

theorem solve_G_order (G F P : ℕ → ℝ) (n : ℕ) (c : ℝ)
    (hn : 0 < n) (hF0 : F 0 ≠ 0) (hc : c ≠ 0)
    (heq : c * (∑ j ∈ Finset.range (n + 1), G j * F (n - j)) = P n) :
    G n = (P n / c - G 0 * F n - lowerProduct G F n) / F 0 := by
  rw [convolution_split G F n hn] at heq
  apply (eq_div_iff hF0).mpr
  have h : G 0 * F n + G n * F 0 + lowerProduct G F n = P n / c := by
    apply (eq_div_iff hc).mpr
    nlinarith [heq]
  linarith

def sourceNumerator (Q0 f0 fn Qn : ℂ) : ℂ := Q0 * fn - f0 * Qn

theorem source_reconstruction (Q0 f0 Y0 Yn Qn fn lower : ℂ)
    (hzero : Y0 * Q0 = f0) (hn : Yn * Q0 + Y0 * Qn + lower = fn) :
    Q0 ^ 2 * Yn + Q0 * lower = sourceNumerator Q0 f0 fn Qn := by
  unfold sourceNumerator
  linear_combination Q0 * hn - Qn * hzero

theorem matrix_source_reconstruction {N : ℕ}
    (Q0 f0 Y0 Yn Qn fn lower : Matrix (Fin N) (Fin N) ℂ)
    (hzero : Y0 * Q0 = f0) (hsym : Y0ᵀ = Y0)
    (hn : Yn * Q0 + Y0 * Qn + lower = fn) :
    Q0ᵀ * Yn * Q0 + Q0ᵀ * lower = Q0ᵀ * fn - f0ᵀ * Qn := by
  have hleft : Q0ᵀ * Y0 = f0ᵀ := by
    rw [← hzero, Matrix.transpose_mul, hsym]
  calc
    _ = Q0ᵀ * (Yn * Q0 + Y0 * Qn + lower) - (Q0ᵀ * Y0) * Qn := by
      simp only [Matrix.mul_add, Matrix.mul_assoc]
      abel
    _ = _ := by rw [hn, hleft]

theorem fourier_second_order {N : ℕ}
    (F S0 H1 H2 C1 C2 : Matrix (Fin N) (Fin N) ℂ)
    (hFS : F * S0 = 1) (hfirst : H1 * F = S0 * C1)
    (hsecond : H2 * F = S0 * C2 + H1 * C1) :
    C2 = F * H2 * F - C1 * S0 * C1 := by
  have hSF : S0 * F = 1 := mul_eq_one_comm.mp hFS
  have hFH : F * H1 = C1 * S0 := by
    have h := congrArg (fun X => F * X * S0) hfirst
    have hright : F * (S0 * (C1 * S0)) = C1 * S0 := by
      rw [← Matrix.mul_assoc, hFS, Matrix.one_mul]
    simpa only [Matrix.mul_assoc, hFS, Matrix.mul_one, hright] using h
  rw [BHierarchy.oz_order_dcf F S0 H2 C2 (H1 * C1) hFS hsecond,
    ← Matrix.mul_assoc, hFH]

/-- An everywhere-finite Fourier numerator is impossible at this zero. -/
theorem fourier_zero_obstruction (C Qminus B : ℂ)
    (hQ : Qminus = 0) (hC : C ≠ 0) : C ≠ Qminus ^ 2 * B := by
  simpa [hQ] using hC

end FMSA.ExactMSA.BSource
