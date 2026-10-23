import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearCompletion
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Dimension-independent algebra of the HS-normalized origin jet.

The 2 × 2 matrices below index block positions, not species: a species sum
is an arbitrary linear functional. Thus these are uniform scalar kernel
identities for every mixture size. The normalized coefficients are still
to be connected to the actual rational defect numerator.
-/
noncomputable section
namespace FMSA.ExactMSA.MultiTailMixture

def originJetD1 (k x t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-k*x*t, 0; 0, k*x*t]
def originJetD2 (k m2 x t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(k*(x-t)-k^2*m2*x*t/2), -(k*(x+t)+k^2*m2*x*t/2);
    -(k*(x+t)+k^2*m2*x*t/2), -(k*(x-t)-k^2*m2*x*t/2)]
def originJetD3 (k m2 x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2*k+k^2*m2*x, 2*k+k^2*m2*x;
    -(2*k+k^2*m2*x), -(2*k+k^2*m2*x)]
def originJetH3 (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-a, -a; a, a]
def originJetH2 (x a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x*a/2-b, x*a/2+b; x*a/2+b, x*a/2-b]
def originJetH1 (x b c0 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-c0+x*b, -c0; c0, c0-x*b]
def originJetH0 (c1 w1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-w1, -c1; -c1, -w1]
def originJetHplus1 (c2 w2 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![w2, -c2; c2, -w2]
def originJetHplus2 (c3 w3 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-w3, -c3; -c3, -w3]

theorem originJet_highest_three_products_zero
    (k m2 x t a b c0 : ℝ) :
    originJetD3 k m2 x * originJetH3 a = 0 ∧
    originJetD2 k m2 x t * originJetH3 a +
      originJetD3 k m2 x * originJetH2 t a b = 0 ∧
    originJetD1 k x t * originJetH3 a +
      originJetD2 k m2 x t * originJetH2 t a b +
      originJetD3 k m2 x * originJetH1 t b c0 = 0 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [originJetD3, originJetH3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [originJetD1, originJetD2, originJetD3, originJetH3, originJetH2,
      originJetH1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem originJet_third_product_identity
    (k m2 x t a b c0 c1 w1 : ℝ) :
    originJetD1 k x t * originJetH2 t a b +
      originJetD2 k m2 x t * originJetH1 t b c0 +
      originJetD3 k m2 x * originJetH0 c1 w1 =
    let p := (k/2*((k*m2*x+2)*b-x*a))*t^2 -
      (2*k+k^2*m2*x)*(t*c0+w1+c1)
    !![p, p; -p, -p] := by
  dsimp only
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originJetD1, originJetD2, originJetD3, originJetH2, originJetH1,
      originJetH0, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem originJet_second_product_identity
    (k m2 x t b c0 c1 c2 w1 w2 : ℝ) :
    originJetD1 k x t * originJetH1 t b c0 +
      originJetD2 k m2 x t * originJetH0 c1 w1 +
      originJetD3 k m2 x * originJetHplus1 c2 w2 =
    let m := t*c0+w1+c1
    let r := w2+c2-t*(w1-c1)/2
    let p := k*x*m-k*x*t^2*b+(2*k+k^2*m2*x)*r
    let q := k*x*m-(2*k+k^2*m2*x)*r
    !![p, q; q, p] := by
  dsimp only
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originJetD1, originJetD2, originJetD3, originJetH1, originJetH0,
      originJetHplus1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def originJetResidueProduct (k m2 x t c1 c2 c3 w1 w2 w3 : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  originJetD1 k x t * originJetH0 c1 w1 +
    originJetD2 k m2 x t * originJetHplus1 c2 w2 +
    originJetD3 k m2 x * originJetHplus2 c3 w3

theorem originJet_residue_product_projections
    (k m2 x t c1 c2 c3 w1 w2 w3 : ℝ) :
    let F := originJetResidueProduct k m2 x t c1 c2 c3 w1 w2 w3
    let r := w2+c2-t*(w1-c1)/2
    F 0 0 + F 1 0 = -2*k*x*r ∧
    F 0 1 + F 1 1 = 2*k*x*r ∧
    F 0 1 - F 0 0 = 2*k*x*r ∧
    F 1 1 - F 1 0 = 2*k*x*r := by
  dsimp only
  simp [originJetResidueProduct, originJetD1, originJetD2, originJetD3,
    originJetH0, originJetHplus1, originJetHplus2, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

def originJetIntegral {n : Type*} (I : (n → ℝ) →ₗ[ℝ] ℝ)
    (F : n → Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => I (fun m => F m i j)

theorem originJet_third_coefficient_zero {n : Type*}
    (I : (n → ℝ) →ₗ[ℝ] ℝ) (k m2 x a b M : ℝ)
    (t c0 c1 w1 : n → ℝ)
    (h2 : I (fun m => (t m)^2) = m2)
    (hM : I (fun m => t m*c0 m+w1 m+c1 m) = -M)
    (ha : a = 2*k*(1+M)+k*m2*b) :
    originJetH3 a + originJetD3 k m2 x +
      originJetIntegral I (fun m =>
        originJetD1 k x (t m) * originJetH2 (t m) a b +
        originJetD2 k m2 x (t m) * originJetH1 (t m) b (c0 m) +
        originJetD3 k m2 x * originJetH0 (c1 m) (w1 m)) = 0 := by
  have hp : I (fun m => (k/2*((k*m2*x+2)*b-x*a))*(t m)^2 -
      (2*k+k^2*m2*x)*(t m*c0 m+w1 m+c1 m)) =
      (k/2*((k*m2*x+2)*b-x*a))*m2+(2*k+k^2*m2*x)*M := by
    change I ((_ : ℝ) • (fun m => (t m)^2) -
      (_ : ℝ) • (fun m => t m*c0 m+w1 m+c1 m)) = _
    rw [map_sub, map_smul, map_smul, h2, hM]
    simp only [smul_eq_mul]
    ring
  have hn : I (fun m => -((k/2*((k*m2*x+2)*b-x*a))*(t m)^2 -
      (2*k+k^2*m2*x)*(t m*c0 m+w1 m+c1 m))) =
      -((k/2*((k*m2*x+2)*b-x*a))*m2+(2*k+k^2*m2*x)*M) := by
    rw [show (fun m => -((k/2*((k*m2*x+2)*b-x*a))*(t m)^2 -
        (2*k+k^2*m2*x)*(t m*c0 m+w1 m+c1 m))) =
      -(fun m => (k/2*((k*m2*x+2)*b-x*a))*(t m)^2 -
        (2*k+k^2*m2*x)*(t m*c0 m+w1 m+c1 m)) by rfl, map_neg, hp]
  simp_rw [originJet_third_product_identity]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | (change -a+(2*k+k^2*m2*x)+I (fun m =>
          (k/2*((k*m2*x+2)*b-x*a))*(t m)^2 -
          (2*k+k^2*m2*x)*(t m*c0 m+w1 m+c1 m)) = 0
       rw [hp, ha]
       ring)
    | (change a + -(2*k+k^2*m2*x)+I (fun m =>
          -((k/2*((k*m2*x+2)*b-x*a))*(t m)^2 -
          (2*k+k^2*m2*x)*(t m*c0 m+w1 m+c1 m))) = 0
       rw [hn, ha]
       ring)

theorem originJet_second_coefficient_zero {n : Type*}
    (I : (n → ℝ) →ₗ[ℝ] ℝ) (k m2 x y a b M R : ℝ)
    (t c0 c1 c2 w1 w2 : n → ℝ)
    (h2 : I (fun m => (t m)^2) = m2)
    (hM : I (fun m => t m*c0 m+w1 m+c1 m) = -M)
    (hR : I (fun m => w2 m+c2 m-t m*(w1 m-c1 m)/2) = R)
    (ha : a = 2*k*(1+M)+k*m2*b) (hb : b = k*y+2*k*R) :
    originJetH2 x a b + originJetD2 k m2 x y +
      originJetIntegral I (fun m =>
        originJetD1 k x (t m) * originJetH1 (t m) b (c0 m) +
        originJetD2 k m2 x (t m) * originJetH0 (c1 m) (w1 m) +
        originJetD3 k m2 x * originJetHplus1 (c2 m) (w2 m)) = 0 := by
  have hp : I (fun m => k*x*(t m*c0 m+w1 m+c1 m)-k*x*(t m)^2*b+
      (2*k+k^2*m2*x)*(w2 m+c2 m-t m*(w1 m-c1 m)/2)) =
      -k*x*M-k*x*m2*b+(2*k+k^2*m2*x)*R := by
    have he : (fun m => k*x*(t m*c0 m+w1 m+c1 m)-k*x*(t m)^2*b+
        (2*k+k^2*m2*x)*(w2 m+c2 m-t m*(w1 m-c1 m)/2)) =
      (k*x) • (fun m => t m*c0 m+w1 m+c1 m) -
      (k*x*b) • (fun m => (t m)^2) +
      (2*k+k^2*m2*x) • (fun m => w2 m+c2 m-t m*(w1 m-c1 m)/2) := by
      funext m
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, map_add, map_sub, map_smul, map_smul, map_smul, h2, hM, hR]
    simp only [smul_eq_mul]
    ring
  have hq : I (fun m => k*x*(t m*c0 m+w1 m+c1 m)-
      (2*k+k^2*m2*x)*(w2 m+c2 m-t m*(w1 m-c1 m)/2)) =
      -k*x*M-(2*k+k^2*m2*x)*R := by
    change I ((k*x) • (fun m => t m*c0 m+w1 m+c1 m) -
      (2*k+k^2*m2*x) • (fun m => w2 m+c2 m-t m*(w1 m-c1 m)/2)) = _
    rw [map_sub, map_smul, map_smul, hM, hR]
    simp only [smul_eq_mul]
    ring
  simp_rw [originJet_second_product_identity]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originJetH2, originJetD2, originJetIntegral] <;>
    simp only [hp, hq] <;> rw [ha, hb] <;> ring

theorem originJet_residue_lagrangian {n : Type*}
    (I : (n → ℝ) →ₗ[ℝ] ℝ) (k m2 x y b R c0i : ℝ)
    (t c1 c2 c3 w1 w2 w3 : n → ℝ)
    (hR : I (fun m => w2 m+c2 m-t m*(w1 m-c1 m)/2) = R)
    (hb : b = k*y+2*k*R) :
    let F := originJetH1 x b c0i + originJetD1 k x y +
      originJetIntegral I (fun m => originJetResidueProduct k m2 x (t m)
        (c1 m) (c2 m) (c3 m) (w1 m) (w2 m) (w3 m))
    F = !![-F 1 0, -F 1 0; F 1 0, F 1 0] := by
  let Q := fun m => originJetResidueProduct k m2 x (t m)
    (c1 m) (c2 m) (c3 m) (w1 m) (w2 m) (w3 m)
  have h1 : I (fun m => Q m 0 0) + I (fun m => Q m 1 0) = -2*k*x*R := by
    rw [← map_add]
    change I (fun m => Q m 0 0 + Q m 1 0) = _
    simp_rw [Q, (originJet_residue_product_projections _ _ _ _ _ _ _ _ _ _).1]
    change I ((-2*k*x) • (fun m => w2 m+c2 m-t m*(w1 m-c1 m)/2)) = _
    rw [map_smul, hR]
    rfl
  have h2 : I (fun m => Q m 0 1) - I (fun m => Q m 0 0) = 2*k*x*R := by
    rw [← map_sub]
    change I (fun m => Q m 0 1 - Q m 0 0) = _
    simp_rw [Q, (originJet_residue_product_projections _ _ _ _ _ _ _ _ _ _).2.2.1]
    change I ((2*k*x) • (fun m => w2 m+c2 m-t m*(w1 m-c1 m)/2)) = _
    rw [map_smul, hR]
    rfl
  have h3 : I (fun m => Q m 1 1) - I (fun m => Q m 1 0) = 2*k*x*R := by
    rw [← map_sub]
    change I (fun m => Q m 1 1 - Q m 1 0) = _
    simp_rw [Q, (originJet_residue_product_projections _ _ _ _ _ _ _ _ _ _).2.2.2]
    change I ((2*k*x) • (fun m => w2 m+c2 m-t m*(w1 m-c1 m)/2)) = _
    rw [map_smul, hR]
    rfl
  dsimp only
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originJetH1, originJetD1, originJetIntegral] <;>
    dsimp only [Q] at h1 h2 h3 <;>
    (try rw [hb]) <;> nlinarith

theorem originJet_constant_lagrangian_projection_zero
    (k m2 x t c1 c2 c3 c4 w1 w2 w3 w4 : ℝ) :
    let F := originJetH0 c1 w1 +
      originJetD1 k x t * originJetHplus1 c2 w2 +
      originJetD2 k m2 x t * originJetHplus2 c3 w3 +
      originJetD3 k m2 x * originJetHplus1 c4 w4
    F 0 0 + F 1 0 - F 0 1 - F 1 1 = 0 := by
  dsimp only
  simp [originJetD1, originJetD2, originJetD3, originJetH0, originJetHplus1,
    originJetHplus2, Matrix.mul_apply, Fin.sum_univ_two]
  ring

end FMSA.ExactMSA.MultiTailMixture
