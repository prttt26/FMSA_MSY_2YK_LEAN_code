import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic.Ring

/-! Real coordinates for complex rectangles, retaining the genuine real
sup norm rather than replacing rectangles by complex Euclidean balls. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.ComplexRectangularCoordinates
variable {I : Type*} [Fintype I]
local instance : DecidableEq I := Classical.decEq _

def coordinatesLinear : (I → ℂ) ≃ₗ[ℝ] (Bool × I → ℝ) where
  toFun z j := if j.1 then (z j.2).im else (z j.2).re
  invFun x i := ⟨x (false,i),x (true,i)⟩
  map_add' z w := by
    funext j
    rcases j with ⟨b,i⟩
    cases b <;> simp
  map_smul' r z := by
    funext j
    rcases j with ⟨b,i⟩
    cases b <;> simp
  left_inv z := by
    funext i
    apply Complex.ext <;> rfl
  right_inv x := by
    funext j
    rcases j with ⟨b,i⟩
    cases b <;> rfl

def coordinates : (I → ℂ) ≃L[ℝ] (Bool × I → ℝ) := by
  letI : FiniteDimensional ℝ (I → ℂ) :=
    FiniteDimensional.of_injective coordinatesLinear.toLinearMap coordinatesLinear.injective
  exact coordinatesLinear.toContinuousLinearEquiv

/-- The real coordinates use real part first and imaginary part second. -/
theorem coordinates_apply (z : I → ℂ) (b : Bool) (i : I) :
    coordinates z (b,i) = if b then (z i).im else (z i).re := rfl

/-- The inverse reconstructs every original complex amplitude. -/
theorem coordinates_symm_apply (x : Bool × I → ℝ) (i : I) :
    coordinates.symm x i = ⟨x (false,i),x (true,i)⟩ := rfl

/-- The real sup norm is exactly the componentwise rectangular bound. -/
theorem coordinates_norm_le_iff (z : I → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    ‖coordinates z‖ ≤ r ↔ ∀ i, |(z i).re| ≤ r ∧ |(z i).im| ≤ r := by
  rw [pi_norm_le_iff_of_nonneg hr]
  constructor
  · intro h i
    constructor
    · simpa [coordinates_apply] using h (false,i)
    · simpa [coordinates_apply] using h (true,i)
  · intro h j
    rcases j with ⟨b,i⟩
    cases b
    · simpa [coordinates_apply] using (h i).1
    · simpa [coordinates_apply] using (h i).2

/-- Genuine complex multiplication has the usual four real matrix blocks. -/
def realMatrix (A : Matrix I I ℂ) : Matrix (Bool × I) (Bool × I) ℝ := fun j k =>
  match j.1,k.1 with
  | false,false => (A j.2 k.2).re
  | false,true => -(A j.2 k.2).im
  | true,false => (A j.2 k.2).im
  | true,true => (A j.2 k.2).re

/-- Exact real matrix action; this is not a norm identification. -/
theorem realMatrix_mulVec (A : Matrix I I ℂ) (z : I → ℂ) :
    Matrix.mulVec (realMatrix A) (coordinates z) = coordinates (Matrix.mulVec A z) := by
  funext j
  rcases j with ⟨b,i⟩
  cases b <;> simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    coordinates_apply,realMatrix,Complex.mul_re,Complex.mul_im,
    Finset.sum_add_distrib,sub_eq_add_neg,add_comm]

def realConjugate (L : (I → ℂ) →L[ℂ] (I → ℂ)) :
    (Bool × I → ℝ) →L[ℝ] (Bool × I → ℝ) :=
  coordinates.toContinuousLinearMap.comp
    ((L.restrictScalars ℝ).comp coordinates.symm.toContinuousLinearMap)

/-- A true complex derivative gives the true real derivative of the
coordinate-transformed function, with no derivative premise on that transform. -/
theorem coordinates_hasFDerivAt (f : (I → ℂ) → (I → ℂ))
    (L : (I → ℂ) →L[ℂ] (I → ℂ)) (z : I → ℂ) (hf : HasFDerivAt f L z) :
    HasFDerivAt (fun x => coordinates (f (coordinates.symm x))) (realConjugate L)
      (coordinates z) := by
  have hf' : HasFDerivAt f (L.restrictScalars ℝ) (coordinates.symm (coordinates z)) := by
    simpa using hf.restrictScalars ℝ
  exact coordinates.toContinuousLinearMap.hasFDerivAt.comp _
    (hf'.comp _ coordinates.symm.toContinuousLinearMap.hasFDerivAt)

/-- The coordinate conjugate of complex matrix multiplication is the exact
four-block real matrix [Re,-Im;Im,Re]. -/
theorem realConjugate_matrix_apply (A : Matrix I I ℂ) (x : Bool × I → ℝ) :
    realConjugate (Matrix.toLin' A).toContinuousLinearMap x = Matrix.mulVec (realMatrix A) x := by
  change coordinates (Matrix.mulVec A (coordinates.symm x)) = _
  rw [← realMatrix_mulVec,coordinates.apply_symm_apply]

section Weights
variable {J : Type*} [Fintype J]

def diagonalLinear (w : J → ℝ) (hw : ∀ j, w j ≠ 0) : (J → ℝ) ≃ₗ[ℝ] (J → ℝ) where
  toFun x j := w j*x j
  invFun x j := x j/w j
  map_add' x y := by funext j; simp [mul_add]
  map_smul' r x := by funext j; simp [smul_eq_mul,mul_left_comm]
  left_inv x := by funext j; simp [hw j]
  right_inv x := by funext j; simp [mul_div_cancel₀,hw j]

def diagonal (w : J → ℝ) (hw : ∀ j, w j ≠ 0) : (J → ℝ) ≃L[ℝ] (J → ℝ) :=
  (diagonalLinear w hw).toContinuousLinearEquiv

end Weights

def normalizedCoordinates (w : Bool × I → ℝ) (hw : ∀ j, w j ≠ 0) :
    (I → ℂ) ≃L[ℝ] (Bool × I → ℝ) :=
  coordinates.trans (diagonal w hw).symm

/-- Each normalized coordinate divides by its own real component width. -/
theorem normalizedCoordinates_apply (w : Bool × I → ℝ) (hw : ∀ j, w j ≠ 0)
    (z : I → ℂ) (j : Bool × I) :
    normalizedCoordinates w hw z j = coordinates z j/w j := rfl

/-- A complex rectangle is exactly a closed REAL sup-norm unit ball under
its positive-width coordinates, not a complex sup-norm ball. -/
theorem mem_normalized_closedBall_iff (w : Bool × I → ℝ) (hw : ∀ j, 0 < w j)
    (z c : I → ℂ) :
    normalizedCoordinates w (fun j => (hw j).ne') (z-c) ∈ Metric.closedBall 0 1 ↔
      ∀ j, |coordinates (z-c) j| ≤ w j := by
  rw [Metric.mem_closedBall,dist_eq_norm,sub_zero,pi_norm_le_iff_of_nonneg zero_le_one]
  apply forall_congr'
  intro j
  rw [normalizedCoordinates_apply,Real.norm_eq_abs,abs_div,abs_of_pos (hw j)]
  have h : |coordinates (z-c) j|/w j ≤ (1 : ℝ) ↔
      |coordinates (z-c) j| ≤ 1*w j := div_le_iff₀ (hw j)
  simpa only [one_mul] using h

/-- The normalized inverse rescales each real/imaginary component by its
own width, preserving the exact original complex amplitude. -/
theorem normalizedCoordinates_symm_coordinates
    (w : Bool × I → ℝ) (hw : ∀ j, w j ≠ 0) (x : Bool × I → ℝ) (j : Bool × I) :
    coordinates ((normalizedCoordinates w hw).symm x) j = w j*x j := by
  change coordinates (coordinates.symm (diagonal w hw x)) j = _
  rw [coordinates.apply_symm_apply]
  rfl

def normalizedConjugate (w : Bool × I → ℝ) (hw : ∀ j, w j ≠ 0)
    (L : (I → ℂ) →L[ℂ] (I → ℂ)) : (Bool × I → ℝ) →L[ℝ] (Bool × I → ℝ) :=
  (normalizedCoordinates w hw).toContinuousLinearMap.comp
    ((L.restrictScalars ℝ).comp (normalizedCoordinates w hw).symm.toContinuousLinearMap)

/-- The derivative of the actual centered, scaled residual is constructed
from the true complex derivative; the center contributes no derivative. -/
theorem normalized_hasFDerivAt (w : Bool × I → ℝ) (hw : ∀ j, w j ≠ 0)
    (f : (I → ℂ) → (I → ℂ)) (L : (I → ℂ) →L[ℂ] (I → ℂ)) (c : I → ℂ)
    (x : Bool × I → ℝ) (hf : HasFDerivAt f L (c + (normalizedCoordinates w hw).symm x)) :
    HasFDerivAt (fun y => normalizedCoordinates w hw (f (c + (normalizedCoordinates w hw).symm y)))
      (normalizedConjugate w hw L) x := by
  exact (normalizedCoordinates w hw).toContinuousLinearMap.hasFDerivAt.comp x
    ((hf.restrictScalars ℝ).comp x
      ((normalizedCoordinates w hw).symm.toContinuousLinearMap.hasFDerivAt.const_add c))

def normalizedRealMatrix (w : Bool × I → ℝ) (A : Matrix I I ℂ) :
    Matrix (Bool × I) (Bool × I) ℝ := fun j k => realMatrix A j k*w k/w j

/-- The exact weighted REAL matrix has component ratios w_col/w_row;
it is derived from genuine complex matrix action, not assumed. -/
theorem normalizedConjugate_matrix_apply
    (w : Bool × I → ℝ) (hw : ∀ j, w j ≠ 0) (A : Matrix I I ℂ) (x : Bool × I → ℝ) :
    normalizedConjugate w hw (Matrix.toLin' A).toContinuousLinearMap x =
      Matrix.mulVec (normalizedRealMatrix w A) x := by
  funext j
  change normalizedCoordinates w hw
    (Matrix.mulVec A ((normalizedCoordinates w hw).symm x)) j = _
  rw [normalizedCoordinates_apply,← realMatrix_mulVec]
  simp only [Matrix.mulVec,dotProduct,normalizedCoordinates_symm_coordinates,
    normalizedRealMatrix,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

section RowNorm
variable {J : Type*} [Fintype J]
local instance : DecidableEq J := Classical.decEq _

/-- Componentwise absolute row sums rigorously control the true REAL sup-
operator norm, including empty coordinate sets. -/
theorem real_matrix_opNorm_le (A : Matrix J J ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hrow : ∀ i, ∑ j, |A i j| ≤ q) :
    ‖(Matrix.toLin' A).toContinuousLinearMap‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro x
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg x))]
  intro i
  change ‖∑ j, A i j*x j‖ ≤ q*‖x‖
  calc
    _ ≤ ∑ j, ‖A i j*x j‖ := norm_sum_le _ _
    _ = ∑ j, |A i j| *|x j| := by simp [norm_mul,Real.norm_eq_abs]
    _ ≤ ∑ j, |A i j| *‖x‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (abs_nonneg _)
    _ = (∑ j, |A i j|)*‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ q*‖x‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg x)

end RowNorm

/-- Verified weighted real row sums imply a genuine operator norm bound
for the ORIGINAL complex matrix in the exact rectangular coordinates. -/
theorem normalizedConjugate_opNorm_le
    (w : Bool × I → ℝ) (hw : ∀ j, w j ≠ 0) (A : Matrix I I ℂ)
    (q : ℝ) (hq : 0 ≤ q) (hrow : ∀ i, ∑ j, |normalizedRealMatrix w A i j| ≤ q) :
    ‖normalizedConjugate w hw (Matrix.toLin' A).toContinuousLinearMap‖ ≤ q := by
  have heq : normalizedConjugate w hw (Matrix.toLin' A).toContinuousLinearMap =
      (Matrix.toLin' (normalizedRealMatrix w A)).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact normalizedConjugate_matrix_apply w hw A x
  rw [heq]
  exact real_matrix_opNorm_le _ q hq hrow

/-- The normalized TRUE Newton derivative defect is exactly the conjugate
of the original complex defect matrix I-CJ. -/
theorem normalized_newton_defect_eq
    (w : Bool × I → ℝ) (hw : ∀ j, w j ≠ 0) (C J : Matrix I I ℂ) :
    ContinuousLinearMap.id ℝ (Bool × I → ℝ) -
      (normalizedConjugate w hw (Matrix.toLin' C).toContinuousLinearMap).comp
        (normalizedConjugate w hw (Matrix.toLin' J).toContinuousLinearMap) =
      normalizedConjugate w hw (Matrix.toLin' (1 - C * J)).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  change x - normalizedCoordinates w hw
    (Matrix.mulVec C ((normalizedCoordinates w hw).symm
      (normalizedCoordinates w hw (Matrix.mulVec J ((normalizedCoordinates w hw).symm x))))) =
    normalizedCoordinates w hw (Matrix.mulVec (1 - C * J) ((normalizedCoordinates w hw).symm x))
  rw [(normalizedCoordinates w hw).symm_apply_apply,Matrix.sub_mulVec,
    Matrix.one_mulVec,map_sub,(normalizedCoordinates w hw).apply_symm_apply,
    Matrix.mulVec_mulVec]

/-- Saved weighted REAL defect row sums control the exact Newton operator
norm needed by the continuous-root theorem. -/
theorem normalized_newton_defect_opNorm_le
    (w : Bool × I → ℝ) (hw : ∀ j, w j ≠ 0) (C J : Matrix I I ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hrow : ∀ i, ∑ j, |normalizedRealMatrix w (1 - C * J) i j| ≤ q) :
    ‖ContinuousLinearMap.id ℝ (Bool × I → ℝ) -
      (normalizedConjugate w hw (Matrix.toLin' C).toContinuousLinearMap).comp
        (normalizedConjugate w hw (Matrix.toLin' J).toContinuousLinearMap)‖ ≤ q := by
  rw [normalized_newton_defect_eq]
  exact normalizedConjugate_opNorm_le w hw _ q hq hrow

/-- The original preconditioned complex Newton map, with its original
center subtracted, is exactly the real normalized Newton map. -/
theorem normalized_newton_map_eq
    (w : Bool × I → ℝ) (hw : ∀ j, w j ≠ 0) (C : Matrix I I ℂ)
    (f : (I → ℂ) → (I → ℂ)) (c : I → ℂ) (x : Bool × I → ℝ) :
    normalizedCoordinates w hw
      ((c + (normalizedCoordinates w hw).symm x)-
        Matrix.mulVec C (f (c + (normalizedCoordinates w hw).symm x))-c) =
      x - normalizedConjugate w hw (Matrix.toLin' C).toContinuousLinearMap
        (normalizedCoordinates w hw (f (c + (normalizedCoordinates w hw).symm x))) := by
  change _ = x - normalizedCoordinates w hw
    (Matrix.mulVec C ((normalizedCoordinates w hw).symm
      (normalizedCoordinates w hw (f (c + (normalizedCoordinates w hw).symm x)))))
  rw [(normalizedCoordinates w hw).symm_apply_apply]
  have heq : (c + (normalizedCoordinates w hw).symm x)-
      Matrix.mulVec C (f (c + (normalizedCoordinates w hw).symm x))-c =
      (normalizedCoordinates w hw).symm x-
        Matrix.mulVec C (f (c + (normalizedCoordinates w hw).symm x)) := by abel
  rw [heq,map_sub,(normalizedCoordinates w hw).apply_symm_apply]

/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.coordinates_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.coordinates_apply
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.coordinates_symm_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.coordinates_symm_apply
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.coordinates_norm_le_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.coordinates_norm_le_iff
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.realMatrix_mulVec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.realMatrix_mulVec
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.coordinates_hasFDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.coordinates_hasFDerivAt
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.realConjugate_matrix_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.realConjugate_matrix_apply
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.normalizedCoordinates_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.normalizedCoordinates_apply
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.mem_normalized_closedBall_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.mem_normalized_closedBall_iff
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.normalizedCoordinates_symm_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.normalizedCoordinates_symm_coordinates
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.normalized_hasFDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.normalized_hasFDerivAt
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.normalizedConjugate_matrix_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.normalizedConjugate_matrix_apply
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.real_matrix_opNorm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.real_matrix_opNorm_le
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.normalizedConjugate_opNorm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.normalizedConjugate_opNorm_le
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.normalized_newton_defect_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.normalized_newton_defect_eq
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.normalized_newton_defect_opNorm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.normalized_newton_defect_opNorm_le
/-- info: 'FMSA.Convergence.ComplexRectangularCoordinates.normalized_newton_map_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangularCoordinates.normalized_newton_map_eq
end FMSA.Convergence.ComplexRectangularCoordinates
