import MSAConvergence.ScaledIntegerIntervals
import MSAConvergence.ComplexRectangularCoordinates
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! From checked scaled-integer boxes and row inequalities to genuine real
rectangles. Every coordinate uses its own actual half-width. -/
noncomputable section
namespace FMSA.Convergence.ScaledRectangleCertificates
open FMSA.Convergence.ScaledIntegerIntervals
open scoped BigOperators

/-- Midpoint of the actual, outward-rounded integer box. -/
def center (s : ℤ) (A : Interval) : ℝ := ((A.lo : ℝ)+(A.hi : ℝ))/(2*(s : ℝ))
/-- Half-width, not the complex Euclidean norm. -/
def radius (s : ℤ) (A : Interval) : ℝ := ((A.hi : ℝ)-(A.lo : ℝ))/(2*(s : ℝ))

theorem radius_pos (s : ℤ) (hs : 0 < s) (A : Interval) (hA : A.lo < A.hi) :
    0 < radius s A := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hA' : (A.lo : ℝ) < A.hi := by exact_mod_cast hA
  exact div_pos (sub_pos.mpr hA') (mul_pos (by norm_num) hsR)

theorem center_sub_radius (s : ℤ) (A : Interval) :
    center s A - radius s A = (A.lo : ℝ)/(s : ℝ) := by
  unfold center radius
  ring

theorem center_add_radius (s : ℤ) (A : Interval) :
    center s A + radius s A = (A.hi : ℝ)/(s : ℝ) := by
  unfold center radius
  ring

theorem encloses_iff_centered (s : ℤ) (A : Interval) (x : ℝ) :
    Encloses s A x ↔ |x-center s A| ≤ radius s A := by
  rw [abs_le]
  have hlo := center_sub_radius s A
  have hhi := center_add_radius s A
  unfold Encloses
  constructor
  · rintro ⟨hl,hu⟩
    constructor <;> linarith
  · rintro ⟨hl,hu⟩
    constructor <;> linarith

theorem encloses_mono (s : ℤ) (hs : 0 < s) {A B : Interval} {x : ℝ}
    (hlo : B.lo ≤ A.lo) (hhi : A.hi ≤ B.hi) (hx : Encloses s A x) :
    Encloses s B x := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  exact ⟨(div_le_div_of_nonneg_right (by exact_mod_cast hlo) hsR.le).trans hx.1,
    hx.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hhi) hsR.le)⟩

theorem strict_interior_of_integer_checks (s : ℤ) (hs : 0 < s) {A B : Interval} {x : ℝ}
    (hlo : B.lo < A.lo) (hhi : A.hi < B.hi) (hx : Encloses s A x) :
    |x-center s B| < radius s B := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hl : (B.lo : ℝ)/(s : ℝ) < x :=
    (div_lt_div_of_pos_right (by exact_mod_cast hlo) hsR).trans_le hx.1
  have hu : x < (B.hi : ℝ)/(s : ℝ) :=
    hx.2.trans_lt (div_lt_div_of_pos_right (by exact_mod_cast hhi) hsR)
  rw [abs_lt]
  have hb0 := center_sub_radius s B
  have hb1 := center_add_radius s B
  constructor <;> linarith

/-- A single integer row comparison bounds the true normalized real row.
The scale and the half-width factor cancel exactly, with no common-width
or complex-norm assumption. -/
theorem weighted_row_bound {I : Type*} [Fintype I]
    (s d n wi : ℤ) (hs : 0 < s) (hd : 0 < d) (hwi : 0 < wi)
    (w u : I → ℤ) (hw : ∀ j, 0 < w j) (a : I → ℝ)
    (ha : ∀ j, |a j| ≤ (u j : ℝ) / (s : ℝ))
    (hcheck : d * ∑ j, u j * w j ≤ n * wi * s) :
    ∑ j, |a j * ((w j : ℝ)/(2*(s : ℝ))) / ((wi : ℝ)/(2*(s : ℝ)))| ≤
      (n : ℝ)/(d : ℝ) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hwiR : (0 : ℝ) < wi := by exact_mod_cast hwi
  have hbound : (d : ℝ) * ∑ j, (u j : ℝ) * (w j : ℝ) ≤
      (n : ℝ) * (wi : ℝ) * (s : ℝ) := by exact_mod_cast hcheck
  calc
    _ = ∑ j, |a j| * (w j : ℝ)/(wi : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      have hwR : (0 : ℝ) < w j := by exact_mod_cast hw j
      have heq : a j * ((w j : ℝ)/(2*(s : ℝ))) / ((wi : ℝ)/(2*(s : ℝ))) =
          a j * (w j : ℝ)/(wi : ℝ) := by field_simp
      rw [heq,abs_div,abs_mul,abs_of_pos hwR,abs_of_pos hwiR]
    _ ≤ ∑ j, ((u j : ℝ) / (s : ℝ)) * (w j : ℝ)/(wi : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      have hwR : (0 : ℝ) ≤ w j := by exact_mod_cast (hw j).le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (ha j) hwR) hwiR.le
    _ = (∑ j, (u j : ℝ)*(w j : ℝ))/((s : ℝ)*(wi : ℝ)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (n : ℝ)/(d : ℝ) := by
      apply (div_le_div_iff₀ (mul_pos hsR hwiR) hdR).mpr
      nlinarith [hbound]


/-- Checked bounds on real matrix entries and integer row sums imply the
actual normalized complex-rectangle derivative bound. -/
theorem complex_normalized_row_bound {I : Type*} [Fintype I]
    (s d n : ℤ) (hs : 0 < s) (hd : 0 < d)
    (w : Bool × I → ℤ) (hw : ∀ j, 0 < w j)
    (u : (Bool × I) → (Bool × I) → ℤ) (A : Matrix I I ℂ)
    (ha : ∀ i j, |ComplexRectangularCoordinates.realMatrix A i j| ≤
      (u i j : ℝ) / (s : ℝ))
    (hcheck : ∀ i, d * ∑ j, u i j * w j ≤ n * w i * s) :
    ∀ i, ∑ j, |ComplexRectangularCoordinates.normalizedRealMatrix
      (fun j => (w j : ℝ)/(2*(s : ℝ))) A i j| ≤ (n : ℝ)/(d : ℝ) := by
  intro i
  exact weighted_row_bound s d n (w i) hs hd (hw i) w (u i) hw
    (ComplexRectangularCoordinates.realMatrix A i) (ha i) (hcheck i)

/-- The actual integer rectangle is exactly the real closed ball required
by the root constructor, under each coordinate's own actual half-width. -/
theorem complex_rectangle_iff_enclosed {I : Type*} [Fintype I]
    (s : ℤ) (hs : 0 < s) (B : Bool × I → Interval)
    (hB : ∀ j, (B j).lo < (B j).hi) (z : I → ℂ) :
    ComplexRectangularCoordinates.normalizedCoordinates (fun j => radius s (B j))
      (fun j => (radius_pos s hs (B j) (hB j)).ne')
      (z - fun i => (⟨center s (B (false,i)),center s (B (true,i))⟩ : ℂ)) ∈
        Metric.closedBall 0 1 ↔
      ∀ j, Encloses s (B j) (ComplexRectangularCoordinates.coordinates z j) := by
  rw [ComplexRectangularCoordinates.mem_normalized_closedBall_iff
    (fun j => radius s (B j)) (fun j => radius_pos s hs (B j) (hB j))]
  apply forall_congr'
  rintro ⟨b,i⟩
  rw [encloses_iff_centered]
  cases b <;> rfl

end FMSA.Convergence.ScaledRectangleCertificates
/-- info: 'FMSA.Convergence.ScaledRectangleCertificates.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledRectangleCertificates.radius_pos
/-- info: 'FMSA.Convergence.ScaledRectangleCertificates.center_sub_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledRectangleCertificates.center_sub_radius
/-- info: 'FMSA.Convergence.ScaledRectangleCertificates.center_add_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledRectangleCertificates.center_add_radius
/-- info: 'FMSA.Convergence.ScaledRectangleCertificates.encloses_iff_centered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledRectangleCertificates.encloses_iff_centered
/-- info: 'FMSA.Convergence.ScaledRectangleCertificates.encloses_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledRectangleCertificates.encloses_mono
/-- info: 'FMSA.Convergence.ScaledRectangleCertificates.strict_interior_of_integer_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledRectangleCertificates.strict_interior_of_integer_checks
/-- info: 'FMSA.Convergence.ScaledRectangleCertificates.weighted_row_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledRectangleCertificates.weighted_row_bound
/-- info: 'FMSA.Convergence.ScaledRectangleCertificates.complex_normalized_row_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledRectangleCertificates.complex_normalized_row_bound
/-- info: 'FMSA.Convergence.ScaledRectangleCertificates.complex_rectangle_iff_enclosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledRectangleCertificates.complex_rectangle_iff_enclosed
