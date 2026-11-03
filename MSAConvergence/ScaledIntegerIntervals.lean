import MSAConvergence.RealIntervalCertificates
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Executable integer interval arithmetic and register-program soundness,
with signed outward rounding at every positive scale. -/
noncomputable section
namespace FMSA.Convergence.ScaledIntegerIntervals

/-- Unbounded integer endpoints at a common positive real scale. -/
structure Interval where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def Encloses (s : ℤ) (A : Interval) (x : ℝ) : Prop :=
  (A.lo : ℝ)/(s : ℝ) ≤ x ∧ x ≤ (A.hi : ℝ)/(s : ℝ)

namespace Interval

def add (A B : Interval) : Interval := ⟨A.lo+B.lo,A.hi+B.hi⟩
def neg (A : Interval) : Interval := ⟨-A.hi,-A.lo⟩
def productLo (A B : Interval) : ℤ :=
  min (min (A.lo*B.lo) (A.lo*B.hi)) (min (A.hi*B.lo) (A.hi*B.hi))
def productHi (A B : Interval) : ℤ :=
  max (max (A.lo*B.lo) (A.lo*B.hi)) (max (A.hi*B.lo) (A.hi*B.hi))

def mul (s : ℤ) (A B : Interval) : Interval :=
  ⟨productLo A B/s,-((-productHi A B)/s)⟩

end Interval

/-- Euclidean integer division rounds toward the lower endpoint also for
negative numerators, before the second scaling of a product. -/
theorem round_down_le (s z : ℤ) (hs : 0 < s) :
    ((z/s : ℤ) : ℝ)/(s : ℝ) ≤ (z : ℝ)/(s : ℝ)^2 := by
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have h : ((z/s : ℤ) : ℝ)*(s : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast Int.ediv_mul_le z hs.ne'
  have hq : ((z/s : ℤ) : ℝ) ≤ (z : ℝ)/(s : ℝ) := (le_div_iff₀ hsR).mpr h
  calc
    _ ≤ ((z : ℝ)/(s : ℝ))/(s : ℝ) := div_le_div_of_nonneg_right hq hsR.le
    _ = _ := by simp only [div_div,pow_two]

/-- Negated lower rounding of the negative numerator is rigorous upper
rounding, including both signs and exact grid endpoints. -/
theorem round_up_ge (s z : ℤ) (hs : 0 < s) :
    (z : ℝ)/(s : ℝ)^2 ≤ ((-((-z)/s) : ℤ) : ℝ)/(s : ℝ) := by
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have hi : z ≤ (-((-z)/s))*s := by
    simpa only [neg_neg,neg_mul] using neg_le_neg (Int.ediv_mul_le (-z) hs.ne')
  have h : (z : ℝ) ≤ ((-((-z)/s) : ℤ) : ℝ)*(s : ℝ) := by exact_mod_cast hi
  have hq : (z : ℝ)/(s : ℝ) ≤ ((-((-z)/s) : ℤ) : ℝ) := (div_le_iff₀ hsR).mpr h
  calc
    _ = ((z : ℝ)/(s : ℝ))/(s : ℝ) := by simp only [div_div,pow_two]
    _ ≤ _ := div_le_div_of_nonneg_right hq hsR.le

/-- A verified lower integer corner comparison implies the true real lower
bound after outward-rounded multiplication. -/
theorem lower_corner (s l x y : ℤ) (hs : 0 < s) (hl : l ≤ x * y) :
    ((l/s : ℤ) : ℝ)/(s : ℝ) ≤ ((x : ℝ)/(s : ℝ))*((y : ℝ)/(s : ℝ)) := by
  have heq : ((x : ℝ)/(s : ℝ))*((y : ℝ)/(s : ℝ)) = ((x * y : ℤ) : ℝ)/(s : ℝ)^2 := by
    push_cast
    ring
  rw [heq]
  apply (round_down_le s l hs).trans
  exact div_le_div_of_nonneg_right (by exact_mod_cast hl) (sq_nonneg (s : ℝ))

/-- The corresponding upper integer corner comparison is equally signed. -/
theorem upper_corner (s u x y : ℤ) (hs : 0 < s) (hu : x * y ≤ u) :
    ((x : ℝ)/(s : ℝ))*((y : ℝ)/(s : ℝ)) ≤ ((-((-u)/s) : ℤ) : ℝ)/(s : ℝ) := by
  have heq : ((x : ℝ)/(s : ℝ))*((y : ℝ)/(s : ℝ)) = ((x * y : ℤ) : ℝ)/(s : ℝ)^2 := by
    push_cast
    ring
  rw [heq]
  apply le_trans _ (round_up_ge s u hs)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hu) (sq_nonneg (s : ℝ))

/-- Addition is exact on the common grid and sound for every enclosed pair. -/
theorem add_sound (s : ℤ) {A B : Interval} {x y : ℝ}
    (hx : Encloses s A x) (hy : Encloses s B y) : Encloses s (A.add B) (x+y) := by
  constructor
  · simpa only [Interval.add,Int.cast_add,add_div] using add_le_add hx.1 hy.1
  · simpa only [Interval.add,Int.cast_add,add_div] using add_le_add hx.2 hy.2

/-- Signed negation reverses interval endpoints exactly. -/
theorem neg_sound (s : ℤ) {A : Interval} {x : ℝ} (hx : Encloses s A x) :
    Encloses s A.neg (-x) := by
  constructor
  · simpa only [Interval.neg,Int.cast_neg,neg_div] using neg_le_neg hx.2
  · simpa only [Interval.neg,Int.cast_neg,neg_div] using neg_le_neg hx.1

/-- Multiplication computes four integer corners and outward rounds once;
no external comparison/interval evaluator is assumed. -/
theorem mul_sound (s : ℤ) (hs : 0 < s) {A B : Interval} {x y : ℝ}
    (hx : Encloses s A x) (hy : Encloses s B y) : Encloses s (A.mul s B) (x * y) := by
  apply FMSA.Convergence.RealIntervalCertificates.mul_interval hx hy
  · refine ⟨lower_corner s _ _ _ hs ?_,lower_corner s _ _ _ hs ?_,
      lower_corner s _ _ _ hs ?_,lower_corner s _ _ _ hs ?_⟩
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  · refine ⟨upper_corner s (Interval.productHi A B) A.lo B.lo hs ?_,
      upper_corner s (Interval.productHi A B) A.lo B.hi hs ?_,
      upper_corner s (Interval.productHi A B) A.hi B.lo hs ?_,
      upper_corner s (Interval.productHi A B) A.hi B.hi hs ?_⟩
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)


namespace Interval

def point (z : ℤ) : Interval := ⟨z,z⟩

def rational (s n : ℤ) (d : ℕ) : Interval :=
  if d=0 then ⟨0,0⟩ else ⟨(n*s)/(d : ℤ),-((-(n*s))/(d : ℤ))⟩

def absUpper (A : Interval) : ℤ := max |A.lo| |A.hi|

end Interval

/-- Exact grid points require no arithmetic oracle. -/
theorem point_sound (s z : ℤ) : Encloses s (Interval.point z) ((z : ℝ)/(s : ℝ)) :=
  ⟨le_rfl,le_rfl⟩

/-- Integer division gives a certified lower real quotient for signed input. -/
theorem quotient_cast_down (n d : ℤ) (hd : 0 < d) :
    ((n/d : ℤ) : ℝ) ≤ (n : ℝ)/(d : ℝ) := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  apply (le_div_iff₀ hdR).mpr
  exact_mod_cast Int.ediv_mul_le n hd.ne'

/-- Negated lower division gives the certified upper real quotient. -/
theorem quotient_cast_up (n d : ℤ) (hd : 0 < d) :
    (n : ℝ)/(d : ℝ) ≤ ((-((-n)/d) : ℤ) : ℝ) := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  apply (div_le_iff₀ hdR).mpr
  have h : n ≤ (-((-n)/d))*d := by
    simpa only [neg_neg,neg_mul] using neg_le_neg (Int.ediv_mul_le (-n) hd.ne')
  exact_mod_cast h

/-- Every exact rational literal is enclosed by computable integer rounding.
Zero denominators use the same total-field value0 as the real semantics. -/
theorem rational_sound (s n : ℤ) (d : ℕ) (hs : 0 < s) :
    Encloses s (Interval.rational s n d) ((n : ℝ)/(d : ℝ)) := by
  by_cases hd : d=0
  · subst d
    simp [Interval.rational,Encloses]
  · have hsR : (0 : ℝ)<s := by exact_mod_cast hs
    have hdI : (0 : ℤ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hdR : (0 : ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have heq : ((n*s : ℤ) : ℝ)/(d : ℝ)/(s : ℝ) = (n : ℝ)/(d : ℝ) := by
      push_cast
      field_simp [hsR.ne',hdR.ne']
    simp only [Encloses,Interval.rational,if_neg hd]
    constructor
    · rw [← heq]
      exact div_le_div_of_nonneg_right (quotient_cast_down (n*s) d hdI) hsR.le
    · rw [← heq]
      exact div_le_div_of_nonneg_right (quotient_cast_up (n*s) d hdI) hsR.le

/-- Signed interval endpoints give a computable integer absolute upper bound. -/
theorem abs_sound (s : ℤ) (hs : 0 < s) {A : Interval} {x : ℝ}
    (hx : Encloses s A x) : |x| ≤ (A.absUpper : ℝ)/(s : ℝ) := by
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  apply FMSA.Convergence.RealIntervalCertificates.abs_bound hx
  · have hl : -A.absUpper ≤ A.lo :=
      (neg_le_neg (le_max_left |A.lo| |A.hi|)).trans (neg_abs_le A.lo)
    have hlR : -(A.absUpper : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast hl
    simpa only [neg_div] using div_le_div_of_nonneg_right hlR hsR.le
  · have hu : A.hi ≤ A.absUpper := (le_abs_self A.hi).trans (le_max_right _ _)
    have huR : (A.hi : ℝ) ≤ (A.absUpper : ℝ) := by exact_mod_cast hu
    exact div_le_div_of_nonneg_right huR hsR.le

/-- An executable finite arithmetic language for real polynomial expressions. -/
inductive Expr (n : ℕ) where
  | input : Fin n → Expr n
  | rational : ℤ → ℕ → Expr n
  | add : Expr n → Expr n → Expr n
  | neg : Expr n → Expr n
  | mul : Expr n → Expr n → Expr n
  deriving Repr, DecidableEq

namespace Expr

def eval {n : ℕ} (v : Fin n → ℝ) : Expr n → ℝ
  | .input i => v i
  | .rational a d => (a : ℝ)/(d : ℝ)
  | .add a b => eval v a+eval v b
  | .neg a => -(eval v a)
  | .mul a b => eval v a*eval v b

def enclose {n : ℕ} (s : ℤ) (v : Fin n → Interval) : Expr n → Interval
  | .input i => v i
  | .rational a d => Interval.rational s a d
  | .add a b => (enclose s v a).add (enclose s v b)
  | .neg a => (enclose s v a).neg
  | .mul a b => (enclose s v a).mul s (enclose s v b)

end Expr

/-- The WHOLE executable evaluator is sound uniformly for every input box,
expression and positive precision scale. No result flag is assumed. -/
theorem Expr.enclose_sound {n : ℕ} (s : ℤ) (hs : 0 < s) (v : Fin n → ℝ)
    (bounds : Fin n → Interval) (hinput : ∀ i, Encloses s (bounds i) (v i)) (e : Expr n) :
    Encloses s (Expr.enclose s bounds e) (Expr.eval v e) := by
  induction e with
  | input i => exact hinput i
  | rational a d => exact rational_sound s a d hs
  | add a b ha hb => exact add_sound s ha hb
  | neg a ha => exact neg_sound s ha
  | mul a b ha hb => exact mul_sound s hs ha hb




/-- Array lookups use a proved zero fallback for out-of-range references. -/
def readInterval (v : Array Interval) (i : ℕ) : Interval := (v[i]?).getD (Interval.point 0)
def readReal (v : Array ℝ) (i : ℕ) : ℝ := (v[i]?).getD 0

def ArrayEncloses (s : ℤ) (A : Array Interval) (v : Array ℝ) : Prop :=
  A.size=v.size ∧ ∀ i, Encloses s (readInterval A i) (readReal v i)

/-- The empty register array is sound, including its default-zero lookups. -/
theorem empty_array_sound (s : ℤ) : ArrayEncloses s #[] #[] := by
  refine ⟨rfl,?_⟩
  intro i
  simpa only [readInterval,readReal,Array.getElem?_empty,Option.getD_none,
    Int.cast_zero,zero_div] using point_sound s 0

/-- Appending a proved result preserves every register enclosure and lookup. -/
theorem push_array_sound (s : ℤ) {A : Array Interval} {v : Array ℝ}
    (hA : ArrayEncloses s A v) {B : Interval} {x : ℝ} (hx : Encloses s B x) :
    ArrayEncloses s (A.push B) (v.push x) := by
  refine ⟨by simp only [Array.size_push,hA.1],?_⟩
  intro i
  simp only [readInterval,readReal,Array.getElem?_push]
  rw [hA.1]
  by_cases hi : i=v.size
  · simpa only [if_pos hi,Option.getD_some] using hx
  · simpa only [readInterval,readReal,if_neg hi] using hA.2 i

/-- A shared arithmetic program refers to previous result registers. Its
integer execution is computable; real execution specifies the exact meaning. -/
inductive Op (n : ℕ) where
  | input : Fin n → Op n
  | rational : ℤ → ℕ → Op n
  | add : ℕ → ℕ → Op n
  | neg : ℕ → Op n
  | mul : ℕ → ℕ → Op n
  deriving Repr, DecidableEq

namespace Op

def eval {n : ℕ} (v : Fin n → ℝ) (previous : Array ℝ) : Op n → ℝ
  | .input i => v i
  | .rational a d => (a : ℝ)/(d : ℝ)
  | .add i j => readReal previous i+readReal previous j
  | .neg i => -(readReal previous i)
  | .mul i j => readReal previous i*readReal previous j

def enclose {n : ℕ} (s : ℤ) (v : Fin n → Interval) (previous : Array Interval) : Op n → Interval
  | .input i => v i
  | .rational a d => Interval.rational s a d
  | .add i j => (readInterval previous i).add (readInterval previous j)
  | .neg i => (readInterval previous i).neg
  | .mul i j => (readInterval previous i).mul s (readInterval previous j)

end Op

/-- Every executable instruction preserves its exact real meaning; even
forward/out-of-range references use the same zero semantics on both sides. -/
theorem Op.enclose_sound {n : ℕ} (s : ℤ) (hs : 0 < s) (v : Fin n → ℝ)
    (bounds : Fin n → Interval) (hinput : ∀ i, Encloses s (bounds i) (v i))
    (previous : Array ℝ) (previousBounds : Array Interval)
    (hprevious : ArrayEncloses s previousBounds previous) (op : Op n) :
    Encloses s (Op.enclose s bounds previousBounds op) (Op.eval v previous op) := by
  cases op with
  | input i => exact hinput i
  | rational a d => exact rational_sound s a d hs
  | add i j => exact add_sound s (hprevious.2 i) (hprevious.2 j)
  | neg i => exact neg_sound s (hprevious.2 i)
  | mul i j => exact mul_sound s hs (hprevious.2 i) (hprevious.2 j)



namespace Program

def eval {n : ℕ} (v : Fin n → ℝ) : List (Op n) → Array ℝ → Array ℝ
  | [],previous => previous
  | op::rest,previous => eval v rest (previous.push (op.eval v previous))

def enclose {n : ℕ} (s : ℤ) (v : Fin n → Interval) : List (Op n) → Array Interval → Array Interval
  | [],previous => previous
  | op::rest,previous => enclose s v rest (previous.push (op.enclose s v previous))

end Program

/-- The WHOLE register program is sound for arbitrary data and positive
precision. Correctness is proved by induction, not assumed from a PASS flag. -/
theorem Program.enclose_sound {n : ℕ} (s : ℤ) (hs : 0 < s) (v : Fin n → ℝ)
    (bounds : Fin n → Interval) (hinput : ∀ i, Encloses s (bounds i) (v i))
    (code : List (Op n)) (previous : Array ℝ) (previousBounds : Array Interval)
    (hprevious : ArrayEncloses s previousBounds previous) :
    ArrayEncloses s (Program.enclose s bounds code previousBounds) (Program.eval v code previous) := by
  induction code generalizing previous previousBounds with
  | nil => exact hprevious
  | cons op rest ih =>
    apply ih
    exact push_array_sound s hprevious
      (Op.enclose_sound s hs v bounds hinput previous previousBounds hprevious op)

/-- A closed program constructs certified bounds for EVERY output register. -/
theorem Program.closed_program_sound {n : ℕ} (s : ℤ) (hs : 0 < s) (v : Fin n → ℝ)
    (bounds : Fin n → Interval) (hinput : ∀ i, Encloses s (bounds i) (v i))
    (code : List (Op n)) (i : ℕ) :
    Encloses s (readInterval (Program.enclose s bounds code #[]) i) (readReal (Program.eval v code #[]) i) :=
  (Program.enclose_sound s hs v bounds hinput code #[] #[] (empty_array_sound s)).2 i



end FMSA.Convergence.ScaledIntegerIntervals

/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.round_down_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.round_down_le
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.round_up_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.round_up_ge
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.lower_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.lower_corner
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.upper_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.upper_corner
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.add_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.add_sound
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.neg_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.neg_sound
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.mul_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.mul_sound
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.point_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.point_sound
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.quotient_cast_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.quotient_cast_down
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.quotient_cast_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.quotient_cast_up
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.rational_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.rational_sound
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.abs_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.abs_sound
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.Expr.enclose_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.Expr.enclose_sound
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.empty_array_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.empty_array_sound
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.push_array_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.push_array_sound
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.Op.enclose_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.Op.enclose_sound
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.Program.enclose_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.Program.enclose_sound
/-- info: 'FMSA.Convergence.ScaledIntegerIntervals.Program.closed_program_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScaledIntegerIntervals.Program.closed_program_sound
