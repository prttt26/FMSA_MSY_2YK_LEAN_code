import MSAConvergence.ScaledIntegerIntervals

/-! Exact local register traces for any value type, with honest actual
proof footprints and exact real/integer-interval specializations. -/
noncomputable section
namespace FMSA.Convergence.GenericRegisterTrace
open FMSA.Convergence.ScaledIntegerIntervals

structure Semantics (n : ℕ) (V : Type*) where
  input : Fin n → V
  literal : ℤ → ℕ → V
  add : V → V → V
  neg : V → V
  mul : V → V → V
  zero : V

def read {V : Type*} (zero : V) (previous : Array V) (i : ℕ) : V :=
  (previous[i]?).getD zero

def Semantics.eval {n : ℕ} {V : Type*} (S : Semantics n V) (previous : Array V) : Op n → V
  | .input i => S.input i
  | .rational a d => S.literal a d
  | .add i j => S.add (read S.zero previous i) (read S.zero previous j)
  | .neg i => S.neg (read S.zero previous i)
  | .mul i j => S.mul (read S.zero previous i) (read S.zero previous j)

def Semantics.value {n : ℕ} {V : Type*} (S : Semantics n V) (f : ℕ → V) : Op n → V
  | .input i => S.input i
  | .rational a d => S.literal a d
  | .add i j => S.add (f i) (f j)
  | .neg i => S.neg (f i)
  | .mul i j => S.mul (f i) (f j)

def Semantics.run {n : ℕ} {V : Type*} (S : Semantics n V) : List (Op n) → Array V → Array V
  | [],previous => previous
  | op::rest,previous => S.run rest (previous.push (S.eval previous op))

def below {n : ℕ} (k : ℕ) : Op n → Prop
  | .input _ => True
  | .rational _ _ => True
  | .add i j => i < k ∧ j < k
  | .neg i => i < k
  | .mul i j => i < k ∧ j < k

def Tracked {V : Type*} (zero : V) (f : ℕ → V) (previous : Array V) : Prop :=
  ∀ i, i < previous.size → read zero previous i = f i

def Trace {n : ℕ} {V : Type*} (S : Semantics n V) (f : ℕ → V) : ℕ → List (Op n) → Prop
  | _,[] => True
  | k,op::rest => below k op ∧ S.value f op = f k ∧ Trace S f (k+1) rest

/-- Earlier exact values determine every local operation, for arbitrary types. -/
theorem op_value_eq {n : ℕ} {V : Type*} (S : Semantics n V) (f : ℕ → V)
    (previous : Array V) (hp : Tracked S.zero f previous) (op : Op n)
    (hb : below previous.size op) : S.eval previous op = S.value f op := by
  cases op with
  | input i => rfl
  | rational a d => rfl
  | add i j => exact congrArg₂ S.add (hp i hb.1) (hp j hb.2)
  | neg i => exact congrArg S.neg (hp i hb)
  | mul i j => exact congrArg₂ S.mul (hp i hb.1) (hp j hb.2)

theorem tracked_push {V : Type*} (zero : V) (f : ℕ → V) (previous : Array V) (x : V)
    (hp : Tracked zero f previous) (hx : x = f previous.size) : Tracked zero f (previous.push x) := by
  intro i hi
  have hi' : i ≤ previous.size := Nat.le_of_lt_succ (by
    simpa only [Array.size_push] using hi)
  simp only [read,Array.getElem?_push]
  by_cases he : i = previous.size
  · rw [if_pos he]
    simpa only [Option.getD_some,he] using hx
  · have hil : i < previous.size := lt_of_le_of_ne hi' he
    simpa only [read,if_neg he] using hp i hil

/-- A locally checked trace determines the exact whole interpreter. -/
theorem run_tracked {n : ℕ} {V : Type*} (S : Semantics n V) (f : ℕ → V)
    (code : List (Op n)) (previous : Array V) (hp : Tracked S.zero f previous)
    (ht : Trace S f previous.size code) : Tracked S.zero f (S.run code previous) := by
  induction code generalizing previous with
  | nil => exact hp
  | cons op rest ih =>
    apply ih
    · exact tracked_push S.zero f previous (S.eval previous op) hp
        ((op_value_eq S f previous hp op ht.1).trans ht.2.1)
    · simpa only [Array.size_push] using ht.2.2

theorem run_size {n : ℕ} {V : Type*} (S : Semantics n V) (code : List (Op n))
    (previous : Array V) : (S.run code previous).size = previous.size+code.length := by
  induction code generalizing previous with
  | nil => rfl
  | cons op rest ih =>
    simp only [Semantics.run,ih,Array.size_push,List.length_cons,Nat.add_assoc,Nat.add_comm]

theorem closed_program_values {n : ℕ} {V : Type*} (S : Semantics n V) (f : ℕ → V)
    (code : List (Op n)) (ht : Trace S f 0 code) (i : ℕ) (hi : i < code.length) :
    read S.zero (S.run code #[]) i = f i := by
  have hp : Tracked S.zero f (#[] : Array V) := by
    intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  apply run_tracked S f code #[] hp ht i
  simpa only [run_size,Array.size_empty,Nat.zero_add] using hi

/-- Local trace blocks compose without reevaluating earlier arithmetic. -/
theorem trace_append {n : ℕ} {V : Type*} (S : Semantics n V) (f : ℕ → V)
    (first second : List (Op n)) (k : ℕ) :
    Trace S f k (first++second) ↔ Trace S f k first ∧ Trace S f (k+first.length) second := by
  induction first generalizing k with
  | nil => simp only [List.nil_append,Trace,List.length_nil,Nat.add_zero,true_and]
  | cons op rest ih =>
    simp only [List.cons_append,Trace,ih,List.length_cons,Nat.add_assoc,Nat.add_comm,and_assoc]

def realSemantics {n : ℕ} (v : Fin n → ℝ) : Semantics n ℝ :=
  ⟨v,fun a d => (a : ℝ)/(d : ℝ),(·+·),Neg.neg,(·*·),0⟩

def intervalSemantics {n : ℕ} (s : ℤ) (bounds : Fin n → Interval) : Semantics n Interval :=
  ⟨bounds,Interval.rational s,Interval.add,Interval.neg,Interval.mul s,Interval.point 0⟩

theorem real_run_eq {n : ℕ} (v : Fin n → ℝ) (code : List (Op n)) (previous : Array ℝ) :
    (realSemantics v).run code previous = Program.eval v code previous := by
  induction code generalizing previous with
  | nil => rfl
  | cons op rest ih =>
    have hop : (realSemantics v).eval previous op = op.eval v previous := by cases op <;> rfl
    simpa only [Semantics.run,Program.eval,hop] using ih (previous.push (op.eval v previous))

theorem interval_run_eq {n : ℕ} (s : ℤ) (bounds : Fin n → Interval) (code : List (Op n))
    (previous : Array Interval) :
    (intervalSemantics s bounds).run code previous = Program.enclose s bounds code previous := by
  induction code generalizing previous with
  | nil => rfl
  | cons op rest ih =>
    have hop : (intervalSemantics s bounds).eval previous op = op.enclose s bounds previous := by
      cases op <;> rfl
    simpa only [Semantics.run,Program.enclose,hop] using ih (previous.push (op.enclose s bounds previous))

end FMSA.Convergence.GenericRegisterTrace
/-- info: 'FMSA.Convergence.GenericRegisterTrace.op_value_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms FMSA.Convergence.GenericRegisterTrace.op_value_eq
/-- info: 'FMSA.Convergence.GenericRegisterTrace.tracked_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.GenericRegisterTrace.tracked_push
/-- info: 'FMSA.Convergence.GenericRegisterTrace.run_tracked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.GenericRegisterTrace.run_tracked
/-- info: 'FMSA.Convergence.GenericRegisterTrace.run_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms FMSA.Convergence.GenericRegisterTrace.run_size
/-- info: 'FMSA.Convergence.GenericRegisterTrace.closed_program_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.GenericRegisterTrace.closed_program_values
/-- info: 'FMSA.Convergence.GenericRegisterTrace.trace_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms FMSA.Convergence.GenericRegisterTrace.trace_append
/-- info: 'FMSA.Convergence.GenericRegisterTrace.real_run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.GenericRegisterTrace.real_run_eq
/-- info: 'FMSA.Convergence.GenericRegisterTrace.interval_run_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms FMSA.Convergence.GenericRegisterTrace.interval_run_eq
