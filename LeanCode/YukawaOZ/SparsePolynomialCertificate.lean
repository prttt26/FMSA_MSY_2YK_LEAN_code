import Mathlib

/-!
Computable sparse integer polynomial certificates. All computations are checked
by the Lean kernel, with no native_decide or externally asserted polynomial axiom.
The polynomial degree does not enter the additive coefficient normalization.
-/

namespace FMSA.ExactMSA.SparseCertificate

abbrev Mono := List Nat
abbrev Term := Mono × Int
abbrev Poly := List Term

def monoEval : Mono → (Nat → ℝ) → ℝ
  | [], _ => 1
  | n :: ns, v => v 0 ^ n * monoEval ns (fun i => v (i + 1))

def monoMul : Mono → Mono → Mono
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: monoMul xs ys

theorem monoMul_sound (xs ys : Mono) (v : Nat → ℝ) :
    monoEval (monoMul xs ys) v = monoEval xs v * monoEval ys v := by
  induction xs generalizing ys v with
  | nil => simp [monoMul, monoEval]
  | cons x xs ih =>
    cases ys with
    | nil => simp [monoMul, monoEval]
    | cons y ys => simp only [monoMul, monoEval, pow_add, ih]; ring

def polyEval : Poly → (Nat → ℝ) → ℝ
  | [], _ => 0
  | (m, c) :: ps, v => (c : ℝ) * monoEval m v + polyEval ps v

theorem append_sound (p q : Poly) (v : Nat → ℝ) :
    polyEval (p ++ q) v = polyEval p v + polyEval q v := by
  induction p with
  | nil => simp [polyEval]
  | cons t p ih => cases t; simp [polyEval, ih, add_assoc]

def insert (m : Mono) (c : Int) : Poly → Poly
  | [] => if c = 0 then [] else [(m,c)]
  | (n,d) :: ps =>
    if m = n then
      if c + d = 0 then ps else (m,c+d) :: ps
    else (n,d) :: insert m c ps

theorem insert_sound (m : Mono) (c : Int) (p : Poly) (v : Nat → ℝ) :
    polyEval (insert m c p) v = (c : ℝ) * monoEval m v + polyEval p v := by
  induction p with
  | nil => by_cases h : c = 0 <;> simp [insert, h, polyEval]
  | cons t p ih =>
    obtain ⟨n,d⟩ := t
    by_cases hmn : m = n
    · subst n
      by_cases hcd : c + d = 0
      · have hreal : (c : ℝ) + (d : ℝ) = 0 := by exact_mod_cast hcd
        simp only [insert, if_true, if_pos hcd, polyEval]
        rw [← add_assoc, ← add_mul, hreal, zero_mul, zero_add]
      · simp only [insert, if_true, if_neg hcd, polyEval, Int.cast_add]
        ring
    · simp only [insert, if_neg hmn, polyEval, ih]
      ring

def normalize : Poly → Poly
  | [] => []
  | (m,c) :: ps => insert m c (normalize ps)

theorem normalize_sound (p : Poly) (v : Nat → ℝ) :
    polyEval (normalize p) v = polyEval p v := by
  induction p with
  | nil => rfl
  | cons t p ih => cases t; simp only [normalize, insert_sound, ih, polyEval]

theorem perm_sound {p q : Poly} (h : List.Perm p q) (v : Nat → ℝ) :
    polyEval p v = polyEval q v := by
  induction h with
  | nil => rfl
  | cons t h ih => cases t; simp only [polyEval, ih]
  | swap t u p => cases t; cases u; simp only [polyEval]; ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Only the first term is inspected. Sorting first makes equal keys adjacent. -/
def insertHead (m : Mono) (c : Int) (p : Poly) : Poly :=
  if c = 0 then p else
  match p with
  | [] => [(m,c)]
  | (n,d) :: ps =>
    if m = n then
      if c + d = 0 then ps else (m,c+d) :: ps
    else (m,c) :: p

theorem insertHead_sound (m : Mono) (c : Int) (p : Poly) (v : Nat → ℝ) :
    polyEval (insertHead m c p) v = (c : ℝ) * monoEval m v + polyEval p v := by
  by_cases hc : c = 0
  · simp [insertHead, hc]
  · cases p with
    | nil => simp [insertHead, hc, polyEval]
    | cons t ps =>
      obtain ⟨n,d⟩ := t
      by_cases hmn : m = n
      · subst n
        by_cases hcd : c + d = 0
        · have hreal : (c : ℝ) + (d : ℝ) = 0 := by exact_mod_cast hcd
          simp only [insertHead, if_neg hc, if_true, if_pos hcd, polyEval]
          rw [← add_assoc, ← add_mul, hreal, zero_mul, zero_add]
        · simp only [insertHead, if_neg hc, if_true, if_neg hcd, polyEval, Int.cast_add]
          ring
      · simp [insertHead, hc, hmn, polyEval]

def collectAdjacent : Poly → Poly
  | [] => []
  | (m,c) :: ps => insertHead m c (collectAdjacent ps)

theorem collectAdjacent_sound (p : Poly) (v : Nat → ℝ) :
    polyEval (collectAdjacent p) v = polyEval p v := by
  induction p with
  | nil => rfl
  | cons t p ih => cases t; simp only [collectAdjacent, insertHead_sound, ih, polyEval]

def mergeFuel : Nat → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, t :: p, u :: q =>
    if compare t.1 u.1 != Ordering.gt then t :: mergeFuel n p (u :: q)
    else u :: mergeFuel n (t :: p) q

theorem mergeFuel_sound (n : Nat) (p q : Poly) (v : Nat → ℝ) :
    polyEval (mergeFuel n p q) v = polyEval p v + polyEval q v := by
  induction n generalizing p q with
  | zero => exact append_sound p q v
  | succ n ih =>
    cases p with
    | nil => simp [mergeFuel, polyEval]
    | cons t p =>
      cases q with
      | nil => simp [mergeFuel, polyEval]
      | cons u q =>
        cases t; cases u
        simp only [mergeFuel]
        split <;> simp only [polyEval, ih] <;> ring

/-- Explicit structural fuel avoids the opaque well-founded accessibility
proof inside the standard mergeSort implementation during kernel reduction.
Insufficient fuel affects completeness, never soundness of a certificate. -/
def sortFuel : Nat → Poly → Poly
  | 0, p => p
  | n+1, p =>
    if p.length ≤ 1 then p else
    let a := sortFuel n (p.take (p.length / 2))
    let b := sortFuel n (p.drop (p.length / 2))
    mergeFuel (a.length + b.length) a b

theorem sortFuel_sound (n : Nat) (p : Poly) (v : Nat → ℝ) :
    polyEval (sortFuel n p) v = polyEval p v := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    unfold sortFuel
    split
    · rfl
    · rw [mergeFuel_sound, ih, ih, ← append_sound, List.take_append_drop]

def normalizeFast (p : Poly) : Poly := collectAdjacent (sortFuel 32 p)

theorem normalizeFast_sound (p : Poly) (v : Nat → ℝ) :
    polyEval (normalizeFast p) v = polyEval p v := by
  rw [normalizeFast, collectAdjacent_sound, sortFuel_sound]

def mulTerm (m : Mono) (c : Int) : Poly → Poly
  | [] => []
  | (n,d) :: ps => (monoMul m n,c*d) :: mulTerm m c ps

theorem mulTerm_sound (m : Mono) (c : Int) (p : Poly) (v : Nat → ℝ) :
    polyEval (mulTerm m c p) v = (c : ℝ) * monoEval m v * polyEval p v := by
  induction p with
  | nil => simp [mulTerm, polyEval]
  | cons t p ih =>
    cases t
    simp only [mulTerm, polyEval, Int.cast_mul, monoMul_sound, ih]
    ring

def rawMul : Poly → Poly → Poly
  | [], _ => []
  | (m,c) :: ps, q => mulTerm m c q ++ rawMul ps q

theorem rawMul_sound (p q : Poly) (v : Nat → ℝ) :
    polyEval (rawMul p q) v = polyEval p v * polyEval q v := by
  induction p with
  | nil => simp [rawMul, polyEval]
  | cons t p ih =>
    cases t
    simp only [rawMul, append_sound, mulTerm_sound, polyEval, ih]
    ring

def polyAdd (p q : Poly) : Poly := normalize (p ++ q)
def polyMul (p q : Poly) : Poly := normalize (rawMul p q)

def polyPow (p : Poly) : Nat → Poly
  | 0 => [([],1)]
  | n+1 => polyMul (polyPow p n) p

theorem polyPow_sound (p : Poly) (n : Nat) (v : Nat → ℝ) :
    polyEval (polyPow p n) v = polyEval p v ^ n := by
  induction n with
  | zero => simp [polyPow, polyEval, monoEval]
  | succ n ih => simp [polyPow, polyMul, normalize_sound, rawMul_sound, ih, pow_succ]

def rawPow (p : Poly) : Nat → Poly
  | 0 => [([],1)]
  | n+1 => rawMul (rawPow p n) p

theorem rawPow_sound (p : Poly) (n : Nat) (v : Nat → ℝ) :
    polyEval (rawPow p n) v = polyEval p v ^ n := by
  induction n with
  | zero => simp [rawPow, polyEval, monoEval]
  | succ n ih => simp [rawPow, rawMul_sound, ih, pow_succ]

def polyNeg : Poly → Poly
  | [] => []
  | (m,c) :: ps => (m,-c) :: polyNeg ps

theorem polyNeg_sound (p : Poly) (v : Nat → ℝ) :
    polyEval (polyNeg p) v = -polyEval p v := by
  induction p with
  | nil => simp [polyNeg, polyEval]
  | cons t p ih => cases t; simp only [polyNeg, polyEval, Int.cast_neg, ih]; ring

/-- Check a supplied integer-polynomial identity without a real-ring tactic. -/
theorem identity_of_normalize_zero (p : Poly) (h : normalize p = []) (v : Nat → ℝ) :
    polyEval p v = 0 := by
  rw [← normalize_sound, h]
  rfl

inductive Expr where
  | const : Int → Expr
  | var : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr
  | pow : Expr → Nat → Expr
  deriving DecidableEq

def eval : Expr → (Nat → ℝ) → ℝ
  | .const c, _ => c
  | .var i, v => v i
  | .add a b, v => eval a v + eval b v
  | .mul a b, v => eval a v * eval b v
  | .neg a, v => -eval a v
  | .pow a n, v => eval a v ^ n

def variableMono (i : Nat) : Mono := List.replicate i 0 ++ [1]

theorem variableMono_sound (i : Nat) (v : Nat → ℝ) :
    monoEval (variableMono i) v = v i := by
  induction i generalizing v with
  | zero => simp [variableMono, monoEval]
  | succ i ih =>
    simpa [variableMono, List.replicate_succ, monoEval] using (ih (fun j => v (j+1)))

def compileRaw : Expr → Poly
  | .const c => [([],c)]
  | .var i => [(variableMono i,1)]
  | .add a b => compileRaw a ++ compileRaw b
  | .mul a b => rawMul (compileRaw a) (compileRaw b)
  | .neg a => polyNeg (compileRaw a)
  | .pow a n => rawPow (compileRaw a) n

theorem compileRaw_sound (e : Expr) (v : Nat → ℝ) : polyEval (compileRaw e) v = eval e v := by
  induction e with
  | const c => simp [compileRaw, polyEval, monoEval, eval]
  | var i => simp [compileRaw, polyEval, variableMono_sound, eval]
  | add a b ha hb => simp [compileRaw, append_sound, ha, hb, eval]
  | mul a b ha hb => simp [compileRaw, rawMul_sound, ha, hb, eval]
  | neg a ha => simp [compileRaw, polyNeg_sound, ha, eval]
  | pow a n ha => simp [compileRaw, rawPow_sound, ha, eval]

def compile (e : Expr) : Poly := normalizeFast (compileRaw e)

theorem compile_sound (e : Expr) (v : Nat → ℝ) : polyEval (compile e) v = eval e v := by
  rw [compile, normalizeFast_sound, compileRaw_sound]

theorem expression_zero (e : Expr) (h : compile e = []) (v : Nat → ℝ) : eval e v = 0 := by
  rw [← compile_sound, h]
  rfl

end FMSA.ExactMSA.SparseCertificate
