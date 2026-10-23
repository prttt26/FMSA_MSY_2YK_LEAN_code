import LeanCode.YukawaOZ.SparsePolynomialCertificate
import Mathlib.Tactic
import Qq

/-! A polynomial tactic which reifies the actual Lean goal, then checks the
integer computation in the kernel. Unrecognised real subexpressions are atoms.
This connects sparse certificates to ordinary mathematical expressions. -/

namespace FMSA.ExactMSA.SparseCertificate

def powCircuit (p : Poly) : Nat → Poly
  | 0 => [([],1)]
  | n+1 => normalizeFast (rawMul (powCircuit p n) p)

theorem powCircuit_sound (p : Poly) (n : Nat) (v : Nat → ℝ) :
    polyEval (powCircuit p n) v = polyEval p v ^ n := by
  induction n with
  | zero => simp [powCircuit, polyEval, monoEval]
  | succ n ih => simp only [powCircuit, normalizeFast_sound, rawMul_sound, ih, pow_succ]

/-- Normalize at circuit nodes to avoid raw expansion of repeated sums. -/
def compileCircuit : Expr → Poly
  | .const c => [([],c)]
  | .var i => [(variableMono i,1)]
  | .add a b => normalizeFast (compileCircuit a ++ compileCircuit b)
  | .mul a b => normalizeFast (rawMul (compileCircuit a) (compileCircuit b))
  | .neg a => polyNeg (compileCircuit a)
  | .pow a n => powCircuit (compileCircuit a) n

theorem compileCircuit_sound (e : Expr) (v : Nat → ℝ) :
    polyEval (compileCircuit e) v = eval e v := by
  induction e with
  | const c => simp [compileCircuit, polyEval, monoEval, eval]
  | var i => simp [compileCircuit, polyEval, variableMono_sound, eval]
  | add a b ha hb => simp [compileCircuit, normalizeFast_sound, append_sound, ha, hb, eval]
  | mul a b ha hb => simp [compileCircuit, normalizeFast_sound, rawMul_sound, ha, hb, eval]
  | neg a ha => simp [compileCircuit, polyNeg_sound, ha, eval]
  | pow a n ha => simp [compileCircuit, powCircuit_sound, ha, eval]

theorem circuit_identity (a b : Expr)
    (h : compileCircuit (.add a (.neg b)) = []) (v : Nat → ℝ) : eval a v = eval b v := by
  have hz : eval (.add a (.neg b)) v = 0 := by
    rw [← compileCircuit_sound, h]
    rfl
  simpa only [eval, ← sub_eq_add_neg, sub_eq_zero] using hz

theorem expression_identity (a b : Expr)
    (h : compile (.add a (.neg b)) = []) (v : Nat → ℝ) : eval a v = eval b v := by
  have hz := expression_zero (.add a (.neg b)) h v
  simpa only [eval, ← sub_eq_add_neg, sub_eq_zero] using hz

end FMSA.ExactMSA.SparseCertificate

open Lean Meta Elab Tactic Qq
open FMSA.ExactMSA.SparseCertificate

namespace FMSA.ExactMSA.SparseTactic

partial def reify (e : Lean.Expr) : StateRefT (Array Lean.Expr) MetaM Lean.Expr := do
  let e := e.consumeMData
  let f := e.getAppFn
  let args := e.getAppArgs
  let opname := f.constName?
  if opname == some ``OfNat.ofNat && args.size == 3 then
    if let some n := args[1]!.rawNatLit? then
      let nn : Q(Nat) := Lean.mkRawNatLit n
      let zn : Q(Int) := q(Int.ofNat $nn)
      return q(SparseCertificate.Expr.const $zn)
  if opname == some ``HAdd.hAdd || opname == some ``HMul.hMul ||
      opname == some ``HSub.hSub then
    let a : Q(SparseCertificate.Expr) ← reify args[args.size-2]!
    let b : Q(SparseCertificate.Expr) ← reify args[args.size-1]!
    if opname == some ``HAdd.hAdd then return q(SparseCertificate.Expr.add $a $b)
    if opname == some ``HMul.hMul then return q(SparseCertificate.Expr.mul $a $b)
    return q(SparseCertificate.Expr.add $a (SparseCertificate.Expr.neg $b))
  if opname == some ``Neg.neg then
    let a : Q(SparseCertificate.Expr) ← reify args.back!
    return q(SparseCertificate.Expr.neg $a)
  if opname == some ``HPow.hPow then
    if let some n ← getNatValue? args.back! then
      let a : Q(SparseCertificate.Expr) ← reify args[args.size-2]!
      let nn : Q(Nat) := Lean.mkRawNatLit n
      return q(SparseCertificate.Expr.pow $a $nn)
  let atoms ← get
  for i in [:atoms.size] do
    if atoms[i]! == e then
      let nn : Q(Nat) := Lean.mkRawNatLit i
      return q(SparseCertificate.Expr.var $nn)
  let i := atoms.size
  modify (·.push e)
  let nn : Q(Nat) := Lean.mkRawNatLit i
  return q(SparseCertificate.Expr.var $nn)

private meta def runSparseRing (useCircuit : Bool) : TacticM Unit := withMainContext do
  let originalGoals ← getGoals
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_, lhs, rhs) := target.eq? | throwError "sparse_ring expects an equality"
  unless ← isDefEq (← inferType lhs) q(ℝ) do
    throwError "sparse_ring currently handles real polynomial equalities"
  let ((a, b), atoms) ← (do
    let a ← reify lhs
    let b ← reify rhs
    pure (a,b)).run #[]
  logInfo m!"sparse_ring: reified {atoms.size} real atoms; checking integer circuit in kernel"
  let a : Q(SparseCertificate.Expr) := a
  let b : Q(SparseCertificate.Expr) := b
  let xs : Q(List ℝ) ← mkListLit q(ℝ) atoms.toList
  let v : Q(Nat → ℝ) := q(fun i => List.getD $xs i 0)
  let certType : Q(Prop) := if useCircuit then
    q(compileCircuit (SparseCertificate.Expr.add $a (SparseCertificate.Expr.neg $b)) = [])
    else q(compile (SparseCertificate.Expr.add $a (SparseCertificate.Expr.neg $b)) = [])
  let cert ← mkFreshExprMVar certType
  setGoals [cert.mvarId!]
  try
    evalTactic (← `(tactic| decide +kernel))
  catch err =>
    for i in [:atoms.size] do
      logInfo m!"sparse_ring atom {i}: {atoms[i]!}"
    throw err
  let h ← instantiateMVars cert
  let result ← mkAppM (if useCircuit then ``circuit_identity else ``expression_identity) #[a,b,h,v]
  let transport ← mkFreshExprMVar (← mkEq (← inferType result) target)
  setGoals [transport.mvarId!]
  evalTactic (← `(tactic| simp [eval, List.getD, sub_eq_add_neg]))
  unless (← getGoals).isEmpty do
    throwError "sparse_ring reification transport did not close: {← (← getMainGoal).getType}"
  let transport ← instantiateMVars transport
  goal.assign (← instantiateMVars (← mkAppM ``Eq.mp #[transport,result]))
  setGoals originalGoals.tail

elab "sparse_ring" : tactic => runSparseRing false
elab "sparse_ring_circuit" : tactic => runSparseRing true

end FMSA.ExactMSA.SparseTactic
