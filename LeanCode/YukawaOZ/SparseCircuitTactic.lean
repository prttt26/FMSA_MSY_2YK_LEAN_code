import LeanCode.YukawaOZ.SparseRingTactic

/-! Each circuit operation is certified separately by kernel reduction. Proposed
normal forms are ordinary integer lists. Native computation proposes those lists,
but every connection to the original expression is proved by a kernel-checked
integer equality and the semantic lemmas below. No native_decide is used. -/

namespace FMSA.ExactMSA.SparseCertificate

theorem dag_add (p q r : Poly) (a b : Expr)
    (h : normalizeFast (p ++ q) = r)
    (ha : ∀ v, polyEval p v = eval a v) (hb : ∀ v, polyEval q v = eval b v) :
    ∀ v, polyEval r v = eval (.add a b) v := by
  intro v
  rw [← h, normalizeFast_sound, append_sound, ha, hb]
  rfl

theorem dag_mul (p q r : Poly) (a b : Expr)
    (h : normalizeFast (rawMul p q) = r)
    (ha : ∀ v, polyEval p v = eval a v) (hb : ∀ v, polyEval q v = eval b v) :
    ∀ v, polyEval r v = eval (.mul a b) v := by
  intro v
  rw [← h, normalizeFast_sound, rawMul_sound, ha, hb]
  rfl

theorem dag_neg (p r : Poly) (a : Expr) (h : polyNeg p = r)
    (ha : ∀ v, polyEval p v = eval a v) :
    ∀ v, polyEval r v = eval (.neg a) v := by
  intro v
  rw [← h, polyNeg_sound, ha]
  rfl

theorem dag_pow (p r : Poly) (a : Expr) (n : Nat) (h : powCircuit p n = r)
    (ha : ∀ v, polyEval p v = eval a v) :
    ∀ v, polyEval r v = eval (.pow a n) v := by
  intro v
  rw [← h, powCircuit_sound, ha]
  rfl

theorem dag_same (p : Poly) (a b : Expr)
    (ha : ∀ v, polyEval p v = eval a v) (hb : ∀ v, polyEval p v = eval b v) :
    ∀ v, eval a v = eval b v := by
  intro v
  exact (ha v).symm.trans (hb v)

theorem dag_final (p q : Poly) (a b : Expr)
    (ha : ∀ v, polyEval p v = eval a v) (hb : ∀ v, polyEval q v = eval b v)
    (h : normalizeFast (p ++ polyNeg q) = []) : ∀ v, eval a v = eval b v := by
  intro v
  have hz : polyEval (normalizeFast (p ++ polyNeg q)) v = 0 := by rw [h]; rfl
  rw [normalizeFast_sound, append_sound, polyNeg_sound, ha, hb] at hz
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz)

end FMSA.ExactMSA.SparseCertificate

open Lean Meta Elab Tactic Qq
open FMSA.ExactMSA.SparseCertificate

namespace FMSA.ExactMSA.SparseTactic

private structure DagNode where
  poly : SparseCertificate.Poly
  term : Lean.Expr
  sound : Lean.Expr

private meta def checked (type : Lean.Expr) : TacticM Lean.Expr := do
  let proof ← mkDecideProof type
  let name ← withOptions (Elab.async.set · false) do
    mkAuxLemma [] type proof (kind? := `_sparse_step)
  return mkConst name

private meta def saveSound (proof : Lean.Expr) : TacticM Lean.Expr := do
  let name ← withOptions (Elab.async.set · false) do
    mkAuxLemma [] (← inferType proof) proof (kind? := `_sparse_semantics)
  return mkConst name

private meta partial def compileDag (source : Lean.Expr) :
    StateRefT (Std.HashMap Lean.Expr DagNode) TacticM DagNode := do
  if let some node := (← get)[source]? then return node
  let e ← whnf source
  let args := e.getAppArgs
  let node ← match e.getAppFn.constName? with
  | some ``SparseCertificate.Expr.const | some ``SparseCertificate.Expr.var => do
    let term ← mkAppM ``compileRaw #[e]
    let poly ← unsafe Lean.Meta.evalExpr SparseCertificate.Poly q(SparseCertificate.Poly) term
    let sound ← saveSound (← mkAppM ``compileRaw_sound #[e])
    pure ⟨poly,term,sound⟩
  | some ``SparseCertificate.Expr.add | some ``SparseCertificate.Expr.mul => do
    let a := args[0]!
    let b := args[1]!
    let pa ← compileDag a
    let pb ← compileDag b
    let isAdd := e.isAppOf ``SparseCertificate.Expr.add
    let poly := normalizeFast (if isAdd then pa.poly ++ pb.poly else rawMul pa.poly pb.poly)
    let term := toExpr poly
    let operation ← if isAdd then mkAppM ``List.append #[pa.term,pb.term]
      else mkAppM ``rawMul #[pa.term,pb.term]
    let expected ← mkAppM ``normalizeFast #[operation]
    let h ← checked (← mkEq expected term)
    let sound ← saveSound (← mkAppM (if isAdd then ``dag_add else ``dag_mul)
      #[pa.term,pb.term,term,a,b,h,pa.sound,pb.sound])
    pure ⟨poly,term,sound⟩
  | some ``SparseCertificate.Expr.neg => do
    let a := args[0]!
    let pa ← compileDag a
    let poly := polyNeg pa.poly
    let term := toExpr poly
    let h ← checked (← mkEq (← mkAppM ``polyNeg #[pa.term]) term)
    let sound ← saveSound (← mkAppM ``dag_neg #[pa.term,term,a,h,pa.sound])
    pure ⟨poly,term,sound⟩
  | some ``SparseCertificate.Expr.pow => do
    let a := args[0]!
    let nn := args[1]!
    let some n ← getNatValue? nn | throwError "sparse circuit requires natural literal powers"
    let pa ← compileDag a
    let poly := powCircuit pa.poly n
    let term := toExpr poly
    let h ← checked (← mkEq (← mkAppM ``powCircuit #[pa.term,nn]) term)
    let sound ← saveSound (← mkAppM ``dag_pow #[pa.term,term,a,nn,h,pa.sound])
    pure ⟨poly,term,sound⟩
  | _ => throwError "unsupported sparse circuit expression {e}"
  modify (·.insert source node)
  let count := (← get).size
  if count % 50 == 0 then
    Lean.Core.liftIOCore (IO.eprintln s!"sparse circuit: {count} certified nodes; latest {node.poly.length} monomials")
  return node

private meta def dagProof (a b : Lean.Expr) : TacticM Lean.Expr := do
  let ((pa,pb), _) ← (do
    let pa ← compileDag a
    let pb ← compileDag b
    pure (pa,pb)).run {}
  if pa.poly == pb.poly then
    mkAppM ``dag_same #[pa.term,a,b,pa.sound,pb.sound]
  else
    let difference ← mkAppM ``List.append #[pa.term,← mkAppM ``polyNeg #[pb.term]]
    let normalized ← mkAppM ``normalizeFast #[difference]
    let h ← checked (← mkEq normalized (toExpr ([] : SparseCertificate.Poly)))
    mkAppM ``dag_final #[pa.term,pb.term,a,b,pa.sound,pb.sound,h]

elab "sparse_expr_dag" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_,lhs,rhs) := (← goal.getType).eq? | throwError "expected an equality"
  unless lhs.isAppOfArity ``eval 2 && rhs.isAppOfArity ``eval 2 do
    throwError "expected eval a v = eval b v"
  let la := lhs.getAppArgs
  let ra := rhs.getAppArgs
  unless ← isDefEq la[1]! ra[1]! do throwError "evaluation assignments differ"
  let proof ← dagProof la[0]! ra[0]!
  goal.assign (mkApp proof la[1]!)
  replaceMainGoal []

elab "sparse_dag" : tactic => withMainContext do
  let originalGoals ← getGoals
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_,lhs,rhs) := target.eq? | throwError "expected an equality"
  let ((a,b),atoms) ← (do
    let a ← reify lhs
    let b ← reify rhs
    pure (a,b)).run #[]
  let xs : Q(List ℝ) ← mkListLit q(ℝ) atoms.toList
  let v : Q(Nat → ℝ) := q(fun i => List.getD $xs i 0)
  let result := mkApp (← dagProof a b) v
  let transport ← mkFreshExprMVar (← mkEq (← inferType result) target)
  setGoals [transport.mvarId!]
  evalTactic (← `(tactic| simp [eval,List.getD,sub_eq_add_neg]))
  unless (← getGoals).isEmpty do throwError "sparse circuit transport did not close"
  goal.assign (← mkAppM ``Eq.mp #[← instantiateMVars transport,result])
  setGoals originalGoals.tail

end FMSA.ExactMSA.SparseTactic
