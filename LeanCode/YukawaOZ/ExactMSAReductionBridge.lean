import LeanCode.YukawaOZ.ExactMSARationalData
import LeanCode.YukawaOZ.SparseCircuitTactic
namespace FMSA.ExactMSA.RationalBridge
open Real SparseCertificate SparseCheckpoints
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def reductionRHSExpr : Expr :=
  .add (.add (.mul dt1Left (.var 8)) (.mul dt2Left (.pow (.var 8) 2)))
    (.mul muSourceExpr (.add (.add (.pow (.var 5) 2) (.pow (.var 4) 2)) (.neg (.const 1))))

theorem reduction_identity (v : Nat → ℝ) :
    eval rawSourceExpr v = eval reductionRHSExpr v := by
  sparse_expr_dag

theorem raw_reduction (xi z k G C S Ez p Dt K : ℝ) :
    rawSource xi z k G C S Ez p Dt K =
      n1Source xi z k G C S Ez p Dt K * Dt + n2Source xi z k G C S Ez p Dt K * Dt^2 +
      muSource xi z k G C S Ez p Dt K * (S^2+C^2-1) := by
  let v : Nat → ℝ := fun i => ([xi,z,k,G,C,S,Ez,p,Dt,K] : List ℝ).getD i 0
  have h := reduction_identity v
  change eval rawSourceExpr v = eval dt1Left v * Dt + eval dt2Left v * Dt^2 +
    eval muSourceExpr v * (S^2+C^2-((1 : Int) : ℝ)) at h
  simpa only [rawSource,n1Source,n2Source,muSource,Int.cast_one] using h
#print axioms raw_reduction

theorem coefficient_reassembly (xi z k G C S Ez p Dt K : ℝ) :
    n1Source xi z k G C S Ez p Dt K * Dt + n2Source xi z k G C S Ez p Dt K * Dt^2
      = Dt * q1Source xi z k G C S Ez p Dt K * (r0Source xi z k G C S Ez p Dt K + Dt*r1Source xi z k G C S Ez p Dt K) := by
  have h := full_division_reassembled
    (fun i => ([xi,z,k,G,C,S,Ez,p,Dt,K] : List ℝ).getD i 0) Dt
  simpa only [n1Source,n2Source,q1Source,r0Source,r1Source] using h
#print axioms coefficient_reassembly
end FMSA.ExactMSA.RationalBridge
