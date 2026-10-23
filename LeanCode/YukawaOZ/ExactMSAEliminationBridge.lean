import LeanCode.YukawaOZ.SparseCircuitTactic
import LeanCode.YukawaOZ.ExactMSARationalData
namespace FMSA.ExactMSA.RationalBridge
open Real SparseCertificate SparseCheckpoints
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
variable (xi z k G C S Ez p Dt K : ℝ)
theorem eliminated_numerator (hvac : 1 - xi ≠ 0) (hz : z ≠ 0) (hk : k ≠ 0)
    (hp : p ≠ 0) (hE : Ez ≠ 0) (hzk : k^2 + z^2 ≠ 0) :
    denSource xi z k G C S Ez p Dt K *
      (deltaSource xi z k G C S Ez p Dt K - m29Source xi z k G C S Ez p Dt K *
        (Dt * fSource xi z k G C S Ez p Dt K - 2*p*K/z)) = rawSource xi z k G C S Ez p Dt K := by
  have hvacAdd : 1 + -xi ≠ 0 := by simpa only [← sub_eq_add_neg] using hvac
  have hzkSwap : z^2 + k^2 ≠ 0 := by simpa only [add_comm] using hzk
  dsimp only [denSource, deltaSource, m29Source, fSource, rawSource]
  simp [rawSourceExpr,eval,List.getD]
  field_simp [hvac,hvacAdd, hz, hk, hp, hE, hzk,hzkSwap]
  sparse_dag
#print axioms eliminated_numerator
end FMSA.ExactMSA.RationalBridge
