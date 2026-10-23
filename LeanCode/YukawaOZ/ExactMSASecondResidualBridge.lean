import LeanCode.YukawaOZ.ExactMSARationalData
namespace FMSA.ExactMSA.RationalBridge
open Real SparseCertificate SparseCheckpoints
set_option maxRecDepth 100000
set_option maxHeartbeats 0
variable (xi z k G C S Ez p Dt K : ℝ)
theorem second_residual_numerator (hvac : 1 - xi ≠ 0) (hz : z ≠ 0) (hp : p ≠ 0) :
    r33DenSource xi z k G C S Ez p Dt K * (2*p*G*fSource xi z k G C S Ez p Dt K - pSource xi z k G C S Ez p Dt K)
      = r0Source xi z k G C S Ez p Dt K + Dt * r1Source xi z k G C S Ez p Dt K := by
  have hvacAdd : 1 + -xi ≠ 0 := by simpa only [← sub_eq_add_neg] using hvac
  dsimp only [r33DenSource, fSource, pSource, r0Source, r1Source]
  simp [residualConstant,residualLinear,eval,List.getD]
  field_simp [hvac,hvacAdd, hz, hp]
  sparse_ring
#print axioms second_residual_numerator
end FMSA.ExactMSA.RationalBridge
