import LeanCode.YukawaOZ.SparseCircuitTactic
import LeanCode.YukawaOZ.ExactMSAPhysicalDictionary
namespace FMSA.ExactMSA.RationalBridge
open Real SparseCertificate SparseCheckpoints
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
variable (xi z k Dt G K : ℝ)
theorem delta_dictionary (hvac : 1-xi ≠ 0) (hz : z ≠ 0) (hk : k ≠ 0) :
    deltaActual xi z k Dt G K = deltaSource xi z k G (Real.cos k) (Real.sin k) (Real.exp (-z)) Real.pi Dt K := by
  have hvacAdd : 1 + -xi ≠ 0 := by simpa only [← sub_eq_add_neg] using hvac
  have hzk : k^2+z^2 ≠ 0 := by positivity
  have hzkswap : z^2+k^2 ≠ 0 := by positivity
  have hE : Real.exp (-z) ≠ 0 := Real.exp_ne_zero _
  have hexp : Real.exp z = 1 / Real.exp (-z) := by
    rw [Real.exp_neg,one_div,inv_inv]
  dsimp only [deltaActual,deltaSource,msaQre,msaQim,msaRez,msaImz,msaA,msaQp,
    uT,wT,uTil,wTil,reph1,reph2,imph1,imph2,bA0,bB0,qp0,rhoOf,Mtil,Ntil,gam]
  rw [hexp]
  by_cases hK : K = 0
  · subst K
    simp only [mul_zero,zero_mul,zero_div,zero_pow]
    field_simp [hvac,hvacAdd,hvacAdd,hz,hk,Real.pi_ne_zero,hE,hzk,hzkswap]
    sparse_dag
  · field_simp [hvac,hz,hk,hK,Real.pi_ne_zero,hE,hzk,hzkswap]
    sparse_dag
#print axioms delta_dictionary
end FMSA.ExactMSA.RationalBridge
