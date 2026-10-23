import LeanCode.YukawaOZ.ExactMSADeltaDictionary
import LeanCode.YukawaOZ.ExactMSAEliminationBridge
import LeanCode.YukawaOZ.ExactMSASecondResidualBridge
import LeanCode.YukawaOZ.ExactMSAReductionBridge

namespace FMSA.ExactMSA.RationalBridge
open Real

/-- The original k-space residual, rather than only encoded coefficients,
vanishes on the regular domain at a Blum--Hoye root. -/
theorem deltaActual_zero (xi z k Dt G K : ℝ) (hvac : 1-xi ≠ 0)
    (hz : z ≠ 0) (hk : k ≠ 0)
    (h29 : Dt * bhF xi z (Dt,G) - 2*π*K/z = 0)
    (h33 : 2*π*(G * bhF xi z (Dt,G)) - bhP xi z (Dt,G) = 0) :
    deltaActual xi z k Dt G K = 0 := by
  have hzk : k^2+z^2 ≠ 0 := by positivity
  have hzkSwap : z^2+k^2 ≠ 0 := by simpa only [add_comm] using hzk
  have hE : Real.exp (-z) ≠ 0 := Real.exp_ne_zero _
  have hf := bhF_dictionary xi z k Dt G K hvac hz
  have hp := bhP_dictionary xi z k Dt G K hvac hz
  rw [hf] at h29 h33
  rw [hp] at h33
  have h33' : 2*π*G*fSource xi z k G (cos k) (sin k) (exp (-z)) π Dt K -
      pSource xi z k G (cos k) (sin k) (exp (-z)) π Dt K = 0 := by
    simpa only [mul_assoc] using h33
  have hs := second_residual_numerator xi z k G (cos k) (sin k) (exp (-z)) π Dt K
    hvac hz pi_ne_zero
  rw [h33', mul_zero] at hs
  have hroot := hs.symm
  have ht : sin k ^ 2 + cos k ^ 2 - 1 = 0 := by
    rw [sin_sq_add_cos_sq, sub_self]
  have hr := raw_reduction xi z k G (cos k) (sin k) (exp (-z)) π Dt K
  rw [ht, mul_zero, add_zero, coefficient_reassembly, hroot, mul_zero] at hr
  have he := eliminated_numerator xi z k G (cos k) (sin k) (exp (-z)) π Dt K
    hvac hz hk pi_ne_zero hE hzk
  rw [h29, mul_zero, sub_zero, hr] at he
  have hd : denSource xi z k G (cos k) (sin k) (exp (-z)) π Dt K ≠ 0 := by
    simp [denSource, hk, hz, pi_ne_zero, hzk, hzkSwap, hvac, ← sub_eq_add_neg]
  have hdelta := (mul_eq_zero.mp he).resolve_left hd
  rw [delta_dictionary xi z k Dt G K hvac hz hk]
  exact hdelta

/-- info: 'FMSA.ExactMSA.RationalBridge.deltaActual_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deltaActual_zero
end FMSA.ExactMSA.RationalBridge
