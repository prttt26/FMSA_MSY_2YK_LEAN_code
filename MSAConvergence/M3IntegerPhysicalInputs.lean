import MSAConvergence.M3PhysicalBounds
import MSAConvergence.ScaledIntegerIntervals

/-! The exact128-bit rational boxes used by the M3 integer program enclose
true physical pi, its inverse and four exponentials, without an oracle. -/
noncomputable section
namespace FMSA.Convergence.M3IntegerPhysicalInputs
open ScaledIntegerIntervals

set_option maxHeartbeats 3000000 in
-- Exact rational power comparison for the128-bit input grid.
theorem pi_input_enclosed : Encloses (2^128) (⟨1069028584064966747858780876442842309226,1069028584064966747862183700112051693862⟩ : Interval) (Real.pi) := by
  have h := M3PhysicalBounds.pi_interval
  norm_num [Encloses] at *
  constructor <;> linarith [h.1,h.2]

set_option maxHeartbeats 3000000 in
-- Exact rational power comparison for the128-bit input grid.
theorem pi_inverse_input_enclosed : Encloses (2^128) (⟨108315241484954818046648587420924854560,108315241484954818046993365542815312259⟩ : Interval) (Real.pi⁻¹) := by
  have h := M3PhysicalBounds.inverse_pi_interval
  norm_num [Encloses] at *
  constructor <;> linarith [h.1,h.2]

set_option maxHeartbeats 3000000 in
-- Exact rational power comparison for the128-bit input grid.
theorem exp7_input_enclosed : Encloses (2^128) (⟨310297353591408453456666808794198138,310297353591408453463829122653711733⟩ : Interval) (Real.exp (-(7 : ℝ))) := by
  have h := M3PhysicalBounds.exp_seed_multiple 14
  norm_num [Encloses] at *
  constructor <;> linarith [h.1,h.2]

set_option maxHeartbeats 3000000 in
-- Exact rational power comparison for the128-bit input grid.
theorem exp14_input_enclosed : Encloses (2^128) (⟨282954560699298259517370576822755,282954560699298259530432946503019⟩ : Interval) (Real.exp (-(14 : ℝ))) := by
  have h := M3PhysicalBounds.exp_seed_multiple 28
  norm_num [Encloses] at *
  constructor <;> linarith [h.1,h.2]

set_option maxHeartbeats 3000000 in
-- Exact rational power comparison for the128-bit input grid.
theorem exp21_input_enclosed : Encloses (2^128) (⟨258021160973090761041186135444,258021160973090761059053144453⟩ : Interval) (Real.exp (-(21 : ℝ))) := by
  have h := M3PhysicalBounds.exp_seed_multiple 42
  norm_num [Encloses] at *
  constructor <;> linarith [h.1,h.2]

set_option maxHeartbeats 3000000 in
-- Exact rational power comparison for the128-bit input grid.
theorem exp28_input_enclosed : Encloses (2^128) (⟨235284843422800231064605145,235284843422800231086328617⟩ : Interval) (Real.exp (-(28 : ℝ))) := by
  have h := M3PhysicalBounds.exp_seed_multiple 56
  norm_num [Encloses] at *
  constructor <;> linarith [h.1,h.2]

end FMSA.Convergence.M3IntegerPhysicalInputs
/-- info: 'FMSA.Convergence.M3IntegerPhysicalInputs.pi_input_enclosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3IntegerPhysicalInputs.pi_input_enclosed
/-- info: 'FMSA.Convergence.M3IntegerPhysicalInputs.pi_inverse_input_enclosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3IntegerPhysicalInputs.pi_inverse_input_enclosed
/-- info: 'FMSA.Convergence.M3IntegerPhysicalInputs.exp7_input_enclosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3IntegerPhysicalInputs.exp7_input_enclosed
/-- info: 'FMSA.Convergence.M3IntegerPhysicalInputs.exp14_input_enclosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3IntegerPhysicalInputs.exp14_input_enclosed
/-- info: 'FMSA.Convergence.M3IntegerPhysicalInputs.exp21_input_enclosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3IntegerPhysicalInputs.exp21_input_enclosed
/-- info: 'FMSA.Convergence.M3IntegerPhysicalInputs.exp28_input_enclosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3IntegerPhysicalInputs.exp28_input_enclosed
