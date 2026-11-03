import MSAConvergence.PureFluidRActualTaylorIdentification
import MSAConvergence.PureFluidRRepeatedKernel
import Mathlib.Analysis.Analytic.Linear

set_option linter.style.header false

/-! Transfer the genuine pure-fluid theta equation to the
physical-coupling Taylor path. -/
noncomputable section
open Filter Topology
namespace FMSA.Convergence.PureFluidThetaCouplingTaylor
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidRActualTaylorIdentification
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidRActualNodeBridge
open FMSA.Convergence.PureFluidActualAnalyticGerm
open FMSA.Convergence.PureFluidActualNodeGerm
open FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.ExactMSA
variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The physical coupling coefficient in the theta node equation. -/
def physicalAlpha (xi : ℝ) (z K : T → ℝ) (t : T) : ℝ :=
  rhoOf xi * (2 * Real.pi * K t / z t) / (F0 xi (z t)) ^ 2

omit [Fintype T] [DecidableEq T] in
/-- A positive Yukawa coupling has a positive physical theta source. -/
theorem physicalAlpha_pos (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t)
    (hK : ∀ t, 0 < K t) (t : T) :
    0 < physicalAlpha xi z K t := by
  have hrho : 0 < rhoOf xi := by
    unfold rhoOf
    positivity
  have hnum : 0 < 2 * Real.pi * K t / z t :=
    div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hK t)) (hz t)
  have hden : 0 < (F0 xi (z t)) ^ 2 := by
    have hne : F0 xi (z t) ≠ 0 := by
      exact ne_of_gt (lt_trans one_pos (actual_F0_gt_one xi (z t) hxi hxi1 (hz t)))
    positivity
  exact div_pos (mul_pos hrho hnum) hden

/-- The ordinary identity map has precisely the formal
one-variable generator as its Taylor series at zero. -/
theorem taylor_id : HasTaylorPowerSeriesAt
    (fun tau : ℝ => tau) (PowerSeries.X : PowerSeries ℝ) := by
  let L : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
  refine ⟨L.fpowerSeries 0, ?_, ?_⟩
  · change HasFPowerSeriesAt (id : ℝ → ℝ) (L.fpowerSeries 0) 0
    simpa [L] using L.hasFPowerSeriesAt 0
  · intro n
    cases n with
    | zero => simp [L, ContinuousLinearMap.fpowerSeries,
        FormalMultilinearSeries.coeff, PowerSeries.coeff_X]
    | succ n =>
      cases n with
      | zero => simp [L, ContinuousLinearMap.fpowerSeries,
          FormalMultilinearSeries.coeff, PowerSeries.coeff_X]
      | succ n => simp [ContinuousLinearMap.fpowerSeries,
          FormalMultilinearSeries.coeff, PowerSeries.coeff_X]

omit [Fintype T] [DecidableEq T] in
/-- An eventual actual theta equation transfers to the exact
one-variable formal coupling equation. -/
theorem theta_value_equation_taylor
    (alpha kappa : T → ℝ)
    (theta R : T → ℝ → ℝ)
    (thetaS RS : T → PowerSeries ℝ)
    (htheta : ∀ t, HasTaylorPowerSeriesAt (theta t) (thetaS t))
    (hR : ∀ t, HasTaylorPowerSeriesAt (R t) (RS t))
    (hval : ∀ᶠ tau : ℝ in 𝓝 0,
      ∀ t, alpha t * tau =
        theta t tau * (1 - kappa t * R t tau) ^ 2) :
    ∀ t, PowerSeries.C (alpha t) * PowerSeries.X =
      thetaS t *
        (1 - PowerSeries.C (kappa t) * RS t) ^ 2 := by
  intro t
  have hleft : HasTaylorPowerSeriesAt
      (fun tau => alpha t * tau)
      (PowerSeries.C (alpha t) * PowerSeries.X) := by
    have h := (taylor_const (alpha t)).mul taylor_id
    convert h using 1
    funext tau
    simp [Pi.mul_apply]
  have hneg : HasTaylorPowerSeriesAt
      (fun tau => -(kappa t * R t tau))
      (-(PowerSeries.C (kappa t) * RS t)) := by
    have h := (taylor_const (-(kappa t))).mul (hR t)
    convert h using 1
    · funext tau
      simp [Pi.mul_apply]
    · simp [map_neg, mul_comm]
  have hgap : HasTaylorPowerSeriesAt
      (fun tau => 1 - kappa t * R t tau)
      (1 - PowerSeries.C (kappa t) * RS t) := by
    have h := (taylor_const 1).add hneg
    convert h using 1
    · funext tau
      simp [Pi.add_apply, sub_eq_add_neg]
    · simp [sub_eq_add_neg]
  have hsq : HasTaylorPowerSeriesAt
      (fun tau => (1 - kappa t * R t tau) ^ 2)
      ((1 - PowerSeries.C (kappa t) * RS t) ^ 2) := by
    have h := hgap.mul hgap
    convert h using 1
    · funext tau
      simp [Pi.mul_apply, pow_two]
    · ring
  have hright : HasTaylorPowerSeriesAt
      (fun tau => theta t tau * (1 - kappa t * R t tau) ^ 2)
      (thetaS t * (1 - PowerSeries.C (kappa t) * RS t) ^ 2) := by
    have h := (htheta t).mul hsq
    convert h using 1
    funext tau
    simp [Pi.mul_apply]
  have heq :
      (fun tau => alpha t * tau) =ᶠ[𝓝 0]
        (fun tau => theta t tau * (1 - kappa t * R t tau) ^ 2) := by
    filter_upwards [hval] with tau h
    exact h t
  exact taylorPowerSeries_eq_of_eventually _ _ _ _ hleft hright heq

omit [Fintype T] [DecidableEq T] in
/-- Algebraic Picard form of the theta equation when the r path
starts at zero. This is a fixed-point identity, not yet a
coefficient positivity or convergence theorem. -/
theorem theta_fixed_point_of_coupling_equation
    (alpha kappa : T → ℝ) (thetaS RS : T → PowerSeries ℝ)
    (hR0 : ∀ t, PowerSeries.constantCoeff (RS t) = 0)
    (heq : ∀ t, PowerSeries.C (alpha t) * PowerSeries.X =
      thetaS t * (1 - PowerSeries.C (kappa t) * RS t) ^ 2) :
    ∀ t, thetaS t =
      PowerSeries.C (alpha t) * PowerSeries.X *
        (1 - PowerSeries.C (kappa t) * RS t)⁻¹ ^ 2 := by
  intro t
  let g : PowerSeries ℝ := 1 - PowerSeries.C (kappa t) * RS t
  have hg0 : PowerSeries.constantCoeff g ≠ 0 := by
    simp [g, hR0 t]
  have hginv : g * g⁻¹ = 1 := PowerSeries.mul_inv_cancel g hg0
  have h := heq t
  change PowerSeries.C (alpha t) * PowerSeries.X = thetaS t * g ^ 2 at h
  calc
    thetaS t = thetaS t * (g ^ 2 * (g⁻¹ ^ 2)) := by
      rw [← mul_pow, hginv, one_pow, mul_one]
    _ = PowerSeries.C (alpha t) * PowerSeries.X * (g⁻¹ ^ 2) := by
      rw [← mul_assoc, ← h]
    _ = _ := rfl

/-- The genuine HS-seeded MSA root germ obeys the physical-coupling
theta equation as an identity of its actual Taylor series. -/
theorem exists_actual_hs_root_germ_with_theta_coupling_taylor
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t) :
    ∃ (p : ℝ → (T → ℝ) × (T → ℝ))
      (thetaS RS : T → PowerSeries ℝ),
      p 0 = ((fun _ => 0), fun t => G0 xi (z t)) ∧
      AnalyticAt ℝ p 0 ∧
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z (p tau).1 (p tau).2 t) (thetaS t)) ∧
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualNodeR xi z (p tau).1 (p tau).2 t) (RS t)) ∧
      RS = (fun t => MvPowerSeries.subst thetaS (RSeries z t)) ∧
      (∀ t, PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X =
        thetaS t *
          (1 - PowerSeries.C (hardKappa xi (z t)) * RS t) ^ 2) ∧
      (∀ t, thetaS t =
        PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X *
          (1 - PowerSeries.C (hardKappa xi (z t)) * RS t)⁻¹ ^ 2) ∧
      (∀ᶠ tau : ℝ in 𝓝 0,
        MultiTail.IsRoot xi z (fun t => tau * K t)
          (p tau).1 (p tau).2) ∧
      ∀ s, ∀ᶠ tau : ℝ in 𝓝 0,
        HasSum (fun n => PowerSeries.coeff n (RS s) * tau ^ n)
          (actualNodeR xi z (p tau).1 (p tau).2 s) := by
  obtain ⟨p, thetaS, HS, RS, hp0, hpa, htheta, _hHS, hRS,
    _hsys, _hHident, hRident, _huniq, hroot, hsum⟩ :=
    exists_actual_hs_root_germ_with_r_taylor_path xi hxi0 hxi1 z K hz
  have hU := actualU_nodes_nonzero_eventually_of_continuous_seed
    xi z hxi1.ne hz p (fun t => G0 xi (z t)) hpa.continuousAt hp0
  have hF := actual_factor_nodes_nonzero_eventually_of_continuous_seed
    xi hxi0 hxi1 z hz p (fun t => G0 xi (z t)) hpa.continuousAt hp0
  have hval : ∀ᶠ tau : ℝ in 𝓝 0,
      ∀ t, physicalAlpha xi z K t * tau =
        actualTheta xi z (p tau).1 (p tau).2 t *
          (1 - hardKappa xi (z t) *
            actualNodeR xi z (p tau).1 (p tau).2 t) ^ 2 := by
    filter_upwards [hroot, hU, hF] with tau hr hu hf
    intro t
    have heq := actual_theta_equation_all_rates xi z
      (fun u => tau * K u) (p tau).1 (p tau).2
      hxi0 hxi1 hz hr hf hu t
    calc
      physicalAlpha xi z K t * tau =
          rhoOf xi * (2 * Real.pi * (tau * K t) / z t) /
            (F0 xi (z t)) ^ 2 := by
        dsimp [physicalAlpha]
        ring
      _ = _ := heq
  have heqn := theta_value_equation_taylor
    (physicalAlpha xi z K) (fun t => hardKappa xi (z t))
    (fun t tau => actualTheta xi z (p tau).1 (p tau).2 t)
    (fun t tau => actualNodeR xi z (p tau).1 (p tau).2 t)
    thetaS RS htheta hRS hval
  have hR0 : ∀ t, PowerSeries.constantCoeff (RS t) = 0 := by
    intro t
    rw [(hRS t).constantCoeff, hp0]
    change actualNodeR xi z (fun _ => 0)
      (fun u => G0 xi (z u)) t = 0
    unfold actualNodeR
    have hdress := actual_dressing_zero_tail xi z
      (fun u => G0 xi (z u)) (z t) hxi1.ne (hz t).ne'
    rw [hdress.1, hdress.2]
    norm_num
  have hfixed := theta_fixed_point_of_coupling_equation
    (physicalAlpha xi z K) (fun t => hardKappa xi (z t))
    thetaS RS hR0 heqn
  exact ⟨p, thetaS, RS, hp0, hpa, htheta, hRS,
    hRident, heqn, hfixed, hroot, hsum⟩

end FMSA.Convergence.PureFluidThetaCouplingTaylor

/-- info: 'FMSA.Convergence.PureFluidThetaCouplingTaylor.physicalAlpha_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaCouplingTaylor.physicalAlpha_pos
/-- info: 'FMSA.Convergence.PureFluidThetaCouplingTaylor.taylor_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaCouplingTaylor.taylor_id
/-- info: 'FMSA.Convergence.PureFluidThetaCouplingTaylor.theta_value_equation_taylor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaCouplingTaylor.theta_value_equation_taylor
/-- info: 'FMSA.Convergence.PureFluidThetaCouplingTaylor.theta_fixed_point_of_coupling_equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaCouplingTaylor.theta_fixed_point_of_coupling_equation
/-- info: 'FMSA.Convergence.PureFluidThetaCouplingTaylor.exists_actual_hs_root_germ_with_theta_coupling_taylor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaCouplingTaylor.exists_actual_hs_root_germ_with_theta_coupling_taylor
