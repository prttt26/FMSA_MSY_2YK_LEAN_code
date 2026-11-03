import MSAConvergence.PureFluidFoldCore
import MSAConvergence.PureFluidPositiveSubstitution

set_option linter.style.header false

/-! The genuine hard-sphere-seeded MSA germ gives a `NodeFamily`, with its Taylor series. -/

noncomputable section
open Filter Topology
namespace FMSA.Convergence.PureFluidFoldBridge
open FMSA.Convergence.PureFluidFoldCore FMSA.Convergence.PureFluidSeriesEval
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidRFormalPath FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidRActualTaylorIdentification FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.PureFluidRActualNodeBridge FMSA.Convergence.PureFluidActualAnalyticGerm
open FMSA.Convergence.PureFluidActualNodeGerm FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidActualDressingCoordinates FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.PureFluidThetaCouplingTaylor FMSA.Convergence.PureFluidPositiveSubstitution
open FMSA.Convergence.PureFluidHPathFormalSubstitution FMSA.Convergence.PureFluidHFormalSolution
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidHActualNodeBridge

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The node form of the formal `H` system. -/
theorem eqH_of_path_system {θ H : T → PowerSeries ℝ} {c : T → T → ℝ}
    (h : HNodePathSystem c θ H) (s : T) :
    H s * (1 - ∑ t, PowerSeries.C (c s t) * (θ t * H t)) = 1 := by
  have h1 := h s
  have h2 : H s * ∑ t, PowerSeries.C (c s t) * (θ t * H t) =
      ∑ t, PowerSeries.C (c s t) * (θ t * (H s * H t)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [mul_sub, mul_one, h2]
  nth_rewrite 1 [h1]
  ring

/-- **Bridge.** The genuine hard-sphere-seeded MSA germ, with positive strengths, has Taylor
series of its actual `θ, H, r` nodes that form a `NodeFamily`. -/
theorem exists_germ_nodeFamily
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t) (hK : ∀ t, 0 < K t) :
    ∃ (p : ℝ → (T → ℝ) × (T → ℝ)) (θS HS RS : T → PowerSeries ℝ),
      p 0 = ((fun _ => 0), fun t => G0 xi (z t)) ∧
      AnalyticAt ℝ p 0 ∧
      (∀ t, HasTaylorPowerSeriesAt (fun τ => actualTheta xi z (p τ).1 (p τ).2 t) (θS t)) ∧
      (∀ t, HasTaylorPowerSeriesAt (fun τ => actualH xi z (p τ).1 (p τ).2 (z t)) (HS t)) ∧
      (∀ t, HasTaylorPowerSeriesAt (fun τ => actualNodeR xi z (p τ).1 (p τ).2 t) (RS t)) ∧
      NodeFamily z (physicalAlpha xi z K) (fun t => hardKappa xi (z t)) θS HS RS ∧
      RNodePathSystem z θS HS RS ∧
      ∀ᶠ τ : ℝ in 𝓝 0, MultiTail.IsRoot xi z (fun t => τ * K t) (p τ).1 (p τ).2 := by
  obtain ⟨p, θS, HS, RS, hp0, hpa, hθ, hH, hR, hsys, hHident, hRident, _huniq, hroot, _hsum⟩ :=
    exists_actual_hs_root_germ_with_r_taylor_path xi hxi0 hxi1 z K hz
  have hU := actualU_nodes_nonzero_eventually_of_continuous_seed
    xi z hxi1.ne hz p (fun t => G0 xi (z t)) hpa.continuousAt hp0
  have hF := actual_factor_nodes_nonzero_eventually_of_continuous_seed
    xi hxi0 hxi1 z hz p (fun t => G0 xi (z t)) hpa.continuousAt hp0
  have hval : ∀ᶠ τ : ℝ in 𝓝 0, ∀ t, physicalAlpha xi z K t * τ =
      actualTheta xi z (p τ).1 (p τ).2 t *
        (1 - hardKappa xi (z t) * actualNodeR xi z (p τ).1 (p τ).2 t) ^ 2 := by
    filter_upwards [hroot, hU, hF] with τ hr hu hf
    intro t
    have heq := actual_theta_equation_all_rates xi z (fun u => τ * K u) (p τ).1 (p τ).2
      hxi0 hxi1 hz hr hf hu t
    calc physicalAlpha xi z K t * τ =
        rhoOf xi * (2 * Real.pi * (τ * K t) / z t) / (F0 xi (z t)) ^ 2 := by
          dsimp [physicalAlpha]; ring
      _ = _ := heq
  have heqn := theta_value_equation_taylor (physicalAlpha xi z K) (fun t => hardKappa xi (z t))
    (fun t τ => actualTheta xi z (p τ).1 (p τ).2 t)
    (fun t τ => actualNodeR xi z (p τ).1 (p τ).2 t) θS RS hθ hR hval
  have hR0 : ∀ t, PowerSeries.constantCoeff (RS t) = 0 := by
    intro t
    rw [(hR t).constantCoeff, hp0]
    change actualNodeR xi z (fun _ => 0) (fun u => G0 xi (z u)) t = 0
    unfold actualNodeR
    have hdress := actual_dressing_zero_tail xi z (fun u => G0 xi (z u)) (z t) hxi1.ne (hz t).ne'
    rw [hdress.1, hdress.2]
    norm_num
  have hfixed := theta_fixed_point_of_coupling_equation (physicalAlpha xi z K)
    (fun t => hardKappa xi (z t)) θS RS hR0 heqn
  have hθ0 : ∀ t, PowerSeries.constantCoeff (θS t) = 0 := by
    intro t
    rw [(hθ t).constantCoeff, hp0]
    exact (actual_hs_seed_nodes xi z (fun u => G0 xi (z u)) hxi1.ne hz).1 t
  have hα : ∀ t, 0 < physicalAlpha xi z K t := physicalAlpha_pos xi hxi0 hxi1 z K hz hK
  have hκ : ∀ t, 0 < hardKappa xi (z t) := fun t => hardKappa_pos xi (z t) hxi0 hxi1 (hz t)
  have hfixed' : ∀ t, θS t = PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X *
      (1 - PowerSeries.C (hardKappa xi (z t)) * MvPowerSeries.subst θS (RSeries z t))⁻¹ ^ 2 := by
    intro t
    simpa only [hRident] using hfixed t
  have hθP := theta_fixed_point_coeffNonneg z hz (physicalAlpha xi z K)
    (fun t => hardKappa xi (z t)) (fun t => (hα t).le) (fun t => (hκ t).le) θS hθ0 hfixed'
  have hRP : ∀ t, CoeffNonneg (RS t) := by
    intro t; rw [hRident]; exact RSeries_subst_coeffNonneg z hz θS hθ0 hθP t
  have hHP : ∀ t, CoeffNonneg (HS t) := by
    intro t
    rw [hHident]
    exact coeffNonneg_subst θS hθ0 hθP _ (fun m => by
      simpa only [physicalH, one_div] using physical_HSeries_coeff_nonneg z hz t m)
  have hHsys : HNodePathSystem (fun s t => (z s + z t)⁻¹) θS HS := by
    have := HSeries_subst_path_system (fun s t => (z s + z t)⁻¹) θS hθ0
    rw [hHident]
    exact this
  refine ⟨p, θS, HS, RS, hp0, hpa, hθ, hH, hR, ?_, hsys, hroot⟩
  exact
    { hz := hz
      hα := hα
      hκ := hκ
      θ_cn := hθP
      H_cn := hHP
      r_cn := hRP
      θ0 := fun t => by simpa using hθ0 t
      r0 := fun t => by simpa using hR0 t
      eqθ := heqn
      eqH := fun s => eqH_of_path_system hHsys s }


end FMSA.Convergence.PureFluidFoldBridge

/-- info: 'FMSA.Convergence.PureFluidFoldBridge.eqH_of_path_system' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldBridge.eqH_of_path_system
/-- info: 'FMSA.Convergence.PureFluidFoldBridge.exists_germ_nodeFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldBridge.exists_germ_nodeFamily
