import MSAConvergence.PureFluidMixedRay

set_option linter.style.header false

/-! The original amplitudes as series in the tail strengths, and their identification with the
Taylor series of the actual germ on every ray. -/

noncomputable section
open Filter Topology
namespace FMSA.Convergence.PureFluidMixedAmplitude
open FMSA.Convergence.PureFluidMixedPicard FMSA.Convergence.PureFluidMixedRay
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidFoldClosedForm FMSA.Convergence.PureFluidFoldPath
open FMSA.Convergence.PureFluidPositiveSubstitution
open FMSA.Convergence.PureFluidThetaCouplingTaylor
open FMSA.Convergence.PureFluidRActualTaylorIdentification
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidRActualNodeBridge
open FMSA.Convergence.PureFluidActualThetaEquation FMSA.Convergence.PureFluidActualNodeGerm
open FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidHActualNodeBridge FMSA.Convergence.PureFluidNodeClosedForm
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidExponentialSplit FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.ExactMSA

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- `D_t` in the tail strengths. -/
def dK (xi : ℝ) (z : T → ℝ) (t : T) : MvPowerSeries T ℝ :=
  MvPowerSeries.C (F0 xi (z t) / rhoOf xi * alphaUnit xi z t) *
    (MvPowerSeries.X t * (hK xi z t * qK xi z t))

/-- `G_t` in the tail strengths. -/
def gK (xi : ℝ) (z : T → ℝ) (t : T) : MvPowerSeries T ℝ :=
  MvPowerSeries.C (hardG0Node xi (z t)) +
    MvPowerSeries.C (2 * Real.pi * rhoOf xi * (F0 xi (z t)) ^ 2)⁻¹ * (rK xi z t * qK xi z t)

theorem taylor_congr {f g : ℝ → ℝ} {S : PowerSeries ℝ} (h : HasTaylorPowerSeriesAt f S)
    (e : f =ᶠ[𝓝 0] g) : HasTaylorPowerSeriesAt g S := by
  obtain ⟨q, hq, hc⟩ := h
  exact ⟨q, hq.congr e, hc⟩

/-- The Taylor series of `r/(1 - κ r)`. -/
theorem taylor_quotient {r : ℝ → ℝ} {RS : PowerSeries ℝ} {κ : ℝ}
    (hr : HasTaylorPowerSeriesAt r RS) (h0 : PowerSeries.constantCoeff RS = 0) :
    HasTaylorPowerSeriesAt (fun x => r x / (1 - κ * r x)) (RS * (1 - PowerSeries.C κ * RS)⁻¹) := by
  obtain ⟨p, hp, hc⟩ := id hr
  have hr0 : r 0 = 0 := by rw [← hr.constantCoeff, h0]
  have han : AnalyticAt ℝ r 0 := hp.analyticAt
  have hd : AnalyticAt ℝ (fun x => 1 - κ * r x) 0 := analyticAt_const.sub (analyticAt_const.mul han)
  have hd0 : (1 - κ * r 0) ≠ 0 := by simp [hr0]
  obtain ⟨Q, hQ⟩ := exists_taylorPowerSeries _ (han.div hd hd0)
  have hne : ∀ᶠ x in 𝓝 (0 : ℝ), 1 - κ * r x ≠ 0 := hd.continuousAt.eventually_ne hd0
  have hT := hQ.mul ((taylor_const 1).add ((taylor_const (-κ)).mul hr))
  have heq := taylorPowerSeries_eq_of_eventually _ _ _ _ hT hr (by
    filter_upwards [hne] with x hx
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [show (1 : ℝ) + -κ * r x = 1 - κ * r x by ring]
    exact div_mul_cancel₀ _ hx)
  have hc1 : PowerSeries.constantCoeff (1 - PowerSeries.C κ * RS) ≠ 0 := by simp [h0]
  have hinv := PowerSeries.mul_inv_cancel (1 - PowerSeries.C κ * RS) hc1
  have hmul : Q * (1 - PowerSeries.C κ * RS) = RS := by
    rw [show (1 : PowerSeries ℝ) - PowerSeries.C κ * RS =
      PowerSeries.C 1 + PowerSeries.C (-κ) * RS by simp only [map_one, map_neg]; ring]
    exact heq
  have hQe : Q = RS * (1 - PowerSeries.C κ * RS)⁻¹ := by
    linear_combination (-Q) * hinv + (1 - PowerSeries.C κ * RS)⁻¹ * hmul
  rw [← hQe]
  exact hQ

/-- On every ray the actual germ has the restricted series as its Taylor series. -/
theorem exists_ray_germ (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1) (z K : T → ℝ)
    (hz : ∀ t, 0 < z t) :
    ∃ p : ℝ → (T → ℝ) × (T → ℝ),
      p 0 = ((fun _ => 0), fun t => G0 xi (z t)) ∧ AnalyticAt ℝ p 0 ∧
      (∀ᶠ τ : ℝ in 𝓝 0, MultiTail.IsRoot xi z (fun t => τ * K t) (p τ).1 (p τ).2) ∧
      (∀ t, HasTaylorPowerSeriesAt (fun τ => (p τ).1 t) (res K (dK xi z t))) ∧
      (∀ t, HasTaylorPowerSeriesAt (fun τ => (p τ).2 t) (res K (gK xi z t))) := by
  obtain ⟨p, θS, HS, RS, hp0, hpa, hθ, hH, hR, _hsys, hHident, hRident, _huniq, hroot, _hsum⟩ :=
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
  have hfixed' : ∀ t, θS t = PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X *
      (1 - PowerSeries.C (hardKappa xi (z t)) * MvPowerSeries.subst θS (RSeries z t))⁻¹ ^ 2 := by
    intro t
    simpa only [hRident] using hfixed t
  have hθe := res_theta_eq xi z K hθ0 hfixed'
  have hRe : ∀ t, res K (rK xi z t) = RS t := fun t => by
    rw [res_r, hθe, hRident]
  have hHe : ∀ t, res K (hK xi z t) = HS t := fun t => by
    rw [res_H, hθe, hHident]
  have hqe : ∀ t, res K (qK xi z t) = (1 - PowerSeries.C (hardKappa xi (z t)) * RS t)⁻¹ := fun t => by
    rw [res_q, hRe]; rfl
  have hρ := rhoOf_pos hxi0
  have hF0 : ∀ t, F0 xi (z t) ≠ 0 := fun t =>
    ne_of_gt (lt_trans one_pos (actual_F0_gt_one xi (z t) hxi0 hxi1 (hz t)))
  refine ⟨p, hp0, hpa, hroot, fun t => ?_, fun t => ?_⟩
  · have hT := (taylor_const (F0 xi (z t) / rhoOf xi)).mul (((hθ t).mul (hH t)).mul
      ((taylor_const 1).add ((taylor_const (-hardKappa xi (z t))).mul (hR t))))
    have hser : PowerSeries.C (F0 xi (z t) / rhoOf xi) * (θS t * HS t *
        (PowerSeries.C 1 + PowerSeries.C (-hardKappa xi (z t)) * RS t)) = res K (dK xi z t) := by
      have hc1 : PowerSeries.constantCoeff (1 - PowerSeries.C (hardKappa xi (z t)) * RS t) ≠ 0 := by
        simp [hR0 t]
      have hq1 := PowerSeries.mul_inv_cancel (1 - PowerSeries.C (hardKappa xi (z t)) * RS t) hc1
      have hfx : θS t = PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X *
          (1 - PowerSeries.C (hardKappa xi (z t)) * RS t)⁻¹ ^ 2 := hfixed t
      have hα : physicalAlpha xi z K t = alphaUnit xi z t * K t := by
        simp only [alphaUnit, physicalAlpha]; ring
      unfold dK
      rw [res_mul, res_C, res_mul, res_X, res_mul, hHe, hqe, ray, hfx, hα]
      simp only [map_mul, map_one, map_neg]
      linear_combination (PowerSeries.C (F0 xi (z t) / rhoOf xi) *
        PowerSeries.C (alphaUnit xi z t) * PowerSeries.C (K t) * PowerSeries.X * HS t *
        (1 - PowerSeries.C (hardKappa xi (z t)) * RS t)⁻¹) * hq1
    rw [← hser]
    refine taylor_congr hT ?_
    filter_upwards [hroot, hU, hF] with τ hr hu hf
    have hD := actual_D_closed_all_rates xi z (fun u => τ * K u) (p τ).1 (p τ).2
      hxi0 hxi1 hz hr hf hu t
    have hw : actualTheta xi z (p τ).1 (p τ).2 t * actualH xi z (p τ).1 (p τ).2 (z t) =
        actualWeight xi z (p τ).1 (p τ).2 t := by
      unfold actualTheta actualH
      field_simp [hu t]
    have hv : (p τ).1 t = F0 xi (z t) * actualWeight xi z (p τ).1 (p τ).2 t *
        (1 - hardKappa xi (z t) * actualNodeR xi z (p τ).1 (p τ).2 t) / rhoOf xi := by
      rw [eq_div_iff hρ.ne', mul_comm, hD]
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [hw, hv]
    ring
  · have hT := (taylor_const (hardG0Node xi (z t))).add
      ((taylor_const (2 * Real.pi * rhoOf xi * (F0 xi (z t)) ^ 2)⁻¹).mul
        (taylor_quotient (κ := hardKappa xi (z t)) (hR t) (hR0 t)))
    have hser : PowerSeries.C (hardG0Node xi (z t)) +
        PowerSeries.C (2 * Real.pi * rhoOf xi * (F0 xi (z t)) ^ 2)⁻¹ *
          (RS t * (1 - PowerSeries.C (hardKappa xi (z t)) * RS t)⁻¹) = res K (gK xi z t) := by
      unfold gK
      rw [res_add, res_C, res_mul, res_C, res_mul, hRe, hqe]
    rw [← hser]
    refine taylor_congr hT ?_
    filter_upwards [hroot, hU, hF] with τ hr hu hf
    have hG := actual_G_closed_all_rates xi z (fun u => τ * K u) (p τ).1 (p τ).2
      hxi0 hxi1 hz hr hf hu t
    have hne : 2 * Real.pi * rhoOf xi * (F0 xi (z t)) ^ 2 ≠ 0 := by
      have := hF0 t; positivity
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [← hG, inv_mul_cancel_left₀ hne]
    ring


end FMSA.Convergence.PureFluidMixedAmplitude

/-- info: 'FMSA.Convergence.PureFluidMixedAmplitude.taylor_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedAmplitude.taylor_congr
/-- info: 'FMSA.Convergence.PureFluidMixedAmplitude.taylor_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedAmplitude.taylor_quotient
/-- info: 'FMSA.Convergence.PureFluidMixedAmplitude.exists_ray_germ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedAmplitude.exists_ray_germ
