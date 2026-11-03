import MSAConvergence.PureFluidRFormalPath
import MSAConvergence.PureFluidRPathFormalSubstitution
import MSAConvergence.AnalyticScalarTaylorPowerSeries
import MSAConvergence.PureFluidHActualTaylorIdentification

set_option linter.style.header false

/-! Transfer the true pure-fluid r-node value equation into a formal
one-parameter Taylor equation on the physical hard-sphere root germ. -/
noncomputable section
open Filter Topology
namespace FMSA.Convergence.PureFluidRActualTaylorIdentification
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidRFormalPath
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidRPathFormalSubstitution
open FMSA.Convergence.PureFluidRActualNodeBridge
open FMSA.Convergence.PureFluidHActualNodeBridge
open FMSA.Convergence.PureFluidHActualTaylorIdentification
open FMSA.Convergence.PureFluidHPathFormalSubstitution
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.ExactMSA
variable {T : Type*} [Fintype T]

/-- An eventual analytic r-node value equation transfers to the exact
one-variable formal Taylor equation. -/
theorem RNodeValue_taylor_path_system
    (z : T → ℝ) (theta H R : T → ℝ → ℝ)
    (thetaS HS RS : T → PowerSeries ℝ)
    (htheta : ∀ t, HasTaylorPowerSeriesAt (theta t) (thetaS t))
    (hH : ∀ t, HasTaylorPowerSeriesAt (H t) (HS t))
    (hR : ∀ t, HasTaylorPowerSeriesAt (R t) (RS t))
    (hval : ∀ᶠ tau : ℝ in 𝓝 0,
      RNodeValue z (fun t => theta t tau)
        (fun t => H t tau) (fun t => R t tau)) :
    RNodePathSystem z thetaS HS RS := by
  intro s
  have hterm (t : T) : HasTaylorPowerSeriesAt
      (fun tau => (z s + z t)⁻¹ *
        (theta t tau * (H t tau * (z t - R t tau))))
      (PowerSeries.C ((z s + z t)⁻¹) *
        (thetaS t * (HS t * (PowerSeries.C (z t) - RS t)))) := by
    have hRneg : HasTaylorPowerSeriesAt
        (fun tau => -(R t tau)) (-RS t) := by
      have h := (taylor_const (-1)).mul (hR t)
      convert h using 1
      · funext tau
        simp [Pi.mul_apply]
      · simp
    have hdiff : HasTaylorPowerSeriesAt
        (fun tau => z t - R t tau) (PowerSeries.C (z t) - RS t) := by
      have h := (taylor_const (z t)).add hRneg
      convert h using 1
      · funext tau
        simp [Pi.add_apply, sub_eq_add_neg]
      · simp [sub_eq_add_neg]
    have hfun : ((fun _ : ℝ => (z s + z t)⁻¹) *
        (theta t * (H t * ((fun _ : ℝ => z t) - R t)))) =
        (fun tau => (z s + z t)⁻¹ *
          (theta t tau * (H t tau * (z t - R t tau)))) := by
      funext tau
      simp [Pi.mul_apply, Pi.sub_apply]
    rw [← hfun]
    exact (taylor_const ((z s + z t)⁻¹)).mul
      ((htheta t).mul ((hH t).mul hdiff))
  have hsum : HasTaylorPowerSeriesAt
      (fun tau => ∑ t, (z s + z t)⁻¹ *
        (theta t tau * (H t tau * (z t - R t tau))))
      (∑ t, PowerSeries.C ((z s + z t)⁻¹) *
        (thetaS t * (HS t * (PowerSeries.C (z t) - RS t)))) := by
    have h := HasTaylorPowerSeriesAt.sum Finset.univ
      (fun t : T => fun tau => (z s + z t)⁻¹ *
        (theta t tau * (H t tau * (z t - R t tau))))
      (fun t : T => PowerSeries.C ((z s + z t)⁻¹) *
        (thetaS t * (HS t * (PowerSeries.C (z t) - RS t))))
      (fun t _ => hterm t)
    convert h using 1
    funext tau
    simp only [Finset.sum_apply]
  have hrhs : HasTaylorPowerSeriesAt
      (fun tau => H s tau * ∑ t, (z s + z t)⁻¹ *
        (theta t tau * (H t tau * (z t - R t tau))))
      (HS s * ∑ t, PowerSeries.C ((z s + z t)⁻¹) *
        (thetaS t * (HS t * (PowerSeries.C (z t) - RS t)))) := by
    have h := (hH s).mul hsum
    convert h using 1
    funext tau
    simp only [Pi.mul_apply]
  have heq : R s =ᶠ[𝓝 0]
      (fun tau => H s tau * ∑ t, (z s + z t)⁻¹ *
        (theta t tau * (H t tau * (z t - R t tau)))) := by
    filter_upwards [hval] with tau hv
    have hs := hv s
    change R s tau = H s tau * ∑ t,
      theta t tau * H t tau * ((z t - R t tau) / (z s + z t)) at hs
    rw [hs]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    ring
  exact taylorPowerSeries_eq_of_eventually _ _ _ _ (hR s) hrhs heq

/-- The actual HS-seeded MSA r nodes have an honest local coupling
Taylor series. With the actual theta and H Taylor paths fixed, this r
series is the unique formal solution of their finite node system. -/
theorem exists_actual_hs_root_germ_with_r_taylor_path
    [DecidableEq T]
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t) :
    ∃ (p : ℝ → (T → ℝ) × (T → ℝ))
      (thetaS HS RS : T → PowerSeries ℝ),
      p 0 = ((fun _ => 0), fun t => G0 xi (z t)) ∧
      AnalyticAt ℝ p 0 ∧
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z (p tau).1 (p tau).2 t)
        (thetaS t)) ∧
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualH xi z (p tau).1 (p tau).2 (z t))
        (HS t)) ∧
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualNodeR xi z (p tau).1 (p tau).2 t)
        (RS t)) ∧
      RNodePathSystem z thetaS HS RS ∧
      HS = (fun s => MvPowerSeries.subst thetaS (physicalH z s)) ∧
      RS = (fun s => MvPowerSeries.subst thetaS (RSeries z s)) ∧
      (∀ Q : T → PowerSeries ℝ,
        RNodePathSystem z thetaS HS Q → Q = RS) ∧
      (∀ᶠ tau : ℝ in 𝓝 0,
        MultiTail.IsRoot xi z (fun t => tau * K t)
          (p tau).1 (p tau).2) ∧
      ∀ s, ∀ᶠ tau : ℝ in 𝓝 0,
        HasSum (fun n => PowerSeries.coeff n (RS s) * tau ^ n)
          (actualNodeR xi z (p tau).1 (p tau).2 s) := by
  obtain ⟨p, hp0, hpa, hthetaa, hHa, hRa, hfacts⟩ :=
    exists_actual_hs_root_germ_with_RNodeValue xi hxi0 hxi1 z K hz
  have htheta_exists : ∀ t, ∃ S : PowerSeries ℝ,
      HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z (p tau).1 (p tau).2 t) S := by
    intro t
    exact exists_taylorPowerSeries _ (hthetaa t)
  choose thetaS hthetaS using htheta_exists
  have hH_exists : ∀ t, ∃ S : PowerSeries ℝ,
      HasTaylorPowerSeriesAt
        (fun tau => actualH xi z (p tau).1 (p tau).2 (z t)) S := by
    intro t
    exact exists_taylorPowerSeries _ (hHa t)
  choose HS hHS using hH_exists
  have hR_exists : ∀ t, ∃ S : PowerSeries ℝ,
      HasTaylorPowerSeriesAt
        (fun tau => actualNodeR xi z (p tau).1 (p tau).2 t) S := by
    intro t
    exact exists_taylorPowerSeries _ (hRa t)
  choose RS hRS using hR_exists
  have htheta0 : ∀ t, PowerSeries.constantCoeff (thetaS t) = 0 := by
    intro t
    rw [(hthetaS t).constantCoeff, hp0]
    exact (actual_hs_seed_nodes xi z
      (fun t => G0 xi (z t)) hxi1.ne hz).1 t
  have hval : ∀ᶠ tau : ℝ in 𝓝 0,
      RNodeValue z
        (fun t => actualTheta xi z (p tau).1 (p tau).2 t)
        (fun t => actualH xi z (p tau).1 (p tau).2 (z t))
        (fun t => actualNodeR xi z (p tau).1 (p tau).2 t) := by
    filter_upwards [hfacts] with tau ht
    exact ht.2.2
  have hHval : ∀ᶠ tau : ℝ in 𝓝 0,
      HNodeValue (fun s t => 1 / (z s + z t))
        (fun t => actualTheta xi z (p tau).1 (p tau).2 t)
        (fun t => actualH xi z (p tau).1 (p tau).2 (z t)) := by
    filter_upwards [hfacts] with tau ht
    exact ht.2.1
  have hHsystem := HNodeValue_taylor_path_system
    (fun s t => 1 / (z s + z t))
    (fun t tau => actualTheta xi z (p tau).1 (p tau).2 t)
    (fun t tau => actualH xi z (p tau).1 (p tau).2 (z t))
    thetaS HS hthetaS hHS hHval
  have hHident : HS =
      (fun s => MvPowerSeries.subst thetaS (physicalH z s)) := by
    simpa only [physicalH, one_div] using
      (HNodePathSystem_eq_HSeries_subst
        (fun s t => 1 / (z s + z t))
        thetaS HS htheta0 hHsystem)
  have hsystem := RNodeValue_taylor_path_system z
    (fun t tau => actualTheta xi z (p tau).1 (p tau).2 t)
    (fun t tau => actualH xi z (p tau).1 (p tau).2 (z t))
    (fun t tau => actualNodeR xi z (p tau).1 (p tau).2 t)
    thetaS HS RS hthetaS hHS hRS hval
  have hRident := RNodePathSystem_eq_RSeries_subst
    z thetaS HS RS htheta0 hHident hsystem
  refine ⟨p, thetaS, HS, RS, hp0, hpa, hthetaS, hHS, hRS,
    hsystem, hHident, hRident, ?_, ?_, ?_⟩
  · intro Q hQ
    exact RNodePathSystem_unique z thetaS HS Q RS htheta0 hQ hsystem
  · filter_upwards [hfacts] with tau ht
    exact ht.1
  · intro s
    exact (hRS s).eventually_hasSum

end FMSA.Convergence.PureFluidRActualTaylorIdentification

/-- info: 'FMSA.Convergence.PureFluidRActualTaylorIdentification.RNodeValue_taylor_path_system' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRActualTaylorIdentification.RNodeValue_taylor_path_system
/-- info: 'FMSA.Convergence.PureFluidRActualTaylorIdentification.exists_actual_hs_root_germ_with_r_taylor_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRActualTaylorIdentification.exists_actual_hs_root_germ_with_r_taylor_path
