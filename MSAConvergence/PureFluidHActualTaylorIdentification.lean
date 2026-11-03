import MSAConvergence.AnalyticScalarTaylorPowerSeries
import MSAConvergence.PureFluidHActualNodeBridge

set_option linter.style.header false

/-! Identify the one-variable Taylor series of actual pure-fluid H nodes
with formal substitution of the unique multivariate H-node solution. -/
noncomputable section
open Filter Topology
namespace FMSA.Convergence.PureFluidHActualTaylorIdentification
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidHPathFormalSubstitution
open FMSA.Convergence.PureFluidHFormalSolution
open FMSA.Convergence.PureFluidHActualNodeBridge
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.ExactMSA
variable {T : Type*} [Fintype T] [DecidableEq T]

omit [DecidableEq T] in
/-- An eventual analytic H-node value equation transfers to the
corresponding one-variable formal Taylor equation. -/
theorem HNodeValue_taylor_path_system
    (c : T → T → ℝ) (theta H : T → ℝ → ℝ)
    (thetaS HS : T → PowerSeries ℝ)
    (htheta : ∀ t, HasTaylorPowerSeriesAt (theta t) (thetaS t))
    (hH : ∀ s, HasTaylorPowerSeriesAt (H s) (HS s))
    (hval : ∀ᶠ tau : ℝ in 𝓝 0,
      HNodeValue c (fun t => theta t tau) (fun s => H s tau)) :
    HNodePathSystem c thetaS HS := by
  intro s
  have hterm (t : T) : HasTaylorPowerSeriesAt
      (fun tau => c s t * theta t tau * H s tau * H t tau)
      (PowerSeries.C (c s t) * (thetaS t * (HS s * HS t))) := by
    have hfun : ((fun _ : ℝ => c s t) * (theta t * (H s * H t))) =
        (fun tau => c s t * theta t tau * H s tau * H t tau) := by
      funext tau
      simp [Pi.mul_apply, mul_assoc]
    rw [← hfun]
    exact (taylor_const (c s t)).mul
      ((htheta t).mul ((hH s).mul (hH t)))
  have hsum := HasTaylorPowerSeriesAt.sum Finset.univ
    (fun t : T => fun tau : ℝ => c s t * theta t tau * H s tau * H t tau)
    (fun t : T => PowerSeries.C (c s t) *
      (thetaS t * (HS s * HS t))) (fun t _ => hterm t)
  have hrhs : HasTaylorPowerSeriesAt
      (fun tau : ℝ => 1 + ∑ t, c s t * theta t tau * H s tau * H t tau)
      (1 + ∑ t, PowerSeries.C (c s t) *
        (thetaS t * (HS s * HS t))) := by
    have hfun : ((fun _ : ℝ => 1) +
        ∑ t : T, (fun tau : ℝ =>
          c s t * theta t tau * H s tau * H t tau)) =
        (fun tau : ℝ => 1 + ∑ t : T,
          c s t * theta t tau * H s tau * H t tau) := by
      funext tau
      simp [Pi.add_apply, Finset.sum_apply]
    rw [← hfun]
    simpa using (taylor_const 1).add hsum
  have heq : (fun tau => H s tau) =ᶠ[𝓝 0]
      (fun tau => 1 + ∑ t, c s t * theta t tau * H s tau * H t tau) := by
    filter_upwards [hval] with tau hv
    simpa only [mul_assoc] using hv s
  exact taylorPowerSeries_eq_of_eventually _ _ _ _ (hH s) hrhs heq

/-- On the genuine analytic hard-sphere-seeded MSA root germ, the Taylor
series of each actual H node is precisely the unique multivariate formal
H solution substituted along the actual theta Taylor path. This is a
formal identity; convergence of the multivariate theta series is separate. -/
theorem exists_actual_hs_root_germ_taylor_identification
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t) :
    ∃ (p : ℝ → (T → ℝ) × (T → ℝ))
      (thetaS HS : T → PowerSeries ℝ),
      p 0 = ((fun _ => 0), fun t => G0 xi (z t)) ∧
      AnalyticAt ℝ p 0 ∧
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z (p tau).1 (p tau).2 t)
        (thetaS t)) ∧
      (∀ s, HasTaylorPowerSeriesAt
        (fun tau => actualH xi z (p tau).1 (p tau).2 (z s))
        (HS s)) ∧
      HS = (fun s => MvPowerSeries.subst thetaS
        (HSeries (fun s t => 1 / (z s + z t)) s)) ∧
      ∀ᶠ tau : ℝ in 𝓝 0,
        MultiTail.IsRoot xi z (fun t => tau * K t)
          (p tau).1 (p tau).2 := by
  obtain ⟨p, hp0, hpa, hthetaa, hHa, hfacts⟩ :=
    exists_actual_hs_root_germ_with_HNodeValue xi hxi0 hxi1 z K hz
  have htheta_exists : ∀ t, ∃ S : PowerSeries ℝ,
      HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z (p tau).1 (p tau).2 t) S := by
    intro t
    exact exists_taylorPowerSeries _ (hthetaa t)
  choose thetaS hthetaS using htheta_exists
  have hH_exists : ∀ s, ∃ S : PowerSeries ℝ,
      HasTaylorPowerSeriesAt
        (fun tau => actualH xi z (p tau).1 (p tau).2 (z s)) S := by
    intro s
    exact exists_taylorPowerSeries _ (hHa s)
  choose HS hHS using hH_exists
  have htheta0 : ∀ t, PowerSeries.constantCoeff (thetaS t) = 0 := by
    intro t
    rw [(hthetaS t).constantCoeff, hp0]
    exact (actual_hs_seed_nodes xi z
      (fun t => G0 xi (z t)) hxi1.ne hz).1 t
  have hval : ∀ᶠ tau : ℝ in 𝓝 0,
      HNodeValue (fun s t => 1 / (z s + z t))
        (fun t => actualTheta xi z (p tau).1 (p tau).2 t)
        (fun s => actualH xi z (p tau).1 (p tau).2 (z s)) := by
    filter_upwards [hfacts] with tau ht
    exact ht.2
  have hsystem := HNodeValue_taylor_path_system
    (fun s t => 1 / (z s + z t))
    (fun t tau => actualTheta xi z (p tau).1 (p tau).2 t)
    (fun s tau => actualH xi z (p tau).1 (p tau).2 (z s))
    thetaS HS hthetaS hHS hval
  have hident := HNodePathSystem_eq_HSeries_subst
    (fun s t => 1 / (z s + z t)) thetaS HS htheta0 hsystem
  refine ⟨p, thetaS, HS, hp0, hpa, hthetaS, hHS, hident, ?_⟩
  filter_upwards [hfacts] with tau ht
  exact ht.1

/-- The formally substituted H series has a genuinely convergent
one-variable coupling expansion near the physical HS seed, and its sum
is the actual H node on the MSA root germ. The claim is local in tau. -/
theorem exists_actual_hs_root_germ_with_convergent_H_path
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t) :
    ∃ (p : ℝ → (T → ℝ) × (T → ℝ))
      (thetaS : T → PowerSeries ℝ),
      p 0 = ((fun _ => 0), fun t => G0 xi (z t)) ∧
      AnalyticAt ℝ p 0 ∧
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z (p tau).1 (p tau).2 t)
        (thetaS t)) ∧
      (∀ᶠ tau : ℝ in 𝓝 0,
        MultiTail.IsRoot xi z (fun t => tau * K t)
          (p tau).1 (p tau).2) ∧
      ∀ s, ∀ᶠ tau : ℝ in 𝓝 0,
        HasSum (fun n => PowerSeries.coeff n
          (MvPowerSeries.subst thetaS
            (HSeries (fun u t => 1 / (z u + z t)) s)) * tau ^ n)
          (actualH xi z (p tau).1 (p tau).2 (z s)) := by
  obtain ⟨p, thetaS, HS, hp0, hpa, hthetaS, hHS, hident, hroot⟩ :=
    exists_actual_hs_root_germ_taylor_identification
      xi hxi0 hxi1 z K hz
  refine ⟨p, thetaS, hp0, hpa, hthetaS, hroot, ?_⟩
  intro s
  simpa only [hident] using (hHS s).eventually_hasSum

end FMSA.Convergence.PureFluidHActualTaylorIdentification

/-- info: 'FMSA.Convergence.PureFluidHActualTaylorIdentification.HNodeValue_taylor_path_system' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHActualTaylorIdentification.HNodeValue_taylor_path_system
/-- info: 'FMSA.Convergence.PureFluidHActualTaylorIdentification.exists_actual_hs_root_germ_taylor_identification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHActualTaylorIdentification.exists_actual_hs_root_germ_taylor_identification
/-- info: 'FMSA.Convergence.PureFluidHActualTaylorIdentification.exists_actual_hs_root_germ_with_convergent_H_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHActualTaylorIdentification.exists_actual_hs_root_germ_with_convergent_H_path
