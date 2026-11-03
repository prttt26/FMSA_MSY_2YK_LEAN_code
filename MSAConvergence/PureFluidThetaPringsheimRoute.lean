import MSAConvergence.PureFluidThetaFixedPointUniqueness
import MSAConvergence.EventuallySignedTaylor

set_option linter.style.header false

/-! Positive Taylor coefficients and analytic continuation give a
Pringsheim lower bound for the genuine physical theta/r node paths. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace FMSA.Convergence.PureFluidThetaPringsheimRoute
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidPositiveSubstitution
open FMSA.Convergence.PureFluidHActualNodeBridge
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Paper.AnalyticTaylor
open FMSA.Paper.TaylorRoot
open FMSA.ExactMSA.BSource
open FormalMultilinearSeries

/-- The algebraic Taylor coefficients previously extracted from an
analytic germ are its canonical analytic jets. -/
theorem taylorPowerSeries_coeff_eq_jet
    (f : ℝ → ℝ) (S : PowerSeries ℝ)
    (hS : HasTaylorPowerSeriesAt f S) (n : ℕ) :
    PowerSeries.coeff n S = jet f n := by
  obtain ⟨p, hp, hcoeff⟩ := hS
  have hj := hasFPowerSeriesAt_jet f hp.analyticAt
  have heq := hp.eq_formalMultilinearSeries hj
  rw [← hcoeff n, heq]
  rw [FormalMultilinearSeries.coeff_ofScalars]

/-- Nonnegative coefficients plus analytic continuation along the
positive axis force the Taylor radius beyond every interior bound.
This is a conditional continuation statement, not an assertion that
the physical branch reaches a particular fold. -/
theorem taylor_radius_lower_bound_of_nonnegative_analytic_branch
    (f : ℝ → ℝ) (S : PowerSeries ℝ)
    (hS : HasTaylorPowerSeriesAt f S)
    (hpos : CoeffNonneg S)
    (b : ℝ) (hb : 0 < b)
    (hanalytic : AnalyticOnNhd ℝ f (Set.Ico 0 b)) :
    ENNReal.ofReal b ≤
      (ofScalars ℝ (fun n => PowerSeries.coeff n S)).radius := by
  have hfun : (fun n => PowerSeries.coeff n S) = jet f := by
    funext n
    exact taylorPowerSeries_coeff_eq_jet f S hS n
  rw [hfun]
  apply le_jet_radius_of_signed_analytic_branch f b hb hanalytic 1
    one_ne_zero
  intro n _
  simpa only [one_mul, ← taylorPowerSeries_coeff_eq_jet f S hS n]
    using hpos n

/-- Analyticity of the actual theta coordinate at an arbitrary point
of an analytic original-amplitude path. -/
theorem actualTheta_analyticAt_of_amplitude_analyticAt
    {T : Type*} [Fintype T]
    (xi : ℝ) (hxi : xi ≠ 1)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (p : ℝ → (T → ℝ) × (T → ℝ))
    (c : ℝ) (hp : AnalyticAt ℝ p c) (t : T) :
    AnalyticAt ℝ
      (fun tau => actualTheta xi z (p tau).1 (p tau).2 t) c := by
  let q : ℝ → (T → ℝ) × (T → ℝ) := fun x => p (x + c)
  have hq : AnalyticAt ℝ q 0 := by
    have hinner : AnalyticAt ℝ (fun x : ℝ => x + c) 0 := by
      fun_prop
    have hp' : AnalyticAt ℝ p (0 + c) := by simpa using hp
    have hcomp := AnalyticAt.comp (g := p)
      (f := fun x : ℝ => x + c) (x := 0) hp' hinner
    simpa only [q, Function.comp_def] using hcomp
  have htheta := actualTheta_analyticAt_germ xi hxi z hz q hq t
  have hback : AnalyticAt ℝ (fun x : ℝ => x - c) c := by
    fun_prop
  have htheta' : AnalyticAt ℝ
      (fun tau => actualTheta xi z (q tau).1 (q tau).2 t) (c - c) := by
    simpa using htheta
  have hcomp := AnalyticAt.comp
    (g := fun tau => actualTheta xi z (q tau).1 (q tau).2 t)
    (f := fun x : ℝ => x - c) (x := c) htheta' hback
  simpa only [q, Function.comp_def, sub_add_cancel] using hcomp

/-- A global analytic original-amplitude continuation to `b`
forces each nonnegative actual theta Taylor series to have radius at
least `b`. The branch continuation remains an explicit premise. -/
theorem actualTheta_radius_lower_bound_of_analytic_amplitude_branch
    {T : Type*} [Fintype T]
    (xi : ℝ) (hxi : xi ≠ 1)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (p : ℝ → (T → ℝ) × (T → ℝ))
    (thetaS : T → PowerSeries ℝ)
    (htheta : ∀ t, HasTaylorPowerSeriesAt
      (fun tau => actualTheta xi z (p tau).1 (p tau).2 t) (thetaS t))
    (hpos : ∀ t, CoeffNonneg (thetaS t))
    (b : ℝ) (hb : 0 < b)
    (hp : AnalyticOnNhd ℝ p (Set.Ico 0 b)) :
    ∀ t, ENNReal.ofReal b ≤
      (ofScalars ℝ (fun n => PowerSeries.coeff n (thetaS t))).radius := by
  intro t
  apply taylor_radius_lower_bound_of_nonnegative_analytic_branch
    _ (thetaS t) (htheta t) (hpos t) b hb
  intro c hc
  exact actualTheta_analyticAt_of_amplitude_analyticAt
    xi hxi z hz p c (hp c hc) t

end FMSA.Convergence.PureFluidThetaPringsheimRoute

/-- info: 'FMSA.Convergence.PureFluidThetaPringsheimRoute.taylorPowerSeries_coeff_eq_jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaPringsheimRoute.taylorPowerSeries_coeff_eq_jet

/-- info: 'FMSA.Convergence.PureFluidThetaPringsheimRoute.taylor_radius_lower_bound_of_nonnegative_analytic_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaPringsheimRoute.taylor_radius_lower_bound_of_nonnegative_analytic_branch

/-- info: 'FMSA.Convergence.PureFluidThetaPringsheimRoute.actualTheta_analyticAt_of_amplitude_analyticAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaPringsheimRoute.actualTheta_analyticAt_of_amplitude_analyticAt

/-- info: 'FMSA.Convergence.PureFluidThetaPringsheimRoute.actualTheta_radius_lower_bound_of_analytic_amplitude_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaPringsheimRoute.actualTheta_radius_lower_bound_of_analytic_amplitude_branch
