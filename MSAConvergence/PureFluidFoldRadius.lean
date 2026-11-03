import MSAConvergence.PureFluidFoldCore
import MSAConvergence.PureFluidThetaPringsheimRoute

set_option linter.style.header false

/-! Radius of a power series in the form used by `EventuallySignedTaylor`, with the links to `Abs`,
`ev` and analyticity. -/

noncomputable section
open Filter Topology FormalMultilinearSeries
open scoped ENNReal NNReal
namespace FMSA.Convergence.PureFluidFoldRadius
open FMSA.Convergence.PureFluidSeriesEval FMSA.Convergence.AnalyticScalarTaylorPowerSeries

/-- The radius of convergence. -/
def rad (S : PowerSeries ℝ) : ℝ≥0∞ := (ofScalars ℝ fun n => PowerSeries.coeff n S).radius

theorem ofScalars_apply_real (S : PowerSeries ℝ) (x : ℝ) (n : ℕ) :
    (ofScalars ℝ (fun n => PowerSeries.coeff n S)) n (fun _ => x) = PowerSeries.coeff n S * x ^ n := by
  rw [ofScalars_apply_eq, smul_eq_mul]

theorem abs_of_lt_rad {S : PowerSeries ℝ} {τ : ℝ} (h : (‖τ‖₊ : ℝ≥0∞) < rad S) : Abs τ S := by
  have := (ofScalars ℝ fun n => PowerSeries.coeff n S).summable_norm_apply
    (x := τ) (by unfold rad at h; simpa [Metric.eball, edist_zero_right, enorm_eq_nnnorm] using h)
  simpa only [Abs, ofScalars_apply_real] using this

theorem ev_eq_sum (S : PowerSeries ℝ) (x : ℝ) :
    (ofScalars ℝ fun n => PowerSeries.coeff n S).sum x = ev x S := by
  simp only [FormalMultilinearSeries.sum, ev, ofScalars_apply_real]

theorem ev_analyticAt {S : PowerSeries ℝ} {τ : ℝ} (h : (‖τ‖₊ : ℝ≥0∞) < rad S) :
    AnalyticAt ℝ (fun x => ev x S) τ := by
  set p := ofScalars ℝ fun n => PowerSeries.coeff n S with hp
  have h' : (‖τ‖₊ : ℝ≥0∞) < p.radius := h
  have hpos : 0 < p.radius := lt_of_le_of_lt bot_le h'
  have hball := p.hasFPowerSeriesOnBall hpos
  have hmem : τ ∈ Metric.eball (0 : ℝ) p.radius := by
    simpa [Metric.eball, edist_zero_right, enorm_eq_nnnorm] using h'
  have ha := hball.analyticAt_of_mem hmem
  have hf : p.sum = fun x => ev x S := funext (ev_eq_sum S)
  rwa [hf] at ha

theorem HasTaylorPowerSeriesAt.ev_eventuallyEq {f : ℝ → ℝ} {S : PowerSeries ℝ}
    (hf : HasTaylorPowerSeriesAt f S) : ∀ᶠ τ in 𝓝 (0 : ℝ), ev τ S = f τ := by
  filter_upwards [hf.eventually_hasSum] with τ hτ using hτ.tsum_eq

/-- A series with a Taylor germ has positive radius. -/
theorem rad_pos_of_taylor {f : ℝ → ℝ} {S : PowerSeries ℝ} (hf : HasTaylorPowerSeriesAt f S) :
    0 < rad S := by
  obtain ⟨p, hp, hpS⟩ := hf
  obtain ⟨r, hr⟩ := hp
  have hq : (ofScalars ℝ fun n => PowerSeries.coeff n S).radius = p.radius := by
    have : p = ofScalars ℝ fun n => PowerSeries.coeff n S := by
      ext n
      rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff, hpS n]
      simp [ofScalars, smul_eq_mul, mul_comm]
    rw [← this]
  unfold rad
  rw [hq]
  exact hr.radius_pos


end FMSA.Convergence.PureFluidFoldRadius

/-- info: 'FMSA.Convergence.PureFluidFoldRadius.ofScalars_apply_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldRadius.ofScalars_apply_real
/-- info: 'FMSA.Convergence.PureFluidFoldRadius.abs_of_lt_rad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldRadius.abs_of_lt_rad
/-- info: 'FMSA.Convergence.PureFluidFoldRadius.ev_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldRadius.ev_eq_sum
/-- info: 'FMSA.Convergence.PureFluidFoldRadius.ev_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldRadius.ev_analyticAt
/-- info: 'FMSA.Convergence.PureFluidFoldRadius.HasTaylorPowerSeriesAt.ev_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldRadius.HasTaylorPowerSeriesAt.ev_eventuallyEq
/-- info: 'FMSA.Convergence.PureFluidFoldRadius.rad_pos_of_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldRadius.rad_pos_of_taylor
