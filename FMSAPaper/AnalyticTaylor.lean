import FMSAPaper.TaylorRoot
import FMSAPaper.SignedPringsheim

/-! Canonical Taylor coefficients of an analytic scalar branch have a positive
radius. Analytic uniqueness identifies their sum along a regular interval;
Pringsheim then supplies the radius lower bound under an all-order sign condition. -/
noncomputable section
open Filter Topology

namespace FMSA.Paper.AnalyticTaylor
open ExactMSA.BSource FormalMultilinearSeries

theorem hasFPowerSeriesAt_jet (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    HasFPowerSeriesAt f (ofScalars ℝ (jet f)) 0 := by
  exact hf.hasFPowerSeriesAt

theorem jet_radius_pos (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    0 < (ofScalars ℝ (jet f)).radius :=
  (hasFPowerSeriesAt_jet f hf).radius_pos

theorem eventually_eq_jet_sum (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    f =ᶠ[𝓝 (0 : ℝ)] (ofScalars ℝ (jet f)).sum := by
  filter_upwards [(hasFPowerSeriesAt_jet f hf).eventually_hasSum] with t ht
  simpa only [zero_add, FormalMultilinearSeries.sum] using ht.tsum_eq.symm

theorem eq_jet_sum_on_interval (f : ℝ → ℝ) (b : ℝ)
    (hf : AnalyticOnNhd ℝ f (Set.Ico 0 b))
    (t : ℝ) (ht : t ∈ Set.Ico 0 b)
    (hr : ENNReal.ofReal t < (ofScalars ℝ (jet f)).radius) :
    f t = (ofScalars ℝ (jet f)).sum t := by
  have hf0 := hf 0 (show (0 : ℝ) ∈ Set.Ico 0 b from ⟨le_rfl, ht.1.trans_lt ht.2⟩)
  have hfa : AnalyticOnNhd ℝ f (Set.Icc 0 t) :=
    hf.mono (fun _ hx => ⟨hx.1, hx.2.trans_lt ht.2⟩)
  have hsa : AnalyticOnNhd ℝ (ofScalars ℝ (jet f)).sum (Set.Icc 0 t) := by
    intro x hx
    apply (ofScalars ℝ (jet f)).analyticOnNhd x
    rw [mem_eball_zero_iff, ← ofReal_norm,
      Real.norm_of_nonneg hx.1]
    exact (ENNReal.ofReal_le_ofReal hx.2).trans_lt hr
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hsa
    (convex_Icc (0 : ℝ) t).isPreconnected ⟨le_rfl, ht.1⟩
    (eventually_eq_jet_sum f hf0) ⟨ht.1, le_rfl⟩

theorem le_jet_radius_of_signed_analytic_branch (f : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hf : AnalyticOnNhd ℝ f (Set.Ico 0 b))
    (s : ℝ) (hs : s ≠ 0) (ha : ∀ n, 0 < n → 0 <= s * jet f n) :
    ENNReal.ofReal b <= (ofScalars ℝ (jet f)).radius := by
  apply SignedPringsheim.le_radius_of_analytic_continuation (jet f) s hs ha
    (jet_radius_pos f (hf 0 ⟨le_rfl, hb⟩)) b hb f
    (hf.mono (fun _ hx => ⟨hx.1.le, hx.2⟩))
  intro t ht hr
  exact eq_jet_sum_on_interval f b hf t ⟨ht.1.le, ht.2⟩ hr

theorem hasSum_jet_on_interval (f : ℝ → ℝ) (b : ℝ)
    (hf : AnalyticOnNhd ℝ f (Set.Ico 0 b))
    (t : ℝ) (ht : t ∈ Set.Ico 0 b)
    (hr : ENNReal.ofReal t < (ofScalars ℝ (jet f)).radius) :
    HasSum (fun n => jet f n * t ^ n) (f t) := by
  rw [eq_jet_sum_on_interval f b hf t ht hr]
  have hm : t ∈ Metric.eball (0 : ℝ) (ofScalars ℝ (jet f)).radius := by
    simpa only [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero,
      abs_of_nonneg ht.1] using hr
  simpa only [ofScalars_apply_eq, smul_eq_mul, FormalMultilinearSeries.sum] using
    ((ofScalars ℝ (jet f)).summable hm).hasSum

end FMSA.Paper.AnalyticTaylor

/-- info: 'FMSA.Paper.AnalyticTaylor.hasFPowerSeriesAt_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AnalyticTaylor.hasFPowerSeriesAt_jet

/-- info: 'FMSA.Paper.AnalyticTaylor.jet_radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AnalyticTaylor.jet_radius_pos

/-- info: 'FMSA.Paper.AnalyticTaylor.eventually_eq_jet_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AnalyticTaylor.eventually_eq_jet_sum

/-- info: 'FMSA.Paper.AnalyticTaylor.eq_jet_sum_on_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AnalyticTaylor.eq_jet_sum_on_interval

/-- info: 'FMSA.Paper.AnalyticTaylor.le_jet_radius_of_signed_analytic_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AnalyticTaylor.le_jet_radius_of_signed_analytic_branch

/-- info: 'FMSA.Paper.AnalyticTaylor.hasSum_jet_on_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AnalyticTaylor.hasSum_jet_on_interval
