import MSAConvergence.PureFluidFoldPath

set_option linter.style.header false

/-! The endpoint of the rebuilt path: its limit is a root, no analytic amplitude continuation exists
across it, and therefore the original Jacobian is singular there. -/

noncomputable section
open Filter Topology Set
open scoped ENNReal NNReal ContDiff
namespace FMSA.Convergence.PureFluidFoldEnd
open FMSA.Convergence.PureFluidFoldPath
open FMSA.Convergence.PureFluidFoldCore FMSA.Convergence.PureFluidSeriesEval
open FMSA.Convergence.PureFluidFoldRadius
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidActualThetaEquation FMSA.Convergence.PureFluidActualAnalyticGerm
open FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidThetaPringsheimRoute
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidThetaCouplingTaylor
open FMSA.ExactMSA

variable {T : Type*} [Fintype T] [DecidableEq T]

theorem abs_of_summable {S : PowerSeries ℝ} {R : ℝ}
    (h : Summable fun n => PowerSeries.coeff n S * R ^ n) : Abs R S :=
  h.norm

/-- A series is the Taylor series of its own sum. -/
theorem hasTaylor_ev {S : PowerSeries ℝ} (h : 0 < rad S) :
    HasTaylorPowerSeriesAt (fun x => ev x S) S := by
  refine ⟨FormalMultilinearSeries.ofScalars ℝ fun n => PowerSeries.coeff n S, ?_, fun n => ?_⟩
  · have hf : (FormalMultilinearSeries.ofScalars ℝ fun n => PowerSeries.coeff n S).sum =
        fun x => ev x S := funext (ev_eq_sum S)
    rw [← hf]
    exact (FormalMultilinearSeries.hasFPowerSeriesOnBall _ h).hasFPowerSeriesAt
  · rw [FormalMultilinearSeries.coeff_ofScalars]

/-- A nonnegative series whose sum continues analytically across `R` has radius beyond `R`. -/
theorem ofReal_lt_rad {S : PowerSeries ℝ} (hS : CN S) {R : ℝ} (hR : 0 < R)
    (hrad : ENNReal.ofReal R ≤ rad S) {ψ : ℝ → ℝ} (hψ : AnalyticAt ℝ ψ R)
    (hleft : ψ =ᶠ[𝓝[<] R] fun x => ev x S) : ENNReal.ofReal R < rad S := by
  have hpos : 0 < rad S := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hR) hrad
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hψ.eventually_analyticAt
  let g : ℝ → ℝ := fun y => if y < R then ev y S else ψ y
  have hltR : ∀ y, y < R → g =ᶠ[𝓝 y] fun x => ev x S := fun y hy => by
    filter_upwards [Iio_mem_nhds hy] with x hx
    exact if_pos hx
  have hgan : ∀ y ∈ Ico 0 (R + ε), AnalyticAt ℝ g y := by
    intro y hy
    rcases lt_trichotomy y R with h | h | h
    · have hn : (‖y‖₊ : ℝ≥0∞) < rad S :=
        (nnnorm_lt_ofReal hR ⟨hy.1, h⟩).trans_le hrad
      exact (ev_analyticAt hn).congr (hltR y h).symm
    · subst h
      refine hψ.congr ?_
      filter_upwards [eventually_nhdsWithin_iff.mp hleft] with x hx
      by_cases hxy : x < y
      · have : g x = ev x S := if_pos hxy
        rw [this]; exact hx hxy
      · exact (if_neg hxy).symm
    · refine (hball ?_).congr ?_
      · rw [Real.dist_eq, abs_of_pos (sub_pos.mpr h)]; linarith [hy.2]
      · filter_upwards [Ioi_mem_nhds h] with x hx
        exact (if_neg (not_lt.mpr (le_of_lt hx))).symm
  obtain ⟨p, hp, hc⟩ := hasTaylor_ev hpos
  have hTg : HasTaylorPowerSeriesAt g S := ⟨p, hp.congr (hltR 0 hR).symm, hc⟩
  have hb := taylor_radius_lower_bound_of_nonnegative_analytic_branch g S hTg (fun n => hS n)
    (R + ε) (by positivity) hgan
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)) hb

section GermSection

variable {xi : ℝ} {z K : T → ℝ} {p : ℝ → (T → ℝ) × (T → ℝ)} {θS HS RS : T → PowerSeries ℝ}
  (G : PureFluidFoldPath.Germ xi z K p θS HS RS) {R : ℝ} (hR : 0 < R) (hrad : Reaches θS HS RS R)
include G hR hrad

theorem Germ.abs_end (t : T) : Abs R (θS t) ∧ Abs R (HS t) ∧ Abs R (RS t) := by
  obtain ⟨h1, h2, h3⟩ := G.F.endpoint_summable (PureFluidFoldPath.Germ.allAbs hR hrad) hR t
  exact ⟨abs_of_summable h1, abs_of_summable h2, abs_of_summable h3⟩

theorem Germ.fac_cont (t : T) : ContinuousOn (fun x => fac xi z RS x t) (Icc 0 R) :=
  continuousOn_const.sub (continuousOn_const.mul
    (ev_continuousOn_Icc hR.le (abs_end G hR hrad t).2.2))

/-- The factor stays strictly positive at the endpoint. -/
theorem Germ.fac_end_pos (t : T) : 0 < fac xi z RS R t := by
  have ht := abs_end G hR hrad t
  have hc := fac_cont G hR hrad t
  have hend : ∀ x ∈ Ico 0 R, 0 < fac xi z RS x t := fun x hx => G.fac_pos hR hrad hx t
  have hne : (𝓝[Ico 0 R] R).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_Ico hR.ne]; exact ⟨hR.le, le_rfl⟩)
  have hw := (hc R ⟨hR.le, le_rfl⟩).mono (fun x hx => ⟨hx.1, hx.2.le⟩ : Ico 0 R ⊆ Icc 0 R)
  have hge : 0 ≤ fac xi z RS R t :=
    ge_of_tendsto hw.tendsto (eventually_nhdsWithin_of_forall fun x hx => (hend x hx).le)
  refine lt_of_le_of_ne hge fun h0 => ?_
  have hal := endpoint_eq hR
    (f := fun x => physicalAlpha xi z K t * x)
    (g := fun x => ev x (θS t) * (fac xi z RS x t) ^ 2)
    (continuousOn_const.mul continuousOn_id)
    ((ev_continuousOn_Icc hR.le ht.1).mul (hc.pow 2))
    (fun x hx => G.F.ev_alpha (PureFluidFoldPath.Germ.allAbs hR hrad) hx t)
  simp only [← h0] at hal
  have := mul_pos (G.F.hα t) hR
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hal
  linarith

theorem Germ.fac_pos_Icc {τ : ℝ} (hτ : τ ∈ Icc 0 R) (t : T) : 0 < fac xi z RS τ t := by
  rcases hτ.2.lt_or_eq with h | h
  · exact G.fac_pos hR hrad ⟨hτ.1, h⟩ t
  · rw [h]; exact fac_end_pos G hR hrad t

theorem Germ.path_cont : ContinuousOn (path xi z θS HS RS) (Icc 0 R) := by
  have hθ t := ev_continuousOn_Icc hR.le (abs_end G hR hrad t).1
  have hH t := ev_continuousOn_Icc hR.le (abs_end G hR hrad t).2.1
  have hr t := ev_continuousOn_Icc hR.le (abs_end G hR hrad t).2.2
  refine ContinuousOn.prodMk (continuousOn_pi.mpr fun t => ?_) (continuousOn_pi.mpr fun t => ?_)
  · exact ((continuousOn_const.mul ((hθ t).mul (hH t))).mul (fac_cont G hR hrad t)).div_const _
  · exact continuousOn_const.add
      (((hr t).div (fac_cont G hR hrad t)
        fun x hx => (fac_pos_Icc G hR hrad hx t).ne').div_const _)

theorem Germ.path_tendsto :
    Tendsto (path xi z θS HS RS) (𝓝[<] R) (𝓝 (path xi z θS HS RS R)) := by
  have h := ((path_cont G hR hrad) R ⟨hR.le, le_rfl⟩).mono
    (fun x hx => ⟨hx.1, hx.2.le⟩ : Ico 0 R ⊆ Icc 0 R)
  exact h.tendsto.mono_left (nhdsWithin_le_of_mem (Ico_mem_nhdsLT hR))

/-- The endpoint value is still an MSA root. -/
theorem Germ.root_end :
    MultiTail.IsRoot xi z (fun t => R * K t) (path xi z θS HS RS R).1 (path xi z θS HS RS R).2 := by
  have hc : ContinuousOn (fun x => MultiTail.residual xi z K (x, path xi z θS HS RS x)) (Icc 0 R) :=
    fun x hx => ContinuousAt.comp_continuousWithinAt (g := MultiTail.residual xi z K)
      (f := fun x => (x, path xi z θS HS RS x))
      (residual_analyticAt xi z K (x, path xi z θS HS RS x)).continuousAt
      (continuousWithinAt_id.prodMk (path_cont G hR hrad x hx))
  have h0 := endpoint_eq hR hc (continuousOn_const (c := (0 : Pairs T)))
    (fun x hx => (residual_zero_iff xi z K _ _ x).mpr (G.root_on hR hrad hx))
  exact (residual_zero_iff xi z K _ _ R).mp h0

/-- The node `U` does not vanish at the endpoint value. -/
theorem Germ.nodeU_end (t : T) :
    actualU xi z (path xi z θS HS RS R).1 (path xi z θS HS RS R).2 (z t) ≠ 0 := by
  have hx : ContinuousOn (fun x => actualU xi z (path xi z θS HS RS x).1
      (path xi z θS HS RS x).2 (z t) * ev x (HS t)) (Icc 0 R) := by
    refine ContinuousOn.mul (fun x hx => ?_)
      (ev_continuousOn_Icc hR.le (abs_end G hR hrad t).2.1)
    exact ContinuousAt.comp_continuousWithinAt
      (g := fun y : Pairs T => actualU xi z y.1 y.2 (z t))
      (nodeU_an xi G.hxi1.ne z G.F.hz t _).continuousAt (path_cont G hR hrad x hx)
  have h := endpoint_eq hR hx (continuousOn_const (c := (1 : ℝ)))
    (fun x hx => G.id_U hR hrad t hx)
  exact left_ne_zero_of_mul_eq_one h

/-- No analytic amplitude germ at `R` continues the path, as soon as one node radius stops at `R`. -/
theorem Germ.no_extension
    (hmax : ∃ t, rad (θS t) ≤ ENNReal.ofReal R ∨ rad (HS t) ≤ ENNReal.ofReal R ∨
      rad (RS t) ≤ ENNReal.ofReal R)
    {q : ℝ → Pairs T} (hq : AnalyticAt ℝ q R) (hleft : q =ᶠ[𝓝[<] R] path xi z θS HS RS) : False := by
  have hq0 : q R = path xi z θS HS RS R :=
    tendsto_nhds_unique
      ((hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hleft)
      (path_tendsto G hR hrad)
  have hU t : AnalyticAt ℝ (fun y => actualU xi z (q y).1 (q y).2 (z t)) R :=
    (nodeU_an xi G.hxi1.ne z G.F.hz t _).comp hq
  have hUne t : actualU xi z (q R).1 (q R).2 (z t) ≠ 0 := by
    rw [hq0]; exact nodeU_end G hR hrad t
  have hnear : ∀ᶠ x in 𝓝[<] R, q x = path xi z θS HS RS x ∧ x ∈ Ico 0 R := by
    filter_upwards [hleft, Ico_mem_nhdsLT hR] with x h1 h2 using ⟨h1, h2⟩
  obtain ⟨t, ht⟩ := hmax
  have hθ : ENNReal.ofReal R < rad (θS t) := by
    refine ofReal_lt_rad (G.F.θ_cn t) hR (hrad t).1
      (ψ := fun y => actualTheta xi z (q y).1 (q y).2 t) ?_ ?_
    · unfold actualTheta
      exact ((weight_an xi z t _).comp hq).mul (hU t)
    · filter_upwards [hnear] with x hx
      rw [hx.1]; exact (G.node_on hR hrad t hx.2).2.1
  have hH : ENNReal.ofReal R < rad (HS t) := by
    refine ofReal_lt_rad (G.F.H_cn t) hR (hrad t).2.1
      (ψ := fun y => actualH xi z (q y).1 (q y).2 (z t)) ?_ ?_
    · unfold actualH
      exact (hU t).inv (hUne t)
    · filter_upwards [hnear] with x hx
      rw [hx.1]; exact (G.node_on hR hrad t hx.2).2.2.1
  have hr : ENNReal.ofReal R < rad (RS t) := by
    refine ofReal_lt_rad (G.F.r_cn t) hR (hrad t).2.2
      (ψ := fun y => actualNodeR xi z (q y).1 (q y).2 t) ?_ ?_
    · unfold actualNodeR
      exact ((nodeG_an xi z t _).comp hq).div (hU t) (hUne t)
    · filter_upwards [hnear] with x hx
      rw [hx.1]; exact (G.node_on hR hrad t hx.2).2.2.2
  rcases ht with h | h | h
  · exact absurd h (not_le.mpr hθ)
  · exact absurd h (not_le.mpr hH)
  · exact absurd h (not_le.mpr hr)

/-- At the endpoint the amplitude Jacobian of the original equations is singular. -/
theorem Germ.jacobian_singular
    (hmax : ∃ t, rad (θS t) ≤ ENNReal.ofReal R ∨ rad (HS t) ≤ ENNReal.ofReal R ∨
      rad (RS t) ≤ ENNReal.ofReal R) :
    ¬ ((fderiv ℝ (MultiTail.residual xi z K) (R, path xi z θS HS RS R)).comp
      (ContinuousLinearMap.inr ℝ ℝ (Pairs T))).IsInvertible := by
  intro hi
  set a := path xi z θS HS RS R with ha
  have hc : ContDiffAt ℝ ω (MultiTail.residual xi z K) (R, a) :=
    (residual_analyticAt xi z K (R, a)).contDiffAt
  let q := hc.implicitFunction (by simp) hi
  have hqa : AnalyticAt ℝ q R := (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  have hR0 : MultiTail.residual xi z K (R, a) = 0 :=
    (residual_zero_iff xi z K _ _ R).mpr (root_end G hR hrad)
  have hmeet : q =ᶠ[𝓝[<] R] path xi z θS HS RS := by
    have hlocal := ((tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun x : ℝ => x) (𝓝[<] R) (𝓝 R)).prodMk_nhds (path_tendsto G hR hrad)).eventually
      (hc.eventually_apply_eq_iff_implicitFunction (by simp) hi)
    filter_upwards [hlocal, Ico_mem_nhdsLT hR] with x hn hx
    exact (hn.mp (((residual_zero_iff xi z K _ _ x).mpr (G.root_on hR hrad hx)).trans hR0.symm))
  exact no_extension G hR hrad hmax hqa hmeet

end GermSection


end FMSA.Convergence.PureFluidFoldEnd

/-- info: 'FMSA.Convergence.PureFluidFoldEnd.abs_of_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.abs_of_summable
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.hasTaylor_ev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.hasTaylor_ev
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.ofReal_lt_rad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.ofReal_lt_rad
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.Germ.abs_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.Germ.abs_end
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.Germ.fac_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.Germ.fac_cont
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.Germ.fac_end_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.Germ.fac_end_pos
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.Germ.fac_pos_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.Germ.fac_pos_Icc
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.Germ.path_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.Germ.path_cont
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.Germ.path_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.Germ.path_tendsto
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.Germ.root_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.Germ.root_end
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.Germ.nodeU_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.Germ.nodeU_end
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.Germ.no_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.Germ.no_extension
/-- info: 'FMSA.Convergence.PureFluidFoldEnd.Germ.jacobian_singular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldEnd.Germ.jacobian_singular
