import MSAConvergence.ActualCanonicalBranch

/-! A regular continuous root lift along a seed-linked complex path excludes
single-valued root germs when a closed subpath changes the lifted value.
The seed may lie before the closed subpath. The genuine Banach-valued Taylor
radius is bounded by any disc containing the path; ordinary vector convergence
outside that radius is excluded. This is a GENERIC analytic implication.
No numerical path, actual complex BH dictionary or M3 instance is supplied. -/

noncomputable section
open Filter Topology Set
open scoped ContDiff
namespace FMSA.Convergence.ComplexPathMonodromy
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {S : Type*} [TopologicalSpace S] [PreconnectedSpace S]

/-- Two continuous lifts through the same regular residual roots coincide
on a connected parameter space once they agree at one point. The parameter
path need only be continuous, including at polygon corners. -/
theorem regular_lifts_eq
    (R : ℂ × E → E) (gamma : S → ℂ) (p q : S → E) (t0 : S)
    (hg : Continuous gamma) (hp : Continuous p) (hq : Continuous q)
    (hpr : ∀ t, R (gamma t,p t) = 0) (hqr : ∀ t, R (gamma t,q t) = 0)
    (hc : ∀ t, ContDiffAt ℂ ∞ R (gamma t,p t))
    (hi : ∀ t, ((fderiv ℂ R (gamma t,p t)).comp
      (ContinuousLinearMap.inr ℂ ℂ E)).IsInvertible)
    (h0 : p t0 = q t0) : p = q := by
  let A : Set S := {t | p t = q t}
  have hclosed : IsClosed A := isClosed_eq hp hq
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hP : Tendsto (fun s => (gamma s,p s)) (𝓝 t) (𝓝 (gamma t,p t)) :=
      (hg.continuousAt.prodMk hp.continuousAt).tendsto
    have hQ : Tendsto (fun s => (gamma s,q s)) (𝓝 t) (𝓝 (gamma t,p t)) := by
      simpa only [show p t = q t from ht] using
        (hg.continuousAt.prodMk hq.continuousAt).tendsto
    have hu := (hc t).eventually_apply_eq_iff_implicitFunction (by simp) (hi t)
    filter_upwards [hP.eventually hu,hQ.eventually hu] with s hps hqs
    exact (hps.mp ((hpr s).trans (hpr t).symm)).symm.trans
      (hqs.mp ((hqr s).trans (hpr t).symm))
  have hall : A = univ := (show IsClopen A from ⟨hclosed,hopen⟩).eq_univ ⟨t0,h0⟩
  funext t
  exact show t ∈ A from hall.symm ▸ mem_univ t

/-- A regular lift which changes value when the base path returns excludes
a single-valued continuous root matching the seed anywhere over that path. -/
theorem changed_lift_excludes_continuous_root
    (R : ℂ × E → E) (gamma : S → ℂ) (p : S → E) (seed t0 t1 : S)
    (hg : Continuous gamma) (hp : Continuous p)
    (hpr : ∀ t, R (gamma t,p t) = 0)
    (hc : ∀ t, ContDiffAt ℂ ∞ R (gamma t,p t))
    (hi : ∀ t, ((fderiv ℂ R (gamma t,p t)).comp
      (ContinuousLinearMap.inr ℂ ℂ E)).IsInvertible)
    (hloop : gamma t0 = gamma t1) (hchange : p t0 ≠ p t1)
    (U : Set ℂ) (hU : ∀ t, gamma t ∈ U) :
    ¬ ∃ f : ℂ → E, ContinuousOn f U ∧
      (∀ z ∈ U, R (z,f z) = 0) ∧ f (gamma seed) = p seed := by
  rintro ⟨f,hf,hr,hseed⟩
  have heq := regular_lifts_eq R gamma p (f ∘ gamma) seed hg hp
    (hf.comp_continuous hg hU) hpr (fun t => hr _ (hU t)) hc hi hseed.symm
  apply hchange
  exact (congrFun heq t0).trans ((congrArg f hloop).trans (congrFun heq t1).symm)

/-- Even a candidate that solves the residual only as a germ at the seed
is impossible: analyticity propagates the residual identity on U, and
regular lift uniqueness then contradicts the changed loop value. -/
theorem changed_lift_excludes_analytic_germ
    (R : ℂ × E → E) (gamma : S → ℂ) (p : S → E) (seed t0 t1 : S)
    (hg : Continuous gamma) (hp : Continuous p)
    (hpr : ∀ t, R (gamma t,p t) = 0)
    (hc : ∀ t, ContDiffAt ℂ ∞ R (gamma t,p t))
    (hi : ∀ t, ((fderiv ℂ R (gamma t,p t)).comp
      (ContinuousLinearMap.inr ℂ ℂ E)).IsInvertible)
    (hloop : gamma t0 = gamma t1) (hchange : p t0 ≠ p t1)
    (U : Set ℂ) (hU : ∀ t, gamma t ∈ U) (hconn : IsPreconnected U)
    (hR : AnalyticOnNhd ℂ R (U ×ˢ (univ : Set E))) (f : ℂ → E) :
    ¬ (AnalyticOnNhd ℂ f U ∧
      (∀ᶠ z in 𝓝 (gamma seed), R (z,f z) = 0) ∧ f (gamma seed) = p seed) := by
  rintro ⟨hf,hr,hseed⟩
  apply changed_lift_excludes_continuous_root R gamma p seed t0 t1 hg hp hpr
    hc hi hloop hchange U hU
  refine ⟨f,hf.continuousOn,?_,hseed⟩
  have ha : AnalyticOnNhd ℂ (fun z => R (z,f z)) U := by
    intro z hz
    exact (hR (z,f z) ⟨hz,mem_univ _⟩).comp (f := fun w => (w,f w)) (x := z) ((analyticAt_id).prod (hf z hz))
  exact ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn (hU seed) hr

/-- A genuine series germ cannot have a radius larger than a disc containing
a seed-linked regular lift with a changed loop value. The path need not be
holomorphic or differentiable at its corners. -/
theorem radius_le_of_changed_lift
    (R : ℂ × E → E) (gamma : S → ℂ) (p : S → E) (seed t0 t1 : S)
    (hg : Continuous gamma) (hp : Continuous p)
    (hpr : ∀ t, R (gamma t,p t) = 0)
    (hc : ∀ t, ContDiffAt ℂ ∞ R (gamma t,p t))
    (hi : ∀ t, ((fderiv ℂ R (gamma t,p t)).comp
      (ContinuousLinearMap.inr ℂ ℂ E)).IsInvertible)
    (hloop : gamma t0 = gamma t1) (hchange : p t0 ≠ p t1)
    (r : ℝ) (hr : 0 < r) (hpath : ∀ t, ‖gamma t‖ < r)
    (hR : AnalyticOnNhd ℂ R ((Metric.ball 0 r) ×ˢ (univ : Set E)))
    (a : FormalMultilinearSeries ℂ ℂ E) (g : ℂ → E)
    (ha : HasFPowerSeriesAt g a 0)
    (hroot : ∀ᶠ z in 𝓝 0, R (z,g z) = 0)
    (hstart : gamma seed = 0) (hseed : p seed = g 0) :
    a.radius ≤ ENNReal.ofReal r := by
  by_contra hle
  have hrad : ENNReal.ofReal r < a.radius := lt_of_not_ge hle
  have hsum : g =ᶠ[𝓝 (0 : ℂ)] a.sum := by
    filter_upwards [ha.eventually_hasSum] with z hz
    simpa only [zero_add,FormalMultilinearSeries.sum] using hz.tsum_eq.symm
  have hsum0 : a.sum 0 = p seed := by
    rw [hseed]
    exact (hsum.self_of_nhds).symm
  have hasum : AnalyticOnNhd ℂ a.sum (Metric.ball 0 r) := by
    intro z hz
    apply a.analyticOnNhd z
    rw [mem_eball_zero_iff, ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by simpa using hz) |>.trans hrad
  have hsumroot : ∀ᶠ z in 𝓝 (gamma seed), R (z,a.sum z) = 0 := by
    rw [hstart]
    filter_upwards [hsum,hroot] with z hz hrz
    rwa [← hz]
  apply changed_lift_excludes_analytic_germ R gamma p seed t0 t1 hg hp hpr hc hi
    hloop hchange (Metric.ball 0 r) (fun t => by simpa using hpath t)
    (convex_ball (0 : ℂ) r).isPreconnected hR a.sum
  exact ⟨hasum,hsumroot,by simpa only [hstart] using hsum0⟩

omit [CompleteSpace E] in
/-- Ordinary vector series convergence at z would give radius at least |z|.
This excludes conditional as well as absolute convergence outside the radius. -/
theorem not_summable_of_radius_lt_norm
    (a : FormalMultilinearSeries ℂ ℂ E) (z : ℂ)
    (hz : a.radius < (‖z‖₊ : ENNReal)) :
    ¬ Summable (fun n => z ^ n • a.coeff n) := by
  intro hs
  have hle : (‖z‖₊ : ENNReal) ≤ a.radius := by
    apply a.le_radius_of_tendsto (l := 0)
    have ht : Tendsto (fun n => ‖z ^ n • a.coeff n‖) atTop (𝓝 (0 : ℝ)) := by
      convert tendsto_norm.comp hs.tendsto_atTop_zero using 1 <;> simp [Function.comp_def]
    simpa only [norm_smul,norm_pow,FormalMultilinearSeries.norm_apply_eq_norm_coef,
      coe_nnnorm,mul_comm] using ht
  exact not_le_of_gt hz hle

/-- info: 'FMSA.Convergence.ComplexPathMonodromy.regular_lifts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexPathMonodromy.regular_lifts_eq
/-- info: 'FMSA.Convergence.ComplexPathMonodromy.changed_lift_excludes_continuous_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexPathMonodromy.changed_lift_excludes_continuous_root
/-- info: 'FMSA.Convergence.ComplexPathMonodromy.changed_lift_excludes_analytic_germ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexPathMonodromy.changed_lift_excludes_analytic_germ
/-- info: 'FMSA.Convergence.ComplexPathMonodromy.radius_le_of_changed_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexPathMonodromy.radius_le_of_changed_lift
/-- info: 'FMSA.Convergence.ComplexPathMonodromy.not_summable_of_radius_lt_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ComplexPathMonodromy.not_summable_of_radius_lt_norm
end FMSA.Convergence.ComplexPathMonodromy
