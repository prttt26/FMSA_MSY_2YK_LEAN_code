import MSAConvergence.M2Curvature

/-! Analytic scalar zero contours and strict local minima derived from
the genuine negative weight derivative and positive punctured axis. -/

noncomputable section
open Set Real Filter Topology
open scoped ContDiff
set_option maxHeartbeats 2000000
namespace FMSA.Convergence.ImplicitZeroContour

/-- A true nonzero weight derivative discharges scalar analytic IFT. -/
theorem exists_analytic_zero_contour (f : ℝ × ℝ → ℝ) (b w d : ℝ)
    (hf : AnalyticAt ℝ f (b,w)) (hzero : f (b,w) = 0)
    (hd : HasDerivAt (fun s => f (b,s)) d w) (hneg : d < 0) :
    ∃ ψ : ℝ → ℝ, ψ b = w ∧ AnalyticAt ℝ ψ b ∧
      (∀ᶠ t in 𝓝 b, f (t,ψ t) = 0) ∧
      (∀ᶠ u in 𝓝 (b,w), f u = 0 ↔ u.2 = ψ u.1) := by
  let L := (fderiv ℝ f (b,w)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)
  have hpair : HasDerivAt (fun s : ℝ => (b,s)) (0,1) w :=
    (hasDerivAt_const w b).prodMk (hasDerivAt_id w)
  have heval : L 1 = d :=
    (hf.differentiableAt.hasFDerivAt.comp_hasDerivAt w hpair).unique hd
  have hmul (v : ℝ) : L v = v*d := by
    calc
      L v = L (v • (1 : ℝ)) := by rw [smul_eq_mul,mul_one]
      _ = v • L 1 := L.map_smul v 1
      _ = v*d := by rw [heval]; rfl
  have hinj : Function.Injective L := by
    intro a c h
    rw [hmul,hmul] at h
    exact mul_right_cancel₀ (ne_of_lt hneg) h
  have hbij : Function.Bijective L.toLinearMap :=
    ⟨hinj,(LinearMap.injective_iff_surjective).mp hinj⟩
  let e := (LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv
  have hi : L.IsInvertible := ⟨e,rfl⟩
  have hc : ContDiffAt ℝ ω f (b,w) := hf.contDiffAt
  let ψ := hc.implicitFunction (by simp) hi
  have hp0 : ψ b = w := hc.implicitFunction_apply_self (by simp) hi
  have hpa : AnalyticAt ℝ ψ b := (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  refine ⟨ψ,hp0,hpa,?_,?_⟩
  · filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with t ht
    exact ht.trans hzero
  · filter_upwards [hc.eventually_apply_eq_iff_implicitFunction (by simp) hi] with u hu
    simpa only [hzero,eq_comm] using hu

/-- Continuity of the genuine derivative gives a strictly decreasing
weight family on one rectangle; no uniform derivative bound is assumed. -/
theorem negative_weight_derivative_rectangle (f : ℝ × ℝ → ℝ) (b w d : ℝ)
    (hf : AnalyticAt ℝ f (b,w))
    (hd : HasDerivAt (fun s => f (b,s)) d w) (hneg : d < 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t, |t-b| < r/2 →
      StrictAntiOn (fun s => f (t,s)) (Ioo (w-r/2) (w+r/2)) := by
  have hpair : HasDerivAt (fun s : ℝ => (b,s)) (0,1) w :=
    (hasDerivAt_const w b).prodMk (hasDerivAt_id w)
  have heval : fderiv ℝ f (b,w) (0,1) = d :=
    (hf.differentiableAt.hasFDerivAt.comp_hasDerivAt w hpair).unique hd
  have hc : ContinuousAt (fun u => fderiv ℝ f u (0,1)) (b,w) :=
    hf.fderiv.continuousAt.clm_apply continuousAt_const
  have hn : ∀ᶠ u in 𝓝 (b,w), fderiv ℝ f u (0,1) < 0 :=
    hc.eventually (Iio_mem_nhds (by
      change fderiv ℝ f (b,w) (0,1) < 0
      rw [heval]
      exact hneg))
  have hgood : ∀ᶠ u in 𝓝 (b,w),
      DifferentiableAt ℝ f u ∧ fderiv ℝ f u (0,1) < 0 := by
    filter_upwards [hf.eventually_analyticAt,hn] with u hu hv
    exact ⟨hu.differentiableAt,hv⟩
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hgood
  refine ⟨r,hr,?_⟩
  intro t ht
  have hpoint (s : ℝ) (hs : s ∈ Ioo (w-r/2) (w+r/2)) :
      DifferentiableAt ℝ f (t,s) ∧ fderiv ℝ f (t,s) (0,1) < 0 := by
    apply hball
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    apply max_lt
    · linarith
    · apply (abs_lt.mpr ?_).trans (by linarith : r/2 < r)
      constructor <;> linarith [hs.1,hs.2]
  have hder (s : ℝ) (hs : s ∈ Ioo (w-r/2) (w+r/2)) :
      HasDerivAt (fun v => f (t,v)) (fderiv ℝ f (t,s) (0,1)) s :=
    (hpoint s hs).1.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s t).prodMk (hasDerivAt_id s))
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) ?_ ?_
  · intro s hs
    exact (hder s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [(hder s (interior_subset hs)).deriv]
    exact (hpoint s (interior_subset hs)).2

/-- A positive punctured coupling axis and negative weight derivative
force a strict local minimum of any continuous local zero contour. -/
theorem strict_minimum_of_positive_axis (f : ℝ × ℝ → ℝ) (b w d : ℝ)
    (hf : AnalyticAt ℝ f (b,w))
    (hd : HasDerivAt (fun s => f (b,s)) d w) (hneg : d < 0)
    (ψ : ℝ → ℝ) (hp0 : ψ b = w) (hpc : ContinuousAt ψ b)
    (hroot : ∀ᶠ t in 𝓝 b, f (t,ψ t) = 0)
    (hpositive : ∀ᶠ t in 𝓝 b, t ≠ b → 0 < f (t,w)) :
    ∀ᶠ t in 𝓝 b, t ≠ b → w < ψ t := by
  obtain ⟨r,hr,hanti⟩ := negative_weight_derivative_rectangle f b w d hf hd hneg
  have htr : ∀ᶠ t in 𝓝 b, |t-b| < r/2 :=
    Metric.eventually_nhds_iff.mpr ⟨r/2,by linarith,by
      intro t ht
      simpa only [Real.dist_eq] using ht⟩
  have hwr : ∀ᶠ t in 𝓝 b, ψ t ∈ Ioo (w-r/2) (w+r/2) :=
    hpc.eventually (Ioo_mem_nhds (by rw [hp0]; linarith) (by rw [hp0]; linarith))
  have hw : w ∈ Ioo (w-r/2) (w+r/2) := ⟨by linarith,by linarith⟩
  filter_upwards [htr,hwr,hroot,hpositive] with t ht hp hz hpos hne
  by_contra hnot
  have hle : ψ t ≤ w := le_of_not_gt hnot
  have hvalue := (hanti t ht).antitoneOn hp hw hle
  rw [hz] at hvalue
  exact (not_le_of_gt (hpos hne)) hvalue

/-- On one actual neighbourhood the zero contour classifies both signs of
f by the order of the weight. This concerns this real observable only. -/
theorem local_sign_classification (f : ℝ × ℝ → ℝ) (b w d : ℝ)
    (hf : AnalyticAt ℝ f (b,w))
    (hd : HasDerivAt (fun s => f (b,s)) d w) (hneg : d < 0)
    (ψ : ℝ → ℝ) (hp0 : ψ b = w) (hpc : ContinuousAt ψ b)
    (hroot : ∀ᶠ t in 𝓝 b, f (t,ψ t) = 0) :
    ∀ᶠ u in 𝓝 (b,w),
      (0 < f u ↔ u.2 < ψ u.1) ∧
      (f u < 0 ↔ ψ u.1 < u.2) ∧ (f u = 0 ↔ u.2 = ψ u.1) := by
  obtain ⟨r,hr,hanti⟩ := negative_weight_derivative_rectangle f b w d hf hd hneg
  have hct : ContinuousAt (fun u : ℝ × ℝ => |u.1-b|) (b,w) := by fun_prop
  have htr : ∀ᶠ u in 𝓝 (b,w), |u.1-b| < r/2 :=
    hct.eventually (Iio_mem_nhds (by change |b-b| < r/2; rw [sub_self,abs_zero]; linarith))
  have hcs : ContinuousAt (fun u : ℝ × ℝ => u.2) (b,w) := continuousAt_snd
  have hsr : ∀ᶠ u in 𝓝 (b,w), u.2 ∈ Ioo (w-r/2) (w+r/2) :=
    hcs.eventually (Ioo_mem_nhds (by change w-r/2 < w; linarith) (by change w < w+r/2; linarith))
  have hcp : ContinuousAt (fun u : ℝ × ℝ => ψ u.1) (b,w) := hpc.comp continuousAt_fst
  have hpr : ∀ᶠ u in 𝓝 (b,w), ψ u.1 ∈ Ioo (w-r/2) (w+r/2) :=
    hcp.eventually (Ioo_mem_nhds (by change w-r/2 < ψ b; rw [hp0]; linarith)
      (by change ψ b < w+r/2; rw [hp0]; linarith))
  have hzr : ∀ᶠ u in 𝓝 (b,w), f (u.1,ψ u.1) = 0 := (continuousAt_fst : ContinuousAt (fun u : ℝ × ℝ => u.1) (b,w)).eventually hroot
  filter_upwards [htr,hsr,hpr,hzr] with u ht hs hp hz
  refine ⟨?_,?_,?_⟩
  · simpa only [hz] using (hanti u.1 ht).lt_iff_gt hp hs
  · simpa only [hz] using (hanti u.1 ht).lt_iff_gt hs hp
  · simpa only [hz] using ((hanti u.1 ht).eq_iff_eq hs hp).trans eq_comm

end FMSA.Convergence.ImplicitZeroContour

/-- info: 'FMSA.Convergence.ImplicitZeroContour.exists_analytic_zero_contour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ImplicitZeroContour.exists_analytic_zero_contour

/-- info: 'FMSA.Convergence.ImplicitZeroContour.negative_weight_derivative_rectangle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ImplicitZeroContour.negative_weight_derivative_rectangle

/-- info: 'FMSA.Convergence.ImplicitZeroContour.strict_minimum_of_positive_axis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ImplicitZeroContour.strict_minimum_of_positive_axis

/-- info: 'FMSA.Convergence.ImplicitZeroContour.local_sign_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ImplicitZeroContour.local_sign_classification
