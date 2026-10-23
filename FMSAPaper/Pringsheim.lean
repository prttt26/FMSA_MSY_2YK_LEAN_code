import FMSAPaper.NonnegativeRecenter

/-! Pringsheim's endpoint obstruction for real nonnegative scalar power
series. A finite positive convergence radius cannot be crossed by a real
analytic continuation agreeing on the interior positive interval. This does
not assert divergence of the series at the boundary itself. -/
noncomputable section
open Filter Topology
open scoped BigOperators NNReal ENNReal

namespace FMSA.Paper.Pringsheim

open FormalMultilinearSeries NonnegativeRecenter

/-- Uniqueness identifies an analytic extension's coefficients with the
recentered original coefficients. Positivity then bounds the original radius. -/
theorem extension_radius_bound (a : ℕ → ℝ) (ha : ∀ n, 0 <= a n)
    (f : ℝ → ℝ) (q : FormalMultilinearSeries ℝ ℝ ℝ) (x y : ℝ) (s : ENNReal)
    (hx0 : 0 <= x) (hy0 : 0 <= y)
    (hx : (‖x‖₊ : ENNReal) < (ofScalars ℝ a).radius)
    (hy : (‖y‖₊ : ENNReal) < s)
    (hq : HasFPowerSeriesOnBall f q x s)
    (he : f =ᶠ[𝓝 x] (ofScalars ℝ a).sum) :
    ENNReal.ofReal (x + y) <= (ofScalars ℝ a).radius := by
  let p := ofScalars ℝ a
  have hp : HasFPowerSeriesAt p.sum (p.changeOrigin x) x := by
    simpa only [zero_add] using
      ((p.hasFPowerSeriesOnBall hx.pos).changeOrigin hx).hasFPowerSeriesAt
  have heq : p.changeOrigin x = q :=
    hp.eq_formalMultilinearSeries_of_eventually hq.hasFPowerSeriesAt he.symm
  apply le_radius_of_recenter_summable a ha x y hx0 hy0 hx
  change Summable (fun k => p.changeOrigin x k (fun _ => y))
  rw [heq]
  exact (hq.hasSum (mem_eball_zero_iff.mpr hy)).summable

/-- Real scalar Pringsheim theorem. The extension need only agree with the
sum on the open positive interval; the sum at the boundary is unrestricted. -/
theorem not_analyticAt_endpoint (a : ℕ → ℝ) (ha : ∀ n, 0 <= a n)
    (R : ℝ) (hR : 0 < R) (hradius : (ofScalars ℝ a).radius = ENNReal.ofReal R)
    (f : ℝ → ℝ) (he : ∀ t ∈ Set.Ioo (0 : ℝ) R, f t = (ofScalars ℝ a).sum t) :
    ¬ AnalyticAt ℝ f R := by
  rintro ⟨q, s, hq⟩
  obtain ⟨eps, heps, hepss⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hq.r_pos
  have heps0 : (0 : ℝ) < eps := by exact_mod_cast heps
  have hqeps : HasFPowerSeriesOnBall f q R (ENNReal.ofReal (eps : ℝ)) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hq.mono heps hepss.le
  let d : ℝ := min R (eps : ℝ) / 4
  have hd : 0 < d := div_pos (lt_min hR heps0) (by norm_num)
  have hdR : d < R := by dsimp [d]; linarith [min_le_left R (eps : ℝ)]
  have hdeps : 3 * d < (eps : ℝ) := by dsimp [d]; linarith [min_le_right R (eps : ℝ)]
  have hnormneg : (‖-d‖₊ : ENNReal) = ENNReal.ofReal d := by
    rw [ENNReal.coe_nnreal_eq ‖-d‖₊, coe_nnnorm, norm_neg, Real.norm_of_nonneg hd.le]
  have hshift : HasFPowerSeriesOnBall f (q.changeOrigin (-d)) (R - d)
      (ENNReal.ofReal ((eps : ℝ) - d)) := by
    have h := hqeps.changeOrigin (y := -d) (by
      rw [hnormneg]
      exact (ENNReal.ofReal_lt_ofReal_iff heps0).mpr (by linarith))
    simpa only [hnormneg, ← ENNReal.ofReal_sub _ hd.le, sub_eq_add_neg] using h
  have hx : (‖R - d‖₊ : ENNReal) < (ofScalars ℝ a).radius := by
    rw [hradius, ENNReal.coe_nnreal_eq ‖R - d‖₊, coe_nnnorm,
      Real.norm_of_nonneg (by linarith : 0 <= R - d)]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr (by linarith)
  have hy : (‖2 * d‖₊ : ENNReal) < ENNReal.ofReal ((eps : ℝ) - d) := by
    rw [ENNReal.coe_nnreal_eq ‖2 * d‖₊, coe_nnnorm,
      Real.norm_of_nonneg (by positivity : 0 <= 2 * d)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hlocal : f =ᶠ[𝓝 (R - d)] (ofScalars ℝ a).sum := by
    filter_upwards [eventually_gt_nhds (show 0 < R - d by linarith),
      eventually_lt_nhds (show R - d < R by linarith)] with t ht0 htR
    exact he t ⟨ht0, htR⟩
  have hbound := extension_radius_bound a ha f (q.changeOrigin (-d)) (R - d) (2 * d)
    (ENNReal.ofReal ((eps : ℝ) - d)) (by linarith) (by positivity) hx hy hshift hlocal
  rw [hradius] at hbound
  have hlt : ENNReal.ofReal R < ENNReal.ofReal (R - d + 2 * d) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  exact (not_le_of_gt hlt) hbound

end FMSA.Paper.Pringsheim

/-- info: 'FMSA.Paper.Pringsheim.extension_radius_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Pringsheim.extension_radius_bound

/-- info: 'FMSA.Paper.Pringsheim.not_analyticAt_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Pringsheim.not_analyticAt_endpoint
