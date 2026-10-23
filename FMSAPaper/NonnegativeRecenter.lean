import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Nonnegative scalar power series can be regrouped after changing origin
without assuming that the final point is in the original convergence disk.
This is the positivity step needed for Pringsheim's endpoint obstruction. -/
noncomputable section
open Filter Topology
open scoped BigOperators NNReal ENNReal

namespace FMSA.Paper.NonnegativeRecenter

open FormalMultilinearSeries

theorem scalar_apply_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 <= a n)
    (n : ℕ) (v : Fin n → ℝ) (hv : ∀ i, 0 <= v i) :
    0 <= ofScalars ℝ a n v := by
  simp only [ofScalars, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, smul_eq_mul, List.prod_ofFn]
  exact mul_nonneg (ha n) (Finset.prod_nonneg (fun i _ => hv i))

/-- Positivity permits regrouping beyond the original disk. Only the center
must lie inside it; convergence at the shifted argument is a separate premise. -/
theorem summable_of_recenter_summable (a : ℕ → ℝ) (ha : ∀ n, 0 <= a n)
    (x y : ℝ) (hx0 : 0 <= x) (hy0 : 0 <= y)
    (hx : (‖x‖₊ : ENNReal) < (ofScalars ℝ a).radius)
    (hy : Summable (fun k => (ofScalars ℝ a).changeOrigin x k (fun _ => y))) :
    Summable (fun n => a n * (x + y) ^ n) := by
  classical
  let p := ofScalars ℝ a
  let f : (Σ k l : ℕ, {s : Finset (Fin (k + l)) // s.card = l}) → ℝ := fun s =>
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) (fun _ => y)
  have hf0 : ∀ s, 0 <= f s := by
    rintro ⟨k, l, s, hs⟩
    dsimp only [f]
    rw [changeOriginSeriesTerm_apply]
    apply scalar_apply_nonneg a ha
    intro i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi, hx0, hy0]
  have hmem : x ∈ Metric.eball (0 : ℝ) p.radius := mem_eball_zero_iff.mpr hx
  have hinner (k : ℕ) :
      HasSum (fun s : Σ l : ℕ, {s : Finset (Fin (k + l)) // s.card = l} => f ⟨k, s⟩)
        (p.changeOrigin x k (fun _ => y)) := by
    have hs : Summable (fun s : Σ l : ℕ, {s : Finset (Fin (k + l)) // s.card = l} => f ⟨k, s⟩) := by
      refine .of_nnnorm_bounded ((p.changeOriginSeries_summable_aux₂ hx k).mul_right (‖y‖₊ ^ k)) ?_
      rintro ⟨l, s, hs⟩
      exact p.nnnorm_changeOriginSeriesTerm_apply_le k l s hs x y
    have houter := ContinuousMultilinearMap.hasSum_eval
      ((p.hasFPowerSeriesOnBall_changeOrigin k hx.pos).hasSum hmem) (fun _ => y)
    rw [zero_add] at houter
    refine HasSum.sigma_of_hasSum ?_ (fun l => hasSum_fintype _) hs
    simpa only [changeOriginSeries, ContinuousMultilinearMap.sum_apply, f] using houter
  have hsf : Summable f := by
    apply (summable_sigma_of_nonneg hf0).mpr
    refine ⟨fun k => (hinner k).summable, ?_⟩
    simpa only [(hinner _).tsum_eq] using hy
  have hreindex := (changeOriginIndexEquiv.symm.summable_iff.mpr hsf).sigma
  have he (n : ℕ) :
      (∑' s : Finset (Fin n), f (changeOriginIndexEquiv.symm ⟨n, s⟩)) = a n * (x + y) ^ n := by
    rw [tsum_fintype]
    simp only [f, changeOriginSeriesTerm_changeOriginIndexEquiv_symm]
    rw [← (p n).map_add_univ (fun _ => x) (fun _ => y)]
    change p n (fun _ => x + y) = _
    exact ofScalars_apply_eq a (x + y) n
  simpa only [Function.comp_apply, he] using hreindex

/-- A convergent recentered expansion forces a lower bound on the original
scalar radius, even if the candidate point was not known to be inside it. -/
theorem le_radius_of_recenter_summable (a : ℕ → ℝ) (ha : ∀ n, 0 <= a n)
    (x y : ℝ) (hx0 : 0 <= x) (hy0 : 0 <= y)
    (hx : (‖x‖₊ : ENNReal) < (ofScalars ℝ a).radius)
    (hy : Summable (fun k => (ofScalars ℝ a).changeOrigin x k (fun _ => y))) :
    ENNReal.ofReal (x + y) <= (ofScalars ℝ a).radius := by
  have hs := summable_of_recenter_summable a ha x y hx0 hy0 hx hy
  let r : ℝ≥0 := NNReal.mk (x + y) (add_nonneg hx0 hy0)
  have h := (ofScalars ℝ a).le_radius_of_summable (r := r)
    (by simpa only [ofScalars_norm, Real.norm_eq_abs, abs_of_nonneg (ha _), r,
      NNReal.coe_mk] using hs)
  simpa only [ENNReal.ofReal_eq_coe_nnreal (add_nonneg hx0 hy0), r] using h

end FMSA.Paper.NonnegativeRecenter

/-- info: 'FMSA.Paper.NonnegativeRecenter.scalar_apply_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.NonnegativeRecenter.scalar_apply_nonneg

/-- info: 'FMSA.Paper.NonnegativeRecenter.summable_of_recenter_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.NonnegativeRecenter.summable_of_recenter_summable

/-- info: 'FMSA.Paper.NonnegativeRecenter.le_radius_of_recenter_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.NonnegativeRecenter.le_radius_of_recenter_summable
