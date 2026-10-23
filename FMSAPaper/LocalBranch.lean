import LeanCode.YukawaOZMix.MSAMultiTailMixtureFamily

/-! Local uniqueness of the physical PY-seeded BH branch. -/
noncomputable section
open Filter Topology
open scoped ContDiff

namespace FMSA.Paper.LocalBranch

theorem continuous_roots_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ × E → E) (x : E) (p q : ℝ → E)
    (hR : ContDiffAt ℝ ∞ R (0, x))
    (hinv : ((fderiv ℝ R (0, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)).IsInvertible)
    (hp : ContinuousAt p 0) (hq : ContinuousAt q 0) (hp0 : p 0 = x) (hq0 : q 0 = x)
    (hpr : ∀ᶠ t in 𝓝 (0 : ℝ), R (t, p t) = 0)
    (hqr : ∀ᶠ t in 𝓝 (0 : ℝ), R (t, q t) = 0) :
    p =ᶠ[𝓝 (0 : ℝ)] q := by
  have hbase : R (0, x) = 0 := by simpa only [hp0] using hpr.self_of_nhds
  have htP : Tendsto (fun t => (t, p t)) (𝓝 (0 : ℝ)) (𝓝 (0, x)) := by
    simpa only [hp0, id_eq] using (continuousAt_id.prodMk hp).tendsto
  have htQ : Tendsto (fun t => (t, q t)) (𝓝 (0 : ℝ)) (𝓝 (0, x)) := by
    simpa only [hq0, id_eq] using (continuousAt_id.prodMk hq).tendsto
  have hu := hR.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  filter_upwards [htP.eventually hu, htQ.eventually hu, hpr, hqr] with t hP hQ hPr hQr
  exact (hP.mp (hPr.trans hbase.symm)).symm.trans (hQ.mp (hQr.trans hbase.symm))

open ExactMSA.MultiTailMixture
variable {N : ℕ} {T : Type*} [Fintype T]

theorem actual_seed_roots_eventuallyEq
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hz : ∀ u, 0 < z u) (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hrho : ∀ i, 0 <= rho i) (hsigma : ∀ i, 0 < sigma i)
    (p q : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContinuousAt p 0) (hq : ContinuousAt q 0)
    (hp0 : p 0 = (0, baseSeed z rho sigma))
    (hq0 : q 0 = (0, baseSeed z rho sigma))
    (hpr : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hqr : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (q t).1 (q t).2) :
    p =ᶠ[𝓝 (0 : ℝ)] q := by
  refine continuous_roots_eventuallyEq (residual z rho sigma K) (0, baseSeed z rho sigma)
    p q (residual_contDiff z rho sigma K).contDiffAt ?_ hp hq hp0 hq0 ?_ ?_
  · rw [residual_partial_triangular]
    exact triangular_isInvertible _ _
      (baseFirst_isUnit_det z rho sigma hz hv hrho hsigma)
      (baseSecond_isUnit_det z rho sigma hz hv hrho hsigma) _
  · filter_upwards [hpr] with t ht
    exact (residual_eq_zero_iff _ _ _ _ _ _ _).mpr ht
  · filter_upwards [hqr] with t ht
    exact (residual_eq_zero_iff _ _ _ _ _ _ _).mpr ht

end FMSA.Paper.LocalBranch

/-- info: 'FMSA.Paper.LocalBranch.continuous_roots_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.LocalBranch.continuous_roots_eventuallyEq

/-- info: 'FMSA.Paper.LocalBranch.actual_seed_roots_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.LocalBranch.actual_seed_roots_eventuallyEq
