import FMSAPaper.RegularContinuation
import FMSAPaper.StrengthScaling
import FMSAPaper.TaylorRoot

/-! The actual MSA Taylor series cannot converge beyond a transverse fold. -/
noncomputable section
open Filter Topology
open scoped ContDiff

namespace FMSA.Paper.FoldRadius

open ExactMSA.MultiTailMixture ExactMSA.BSource
open Abel TaylorRoot
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Convergence at any positive coupling produces an analytic actual root
through the same seed on the entire open symmetric interval. -/
theorem analytic_root_of_convergence_at
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (r : ℝ) (hr : 0 < r) (b : TailMatrix T N × TailMatrix T N)
    (hD : ∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j * r ^ n) (b.1 u i j))
    (hG : ∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j * r ^ n) (b.2 u i j)) :
    ∃ q : ℝ → TailMatrix T N × TailMatrix T N,
      q 0 = p 0 ∧ AnalyticOnNhd ℝ q (Set.Ioo (-r) r) ∧
      ∀ t ∈ Set.Ioo (-r) r, IsRoot z rho sigma (t • K) (q t).1 (q t).2 := by
  let v := fun t => p (r * t)
  have hv : ContDiffAt ℝ ∞ v 0 := by
    have hp' : ContDiffAt ℝ ∞ p (r * 0) := by simpa using hp
    exact hp'.comp 0 (contDiffAt_const.mul contDiffAt_id)
  have hvD : ∀ u i j, HasSum (fun n => (branchCoefficients v n).1 u i j) (b.1 u i j) := by
    intro u i j
    have hj (n : ℕ) := StrengthScaling.jet_rescale (fun t => (p t).1 u i j) r n
    simpa only [branchCoefficients, v, hj, mul_comm] using hD u i j
  have hvG : ∀ u i j, HasSum (fun n => (branchCoefficients v n).2 u i j) (b.2 u i j) := by
    intro u i j
    have hj (n : ℕ) := StrengthScaling.jet_rescale (fun t => (p t).2 u i j) r n
    simpa only [branchCoefficients, v, hj, mul_comm] using hG u i j
  have hvroot := StrengthScaling.local_root_rescale z rho sigma K p r hroot
  have hsol := (actual_endpoint_of_smooth_root z rho sigma (r • K) v b hv hvroot hvD hvG).2.2
  let q := fun t => amplitudeSeries (branchCoefficients v) (t / r)
  have hdiv : ∀ t ∈ Set.Ioo (-r) r, t / r ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor
    · exact (lt_div_iff₀ hr).mpr (by linarith [ht.1])
    · exact (div_lt_iff₀ hr).mpr (by simpa using ht.2)
  refine ⟨q, ?_, ?_, ?_⟩
  · apply Prod.ext <;> funext u i j
    · simpa only [q, amplitudeSeries, zero_div, jet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
        div_one, branchCoefficients, v, mul_zero] using series_jet _ _ (hvD u i j) 0
    · simpa only [q, amplitudeSeries, zero_div, jet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
        div_one, branchCoefficients, v, mul_zero] using series_jet _ _ (hvG u i j) 0
  · intro t ht
    have hs : AnalyticAt ℝ (amplitudeSeries (branchCoefficients v)) (t / r) := by
      apply AnalyticAt.prod
      all_goals apply analyticAt_pi_iff.mpr; intro u
      all_goals apply analyticAt_pi_iff.mpr; intro i
      all_goals apply analyticAt_pi_iff.mpr; intro j
      · exact powerSeries_analytic_of_hasSum _ _ (hvD u i j) _ (hdiv t ht)
      · exact powerSeries_analytic_of_hasSum _ _ (hvG u i j) _ (hdiv t ht)
    exact hs.comp (f := fun s : ℝ => s / r) (x := t) (by fun_prop)
  · intro t ht
    simpa only [smul_smul, div_mul_cancel₀ t hr.ne', q] using hsol (t / r) (hdiv t ht)

/-- The fold assumptions describe a finite continuous branch, regular before
the fold, with coupling derivative outside the amplitude Jacobian image.
Under these explicit assumptions no componentwise Taylor sum exists at r>f. -/
theorem actual_nonconvergence_beyond_fold
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0)
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (f : ℝ) (hf : 0 < f) (hpcont : ContinuousOn p (Set.Icc 0 f))
    (hproot : ∀ t ∈ Set.Ico 0 f, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hinv : ∀ t ∈ Set.Ico 0 f,
      ((fderiv ℝ (residual z rho sigma K) (t, p t)).comp
        (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible)
    (htransverse : (fderiv ℝ (residual z rho sigma K) (f, p f)) (1, 0) ∉
      Set.range (fun w => (fderiv ℝ (residual z rho sigma K) (f, p f)) (0, w)))
    (r : ℝ) (hfr : f < r) :
    ¬ ∃ b : TailMatrix T N × TailMatrix T N,
      (∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j * r ^ n) (b.1 u i j)) ∧
      (∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j * r ^ n) (b.2 u i j)) := by
  rintro ⟨b, hD, hG⟩
  obtain ⟨q, hq0, hqa, hqr⟩ := analytic_root_of_convergence_at z rho sigma K p hp hlocal
    r (hf.trans hfr) b hD hG
  have hsub : Set.Icc 0 f ⊆ Set.Ioo (-r) r := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hfat : f ∈ Set.Ioo (-r) r := hsub ⟨hf.le, le_rfl⟩
  have hRq : (fun t => residual z rho sigma K (t, q t)) =ᶠ[𝓝 f] (fun _ => 0) := by
    filter_upwards [isOpen_Ioo.mem_nhds hfat] with t ht
    exact (residual_eq_zero_iff _ _ _ _ _ _ _).mpr (hqr t ht)
  apply RegularContinuation.no_differentiable_extension (residual z rho sigma K) p q f hf
    hpcont (hqa.continuousOn.mono hsub) hq0.symm
    (fun t ht => (residual_eq_zero_iff _ _ _ _ _ _ _).mpr (hproot t ht))
    (fun t ht => (residual_eq_zero_iff _ _ _ _ _ _ _).mpr
      (hqr t (hsub (Set.Ico_subset_Icc_self ht))))
    (fun _ _ => (residual_contDiff z rho sigma K).contDiffAt) hinv
    (fderiv ℝ (residual z rho sigma K) (f, p f))
    ((residual_contDiff z rho sigma K).differentiable (by simp)).differentiableAt.hasFDerivAt
    htransverse hRq
  exact (hqa f hfat).differentiableAt

/-- The common radius is the infimum of the scalar component radii. Empty
amplitude families have radius infinity, as expected for the zero series. -/
def amplitudeRadius (a : ℕ → TailMatrix T N × TailMatrix T N) : ENNReal :=
  ⨅ u, ⨅ i, ⨅ j, min
    (FormalMultilinearSeries.ofScalars ℝ (fun n => (a n).1 u i j)).radius
    (FormalMultilinearSeries.ofScalars ℝ (fun n => (a n).2 u i j)).radius

omit [Fintype T] in
theorem hasSum_inside_amplitudeRadius
    (a : ℕ → TailMatrix T N × TailMatrix T N) (r : ℝ) (hr : 0 <= r)
    (hrad : ENNReal.ofReal r < amplitudeRadius a) :
    (∀ u i j, HasSum (fun n => (a n).1 u i j * r ^ n) ((amplitudeSeries a r).1 u i j)) ∧
    (∀ u i j, HasSum (fun n => (a n).2 u i j * r ^ n) ((amplitudeSeries a r).2 u i j)) := by
  have hbound (u : T) (i j : Fin N) : amplitudeRadius a <= min
      (FormalMultilinearSeries.ofScalars ℝ (fun n => (a n).1 u i j)).radius
      (FormalMultilinearSeries.ofScalars ℝ (fun n => (a n).2 u i j)).radius :=
    iInf_le_of_le u (iInf_le_of_le i (iInf_le_of_le j le_rfl))
  constructor <;> intro u i j
  · have hlt := hrad.trans_le ((hbound u i j).trans (min_le_left _ _))
    have hm : r ∈ Metric.eball (0 : ℝ)
        (FormalMultilinearSeries.ofScalars ℝ (fun n => (a n).1 u i j)).radius := by
      simpa only [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg hr] using hlt
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, amplitudeSeries] using
      ((FormalMultilinearSeries.ofScalars ℝ (fun n => (a n).1 u i j)).summable hm).hasSum
  · have hlt := hrad.trans_le ((hbound u i j).trans (min_le_right _ _))
    have hm : r ∈ Metric.eball (0 : ℝ)
        (FormalMultilinearSeries.ofScalars ℝ (fun n => (a n).2 u i j)).radius := by
      simpa only [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg hr] using hlt
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, amplitudeSeries] using
      ((FormalMultilinearSeries.ofScalars ℝ (fun n => (a n).2 u i j)).summable hm).hasSum

/-- Nonconvergence at every positive coupling beyond f bounds the common
radius by f. This uses the actual Mathlib component radii, not a fitted radius. -/
theorem amplitudeRadius_le_of_nonconvergence
    (a : ℕ → TailMatrix T N × TailMatrix T N) (f : ℝ) (hf : 0 <= f)
    (hdiv : ∀ r, f < r → ¬ ∃ b : TailMatrix T N × TailMatrix T N,
      (∀ u i j, HasSum (fun n => (a n).1 u i j * r ^ n) (b.1 u i j)) ∧
      (∀ u i j, HasSum (fun n => (a n).2 u i j * r ^ n) (b.2 u i j))) :
    amplitudeRadius a <= ENNReal.ofReal f := by
  by_contra h
  obtain ⟨r, hr, hfr, hra⟩ := ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge h)
  have hfr' : f < r := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hf).mp hfr
  exact hdiv r hfr' ⟨amplitudeSeries a r, hasSum_inside_amplitudeRadius a r hr hra⟩

theorem actual_radius_le_fold
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0)
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (f : ℝ) (hf : 0 < f) (hpcont : ContinuousOn p (Set.Icc 0 f))
    (hproot : ∀ t ∈ Set.Ico 0 f, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hinv : ∀ t ∈ Set.Ico 0 f,
      ((fderiv ℝ (residual z rho sigma K) (t, p t)).comp
        (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible)
    (htransverse : (fderiv ℝ (residual z rho sigma K) (f, p f)) (1, 0) ∉
      Set.range (fun w => (fderiv ℝ (residual z rho sigma K) (f, p f)) (0, w))) :
    amplitudeRadius (branchCoefficients p) <= ENNReal.ofReal f := by
  exact amplitudeRadius_le_of_nonconvergence (branchCoefficients p) f hf.le
    (actual_nonconvergence_beyond_fold z rho sigma K p hp hlocal f hf hpcont hproot hinv htransverse)

end FMSA.Paper.FoldRadius

/-- info: 'FMSA.Paper.FoldRadius.analytic_root_of_convergence_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FoldRadius.analytic_root_of_convergence_at

/-- info: 'FMSA.Paper.FoldRadius.actual_nonconvergence_beyond_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FoldRadius.actual_nonconvergence_beyond_fold

/-- info: 'FMSA.Paper.FoldRadius.hasSum_inside_amplitudeRadius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FoldRadius.hasSum_inside_amplitudeRadius

/-- info: 'FMSA.Paper.FoldRadius.amplitudeRadius_le_of_nonconvergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FoldRadius.amplitudeRadius_le_of_nonconvergence

/-- info: 'FMSA.Paper.FoldRadius.actual_radius_le_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FoldRadius.actual_radius_le_fold
