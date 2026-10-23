import FMSAPaper.LocalBranch
import FMSAPaper.AbelEndpoint

/-! The actual polynomial BH residual is real analytic. Mathlib's implicit
function theorem at order omega gives analyticity of every continuous regular
root germ, including the physical PY-seeded branch. -/
noncomputable section
open Filter Topology
open scoped ContDiff BigOperators

namespace FMSA.Paper.ActualAnalyticBranch

open ExactMSA.MultiTailMixture
variable {N : ℕ} {T : Type*} [Fintype T]

theorem residual_analyticAt (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) :
    AnalyticAt ℝ (residual z rho sigma K) x := by
  have hD : ∀ u i j, AnalyticAt ℝ
      (fun y : ℝ × (TailMatrix T N × TailMatrix T N) => y.2.1 u i j) x := by
    intro u i j
    have h : AnalyticAt ℝ
        (fun y : ℝ × (TailMatrix T N × TailMatrix T N) => y.2.1) x :=
      analyticAt_fst.comp analyticAt_snd
    have hu := analyticAt_pi_iff.mp h u
    have hi := analyticAt_pi_iff.mp hu i
    exact analyticAt_pi_iff.mp hi j
  have hG : ∀ u i j, AnalyticAt ℝ
      (fun y : ℝ × (TailMatrix T N × TailMatrix T N) => y.2.2 u i j) x := by
    intro u i j
    have h : AnalyticAt ℝ
        (fun y : ℝ × (TailMatrix T N × TailMatrix T N) => y.2.2) x :=
      analyticAt_snd.comp analyticAt_snd
    have hu := analyticAt_pi_iff.mp h u
    have hi := analyticAt_pi_iff.mp hu i
    exact analyticAt_pi_iff.mp hi j
  have ht : AnalyticAt ℝ (fun y : ℝ × (TailMatrix T N × TailMatrix T N) => y.1) x :=
    analyticAt_fst
  unfold ExactMSA.MultiTailMixture.residual
  apply AnalyticAt.prod
  all_goals apply analyticAt_pi_iff.mpr; intro u
  all_goals apply analyticAt_pi_iff.mpr; intro i
  all_goals apply analyticAt_pi_iff.mpr; intro j
  all_goals simp only [firstLHS, secondLHS, secondRHS, dressedQhat, Qhat,
    amplitudeA, amplitudeQp, W, C, MSAMixture.mixDA, MSAMixture.mixDqp,
    MSAMixture.mixM, MSAMixture.mixN, MSAMixture.Wt, MSAMixture.Ct, MSAMixture.gam]
  all_goals fun_prop

omit [Fintype T] in
theorem continuous_regular_root_analyticAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ × E → E) (p : ℝ → E) (t0 : ℝ)
    (hR : AnalyticAt ℝ R (t0, p t0)) (hp : ContinuousAt p t0)
    (hroot : ∀ᶠ t in 𝓝 t0, R (t, p t) = 0)
    (hinv : ((fderiv ℝ R (t0, p t0)).comp (ContinuousLinearMap.inr ℝ ℝ E)).IsInvertible) :
    AnalyticAt ℝ p t0 := by
  have hc : ContDiffAt ℝ ω R (t0, p t0) := hR.contDiffAt
  have hi := (hc.contDiffAt_implicitFunction (by simp) hinv).analyticAt
  have ht : Tendsto (fun t => (t, p t)) (𝓝 t0) (𝓝 (t0, p t0)) :=
    (continuousAt_id.prodMk hp).tendsto
  have hbase : R (t0, p t0) = 0 := hroot.self_of_nhds
  apply hi.congr
  filter_upwards [ht.eventually (hc.eventually_apply_eq_iff_implicitFunction (by simp) hinv),
    hroot] with t hu hr
  exact hu.mp (hr.trans hbase.symm)

theorem actual_regular_root_analyticAt
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (t0 : ℝ)
    (hp : ContinuousAt p t0)
    (hroot : ∀ᶠ t in 𝓝 t0, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hinv : ((fderiv ℝ (residual z rho sigma K) (t0, p t0)).comp
      (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible) :
    AnalyticAt ℝ p t0 := by
  apply continuous_regular_root_analyticAt (residual z rho sigma K) p t0
    (residual_analyticAt z rho sigma K _) hp _ hinv
  filter_upwards [hroot] with t ht
  exact (residual_eq_zero_iff _ _ _ _ _ _ _).mpr ht

theorem actual_seed_root_analyticAt
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hz : ∀ u, 0 < z u) (hv : 0 < MatrixQ0.vacMix rho sigma)
    (hrho : ∀ i, 0 <= rho i) (hsigma : ∀ i, 0 < sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContinuousAt p 0) (hp0 : p 0 = (0, baseSeed z rho sigma))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) :
    AnalyticAt ℝ p 0 := by
  apply actual_regular_root_analyticAt z rho sigma K p 0 hp hroot
  rw [hp0, residual_partial_triangular]
  exact triangular_isInvertible _ _
    (baseFirst_isUnit_det z rho sigma hz hv hrho hsigma)
    (baseSecond_isUnit_det z rho sigma hz hv hrho hsigma) _

/-- Regularity gives analyticity throughout the half-open real branch. At zero
we use the two-sided local root germ; at interior points the interval supplies it. -/
theorem actual_regular_branch_analyticOnNhd
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (hp0 : ContinuousAt p 0) (hp : ContinuousOn p (Set.Icc 0 b))
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hroot : ∀ t ∈ Set.Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hinv : ∀ t ∈ Set.Ico 0 b,
      ((fderiv ℝ (residual z rho sigma K) (t, p t)).comp
        (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible) :
    AnalyticOnNhd ℝ p (Set.Ico 0 b) := by
  intro t ht
  by_cases hzero : t = 0
  · subst t
    exact actual_regular_root_analyticAt z rho sigma K p 0 hp0 hlocal (hinv 0 ht)
  · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hzero)
    apply actual_regular_root_analyticAt z rho sigma K p t
      (hp.continuousAt (Icc_mem_nhds ht0 ht.2)) _ (hinv t ht)
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Set.Ioo (0 : ℝ) b from ⟨ht0, ht.2⟩)] with u hu
    exact hroot u ⟨hu.1.le, hu.2⟩

end FMSA.Paper.ActualAnalyticBranch

/-- info: 'FMSA.Paper.ActualAnalyticBranch.residual_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticBranch.residual_analyticAt

/-- info: 'FMSA.Paper.ActualAnalyticBranch.continuous_regular_root_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticBranch.continuous_regular_root_analyticAt

/-- info: 'FMSA.Paper.ActualAnalyticBranch.actual_regular_root_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticBranch.actual_regular_root_analyticAt

/-- info: 'FMSA.Paper.ActualAnalyticBranch.actual_seed_root_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticBranch.actual_seed_root_analyticAt

/-- info: 'FMSA.Paper.ActualAnalyticBranch.actual_regular_branch_analyticOnNhd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualAnalyticBranch.actual_regular_branch_analyticOnNhd
