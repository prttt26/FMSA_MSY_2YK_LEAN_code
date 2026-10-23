import FMSAPaper.AbelEndpoint
import FMSAPaper.SmoothJets
import FMSAPaper.LocalBranch

/-! The local root-series premise is discharged from the actual smooth root's
Taylor coefficients and convergence. No analyticity of that smooth branch is
assumed: polynomial residual transport plus analyticity of the convergent series
forces its residual to vanish locally. -/
noncomputable section
open Filter Topology
open scoped ContDiff BigOperators

namespace FMSA.Paper.TaylorRoot
open ExactMSA.BSource ExactMSA.MultiTailMixture Abel SmoothJets

theorem series_jet (a : ℕ → ℝ) (b : ℝ) (h : HasSum a b) (n : ℕ) :
    jet (fun t => ∑' k, a k * t ^ k) n = a n := by
  let p := FormalMultilinearSeries.ofScalars ℝ a
  have hr : (1 : ENNReal) <= p.radius := by
    have ht := h.summable.tendsto_atTop_zero.norm
    have ht' : Tendsto (fun k => ‖p k‖ * ((1 : NNReal) : ℝ) ^ k) atTop (𝓝 (0 : ℝ)) := by
      simpa only [p, FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one,
        one_pow, mul_one, norm_zero] using ht
    exact p.le_radius_of_tendsto ht'
  have hp := p.hasFPowerSeriesOnBall (lt_of_lt_of_le (by norm_num) hr)
  have he : p.sum = fun t => ∑' k, a k * t ^ k := by
    change FormalMultilinearSeries.ofScalarsSum a = _
    simpa only [smul_eq_mul] using FormalMultilinearSeries.ofScalarsSum_eq_tsum (E := ℝ) a
  rw [he] at hp
  have hc := hp.factorial_smul (1 : ℝ) n
  have hc' : (n.factorial : ℝ) * a n =
      iteratedDeriv n (fun t => ∑' k, a k * t ^ k) 0 := by
    simpa only [p, FormalMultilinearSeries.ofScalars_apply_eq,
      one_pow, smul_eq_mul, mul_one, nsmul_eq_mul, iteratedDeriv] using hc
  unfold jet
  rw [← hc']
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem jetEq_taylor_sum (f : ℝ → ℝ) (b : ℝ)
    (hf : ContDiffAt ℝ ∞ f 0) (hs : HasSum (jet f) b) :
    JetEq f (fun t => ∑' n, jet f n * t ^ n) := by
  have ha := powerSeries_analytic_of_hasSum (jet f) b hs 0 (by norm_num)
  refine ⟨hf, ha.contDiffAt, ?_⟩
  intro n
  exact (series_jet (jet f) b hs n).symm

theorem analytic_zero_of_matching_root_jets (f g : ℝ → ℝ)
    (hg : AnalyticAt ℝ g 0) (he : JetEq f g) (hf : f =ᶠ[𝓝 (0 : ℝ)] 0) :
    g =ᶠ[𝓝 (0 : ℝ)] 0 := by
  apply locally_zero_of_analytic_zero_jets g hg
  intro n
  rw [← he.coeff_eq n]
  have hd := hf.iteratedDeriv_eq n
  simp only [jet, hd]
  simp

variable {N : ℕ} {T : Type*} [Fintype T]

def branchCoefficients (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) :
    TailMatrix T N × TailMatrix T N :=
  ((fun u i j => jet (fun t => (p t).1 u i j) n),
   (fun u i j => jet (fun t => (p t).2 u i j) n))

theorem actual_taylor_local_root
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hD : ∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j) (b.1 u i j))
    (hG : ∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j) (b.2 u i j)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K)
      (amplitudeSeries (branchCoefficients p) t).1
      (amplitudeSeries (branchCoefficients p) t).2 := by
  let s := amplitudeSeries (branchCoefficients p)
  have hjD : ∀ u i j, JetEq (fun t => (p t).1 u i j) (fun t => (s t).1 u i j) := by
    intro u i j
    exact jetEq_taylor_sum _ _ (by fun_prop) (hD u i j)
  have hjG : ∀ u i j, JetEq (fun t => (p t).2 u i j) (fun t => (s t).2 u i j) := by
    intro u i j
    exact jetEq_taylor_sum _ _ (by fun_prop) (hG u i j)
  have hj := actual_residual_jetEq z rho sigma K
    (fun t => (p t).1) (fun t => (p t).2)
    (fun t => (s t).1) (fun t => (s t).2) hjD hjG
  have ha := actual_residual_analytic z rho sigma K
    (fun t => (s t).1) (fun t => (s t).2) 0
    (fun u i j => powerSeries_analytic_of_hasSum _ _ (hD u i j) 0 (by norm_num))
    (fun u i j => powerSeries_analytic_of_hasSum _ _ (hG u i j) 0 (by norm_num))
  have hz : (fun t => residual z rho sigma K (t, p t)) =ᶠ[𝓝 (0 : ℝ)] 0 := by
    filter_upwards [hroot] with t ht
    exact (residual_eq_zero_iff _ _ _ _ _ _ _).mpr ht
  have hd : ∀ u i j, ∀ᶠ t in 𝓝 (0 : ℝ),
      (residual z rho sigma K (t, s t)).1 u i j = 0 := by
    intro u i j
    apply analytic_zero_of_matching_root_jets _ _
      ((((entry u i j).comp (ContinuousLinearMap.fst ℝ
        (TailMatrix T N) (TailMatrix T N))).analyticAt _).comp ha) (hj.1 u i j)
    filter_upwards [hz] with t ht
    exact congrArg (fun x : TailMatrix T N × TailMatrix T N => x.1 u i j) ht
  have hg : ∀ u i j, ∀ᶠ t in 𝓝 (0 : ℝ),
      (residual z rho sigma K (t, s t)).2 u i j = 0 := by
    intro u i j
    apply analytic_zero_of_matching_root_jets _ _
      ((((entry u i j).comp (ContinuousLinearMap.snd ℝ
        (TailMatrix T N) (TailMatrix T N))).analyticAt _).comp ha) (hj.2 u i j)
    filter_upwards [hz] with t ht
    exact congrArg (fun x : TailMatrix T N × TailMatrix T N => x.2 u i j) ht
  have hd' : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u i j,
      (residual z rho sigma K (t, s t)).1 u i j = 0 := by
    simpa only [eventually_all] using hd
  have hg' : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u i j,
      (residual z rho sigma K (t, s t)).2 u i j = 0 := by
    simpa only [eventually_all] using hg
  filter_upwards [hd', hg'] with t htD htG
  apply (residual_eq_zero_iff _ _ _ _ _ _ _).mp
  apply Prod.ext <;> funext u i j
  · exact htD u i j
  · exact htG u i j

theorem actual_endpoint_of_smooth_root
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hD : ∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j) (b.1 u i j))
    (hG : ∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j) (b.2 u i j)) :
    IsRoot z rho sigma K b.1 b.2 ∧
      Tendsto (amplitudeSeries (branchCoefficients p)) (𝓝[<] (1 : ℝ)) (𝓝 b) ∧
      ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        IsRoot z rho sigma (t • K)
          (amplitudeSeries (branchCoefficients p) t).1
          (amplitudeSeries (branchCoefficients p) t).2 := by
  exact actual_msa_endpoint_of_local_identity z rho sigma K (branchCoefficients p) b hD hG
    (actual_taylor_local_root z rho sigma K p b hp hroot hD hG)

theorem actual_taylor_seed_identification
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hz : ∀ u, 0 < z u) (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hrho : ∀ i, 0 <= rho i) (hsigma : ∀ i, 0 < sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0) (hp0 : p 0 = (0, baseSeed z rho sigma))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hD : ∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j) (b.1 u i j))
    (hG : ∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j) (b.2 u i j)) :
    p =ᶠ[𝓝 (0 : ℝ)] amplitudeSeries (branchCoefficients p) := by
  let s := amplitudeSeries (branchCoefficients p)
  have hs : AnalyticAt ℝ s 0 := by
    apply AnalyticAt.prod
    all_goals apply analyticAt_pi_iff.mpr; intro u
    all_goals apply analyticAt_pi_iff.mpr; intro i
    all_goals apply analyticAt_pi_iff.mpr; intro j
    · exact powerSeries_analytic_of_hasSum _ _ (hD u i j) 0 (by norm_num)
    · exact powerSeries_analytic_of_hasSum _ _ (hG u i j) 0 (by norm_num)
  have hs0 : s 0 = p 0 := by
    apply Prod.ext <;> funext u i j
    · simpa only [s, amplitudeSeries, jet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
        div_one, branchCoefficients] using series_jet _ _ (hD u i j) 0
    · simpa only [s, amplitudeSeries, jet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
        div_one, branchCoefficients] using series_jet _ _ (hG u i j) 0
  exact LocalBranch.actual_seed_roots_eventuallyEq z rho sigma K hz hv hrho hsigma
    p s hp.continuousAt hs.continuousAt hp0 (hs0.trans hp0) hroot
    (actual_taylor_local_root z rho sigma K p b hp hroot hD hG)

/-- F3 for an actual physical PY seed: the root family and all seed regularity
are supplied by the existing physical theorem. The only conditional input in
the convergence implication is convergence itself. -/
theorem exists_physical_taylor_convergence_theorem
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hz : ∀ u, 0 < z u) (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hrho : ∀ i, 0 <= rho i) (hsigma : ∀ i, 0 < sigma i) :
    ∃ p : ℝ → TailMatrix T N × TailMatrix T N,
      p 0 = (0, baseSeed z rho sigma) ∧ ContDiffAt ℝ ∞ p 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) ∧
      ∀ b : TailMatrix T N × TailMatrix T N,
        (∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j) (b.1 u i j)) →
        (∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j) (b.2 u i j)) →
        (p =ᶠ[𝓝 (0 : ℝ)] amplitudeSeries (branchCoefficients p)) ∧
        IsRoot z rho sigma K b.1 b.2 ∧
        Tendsto (amplitudeSeries (branchCoefficients p)) (𝓝[<] (1 : ℝ)) (𝓝 b) ∧
        ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
          IsRoot z rho sigma (t • K)
            (amplitudeSeries (branchCoefficients p) t).1
            (amplitudeSeries (branchCoefficients p) t).2 := by
  obtain ⟨p, hp0, hr, hp⟩ := exists_contDiffAt_root z rho sigma K hz hv hrho hsigma
  refine ⟨p, hp0, hp, hr, fun b hD hG => ⟨?_, ?_⟩⟩
  · exact actual_taylor_seed_identification z rho sigma K hz hv hrho hsigma p b hp hp0 hr hD hG
  · exact actual_endpoint_of_smooth_root z rho sigma K p b hp hr hD hG

theorem actual_nonconvergence_of_no_real_root
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContDiffAt ℝ ∞ p 0)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hnoroot : ¬ ∃ D G, IsRoot z rho sigma K D G) :
    ¬ ∃ b : TailMatrix T N × TailMatrix T N,
      (∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j) (b.1 u i j)) ∧
      (∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j) (b.2 u i j)) := by
  rintro ⟨b, hD, hG⟩
  exact hnoroot ⟨b.1, b.2, (actual_endpoint_of_smooth_root z rho sigma K p b hp hroot hD hG).1⟩

end FMSA.Paper.TaylorRoot

/-- info: 'FMSA.Paper.TaylorRoot.series_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.TaylorRoot.series_jet

/-- info: 'FMSA.Paper.TaylorRoot.jetEq_taylor_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.TaylorRoot.jetEq_taylor_sum

/-- info: 'FMSA.Paper.TaylorRoot.analytic_zero_of_matching_root_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.TaylorRoot.analytic_zero_of_matching_root_jets

/-- info: 'FMSA.Paper.TaylorRoot.actual_taylor_local_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.TaylorRoot.actual_taylor_local_root

/-- info: 'FMSA.Paper.TaylorRoot.actual_endpoint_of_smooth_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.TaylorRoot.actual_endpoint_of_smooth_root

/-- info: 'FMSA.Paper.TaylorRoot.actual_taylor_seed_identification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.TaylorRoot.actual_taylor_seed_identification

/-- info: 'FMSA.Paper.TaylorRoot.exists_physical_taylor_convergence_theorem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.TaylorRoot.exists_physical_taylor_convergence_theorem

/-- info: 'FMSA.Paper.TaylorRoot.actual_nonconvergence_of_no_real_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.TaylorRoot.actual_nonconvergence_of_no_real_root
