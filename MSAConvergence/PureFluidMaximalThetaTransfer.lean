import MSAConvergence.PureFluidScalarMixtureBridge

set_option linter.style.header false

/-! Identify the positive pure-fluid HS germ with the constructed
one-species maximal canonical branch near zero coupling. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace FMSA.Convergence.PureFluidMaximalThetaTransfer
open FMSA.Convergence.PureFluidScalarMixtureBridge
open FMSA.Convergence.ActualCanonicalBranch
open FMSA.Convergence.CanonicalNeighborhood
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidPositiveSubstitution
open FMSA.Convergence.PureFluidHActualNodeBridge
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.PureFluidThetaPringsheimRoute
open FMSA.Convergence.MaximalMSAConvergence
open FMSA.Paper.AnalyticTaylor
open FMSA.Paper.TaylorRoot
open FMSA.ExactMSA.BSource
open FMSA.Paper.StableIntervalRadius
open FMSA.ExactMSA FMSA.ExactMSA.MultiTailMixture
open FMSA.MatrixQ0 MSAMixture

variable {T : Type*} [Fintype T]

def liftPath (p : ℝ → (T → ℝ) × (T → ℝ)) :
    ℝ → MultiTailMixture.TailMatrix T 1 ×
      MultiTailMixture.TailMatrix T 1 :=
  fun tau => (liftTail (p tau).1, liftTail (p tau).2)

theorem liftPath_analyticAt (p : ℝ → (T → ℝ) × (T → ℝ))
    (hp : AnalyticAt ℝ p 0) : AnalyticAt ℝ (liftPath p) 0 := by
  apply AnalyticAt.prod
  · apply analyticAt_pi_iff.mpr
    intro t
    apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    change AnalyticAt ℝ (fun tau => (p tau).1 t) 0
    exact analyticAt_pi_iff.mp (analyticAt_fst.comp hp) t
  · apply analyticAt_pi_iff.mpr
    intro t
    apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    change AnalyticAt ℝ (fun tau => (p tau).2 t) 0
    exact analyticAt_pi_iff.mp (analyticAt_snd.comp hp) t

/-- Regular-root uniqueness at the canonical PY seed identifies the
constructed maximal branch with any analytic pure-fluid HS root germ. -/
theorem maximalPath_eventuallyEq_liftGerm
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t)
    (M : FMSA.Convergence.MaximalCanonicalBranch.MaximalBranch
      z (rho1 xi) sigma1 (liftTail K)
      (0, MultiTailMixture.baseSeed z (rho1 xi) sigma1))
    (p : ℝ → (T → ℝ) × (T → ℝ))
    (hp0 : p 0 = (0, fun t => G0 xi (z t)))
    (hpa : AnalyticAt ℝ p 0)
    (hpr : ∀ᶠ tau : ℝ in 𝓝 0,
      MultiTail.IsRoot xi z (fun t => tau * K t)
        (p tau).1 (p tau).2) :
    M.path =ᶠ[𝓝 0] liftPath p := by
  have hv : vacMix (rho1 xi) sigma1 ≠ 0 := by
    rw [vacMix_rho1_sigma1]
    linarith
  have hrho : ∀ i, 0 ≤ rho1 xi i := by
    intro i
    simp only [rho1, rhoOf]
    positivity
  have hsigma : ∀ i, 0 < sigma1 i := by
    intro i
    simp [sigma1]
  have hK : ∀ u i j, liftTail K u i j = liftTail K u j i := by
    intros
    rfl
  have h0 : (0 : ℝ) ∈ initialCouplings M.bound :=
    ⟨le_rfl, by simpa using M.positive⟩
  have heq : M.path 0 = liftPath p 0 := by
    have hseed : liftTail (fun t => G0 xi (z t)) =
        MultiTailMixture.baseSeed z (rho1 xi) sigma1 := by
      rw [← lift_lowerTail (MultiTailMixture.baseSeed z (rho1 xi) sigma1)]
      exact congrArg liftTail (baseSeed_eq_pure xi hxi0 hxi1 z hz).symm
    have hzero : liftTail (fun _ : T => 0) =
        (0 : MultiTailMixture.TailMatrix T 1) := by
      funext t i j
      rfl
    rw [M.at_seed]
    change (0, MultiTailMixture.baseSeed z (rho1 xi) sigma1) =
      (liftTail (p 0).1, liftTail (p 0).2)
    rw [hp0]
    rw [hseed]
    apply Prod.ext
    · exact hzero.symm
    · rfl
  have hqroot : ∀ᶠ tau in 𝓝 (0 : ℝ),
      MultiTailMixture.IsRoot z (rho1 xi) sigma1
        (tau • liftTail K) (liftPath p tau).1 (liftPath p tau).2 := by
    filter_upwards [hpr] with tau ht
    have hk : tau • liftTail K = liftTail (fun t => tau * K t) := by
      funext t i j
      simp [liftTail, Pi.smul_apply, smul_eq_mul]
    rw [hk]
    exact (isRoot_iff xi hxi1.ne z (fun t => tau * K t)
      (p tau).1 (p tau).2).mpr ht
  have hseed : M.path 0 ∈ canonicalAmplitudes z (rho1 xi) sigma1 :=
    M.canonical 0 h0
  have he := canonical_root_germs_eventuallyEqWithin
    z hz (rho1 xi) sigma1 hsigma hrho (liftTail K) hK hv
    M.path (liftPath p) Set.univ 0
    (M.analytic 0 h0).continuousAt.continuousWithinAt
    (liftPath_analyticAt p hpa).continuousAt.continuousWithinAt
    heq (M.roots 0 h0)
    (by simpa using M.local_roots)
    (by simpa using hqroot)
    hseed
  simpa using he

/-- The theta Taylor coefficients of the actual constructed maximal
one-species branch are nonnegative at every tail node. -/
theorem maximalBranch_theta_taylor_nonnegative
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t)
    (hKpos : ∀ t, 0 < K t)
    (M : FMSA.Convergence.MaximalCanonicalBranch.MaximalBranch
      z (rho1 xi) sigma1 (liftTail K)
      (0, MultiTailMixture.baseSeed z (rho1 xi) sigma1)) :
    ∃ thetaS : T → PowerSeries ℝ,
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z
          (lowerPath M.path tau).1 (lowerPath M.path tau).2 t)
        (thetaS t)) ∧
      ∀ t, CoeffNonneg (thetaS t) := by
  obtain ⟨p, thetaP, _RP, hp0, hpa, hthetaP, _hRP,
    hposP, _hposR, hroot, _hthetaSum, _hRSum⟩ :=
    exists_actual_hs_root_germ_with_nonnegative_theta_r_taylor
      xi hxi0 hxi1 z K hz hKpos
  have he := maximalPath_eventuallyEq_liftGerm
    xi hxi0 hxi1 z K hz M p hp0 hpa hroot
  have hproj : lowerPath M.path =ᶠ[𝓝 (0 : ℝ)] p := by
    filter_upwards [he] with tau ht
    unfold lowerPath
    rw [ht]
    rfl
  let q := lowerPath M.path
  have h0 : (0 : ℝ) ∈ initialCouplings M.bound :=
    ⟨le_rfl, by simpa using M.positive⟩
  have hqa : AnalyticAt ℝ q 0 :=
    lowerPath_analyticOn M.path M.analytic 0 h0
  let thetaM : T → PowerSeries ℝ := fun t => Classical.choose
      (exists_taylorPowerSeries
        (fun tau => actualTheta xi z (q tau).1 (q tau).2 t)
        (actualTheta_analyticAt_of_amplitude_analyticAt
          xi hxi1.ne z hz q 0 hqa t))
  have hthetaM : ∀ t, HasTaylorPowerSeriesAt
      (fun tau => actualTheta xi z (q tau).1 (q tau).2 t)
      (thetaM t) := by
    intro t
    exact Classical.choose_spec _
  refine ⟨thetaM, hthetaM, ?_⟩
  intro t n
  let f := fun tau => actualTheta xi z (q tau).1 (q tau).2 t
  let g := fun tau => actualTheta xi z (p tau).1 (p tau).2 t
  have hfg : f =ᶠ[𝓝 (0 : ℝ)] g := by
    filter_upwards [hproj] with tau ht
    simp only [f, g, q, ht]
  have hEq := taylorPowerSeries_eq_of_eventually
    f g (thetaM t) (thetaP t) (hthetaM t) (hthetaP t) hfg
  change 0 ≤ PowerSeries.coeff n (thetaM t)
  rw [hEq]
  exact hposP t n

/-- Every positive interior bound of the constructed maximal branch
is a lower bound for each physical theta-node Taylor radius. -/
theorem maximalBranch_theta_radius_lower_bound
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t)
    (hKpos : ∀ t, 0 < K t)
    (M : FMSA.Convergence.MaximalCanonicalBranch.MaximalBranch
      z (rho1 xi) sigma1 (liftTail K)
      (0, MultiTailMixture.baseSeed z (rho1 xi) sigma1))
    (b : ℝ) (hb : 0 < b) (hbound : ENNReal.ofReal b ≤ M.bound) :
    ∃ thetaS : T → PowerSeries ℝ,
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z
          (lowerPath M.path tau).1 (lowerPath M.path tau).2 t)
        (thetaS t)) ∧
      (∀ t, CoeffNonneg (thetaS t)) ∧
      ∀ t, ENNReal.ofReal b ≤
        (FormalMultilinearSeries.ofScalars ℝ
          (fun n => PowerSeries.coeff n (thetaS t))).radius := by
  obtain ⟨thetaS, htheta, hpos⟩ :=
    maximalBranch_theta_taylor_nonnegative
      xi hxi0 hxi1 z K hz hKpos M
  refine ⟨thetaS, htheta, hpos, ?_⟩
  have hsub : Set.Ico (0 : ℝ) b ⊆ initialCouplings M.bound := by
    intro tau ht
    refine ⟨ht.1, ?_⟩
    exact lt_of_lt_of_le
      ((ENNReal.ofReal_lt_ofReal_iff hb).mpr ht.2) hbound
  have hanalytic : AnalyticOnNhd ℝ (lowerPath M.path) (Set.Ico 0 b) := by
    intro tau ht
    exact lowerPath_analyticOn M.path M.analytic tau (hsub ht)
  exact actualTheta_radius_lower_bound_of_analytic_amplitude_branch
    xi hxi1.ne z hz (lowerPath M.path) thetaS htheta hpos b hb hanalytic

/-- The theta Taylor radius reaches at least the full maximal
canonical initial-branch bound, including an infinite bound. -/
theorem maximalBranch_theta_radius_ge_bound
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t)
    (hKpos : ∀ t, 0 < K t)
    (M : FMSA.Convergence.MaximalCanonicalBranch.MaximalBranch
      z (rho1 xi) sigma1 (liftTail K)
      (0, MultiTailMixture.baseSeed z (rho1 xi) sigma1)) :
    ∃ thetaS : T → PowerSeries ℝ,
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z
          (lowerPath M.path tau).1 (lowerPath M.path tau).2 t)
        (thetaS t)) ∧
      (∀ t, CoeffNonneg (thetaS t)) ∧
      ∀ t, M.bound ≤
        (FormalMultilinearSeries.ofScalars ℝ
          (fun n => PowerSeries.coeff n (thetaS t))).radius := by
  obtain ⟨thetaS, htheta, hpos⟩ :=
    maximalBranch_theta_taylor_nonnegative
      xi hxi0 hxi1 z K hz hKpos M
  refine ⟨thetaS, htheta, hpos, ?_⟩
  intro t
  by_contra hn
  have hlt :
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n => PowerSeries.coeff n (thetaS t))).radius < M.bound :=
    lt_of_not_ge hn
  obtain ⟨r, hr0, hradius, hrM⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hrpos : 0 < r := by
    rcases hr0.eq_or_lt with heq | hpos
    · subst r
      simp at hradius
    · exact hpos
  obtain ⟨thetaR, hthetaR, _hposR, hradR⟩ :=
    maximalBranch_theta_radius_lower_bound
      xi hxi0 hxi1 z K hz hKpos M r hrpos hrM.le
  have hEq : thetaR t = thetaS t :=
    taylorPowerSeries_unique _ _ _ (hthetaR t) (htheta t)
  have hR := hradR t
  rw [hEq] at hR
  exact (not_lt_of_ge hR) hradius

/-- The positive theta Taylor series actually sums to each selected
maximal-branch node throughout every initial interval below its bound. -/
theorem maximalBranch_theta_hasSum_before_bound
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t)
    (hKpos : ∀ t, 0 < K t)
    (M : FMSA.Convergence.MaximalCanonicalBranch.MaximalBranch
      z (rho1 xi) sigma1 (liftTail K)
      (0, MultiTailMixture.baseSeed z (rho1 xi) sigma1))
    (b : ℝ) (hb : 0 < b) (hbound : ENNReal.ofReal b ≤ M.bound) :
    ∃ thetaS : T → PowerSeries ℝ,
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z
          (lowerPath M.path tau).1 (lowerPath M.path tau).2 t)
        (thetaS t)) ∧
      (∀ t, CoeffNonneg (thetaS t)) ∧
      ∀ t tau, tau ∈ Set.Ico (0 : ℝ) b →
        HasSum (fun n => PowerSeries.coeff n (thetaS t) * tau ^ n)
          (actualTheta xi z
            (lowerPath M.path tau).1 (lowerPath M.path tau).2 t) := by
  obtain ⟨thetaS, htheta, hpos, hrad⟩ :=
    maximalBranch_theta_radius_lower_bound
      xi hxi0 hxi1 z K hz hKpos M b hb hbound
  refine ⟨thetaS, htheta, hpos, ?_⟩
  have hsub : Set.Ico (0 : ℝ) b ⊆ initialCouplings M.bound := by
    intro tau ht
    exact ⟨ht.1,
      lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hb).mpr ht.2) hbound⟩
  have ha : AnalyticOnNhd ℝ (lowerPath M.path) (Set.Ico 0 b) := by
    intro tau ht
    exact lowerPath_analyticOn M.path M.analytic tau (hsub ht)
  intro t tau ht
  let f := fun x => actualTheta xi z
    (lowerPath M.path x).1 (lowerPath M.path x).2 t
  have hf : AnalyticOnNhd ℝ f (Set.Ico 0 b) := by
    intro x hx
    exact actualTheta_analyticAt_of_amplitude_analyticAt
      xi hxi1.ne z hz (lowerPath M.path) x (ha x hx) t
  have hcoeff : (fun n => PowerSeries.coeff n (thetaS t)) = jet f := by
    funext n
    exact taylorPowerSeries_coeff_eq_jet f (thetaS t) (htheta t) n
  have hr : ENNReal.ofReal tau <
      (FormalMultilinearSeries.ofScalars ℝ (jet f)).radius := by
    rw [← hcoeff]
    exact lt_of_lt_of_le
      ((ENNReal.ofReal_lt_ofReal_iff hb).mpr ht.2) (hrad t)
  have hsum := hasSum_jet_on_interval f b hf tau ht hr
  have hfun : (fun n => jet f n * tau ^ n) =
      (fun n => PowerSeries.coeff n (thetaS t) * tau ^ n) := by
    funext n
    rw [← congrFun hcoeff n]
  rw [hfun] at hsum
  exact hsum

/-- For every physical one-species state and positive finite-tail
coupling vector, the canonical maximal branch and its theta-node
Pringsheim lower bounds are constructed from the physical data. -/
theorem exists_pure_maximal_theta_radius_lower_bound
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t)
    (hKpos : ∀ t, 0 < K t) :
    ∃ M : FMSA.Convergence.MaximalCanonicalBranch.MaximalBranch
        z (rho1 xi) sigma1 (liftTail K)
        (0, MultiTailMixture.baseSeed z (rho1 xi) sigma1),
      ∀ b : ℝ, 0 < b → ENNReal.ofReal b ≤ M.bound →
        ∃ thetaS : T → PowerSeries ℝ,
          (∀ t, HasTaylorPowerSeriesAt
            (fun tau => actualTheta xi z
              (lowerPath M.path tau).1 (lowerPath M.path tau).2 t)
            (thetaS t)) ∧
          (∀ t, CoeffNonneg (thetaS t)) ∧
          ∀ t, ENNReal.ofReal b ≤
            (FormalMultilinearSeries.ofScalars ℝ
              (fun n => PowerSeries.coeff n (thetaS t))).radius := by
  have hv : 0 < vacMix (rho1 xi) sigma1 := by
    rw [vacMix_rho1_sigma1]
    linarith
  have hrho : ∀ i, 0 ≤ rho1 xi i := by
    intro i
    simp only [rho1, rhoOf]
    positivity
  have hsigma : ∀ i, 0 < sigma1 i := by
    intro i
    simp [sigma1]
  obtain ⟨M, _⟩ := exists_scalar_hs_maximal_branch
    z hz (rho1 xi) sigma1 hsigma hrho (liftTail K) hv
  exact ⟨M, fun b hb hbound =>
    maximalBranch_theta_radius_lower_bound
      xi hxi0 hxi1 z K hz hKpos M b hb hbound⟩

end FMSA.Convergence.PureFluidMaximalThetaTransfer

/-- info: 'FMSA.Convergence.PureFluidMaximalThetaTransfer.liftPath_analyticAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidMaximalThetaTransfer.liftPath_analyticAt

/-- info: 'FMSA.Convergence.PureFluidMaximalThetaTransfer.maximalPath_eventuallyEq_liftGerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidMaximalThetaTransfer.maximalPath_eventuallyEq_liftGerm

/-- info: 'FMSA.Convergence.PureFluidMaximalThetaTransfer.maximalBranch_theta_taylor_nonnegative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidMaximalThetaTransfer.maximalBranch_theta_taylor_nonnegative

/-- info: 'FMSA.Convergence.PureFluidMaximalThetaTransfer.maximalBranch_theta_radius_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidMaximalThetaTransfer.maximalBranch_theta_radius_lower_bound

/-- info: 'FMSA.Convergence.PureFluidMaximalThetaTransfer.maximalBranch_theta_radius_ge_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidMaximalThetaTransfer.maximalBranch_theta_radius_ge_bound

/-- info: 'FMSA.Convergence.PureFluidMaximalThetaTransfer.maximalBranch_theta_hasSum_before_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidMaximalThetaTransfer.maximalBranch_theta_hasSum_before_bound

/-- info: 'FMSA.Convergence.PureFluidMaximalThetaTransfer.exists_pure_maximal_theta_radius_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidMaximalThetaTransfer.exists_pure_maximal_theta_radius_lower_bound
