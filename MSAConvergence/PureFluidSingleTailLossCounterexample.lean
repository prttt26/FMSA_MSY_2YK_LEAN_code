import MSAConvergence.PureFluidMaximalThetaTransfer
import MSAConvergence.SingleTailCanonicalRadius

set_option linter.style.header false

/-! A physical one-tail pure fluid already separates first canonical
loss from the original-amplitude Taylor radius. -/
noncomputable section
open Real Filter Topology
open scoped ENNReal
namespace FMSA.Convergence.PureFluidSingleTailLossCounterexample
open FMSA.Convergence.PureFluidScalarMixtureBridge
open FMSA.Convergence.PureFluidMaximalThetaTransfer
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidThetaPringsheimRoute
open FMSA.Convergence.PureFluidPositiveSubstitution
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.SingleTailCanonicalRadius
open FMSA.Convergence.MaximalCanonicalBranch
open FMSA.Convergence.ActualCanonicalBranch
open FMSA.Paper.StableIntervalRadius FMSA.Paper.FoldRadius FMSA.Paper.TaylorRoot
open FMSA.Paper.AnalyticTaylor FMSA.ExactMSA.BSource
open FMSA.Paper.SingleTailRadius
open FMSA.ExactMSA FMSA.ExactMSA.MultiTailMixture FMSA.MatrixQ0

/-- Every positive-density unit-diameter pure fluid with one positive
Yukawa tail has a constructed maximal canonical branch whose original
amplitude Taylor radius is strictly larger than its first canonical
endpoint. The amplitude series sums throughout that initial interval,
and the branch is an actual pure-fluid BH root there. -/
theorem exists_physical_single_tail_radius_after_canonical_loss
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : Fin 1 → ℝ) (hz : 0 < z 0) (hK : 0 < K 0) :
    ∃ M : MaximalBranch z (rho1 xi) sigma1 (liftTail K)
        (0, baseSeed z (rho1 xi) sigma1),
      M.bound < amplitudeRadius (branchCoefficients M.path) ∧
      AmplitudeHasSumBefore M.path M.bound ∧
      AmplitudeHasSumTo M.path
        (physBranch z (rho1 xi) sigma1 (liftTail K))
        (ENNReal.ofReal (foldCoupling z (rho1 xi) sigma1 (liftTail K))) ∧
      (∀ tau ∈ initialCouplings M.bound,
        FMSA.ExactMSA.MultiTail.IsRoot xi z
          (fun t => tau * K t)
          (lowerPath M.path tau).1 (lowerPath M.path tau).2) := by
  have hr : 0 < rho1 xi 0 := by
    simp only [rho1, rhoOf]
    positivity
  have hs : 0 < sigma1 0 := by simp [sigma1]
  have hv : 0 < vacMix (rho1 xi) sigma1 := by
    rw [vacMix_rho1_sigma1]
    linarith
  have hk : 0 < liftTail K (default : Fin 1) 0 0 := by
    simpa [liftTail] using hK
  obtain ⟨M, _hmax, hstrict, hsum, _hfinite, _hlimit, _hext⟩ :=
    exists_hs_branch_with_strict_radius_and_limit
      z (rho1 xi) sigma1 (liftTail K) hz hr hs hv hk
  have hzall : ∀ t : Fin 1, 0 < z t := by
    intro t
    simpa only [Subsingleton.elim t 0] using hz
  exact ⟨M, hstrict, hsum,
    maximal_taylor_sums_to_explicit_until_fold
      z (rho1 xi) sigma1 (liftTail K) hz hr hs hv hk M,
    (maximalBranch_pure_path xi hxi0 hxi1 z K hzall M).2.2⟩

/-- The explicit single-tail root is also a two-sided pure-fluid HS
germ, so its theta Taylor data can be compared with the maximal branch. -/
theorem explicit_branch_pure_hs_germ
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : Fin 1 → ℝ) (hz : 0 < z 0) (hK : 0 < K 0) :
    let p := lowerPath (physBranch z (rho1 xi) sigma1 (liftTail K))
    p 0 = (0, fun t => G0 xi (z t)) ∧
    AnalyticAt ℝ p 0 ∧
    ∀ᶠ tau : ℝ in 𝓝 0,
      FMSA.ExactMSA.MultiTail.IsRoot xi z (fun t => tau * K t)
        (p tau).1 (p tau).2 := by
  have hr : 0 < rho1 xi 0 := by
    simp only [rho1, rhoOf]
    positivity
  have hs : 0 < sigma1 0 := by simp [sigma1]
  have hv : 0 < vacMix (rho1 xi) sigma1 := by
    rw [vacMix_rho1_sigma1]
    linarith
  have hk : 0 < liftTail K (default : Fin 1) 0 0 := by
    simpa [liftTail] using hK
  have hzall : ∀ t : Fin 1, 0 < z t := by
    intro t
    simpa only [Subsingleton.elim t 0] using hz
  let q := physBranch z (rho1 xi) sigma1 (liftTail K)
  let p := lowerPath q
  have hq0 : q 0 = (0, baseSeed z (rho1 xi) sigma1) :=
    physBranch_zero z (rho1 xi) sigma1 (liftTail K) hz hr hs hv hk
  have hp0 : p 0 = (0, fun t => G0 xi (z t)) := by
    change (lowerTail (q 0).1, lowerTail (q 0).2) = _
    rw [hq0]
    apply Prod.ext
    · funext t
      rfl
    · exact baseSeed_eq_pure xi hxi0 hxi1 z hzall
  have hfold : 0 < foldCoupling z (rho1 xi) sigma1 (liftTail K) :=
    foldCoupling_pos z (rho1 xi) sigma1 (liftTail K) hz hr hs hv hk
  have hqa : AnalyticOnNhd ℝ q
      (Set.Ico 0 (foldCoupling z (rho1 xi) sigma1 (liftTail K))) :=
    physBranch_analyticOnNhd z (rho1 xi) sigma1 (liftTail K) hz hr hs hv hk
  have hpa : AnalyticAt ℝ p 0 :=
    lowerPath_analyticOn q hqa 0 ⟨le_rfl, hfold⟩
  have hqr : ∀ᶠ tau : ℝ in 𝓝 0,
      IsRoot z (rho1 xi) sigma1 (tau • liftTail K)
        (q tau).1 (q tau).2 :=
    physBranch_local_root z (rho1 xi) sigma1 (liftTail K) hz hr hs hv hk
  have hpr : ∀ᶠ tau : ℝ in 𝓝 0,
      FMSA.ExactMSA.MultiTail.IsRoot xi z (fun t => tau * K t)
        (p tau).1 (p tau).2 := by
    filter_upwards [hqr] with tau ht
    have hstrength : tau • liftTail K =
        liftTail (fun t => tau * K t) := by
      funext t i j
      simp [liftTail, Pi.smul_apply, smul_eq_mul]
    rw [hstrength, ← lift_lowerTail (q tau).1,
      ← lift_lowerTail (q tau).2] at ht
    exact (isRoot_iff xi hxi1.ne z (fun t => tau * K t)
      (lowerTail (q tau).1) (lowerTail (q tau).2)).mp ht
  exact ⟨hp0, hpa, hpr⟩

/-- The explicit analytic one-tail branch remains a genuine pure-fluid
BH root at every nonnegative coupling strictly below its fold. -/
theorem explicit_pure_branch_isRoot_before_fold
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : Fin 1 → ℝ) (hz : 0 < z 0) (hK : 0 < K 0)
    (tau : ℝ)
    (ht : tau ∈ Set.Ico (0 : ℝ)
      (foldCoupling z (rho1 xi) sigma1 (liftTail K))) :
    FMSA.ExactMSA.MultiTail.IsRoot xi z (fun t => tau * K t)
      (lowerPath (physBranch z (rho1 xi) sigma1 (liftTail K)) tau).1
      (lowerPath (physBranch z (rho1 xi) sigma1 (liftTail K)) tau).2 := by
  have hr : 0 < rho1 xi 0 := by
    simp only [rho1, rhoOf]
    positivity
  have hs : 0 < sigma1 0 := by simp [sigma1]
  have hv : 0 < vacMix (rho1 xi) sigma1 := by
    rw [vacMix_rho1_sigma1]
    linarith
  have hk : 0 < liftTail K (default : Fin 1) 0 0 := by
    simpa [liftTail] using hK
  let q := physBranch z (rho1 xi) sigma1 (liftTail K)
  have hq : IsRoot z (rho1 xi) sigma1 (tau • liftTail K)
      (q tau).1 (q tau).2 :=
    physBranch_isRoot z (rho1 xi) sigma1 (liftTail K)
      hz hr hs hv hk
      ⟨(zero_mem_Ioo z (rho1 xi) sigma1 (liftTail K)
        hz hr hs hv hk).1.le.trans ht.1, ht.2.le⟩
  have hstrength : tau • liftTail K =
      liftTail (fun t => tau * K t) := by
    funext t i j
    simp [liftTail, Pi.smul_apply, smul_eq_mul]
  rw [hstrength, ← lift_lowerTail (q tau).1,
    ← lift_lowerTail (q tau).2] at hq
  exact (isRoot_iff xi hxi1.ne z (fun t => tau * K t)
    (lowerTail (q tau).1) (lowerTail (q tau).2)).mp hq

/-- Even the positive physical theta-node series reaches strictly
beyond the first canonical loss in the one-tail pure fluid. Thus a
general upper bound by first physical loss would be false. -/
theorem theta_radius_strictly_after_canonical_loss
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : Fin 1 → ℝ) (hz : 0 < z 0) (hK : 0 < K 0)
    (M : MaximalBranch z (rho1 xi) sigma1 (liftTail K)
      (0, baseSeed z (rho1 xi) sigma1)) :
    ∃ thetaS : PowerSeries ℝ,
      HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z
          (lowerPath M.path tau).1 (lowerPath M.path tau).2 0)
        thetaS ∧
      M.bound < (FormalMultilinearSeries.ofScalars ℝ
        (fun n => PowerSeries.coeff n thetaS)).radius ∧
      ENNReal.ofReal (foldCoupling z (rho1 xi) sigma1 (liftTail K)) ≤
        (FormalMultilinearSeries.ofScalars ℝ
          (fun n => PowerSeries.coeff n thetaS)).radius ∧
      ∀ tau ∈ Set.Ico (0 : ℝ)
          (foldCoupling z (rho1 xi) sigma1 (liftTail K)),
        HasSum (fun n => PowerSeries.coeff n thetaS * tau ^ n)
          (actualTheta xi z
            (lowerPath (physBranch z (rho1 xi) sigma1 (liftTail K)) tau).1
            (lowerPath (physBranch z (rho1 xi) sigma1 (liftTail K)) tau).2 0) := by
  have hr : 0 < rho1 xi 0 := by
    simp only [rho1, rhoOf]
    positivity
  have hs : 0 < sigma1 0 := by simp [sigma1]
  have hv : 0 < vacMix (rho1 xi) sigma1 := by
    rw [vacMix_rho1_sigma1]
    linarith
  have hk : 0 < liftTail K (default : Fin 1) 0 0 := by
    simpa [liftTail] using hK
  have hzall : ∀ t : Fin 1, 0 < z t := by
    intro t
    simpa only [Subsingleton.elim t 0] using hz
  obtain ⟨thetaM, hthetaM, hposM⟩ :=
    maximalBranch_theta_taylor_nonnegative
      xi hxi0 hxi1 z K hzall
      (fun t => by simpa only [Subsingleton.elim t 0] using hK) M
  let q := physBranch z (rho1 xi) sigma1 (liftTail K)
  let p := lowerPath q
  obtain ⟨hp0, hpa, hpr⟩ :=
    explicit_branch_pure_hs_germ xi hxi0 hxi1 z K hz hK
  have hMQ := maximalPath_eventuallyEq_liftGerm
    xi hxi0 hxi1 z K hzall M p hp0 hpa hpr
  have hproj : lowerPath M.path =ᶠ[𝓝 (0 : ℝ)] p := by
    filter_upwards [hMQ] with tau ht
    unfold lowerPath
    rw [ht]
    rfl
  let fold := foldCoupling z (rho1 xi) sigma1 (liftTail K)
  have hfold : 0 < fold :=
    foldCoupling_pos z (rho1 xi) sigma1 (liftTail K) hz hr hs hv hk
  have hqa : AnalyticOnNhd ℝ q (Set.Ico 0 fold) :=
    physBranch_analyticOnNhd z (rho1 xi) sigma1 (liftTail K) hz hr hs hv hk
  have hpaOn : AnalyticOnNhd ℝ p (Set.Ico 0 fold) :=
    lowerPath_analyticOn q hqa
  let fM := fun tau => actualTheta xi z
    (lowerPath M.path tau).1 (lowerPath M.path tau).2 0
  let fE := fun tau => actualTheta xi z (p tau).1 (p tau).2 0
  have hfE : AnalyticOnNhd ℝ fE (Set.Ico 0 fold) := by
    intro tau ht
    exact actualTheta_analyticAt_of_amplitude_analyticAt
      xi hxi1.ne z hzall p tau (hpaOn tau ht) 0
  obtain ⟨thetaE, hthetaE⟩ :=
    exists_taylorPowerSeries fE (hfE 0 ⟨le_rfl, hfold⟩)
  have hfg : fM =ᶠ[𝓝 (0 : ℝ)] fE := by
    filter_upwards [hproj] with tau ht
    simp only [fM, fE, ht]
  have hEq : thetaM 0 = thetaE :=
    taylorPowerSeries_eq_of_eventually
      fM fE (thetaM 0) thetaE (hthetaM 0) hthetaE hfg
  have hposE : CoeffNonneg thetaE := by
    intro n
    rw [← hEq]
    exact hposM 0 n
  have hrad : ENNReal.ofReal fold ≤
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n => PowerSeries.coeff n thetaE)).radius :=
    taylor_radius_lower_bound_of_nonnegative_analytic_branch
      fE thetaE hthetaE hposE fold hfold hfE
  obtain ⟨hfinite, hbeforeFold⟩ :=
    maximal_bound_finite_before_fold
      z (rho1 xi) sigma1 (liftTail K) hz hr hs hv hk M
  have hstrict : M.bound < ENNReal.ofReal fold := by
    calc
      M.bound = ENNReal.ofReal M.bound.toReal :=
        (ENNReal.ofReal_toReal hfinite).symm
      _ < ENNReal.ofReal fold :=
        (ENNReal.ofReal_lt_ofReal_iff hfold).mpr hbeforeFold
  have hcoeff : (fun n => PowerSeries.coeff n thetaE) = jet fE := by
    funext n
    exact taylorPowerSeries_coeff_eq_jet fE thetaE hthetaE n
  have hsum : ∀ tau ∈ Set.Ico (0 : ℝ) fold,
      HasSum (fun n => PowerSeries.coeff n thetaE * tau ^ n)
        (actualTheta xi z (p tau).1 (p tau).2 0) := by
    intro tau ht
    have hradius : ENNReal.ofReal tau <
        (FormalMultilinearSeries.ofScalars ℝ (jet fE)).radius := by
      rw [← hcoeff]
      exact lt_of_lt_of_le
        ((ENNReal.ofReal_lt_ofReal_iff hfold).mpr ht.2) hrad
    have hjet := hasSum_jet_on_interval fE fold hfE tau ht hradius
    have hfun : (fun n => jet fE n * tau ^ n) =
        (fun n => PowerSeries.coeff n thetaE * tau ^ n) := by
      funext n
      rw [← congrFun hcoeff n]
    rw [hfun] at hjet
    exact hjet
  refine ⟨thetaM 0, hthetaM 0, ?_, ?_, ?_⟩
  · rw [hEq]
    exact hstrict.trans_le hrad
  · rw [hEq]
    exact hrad
  · intro tau ht
    rw [hEq]
    exact hsum tau ht

/-- A fully data-constructed physical counterexample to identifying
the first canonical instability with either the original-amplitude
or theta-node Taylor radius. Both radii extend strictly past it. -/
theorem exists_physical_single_tail_two_radii_after_loss
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : Fin 1 → ℝ) (hz : 0 < z 0) (hK : 0 < K 0) :
    ∃ M : MaximalBranch z (rho1 xi) sigma1 (liftTail K)
        (0, baseSeed z (rho1 xi) sigma1),
      M.bound < amplitudeRadius (branchCoefficients M.path) ∧
      AmplitudeHasSumBefore M.path M.bound ∧
      AmplitudeHasSumTo M.path
        (physBranch z (rho1 xi) sigma1 (liftTail K))
        (ENNReal.ofReal (foldCoupling z (rho1 xi) sigma1 (liftTail K))) ∧
      ∃ thetaS : PowerSeries ℝ,
        HasTaylorPowerSeriesAt
          (fun tau => actualTheta xi z
            (lowerPath M.path tau).1 (lowerPath M.path tau).2 0)
          thetaS ∧
        M.bound < (FormalMultilinearSeries.ofScalars ℝ
          (fun n => PowerSeries.coeff n thetaS)).radius ∧
        ENNReal.ofReal (foldCoupling z (rho1 xi) sigma1 (liftTail K)) ≤
          (FormalMultilinearSeries.ofScalars ℝ
            (fun n => PowerSeries.coeff n thetaS)).radius ∧
        ∀ tau ∈ Set.Ico (0 : ℝ)
            (foldCoupling z (rho1 xi) sigma1 (liftTail K)),
          FMSA.ExactMSA.MultiTail.IsRoot xi z
            (fun t => tau * K t)
            (lowerPath (physBranch z (rho1 xi) sigma1 (liftTail K)) tau).1
            (lowerPath (physBranch z (rho1 xi) sigma1 (liftTail K)) tau).2 ∧
          HasSum (fun n => PowerSeries.coeff n thetaS * tau ^ n)
            (actualTheta xi z
              (lowerPath (physBranch z (rho1 xi) sigma1 (liftTail K)) tau).1
              (lowerPath (physBranch z (rho1 xi) sigma1 (liftTail K)) tau).2 0) := by
  obtain ⟨M, hAmplitude, hSum, hFullSum, _hRoot⟩ :=
    exists_physical_single_tail_radius_after_canonical_loss
      xi hxi0 hxi1 z K hz hK
  obtain ⟨thetaS, hTheta, hRadius, hFoldRadius, hSumTheta⟩ :=
    theta_radius_strictly_after_canonical_loss
      xi hxi0 hxi1 z K hz hK M
  exact ⟨M, hAmplitude, hSum, hFullSum, thetaS, hTheta, hRadius,
    hFoldRadius, fun tau ht =>
      ⟨explicit_pure_branch_isRoot_before_fold
        xi hxi0 hxi1 z K hz hK tau ht,
        hSumTheta tau ht⟩⟩

end FMSA.Convergence.PureFluidSingleTailLossCounterexample

/-- info: 'FMSA.Convergence.PureFluidSingleTailLossCounterexample.exists_physical_single_tail_radius_after_canonical_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidSingleTailLossCounterexample.exists_physical_single_tail_radius_after_canonical_loss

/-- info: 'FMSA.Convergence.PureFluidSingleTailLossCounterexample.explicit_branch_pure_hs_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidSingleTailLossCounterexample.explicit_branch_pure_hs_germ

/-- info: 'FMSA.Convergence.PureFluidSingleTailLossCounterexample.explicit_pure_branch_isRoot_before_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidSingleTailLossCounterexample.explicit_pure_branch_isRoot_before_fold

/-- info: 'FMSA.Convergence.PureFluidSingleTailLossCounterexample.theta_radius_strictly_after_canonical_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidSingleTailLossCounterexample.theta_radius_strictly_after_canonical_loss

/-- info: 'FMSA.Convergence.PureFluidSingleTailLossCounterexample.exists_physical_single_tail_two_radii_after_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidSingleTailLossCounterexample.exists_physical_single_tail_two_radii_after_loss
