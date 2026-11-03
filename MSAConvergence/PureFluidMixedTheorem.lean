import MSAConvergence.PureFluidMixedAmplitude

set_option linter.style.header false

/-! All mixed Taylor coefficients of the pure-fluid hard-sphere germ in the tail strengths are
nonnegative, for arbitrary finite tails. On a positive ray every coefficient is strictly positive. -/

noncomputable section
open Filter Topology
open scoped ContDiff
namespace FMSA.Convergence.PureFluidMixedTheorem
open FMSA.Convergence.PureFluidMixedPicard FMSA.Convergence.PureFluidMixedRay
open FMSA.Convergence.PureFluidMixedAmplitude
open FMSA.Convergence.PureFluidFoldPath FMSA.Convergence.PureFluidFoldTheorem
open FMSA.Convergence.PureFluidFoldSigns FMSA.Convergence.PureFluidFoldBridge
open FMSA.Convergence.PureFluidSeriesEval
open FMSA.Convergence.PureFluidRFormalSolution FMSA.Convergence.PureFluidRLabelSubstitution
open FMSA.Convergence.PureFluidHFormalSolution FMSA.Convergence.PureFluidHPathFormalSubstitution
open FMSA.Convergence.PureFluidThetaCouplingTaylor
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidActualAnalyticGerm
open FMSA.Convergence.PureFluidExponentialSplit FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidNodeClosedForm
open FMSA.Paper.StableIntervalRadius
open FMSA.ExactMSA FMSA.ExactMSA.BSource

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The hard-sphere root as an analytic function of all tail strengths at once. -/
theorem exists_joint_germ (xi : ℝ) (hxi : xi ∈ Set.Ioo (0 : ℝ) 1) (z : T → ℝ) (hz : ∀ u, 0 < z u) :
    ∃ (Φ : (T → ℝ) → Pairs T) (P : FormalMultilinearSeries ℝ (T → ℝ) (Pairs T)),
      Φ 0 = ((fun _ => 0), fun u => G0 xi (z u)) ∧ HasFPowerSeriesAt Φ P 0 ∧
      ∀ᶠ K : T → ℝ in 𝓝 0, MultiTail.IsRoot xi z K (Φ K).1 (Φ K).2 := by
  have hF (u : T) : F0 xi (z u) ≠ 0 := by
    have h := bhF_base_ne_zero hxi (hz u)
    simpa [bhF, F0] using h
  set a : Pairs T := ((fun _ => 0), fun u => G0 xi (z u)) with ha
  set S := MultiTail.residual xi z (0 : T → ℝ) with hS
  have hinv0 : ((fderiv ℝ S ((0 : ℝ), a)).comp
      (ContinuousLinearMap.inr ℝ ℝ (Pairs T))).IsInvertible := by
    rw [hS, show a = ((0 : T → ℝ), fun u => G0 xi (z u)) from rfl,
      MultiTail.residual_partial_triangular]
    exact MultiTail.triangular_isInvertible _ hF _
  let Res : (T → ℝ) × Pairs T → Pairs T := fun x => MultiTail.residual xi z x.1 (1, x.2)
  have hRes : Res = fun x => S (0, x.2) - ((fun u => 2 * Real.pi * x.1 u / z u), (0 : T → ℝ)) := by
    funext x
    refine Prod.ext (funext fun u => ?_) (funext fun u => ?_)
    · simp [Res, S, MultiTail.residual]
    · simp [Res, S, MultiTail.residual]
  have hResAn : ∀ x, AnalyticAt ℝ Res x := fun x => by
    rw [hRes]
    refine AnalyticAt.sub (AnalyticAt.comp (g := S) (f := fun x : (T → ℝ) × Pairs T => (0, x.2))
      (residual_analyticAt xi z 0 (0, x.2)) (analyticAt_const.prod analyticAt_snd))
      (AnalyticAt.prod (analyticAt_pi_iff.mpr fun u => ?_) analyticAt_const)
    have h1 : AnalyticAt ℝ (fun y : (T → ℝ) × Pairs T => y.1 u) x :=
      analyticAt_pi_iff.mp analyticAt_fst u
    fun_prop (disch := exact h1)
  have hι : HasFDerivAt (fun y : Pairs T => ((0 : T → ℝ), y))
      (ContinuousLinearMap.inr ℝ (T → ℝ) (Pairs T)) a := hasFDerivAt_prodMk_right _ _
  have hι' : HasFDerivAt (fun y : Pairs T => ((0 : ℝ), y))
      (ContinuousLinearMap.inr ℝ ℝ (Pairs T)) a := hasFDerivAt_prodMk_right _ _
  have hd1 := (hResAn (0, a)).differentiableAt.hasFDerivAt.comp a hι
  have hd2 := (residual_analyticAt xi z 0 ((0 : ℝ), a)).differentiableAt.hasFDerivAt.comp a hι'
  have hfun : (Res ∘ fun y : Pairs T => ((0 : T → ℝ), y)) =
      (S ∘ fun y : Pairs T => ((0 : ℝ), y)) := by
    funext y
    refine Prod.ext (funext fun u => ?_) (funext fun u => ?_)
    · simp [Res, S, MultiTail.residual]
    · simp [Res, S, MultiTail.residual]
  have hJ : (fderiv ℝ Res (0, a)).comp (ContinuousLinearMap.inr ℝ (T → ℝ) (Pairs T)) =
      (fderiv ℝ S ((0 : ℝ), a)).comp (ContinuousLinearMap.inr ℝ ℝ (Pairs T)) := by
    rw [hfun] at hd1
    exact hd1.unique hd2
  have hi : ((fderiv ℝ Res (0, a)).comp
      (ContinuousLinearMap.inr ℝ (T → ℝ) (Pairs T))).IsInvertible := by
    rw [hJ]; exact hinv0
  have hc : ContDiffAt ℝ ω Res (0, a) := (hResAn (0, a)).contDiffAt
  have hb : Res (0, a) = 0 := by
    have h := MultiTail.residual_base z (0 : T → ℝ) hxi hz
    refine (congrFun hfun a).trans ?_
    exact h
  refine ⟨hc.implicitFunction (by simp) hi, ?_⟩
  have hqa : AnalyticAt ℝ (hc.implicitFunction (by simp) hi) 0 :=
    (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  obtain ⟨P, hP⟩ := hqa
  refine ⟨P, hc.implicitFunction_apply_self (by simp) hi, hP, ?_⟩
  filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with K hK
  have h0 := hK.trans hb
  have h1 := (residual_zero_iff xi z K (hc.implicitFunction (by simp) hi K).1
    (hc.implicitFunction (by simp) hi K).2 1).mp h0
  have e : (fun t => 1 * K t) = K := funext fun t => one_mul _
  rw [e] at h1
  exact h1

/-- The `n`-th term of the joint series along `K` is the Taylor coefficient along the ray. -/
theorem ray_taylor_of_joint {Φ : (T → ℝ) → Pairs T}
    {P : FormalMultilinearSeries ℝ (T → ℝ) (Pairs T)} (hP : HasFPowerSeriesAt Φ P 0) (K : T → ℝ) :
    (∀ t, HasTaylorPowerSeriesAt (fun τ : ℝ => (Φ (τ • K)).1 t)
      (PowerSeries.mk fun n => (P n fun _ => K).1 t)) ∧
    (∀ t, HasTaylorPowerSeriesAt (fun τ : ℝ => (Φ (τ • K)).2 t)
      (PowerSeries.mk fun n => (P n fun _ => K).2 t)) := by
  let u : ℝ →L[ℝ] (T → ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight K
  have hu : HasFPowerSeriesAt (Φ ∘ u) (P.compContinuousLinearMap u) 0 := by
    apply HasFPowerSeriesAt.compContinuousLinearMap
    simpa using hP
  obtain ⟨r, hr⟩ := hu
  constructor
  · intro t
    let π : Pairs T →L[ℝ] ℝ := (ContinuousLinearMap.proj t).comp (ContinuousLinearMap.fst ℝ _ _)
    refine ⟨π.compFormalMultilinearSeries (P.compContinuousLinearMap u),
      ⟨r, π.comp_hasFPowerSeriesOnBall hr⟩, fun n => ?_⟩
    simp [FormalMultilinearSeries.coeff, π, u, FormalMultilinearSeries.compContinuousLinearMap,
      ContinuousLinearMap.compFormalMultilinearSeries]
  · intro t
    let π : Pairs T →L[ℝ] ℝ := (ContinuousLinearMap.proj t).comp (ContinuousLinearMap.snd ℝ _ _)
    refine ⟨π.compFormalMultilinearSeries (P.compContinuousLinearMap u),
      ⟨r, π.comp_hasFPowerSeriesOnBall hr⟩, fun n => ?_⟩
    simp [FormalMultilinearSeries.coeff, π, u, FormalMultilinearSeries.compContinuousLinearMap,
      ContinuousLinearMap.compFormalMultilinearSeries]

section Signs

variable {xi : ℝ} {z : T → ℝ}

theorem alphaUnit_pos (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) :
    0 < alphaUnit xi z t :=
  physicalAlpha_pos xi hxi0 hxi1 z _ hz (fun _ => one_pos) t

theorem kappaOf_pos (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) :
    0 < kappaOf xi z t := hardKappa_pos xi (z t) hxi0 hxi1 (hz t)

theorem thetaK_nn (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) :
    NN (thetaK xi z t) :=
  thetaM_nn hz (fun u => (alphaUnit_pos hxi0 hxi1 hz u).le)
    (fun u => (kappaOf_pos hxi0 hxi1 hz u).le) t

theorem rK_nn (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) : NN (rK xi z t) :=
  nn_subst (thetaK_constantCoeff xi z) (thetaK_nn hxi0 hxi1 hz) (RSeries_nn z hz t)

theorem hK_nn (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) : NN (hK xi z t) :=
  nn_subst (thetaK_constantCoeff xi z) (thetaK_nn hxi0 hxi1 hz) fun m => by
    simpa only [physicalH, one_div] using physical_HSeries_coeff_nonneg z hz t m

theorem qK_nn (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) : NN (qK xi z t) :=
  nn_inv (by simp [rK_constantCoeff])
    (nn_mul (nn_C (kappaOf_pos hxi0 hxi1 hz t).le) (rK_nn hxi0 hxi1 hz t))

/-- All mixed coefficients of `D_t` are nonnegative. -/
theorem dK_nn (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) : NN (dK xi z t) := by
  have hF0 : 0 < F0 xi (z t) := lt_trans one_pos (actual_F0_gt_one xi (z t) hxi0 hxi1 (hz t))
  exact nn_mul (nn_C (mul_nonneg (div_pos hF0 (rhoOf_pos hxi0)).le
    (alphaUnit_pos hxi0 hxi1 hz t).le)) (nn_mul (nn_X t)
      (nn_mul (hK_nn hxi0 hxi1 hz t) (qK_nn hxi0 hxi1 hz t)))

/-- A monomial of `D_t` without `K_t` vanishes. -/
theorem dK_coeff_eq_zero (t : T) {m : T →₀ ℕ} (hm : m t = 0) :
    MvPowerSeries.coeff m (dK xi z t) = 0 := by
  unfold dK
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_mul]
  rw [Finset.sum_eq_zero, mul_zero]
  intro p hp
  rw [MvPowerSeries.coeff_X]
  split_ifs with h
  · have hs := Finset.mem_antidiagonal.mp hp
    have : m t = p.1 t + p.2 t := by rw [← hs]; rfl
    rw [h] at this
    simp at this
    omega
  · simp

/-- All mixed coefficients of `G_t` beyond the hard-sphere value are nonnegative. -/
theorem gK_nn (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) {m : T →₀ ℕ}
    (hm : m ≠ 0) : 0 ≤ MvPowerSeries.coeff m (gK xi z t) := by
  have hF0 : 0 < F0 xi (z t) := lt_trans one_pos (actual_F0_gt_one xi (z t) hxi0 hxi1 (hz t))
  have hρ := rhoOf_pos hxi0
  unfold gK
  rw [map_add, MvPowerSeries.coeff_C, if_neg hm, zero_add, MvPowerSeries.coeff_C_mul]
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (nn_mul (rK_nn hxi0 hxi1 hz t) (qK_nn hxi0 hxi1 hz t) m)

end Signs

/-- **Mixed coefficients.** For every finite set of positive rates, the hard-sphere root is an
analytic function `Φ` of all tail strengths, and the `n`-th term of its Taylor series at `K` is a
polynomial in `K` whose monomial coefficients are those of `dK`, `gK`. They are nonnegative, those of
`G_t` beyond the hard-sphere value, and monomials of `D_t` without `K_t` vanish. -/
theorem mixed_coefficients_nonneg (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1) (z : T → ℝ)
    (hz : ∀ t, 0 < z t) :
    ∃ (Φ : (T → ℝ) → Pairs T) (P : FormalMultilinearSeries ℝ (T → ℝ) (Pairs T)),
      Φ 0 = ((fun _ => 0), fun u => G0 xi (z u)) ∧ HasFPowerSeriesAt Φ P 0 ∧
      (∀ᶠ K : T → ℝ in 𝓝 0, MultiTail.IsRoot xi z K (Φ K).1 (Φ K).2) ∧
      (∀ t m, 0 ≤ MvPowerSeries.coeff m (dK xi z t)) ∧
      (∀ t (m : T →₀ ℕ), m t = 0 → MvPowerSeries.coeff m (dK xi z t) = 0) ∧
      (∀ t (m : T →₀ ℕ), m ≠ 0 → 0 ≤ MvPowerSeries.coeff m (gK xi z t)) ∧
      ∀ (K : T → ℝ) (n : ℕ) (t : T),
        (P n fun _ => K).1 t = (∑ m ∈ Finset.univ.finsuppAntidiag n,
          MvPowerSeries.coeff m (dK xi z t) * m.prod fun u k => K u ^ k) ∧
        (P n fun _ => K).2 t = ∑ m ∈ Finset.univ.finsuppAntidiag n,
          MvPowerSeries.coeff m (gK xi z t) * m.prod fun u k => K u ^ k := by
  obtain ⟨Φ, P, hΦ0, hP, hroot⟩ := exists_joint_germ xi ⟨hxi0, hxi1⟩ z hz
  refine ⟨Φ, P, hΦ0, hP, hroot, dK_nn hxi0 hxi1 hz, fun t m hm => dK_coeff_eq_zero t hm,
    fun t m hm => gK_nn hxi0 hxi1 hz t hm, fun K n t => ?_⟩
  obtain ⟨p, hp0, hpa, hpr, hD, hG⟩ := exists_ray_germ xi hxi0 hxi1 z K hz
  have hu : Tendsto (fun τ : ℝ => τ • K) (𝓝 0) (𝓝 0) := by
    have : Continuous fun τ : ℝ => τ • K := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have hcont : ContinuousAt (fun τ : ℝ => Φ (τ • K)) 0 := by
    refine ContinuousAt.comp (g := Φ) (f := fun τ : ℝ => τ • K) ?_ (continuous_id.smul
      continuous_const).continuousAt
    simpa using hP.analyticAt.continuousAt
  have hrr : ∀ᶠ τ : ℝ in 𝓝 0, MultiTail.IsRoot xi z (fun t => τ * K t)
      (Φ (τ • K)).1 (Φ (τ • K)).2 := hu.eventually hroot
  have hgerm := seed_germ_unique xi ⟨hxi0, hxi1⟩ z K hz (p := fun τ : ℝ => Φ (τ • K)) (q := p)
    (by simpa using hΦ0) hp0 hcont hpa.continuousAt hrr hpr
  obtain ⟨hTD, hTG⟩ := ray_taylor_of_joint hP K
  have e1 := taylorPowerSeries_eq_of_eventually _ _ _ _ (hTD t) (hD t) (by
    filter_upwards [hgerm] with τ h
    exact congrFun (congrArg Prod.fst h) t)
  have e2 := taylorPowerSeries_eq_of_eventually _ _ _ _ (hTG t) (hG t) (by
    filter_upwards [hgerm] with τ h
    exact congrFun (congrArg Prod.snd h) t)
  constructor
  · rw [← coeff_res, ← e1, PowerSeries.coeff_mk]
  · rw [← coeff_res, ← e2, PowerSeries.coeff_mk]

/-- A term of the substitution bounds its coefficient from below. -/
theorem coeff_subst_ge {a : T → PowerSeries ℝ} (h0 : ∀ t, PowerSeries.constantCoeff (a t) = 0)
    (ha : ∀ t, CN (a t)) {f : MvPowerSeries T ℝ} (hf : NN f) (m : T →₀ ℕ) (n : ℕ) :
    MvPowerSeries.coeff m f * PowerSeries.coeff n (m.prod fun t k => a t ^ k) ≤
      PowerSeries.coeff n (MvPowerSeries.subst a f) := by
  classical
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  change _ ≤ MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.subst a f)
  rw [MvPowerSeries.coeff_subst hs]
  have hfin := MvPowerSeries.coeff_subst_finite hs f (Finsupp.single () n)
  have hnn : ∀ d : T →₀ ℕ, 0 ≤ MvPowerSeries.coeff d f •
      MvPowerSeries.coeff (Finsupp.single () n) (d.prod fun t k => a t ^ k) := fun d => by
    simpa only [smul_eq_mul, PowerSeries.coeff] using
      mul_nonneg (hf d) (PureFluidPositiveSubstitution.coeffNonneg_finsupp_prod a ha d n)
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by simp)]
  by_cases hm : MvPowerSeries.coeff m f *
      PowerSeries.coeff n (m.prod fun t k => a t ^ k) = 0
  · rw [hm]
    exact Finset.sum_nonneg fun d _ => hnn d
  · have hmem : m ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hm
    exact Finset.single_le_sum (f := fun d => MvPowerSeries.coeff d f •
      MvPowerSeries.coeff (Finsupp.single () n) (d.prod fun t k => a t ^ k))
      (fun d _ => hnn d) hmem

/-- A lower bound by `β X` passes to powers. -/
theorem coeff_pow_ge {A : PowerSeries ℝ} {β : ℝ} (hβ : 0 ≤ β) (hA : CN A)
    (hd : CN (A - PowerSeries.C β * PowerSeries.X)) (n : ℕ) :
    β ^ n ≤ PowerSeries.coeff n (A ^ n) := by
  have hX : ∀ k, CN (PowerSeries.C (β ^ k) * PowerSeries.X ^ k : PowerSeries ℝ) := fun k =>
    cn_mul (cn_C (pow_nonneg hβ k)) (PureFluidPositiveSubstitution.coeffNonneg_pow _ cn_X k)
  have hmain : ∀ k, CN (A ^ k - PowerSeries.C (β ^ k) * PowerSeries.X ^ k) := by
    intro k
    induction k with
    | zero =>
      intro m
      simp
    | succ k ih =>
      have heq : A ^ (k + 1) - PowerSeries.C (β ^ (k + 1)) * PowerSeries.X ^ (k + 1) =
          (A ^ k - PowerSeries.C (β ^ k) * PowerSeries.X ^ k) * A +
            PowerSeries.C (β ^ k) * PowerSeries.X ^ k *
              (A - PowerSeries.C β * PowerSeries.X) := by
        rw [pow_succ β, map_mul]
        ring
      rw [heq]
      exact cn_add (cn_mul ih hA) (cn_mul (hX k) hd)
  have h := hmain n n
  rw [map_sub, PowerSeries.coeff_C_mul_X_pow, if_pos rfl] at h
  linarith

section Strict

variable {xi : ℝ} {z K : T → ℝ}

/-- On a positive ray every coefficient of `r_t` from order one is strictly positive. -/
theorem ray_r_coeff_pos (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (hKp : ∀ t, 0 < K t)
    (t : T) {n : ℕ} (hn : 1 ≤ n) : 0 < PowerSeries.coeff n (res K (rK xi z t)) := by
  have hK' : ∀ u, 0 ≤ K u := fun u => (hKp u).le
  have hθ0 : ∀ u, PowerSeries.constantCoeff (res K (thetaK xi z u)) = 0 := fun u =>
    MvPowerSeries.constantCoeff_subst_eq_zero (ray_hasSubst K) (ray_constantCoeff K)
      (thetaK_constantCoeff xi z u)
  have hθCN : ∀ u, CN (res K (thetaK xi z u)) := fun u =>
    res_coeffNonneg hK' (thetaK_nn hxi0 hxi1 hz u)
  have hα : 0 < physicalAlpha xi z K t := physicalAlpha_pos xi hxi0 hxi1 z K hz hKp t
  have hκ : 0 < hardKappa xi (z t) := hardKappa_pos xi (z t) hxi0 hxi1 (hz t)
  set R1 := res K (rK xi z t) with hR1
  have hR1e : MvPowerSeries.subst (fun u => res K (thetaK xi z u)) (RSeries z t) = R1 :=
    (res_r xi z K t).symm
  have hR0 : PowerSeries.constantCoeff R1 = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero (ray_hasSubst K) (ray_constantCoeff K)
      (rK_constantCoeff xi z t)
  have hRCN : CN R1 := res_coeffNonneg hK' (rK_nn hxi0 hxi1 hz t)
  set q := (1 - PowerSeries.C (hardKappa xi (z t)) * R1)⁻¹ with hq
  have hqm : (1 - PowerSeries.C (hardKappa xi (z t)) * R1) * q = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp [hR0])
  have hqCN : CN q := by
    have := res_coeffNonneg hK' (qK_nn hxi0 hxi1 hz t)
    rw [res_q] at this
    exact this
  have hE : q - 1 = PowerSeries.C (hardKappa xi (z t)) * (R1 * q) := by
    linear_combination hqm
  have hECN : CN (q - 1) := by
    rw [hE]
    exact cn_mul (cn_C hκ.le) (cn_mul hRCN hqCN)
  have hfix := res_theta_fixed xi z K t
  rw [hR1e, ← hq] at hfix
  have hd : CN (res K (thetaK xi z t) -
      PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X) := by
    have heq : res K (thetaK xi z t) -
        PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X =
        PowerSeries.C (physicalAlpha xi z K t) * (PowerSeries.X *
          ((q - 1) * (q - 1) + (q - 1) + (q - 1))) := by
      rw [hfix]
      ring
    rw [heq]
    exact cn_mul (cn_C hα.le) (cn_mul cn_X (cn_add (cn_add (cn_mul hECN hECN) hECN) hECN))
  have hpow := coeff_pow_ge hα.le (hθCN t) hd n
  have hm : (Finsupp.single t n : T →₀ ℕ) ≠ 0 := by
    simpa [Finsupp.single_eq_zero] using (by omega : n ≠ 0)
  have hcoef := RSeries_coeff_pos_all (Finsupp.single t n) hm z hz t
  have hge := coeff_subst_ge hθ0 hθCN (RSeries_nn z hz t) (Finsupp.single t n) n
  have hp : (Finsupp.single t n).prod (fun u k => res K (thetaK xi z u) ^ k) =
      res K (thetaK xi z t) ^ n := Finsupp.prod_single_index (pow_zero _)
  rw [hp, hR1e] at hge
  exact lt_of_lt_of_le (mul_pos hcoef (lt_of_lt_of_le (pow_pos hα n) hpow)) hge

/-- On a positive ray every coefficient of `D_t` and `G_t` from order one is strictly positive. -/
theorem ray_coeff_pos (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (hKp : ∀ t, 0 < K t)
    (t : T) {n : ℕ} (hn : 1 ≤ n) :
    0 < PowerSeries.coeff n (res K (dK xi z t)) ∧
      0 < PowerSeries.coeff n (res K (gK xi z t)) := by
  have hK' : ∀ u, 0 ≤ K u := fun u => (hKp u).le
  have hκ : 0 < hardKappa xi (z t) := hardKappa_pos xi (z t) hxi0 hxi1 (hz t)
  have hρ := rhoOf_pos hxi0
  have hF0 : 0 < F0 xi (z t) := lt_trans one_pos (actual_F0_gt_one xi (z t) hxi0 hxi1 (hz t))
  set R1 := res K (rK xi z t) with hR1
  set H1 := res K (hK xi z t) with hH1
  have hR0 : PowerSeries.constantCoeff R1 = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero (ray_hasSubst K) (ray_constantCoeff K)
      (rK_constantCoeff xi z t)
  have hRCN : CN R1 := res_coeffNonneg hK' (rK_nn hxi0 hxi1 hz t)
  have hHCN : CN H1 := res_coeffNonneg hK' (hK_nn hxi0 hxi1 hz t)
  set q := res K (qK xi z t) with hq
  have hqi : q = (1 - PowerSeries.C (hardKappa xi (z t)) * R1)⁻¹ := res_q xi z K t
  have hqm : (1 - PowerSeries.C (hardKappa xi (z t)) * R1) * q = 1 := by
    rw [hqi]
    exact PowerSeries.mul_inv_cancel _ (by simp [hR0])
  have hqCN : CN q := res_coeffNonneg hK' (qK_nn hxi0 hxi1 hz t)
  have hE : q - 1 = PowerSeries.C (hardKappa xi (z t)) * (R1 * q) := by
    linear_combination hqm
  have hECN : CN (q - 1) := by
    rw [hE]
    exact cn_mul (cn_C hκ.le) (cn_mul hRCN hqCN)
  have hRq : ∀ k, 1 ≤ k → 0 < PowerSeries.coeff k (R1 * q) := fun k hk => by
    have heq : R1 * q = R1 + R1 * (q - 1) := by ring
    rw [heq, map_add]
    exact add_pos_of_pos_of_nonneg (ray_r_coeff_pos hxi0 hxi1 hz hKp t hk) (cn_mul hRCN hECN k)
  have hqpos : ∀ k, 0 < PowerSeries.coeff k q := fun k => by
    have heq : q = 1 + PowerSeries.C (hardKappa xi (z t)) * (R1 * q) := by
      linear_combination hE
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have h1 := hECN 0
      rw [map_sub, PowerSeries.coeff_one, if_pos rfl] at h1
      linarith
    · rw [heq, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one, if_neg (by omega), zero_add]
      exact mul_pos hκ (hRq k h)
  constructor
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hθ0 : ∀ u, PowerSeries.constantCoeff (res K (thetaK xi z u)) = 0 := fun u =>
      MvPowerSeries.constantCoeff_subst_eq_zero (ray_hasSubst K) (ray_constantCoeff K)
        (thetaK_constantCoeff xi z u)
    have hsys := eqH_of_path_system
      (HSeries_subst_path_system (fun s u => (z s + z u)⁻¹) _ hθ0) t
    have hH0 : PowerSeries.coeff 0 H1 = 1 := by
      have h := congrArg PowerSeries.constantCoeff hsys
      have hHe : H1 = MvPowerSeries.subst (fun u => res K (thetaK xi z u))
          (HSeries (fun s u => (z s + z u)⁻¹) t) := res_H xi z K t
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hHe]
      simpa [map_sum, hθ0] using h
    have hW : 0 < PowerSeries.coeff k (H1 * q) := by
      rw [PowerSeries.coeff_mul]
      have hmem : ((0, k) : ℕ × ℕ) ∈ Finset.antidiagonal k := by simp
      have hle := Finset.single_le_sum (f := fun p : ℕ × ℕ =>
        PowerSeries.coeff p.1 H1 * PowerSeries.coeff p.2 q)
        (fun p _ => mul_nonneg (hHCN p.1) (hqCN p.2)) hmem
      refine lt_of_lt_of_le ?_ hle
      simpa [hH0] using hqpos k
    have hform : res K (dK xi z t) =
        PowerSeries.C (F0 xi (z t) / rhoOf xi * alphaUnit xi z t * K t) * PowerSeries.X *
          (H1 * q) := by
      unfold dK
      rw [res_mul, res_C, res_mul, res_X, res_mul, ray]
      simp only [map_mul]
      ring
    rw [hform, PureFluidThetaFixedPointUniqueness.coeff_C_X_mul_succ]
    exact mul_pos (mul_pos (mul_pos (div_pos hF0 hρ) (alphaUnit_pos hxi0 hxi1 hz t)) (hKp t)) hW
  · have hform : res K (gK xi z t) = PowerSeries.C (hardG0Node xi (z t)) +
        PowerSeries.C (2 * Real.pi * rhoOf xi * (F0 xi (z t)) ^ 2)⁻¹ * (R1 * q) := by
      unfold gK
      rw [res_add, res_C, res_mul, res_C, res_mul]
    rw [hform, map_add, PowerSeries.coeff_C, if_neg (by omega), zero_add,
      PowerSeries.coeff_C_mul]
    exact mul_pos (inv_pos.mpr (by positivity)) (hRq n hn)

end Strict

/-- The strict sign for the Taylor series of any root germ through the hard-sphere seed, in particular
the germ of `taylor_radius_is_fold`. -/
theorem ray_germ_coeff_pos {xi : ℝ} {z K : T → ℝ} (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (hz : ∀ t, 0 < z t) (hKp : ∀ t, 0 < K t) {p : ℝ → Pairs T}
    (hp0 : p 0 = ((fun _ => 0), fun u => G0 xi (z u))) (hp : ContinuousAt p 0)
    (hr : ∀ᶠ τ : ℝ in 𝓝 0, MultiTail.IsRoot xi z (fun t => τ * K t) (p τ).1 (p τ).2) (t : T)
    {DS GS : PowerSeries ℝ} (hD : HasTaylorPowerSeriesAt (fun τ => (p τ).1 t) DS)
    (hG : HasTaylorPowerSeriesAt (fun τ => (p τ).2 t) GS) {n : ℕ} (hn : 1 ≤ n) :
    0 < PowerSeries.coeff n DS ∧ 0 < PowerSeries.coeff n GS := by
  obtain ⟨p', hp0', hpa', hr', hD', hG'⟩ := exists_ray_germ xi hxi0 hxi1 z K hz
  have hg := seed_germ_unique xi ⟨hxi0, hxi1⟩ z K hz hp0 hp0' hp hpa'.continuousAt hr hr'
  have e1 := taylorPowerSeries_eq_of_eventually _ _ _ _ hD (hD' t) (by
    filter_upwards [hg] with τ h
    exact congrFun (congrArg Prod.fst h) t)
  have e2 := taylorPowerSeries_eq_of_eventually _ _ _ _ hG (hG' t) (by
    filter_upwards [hg] with τ h
    exact congrFun (congrArg Prod.snd h) t)
  rw [e1, e2]
  exact ray_coeff_pos hxi0 hxi1 hz hKp t hn


end FMSA.Convergence.PureFluidMixedTheorem

/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.exists_joint_germ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.exists_joint_germ
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.ray_taylor_of_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.ray_taylor_of_joint
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.alphaUnit_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.alphaUnit_pos
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.kappaOf_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.kappaOf_pos
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.thetaK_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.thetaK_nn
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.rK_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.rK_nn
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.hK_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.hK_nn
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.qK_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.qK_nn
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.dK_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.dK_nn
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.dK_coeff_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.dK_coeff_eq_zero
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.gK_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.gK_nn
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.mixed_coefficients_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.mixed_coefficients_nonneg
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.coeff_subst_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.coeff_subst_ge
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.coeff_pow_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.coeff_pow_ge
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.ray_r_coeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.ray_r_coeff_pos
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.ray_coeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.ray_coeff_pos
/-- info: 'FMSA.Convergence.PureFluidMixedTheorem.ray_germ_coeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedTheorem.ray_germ_coeff_pos
