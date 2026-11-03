import MSAConvergence.PureFluidFoldBridge
import MSAConvergence.PureFluidFoldClosedForm
import MSAConvergence.PureFluidFoldRadius
import MSAConvergence.PureFluidMaximalThetaTransfer

set_option linter.style.header false

/-! The original-amplitude path rebuilt from the node series, analytic on the real ray up to the
joint radius `R`, and a genuine MSA root there by the identity theorem. No canonicity is used. -/

noncomputable section
open Filter Topology Set
open scoped ENNReal NNReal
namespace FMSA.Convergence.PureFluidFoldPath
open FMSA.Convergence.PureFluidFoldCore FMSA.Convergence.PureFluidSeriesEval
open FMSA.Convergence.PureFluidFoldRadius FMSA.Convergence.PureFluidFoldClosedForm
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidRFormalPath FMSA.Convergence.PureFluidRActualNodeBridge
open FMSA.Convergence.PureFluidActualThetaEquation FMSA.Convergence.PureFluidActualAnalyticGerm
open FMSA.Convergence.PureFluidActualNodeGerm FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidActualDressingCoordinates FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.PureFluidThetaCouplingTaylor FMSA.Convergence.PureFluidPositiveSubstitution
open FMSA.Convergence.PureFluidHActualNodeBridge FMSA.Convergence.PureFluidNodeClosedForm
open FMSA.Convergence.PureFluidThetaPringsheimRoute FMSA.Convergence.PureFluidScalarMixtureBridge
open FMSA.Convergence.PureFluidMaximalThetaTransfer FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidHardSphereUnimodular FMSA.Convergence.PureFluidExponentialSplit
open FMSA.ExactMSA

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The factor `f_t = 1 - κ_t r_t` from the series. -/
def fac (xi : ℝ) (z : T → ℝ) (RS : T → PowerSeries ℝ) (τ : ℝ) (t : T) : ℝ :=
  1 - hardKappa xi (z t) * ev τ (RS t)

/-- `D` rebuilt from the nodes. -/
def ampD (xi : ℝ) (z : T → ℝ) (θS HS RS : T → PowerSeries ℝ) (τ : ℝ) (t : T) : ℝ :=
  F0 xi (z t) * (ev τ (θS t) * ev τ (HS t)) * fac xi z RS τ t / rhoOf xi

/-- `G` rebuilt from the nodes. -/
def ampG (xi : ℝ) (z : T → ℝ) (RS : T → PowerSeries ℝ) (τ : ℝ) (t : T) : ℝ :=
  hardG0Node xi (z t) + ev τ (RS t) / fac xi z RS τ t / (2 * Real.pi * rhoOf xi * (F0 xi (z t)) ^ 2)

/-- The rebuilt path. -/
def path (xi : ℝ) (z : T → ℝ) (θS HS RS : T → PowerSeries ℝ) (τ : ℝ) : (T → ℝ) × (T → ℝ) :=
  (ampD xi z θS HS RS τ, ampG xi z RS τ)

/-- The data from the bridge theorem. -/
structure Germ (xi : ℝ) (z K : T → ℝ) (p : ℝ → (T → ℝ) × (T → ℝ))
    (θS HS RS : T → PowerSeries ℝ) : Prop where
  hxi0 : 0 < xi
  hxi1 : xi < 1
  hp0 : p 0 = ((fun _ => 0), fun t => G0 xi (z t))
  hpa : AnalyticAt ℝ p 0
  hθ : ∀ t, HasTaylorPowerSeriesAt (fun τ => actualTheta xi z (p τ).1 (p τ).2 t) (θS t)
  hH : ∀ t, HasTaylorPowerSeriesAt (fun τ => actualH xi z (p τ).1 (p τ).2 (z t)) (HS t)
  hR : ∀ t, HasTaylorPowerSeriesAt (fun τ => actualNodeR xi z (p τ).1 (p τ).2 t) (RS t)
  F : NodeFamily z (physicalAlpha xi z K) (fun t => hardKappa xi (z t)) θS HS RS
  hroot : ∀ᶠ τ : ℝ in 𝓝 0, MultiTail.IsRoot xi z (fun t => τ * K t) (p τ).1 (p τ).2

variable {xi : ℝ} {z K : T → ℝ} {p : ℝ → (T → ℝ) × (T → ℝ)} {θS HS RS : T → PowerSeries ℝ}

theorem rhoOf_pos (hxi0 : 0 < xi) : 0 < rhoOf xi := by
  unfold rhoOf; positivity

/-- Near zero the rebuilt path is the germ. -/
theorem Germ.path_eventuallyEq (G : Germ xi z K p θS HS RS) :
    path xi z θS HS RS =ᶠ[𝓝 0] p := by
  have hz := G.F.hz
  have hU := actualU_nodes_nonzero_eventually_of_continuous_seed
    xi z G.hxi1.ne hz p (fun t => G0 xi (z t)) G.hpa.continuousAt G.hp0
  have hF := actual_factor_nodes_nonzero_eventually_of_continuous_seed
    xi G.hxi0 G.hxi1 z hz p (fun t => G0 xi (z t)) G.hpa.continuousAt G.hp0
  have hevθ : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ t, ev τ (θS t) = actualTheta xi z (p τ).1 (p τ).2 t :=
    eventually_all.mpr fun t => HasTaylorPowerSeriesAt.ev_eventuallyEq (G.hθ t)
  have hevH : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ t, ev τ (HS t) = actualH xi z (p τ).1 (p τ).2 (z t) :=
    eventually_all.mpr fun t => HasTaylorPowerSeriesAt.ev_eventuallyEq (G.hH t)
  have hevR : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ t, ev τ (RS t) = actualNodeR xi z (p τ).1 (p τ).2 t :=
    eventually_all.mpr fun t => HasTaylorPowerSeriesAt.ev_eventuallyEq (G.hR t)
  filter_upwards [G.hroot, hU, hF, hevθ, hevH, hevR] with τ hr hu hf h1 h2 h3
  have hρ := rhoOf_pos G.hxi0
  have hF0 : ∀ t, F0 xi (z t) ≠ 0 := fun t =>
    ne_of_gt (lt_trans one_pos (actual_F0_gt_one xi (z t) G.hxi0 G.hxi1 (hz t)))
  have hD := actual_D_closed_all_rates xi z (fun t => τ * K t) (p τ).1 (p τ).2 G.hxi0 G.hxi1 hz hr hf hu
  have hG := actual_G_closed_all_rates xi z (fun t => τ * K t) (p τ).1 (p τ).2 G.hxi0 G.hxi1 hz hr hf hu
  refine Prod.ext (funext fun t => ?_) (funext fun t => ?_)
  · have hw : ev τ (θS t) * ev τ (HS t) = actualWeight xi z (p τ).1 (p τ).2 t := by
      rw [h1, h2]
      unfold actualTheta actualH
      field_simp [hu t]
    change F0 xi (z t) * (ev τ (θS t) * ev τ (HS t)) * fac xi z RS τ t / rhoOf xi = (p τ).1 t
    rw [hw, fac, h3, eq_comm, eq_div_iff hρ.ne', mul_comm, hD t]
  · change hardG0Node xi (z t) + ev τ (RS t) / fac xi z RS τ t /
      (2 * Real.pi * rhoOf xi * (F0 xi (z t)) ^ 2) = (p τ).2 t
    have hne : 2 * Real.pi * rhoOf xi * (F0 xi (z t)) ^ 2 ≠ 0 := by
      have := hF0 t; positivity
    rw [fac, h3, ← hG t, mul_div_cancel_left₀ _ hne]
    ring


abbrev Pairs (T : Type*) := (T → ℝ) × (T → ℝ)

theorem pair_D_an (t : T) (x : Pairs T) : AnalyticAt ℝ (fun y : Pairs T => y.1 t) x :=
  analyticAt_pi_iff.mp analyticAt_fst t

theorem pair_G_an (t : T) (x : Pairs T) : AnalyticAt ℝ (fun y : Pairs T => y.2 t) x :=
  analyticAt_pi_iff.mp analyticAt_snd t

/-- The BH weight is entire in the amplitudes. -/
theorem weight_an (xi : ℝ) (z : T → ℝ) (t : T) (x : Pairs T) :
    AnalyticAt ℝ (fun y : Pairs T => actualWeight xi z y.1 y.2 t) x := by
  have hD := pair_D_an t x
  have hG := pair_G_an t x
  unfold actualWeight tailAlpha MultiTail.W MultiTail.C gam
  fun_prop (disch := first | exact hD | exact hG | positivity)

/-- The node value of `U` is entire in the amplitudes. -/
theorem nodeU_an (xi : ℝ) (hxi : xi ≠ 1) (z : T → ℝ) (hz : ∀ t, 0 < z t) (s : T) (x : Pairs T) :
    AnalyticAt ℝ (fun y : Pairs T => actualU xi z y.1 y.2 (z s)) x := by
  have hfun : (fun y : Pairs T => actualU xi z y.1 y.2 (z s)) =
      fun y => 1 - ∑ t, actualWeight xi z y.1 y.2 t / (z s + z t) := by
    funext y
    rw [actualU_eq_candidateU_explicit xi z y.1 y.2 hxi (fun t => (hz t).ne') (z s) (hz s).ne'
      (fun t => (add_pos (hz s) (hz t)).ne')]
    rfl
  rw [hfun]
  refine analyticAt_const.sub ?_
  have hs : AnalyticAt ℝ (∑ t : T,
      fun y : Pairs T => actualWeight xi z y.1 y.2 t / (z s + z t)) x :=
    Finset.analyticAt_sum _ fun t _ => (weight_an xi z t x).div_const
  convert hs using 1
  funext y
  simp only [Finset.sum_apply]

/-- The node value of `g` is entire in the amplitudes. -/
theorem nodeG_an (xi : ℝ) (z : T → ℝ) (s : T) (x : Pairs T) :
    AnalyticAt ℝ (fun y : Pairs T => actualG xi z y.1 y.2 (z s)) x := by
  have hD : ∀ t, AnalyticAt ℝ (fun y : Pairs T => y.1 t) x := fun t => pair_D_an t x
  have hG : ∀ t, AnalyticAt ℝ (fun y : Pairs T => y.2 t) x := fun t => pair_G_an t x
  unfold actualG dressingG dressingD rationalPart exponentialPart MultiTail.amplitudeA
    MultiTail.amplitudeQp MultiTail.momentM MultiTail.momentN MultiTail.W MultiTail.C Mtil Ntil gam
  dsimp only
  fun_prop (disch := first | exact hD _ | exact hG _ | positivity)


theorem residual_zero_iff (xi : ℝ) (z K D G : T → ℝ) (τ : ℝ) :
    MultiTail.residual xi z K (τ, (D, G)) = 0 ↔
      MultiTail.IsRoot xi z (fun t => τ * K t) D G := by
  constructor
  · intro h
    constructor
    · intro u
      have hh := congrFun (congrArg Prod.fst h) u
      simp only [MultiTail.residual, Prod.fst_zero, Pi.zero_apply, sub_eq_zero] at hh
      rw [hh]; ring
    · intro u
      have hh := congrFun (congrArg Prod.snd h) u
      simpa only [MultiTail.residual, Prod.snd_zero, Pi.zero_apply, sub_eq_zero] using hh
  · intro h
    refine Prod.ext (funext fun u => ?_) (funext fun u => ?_)
    · simp only [MultiTail.residual, Prod.fst_zero, Pi.zero_apply, sub_eq_zero]
      rw [h.1 u]; ring
    · simp only [MultiTail.residual, Prod.snd_zero, Pi.zero_apply, sub_eq_zero]
      exact h.2 u

/-- Identity theorem on the ray, from a germ at the origin. -/
theorem eqOn_of_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : ℝ} (hR : 0 < R)
    {f g : ℝ → E} (hf : ∀ τ ∈ Ico 0 R, AnalyticAt ℝ f τ) (hg : ∀ τ ∈ Ico 0 R, AnalyticAt ℝ g τ)
    (h : f =ᶠ[𝓝 0] g) : EqOn f g (Ico 0 R) :=
  AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg (convex_Ico 0 R).isPreconnected
    ⟨le_rfl, hR⟩ h

/-- Passing an equality from `[0,R)` to `R`. -/
theorem endpoint_eq {E : Type*} [TopologicalSpace E] [T2Space E] {R : ℝ} (hR : 0 < R) {f g : ℝ → E}
    (hf : ContinuousOn f (Icc 0 R)) (hg : ContinuousOn g (Icc 0 R)) (h : EqOn f g (Ico 0 R)) :
    f R = g R := by
  have hne : (𝓝[Ico 0 R] R).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_Ico hR.ne]; exact ⟨hR.le, le_rfl⟩)
  have h1 := (hf R ⟨hR.le, le_rfl⟩).mono (fun x hx => ⟨hx.1, hx.2.le⟩ : Ico 0 R ⊆ Icc 0 R)
  have h2 := (hg R ⟨hR.le, le_rfl⟩).mono (fun x hx => ⟨hx.1, hx.2.le⟩ : Ico 0 R ⊆ Icc 0 R)
  exact tendsto_nhds_unique_of_eventuallyEq h1.tendsto h2.tendsto
    (eventually_nhdsWithin_of_forall h)

theorem nnnorm_lt_ofReal {τ R : ℝ} (hR : 0 < R) (hτ : τ ∈ Ico 0 R) :
    (‖τ‖₊ : ℝ≥0∞) < ENNReal.ofReal R := by
  rw [Real.nnnorm_of_nonneg hτ.1, ← ENNReal.ofReal_eq_coe_nnreal hτ.1]
  exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hτ.2

/-- The three radii reach `R`. -/
def Reaches (θS HS RS : T → PowerSeries ℝ) (R : ℝ) : Prop :=
  ∀ t, ENNReal.ofReal R ≤ rad (θS t) ∧ ENNReal.ofReal R ≤ rad (HS t) ∧ ENNReal.ofReal R ≤ rad (RS t)

section GermSection

variable (G : Germ xi z K p θS HS RS) {R : ℝ}
include G

omit G in
theorem Germ.allAbs (hR : 0 < R) (hrad : Reaches θS HS RS R) : AllAbs θS HS RS R := fun _ hτ t =>
  ⟨abs_of_lt_rad ((nnnorm_lt_ofReal hR hτ).trans_le (hrad t).1),
    abs_of_lt_rad ((nnnorm_lt_ofReal hR hτ).trans_le (hrad t).2.1),
    abs_of_lt_rad ((nnnorm_lt_ofReal hR hτ).trans_le (hrad t).2.2)⟩

theorem Germ.fac_pos (hR : 0 < R) (hrad : Reaches θS HS RS R) {τ : ℝ} (hτ : τ ∈ Ico 0 R) (t : T) :
    0 < fac xi z RS τ t := G.F.factor_pos (allAbs hR hrad) hR hτ t

theorem Germ.path_an (hR : 0 < R) (hrad : Reaches θS HS RS R) {τ : ℝ} (hτ : τ ∈ Ico 0 R) :
    AnalyticAt ℝ (path xi z θS HS RS) τ := by
  have hθ t := ev_analyticAt ((nnnorm_lt_ofReal hR hτ).trans_le (hrad t).1)
  have hH t := ev_analyticAt ((nnnorm_lt_ofReal hR hτ).trans_le (hrad t).2.1)
  have hr t := ev_analyticAt ((nnnorm_lt_ofReal hR hτ).trans_le (hrad t).2.2)
  have hf t : AnalyticAt ℝ (fun x => fac xi z RS x t) τ :=
    analyticAt_const.sub (analyticAt_const.mul (hr t))
  refine AnalyticAt.prod (analyticAt_pi_iff.mpr fun t => ?_) (analyticAt_pi_iff.mpr fun t => ?_)
  · exact ((analyticAt_const.mul ((hθ t).mul (hH t))).mul (hf t)).div_const
  · exact analyticAt_const.add
      (((hr t).div (hf t) (G.fac_pos hR hrad hτ t).ne').div_const)

/-- The germ facts in one place. -/
theorem Germ.near_zero : ∀ᶠ τ in 𝓝 (0 : ℝ), path xi z θS HS RS τ = p τ ∧
    MultiTail.IsRoot xi z (fun t => τ * K t) (p τ).1 (p τ).2 ∧
    (∀ t, actualU xi z (p τ).1 (p τ).2 (z t) ≠ 0) ∧
    (∀ t, ev τ (θS t) = actualTheta xi z (p τ).1 (p τ).2 t) ∧
    (∀ t, ev τ (HS t) = actualH xi z (p τ).1 (p τ).2 (z t)) ∧
    (∀ t, ev τ (RS t) = actualNodeR xi z (p τ).1 (p τ).2 t) := by
  have hU := actualU_nodes_nonzero_eventually_of_continuous_seed
    xi z G.hxi1.ne G.F.hz p (fun t => G0 xi (z t)) G.hpa.continuousAt G.hp0
  have hevθ := eventually_all.mpr fun t => HasTaylorPowerSeriesAt.ev_eventuallyEq (G.hθ t)
  have hevH := eventually_all.mpr fun t => HasTaylorPowerSeriesAt.ev_eventuallyEq (G.hH t)
  have hevR := eventually_all.mpr fun t => HasTaylorPowerSeriesAt.ev_eventuallyEq (G.hR t)
  filter_upwards [G.path_eventuallyEq, G.hroot, hU, hevθ, hevH, hevR] with τ h0 h1 h2 h3 h4 h5
  exact ⟨h0, h1, h2, h3, h4, h5⟩

theorem Germ.root_on (hR : 0 < R) (hrad : Reaches θS HS RS R) {τ : ℝ} (hτ : τ ∈ Ico 0 R) :
    MultiTail.IsRoot xi z (fun t => τ * K t) (path xi z θS HS RS τ).1 (path xi z θS HS RS τ).2 := by
  have han : ∀ x ∈ Ico 0 R, AnalyticAt ℝ
      (fun x => MultiTail.residual xi z K (x, path xi z θS HS RS x)) x := fun x hx =>
    AnalyticAt.comp (g := MultiTail.residual xi z K) (f := fun x => (x, path xi z θS HS RS x))
      (residual_analyticAt xi z K (x, path xi z θS HS RS x))
      (analyticAt_id.prod (G.path_an hR hrad hx))
  have hzero := eqOn_of_germ hR han (fun _ _ => analyticAt_const (v := (0 : Pairs T))) (by
    filter_upwards [G.near_zero] with x hx
    rw [hx.1]
    exact (residual_zero_iff xi z K _ _ x).mpr hx.2.1)
  exact (residual_zero_iff xi z K _ _ τ).mp (hzero hτ)

theorem Germ.id_weight (hR : 0 < R) (hrad : Reaches θS HS RS R) (t : T) {τ : ℝ} (hτ : τ ∈ Ico 0 R) :
    actualWeight xi z (path xi z θS HS RS τ).1 (path xi z θS HS RS τ).2 t =
      ev τ (θS t) * ev τ (HS t) := by
  refine eqOn_of_germ hR (f := fun x => actualWeight xi z (path xi z θS HS RS x).1
      (path xi z θS HS RS x).2 t) (g := fun x => ev x (θS t) * ev x (HS t))
    (fun x hx => (weight_an xi z t _).comp (G.path_an hR hrad hx))
    (fun x hx => (ev_analyticAt ((nnnorm_lt_ofReal hR hx).trans_le (hrad t).1)).mul
      (ev_analyticAt ((nnnorm_lt_ofReal hR hx).trans_le (hrad t).2.1))) ?_ hτ
  filter_upwards [G.near_zero] with x hx
  obtain ⟨h0, -, hu, h3, h4, -⟩ := hx
  simp only [h0, h3, h4, actualTheta, actualH]
  field_simp [hu t]

theorem Germ.id_U (hR : 0 < R) (hrad : Reaches θS HS RS R) (t : T) {τ : ℝ} (hτ : τ ∈ Ico 0 R) :
    actualU xi z (path xi z θS HS RS τ).1 (path xi z θS HS RS τ).2 (z t) * ev τ (HS t) = 1 := by
  refine eqOn_of_germ hR (f := fun x => actualU xi z (path xi z θS HS RS x).1
      (path xi z θS HS RS x).2 (z t) * ev x (HS t)) (g := fun _ => 1)
    (fun x hx => ((nodeU_an xi G.hxi1.ne z G.F.hz t _).comp (G.path_an hR hrad hx)).mul
      (ev_analyticAt ((nnnorm_lt_ofReal hR hx).trans_le (hrad t).2.1)))
    (fun _ _ => analyticAt_const) ?_ hτ
  filter_upwards [G.near_zero] with x hx
  obtain ⟨h0, -, hu, -, h4, -⟩ := hx
  simp only [h0, h4, actualH]
  exact mul_inv_cancel₀ (hu t)

theorem Germ.id_G (hR : 0 < R) (hrad : Reaches θS HS RS R) (t : T) {τ : ℝ} (hτ : τ ∈ Ico 0 R) :
    actualG xi z (path xi z θS HS RS τ).1 (path xi z θS HS RS τ).2 (z t) * ev τ (HS t) =
      ev τ (RS t) := by
  refine eqOn_of_germ hR (f := fun x => actualG xi z (path xi z θS HS RS x).1
      (path xi z θS HS RS x).2 (z t) * ev x (HS t)) (g := fun x => ev x (RS t))
    (fun x hx => ((nodeG_an xi z t _).comp (G.path_an hR hrad hx)).mul
      (ev_analyticAt ((nnnorm_lt_ofReal hR hx).trans_le (hrad t).2.1)))
    (fun x hx => ev_analyticAt ((nnnorm_lt_ofReal hR hx).trans_le (hrad t).2.2)) ?_ hτ
  filter_upwards [G.near_zero] with x hx
  obtain ⟨h0, -, -, -, h4, h5⟩ := hx
  simp only [h0, h4, h5, actualH, actualNodeR]
  rfl

/-- On the ray the three node series are the actual coordinates of the rebuilt path. -/
theorem Germ.node_on (hR : 0 < R) (hrad : Reaches θS HS RS R) (t : T) {τ : ℝ} (hτ : τ ∈ Ico 0 R) :
    actualU xi z (path xi z θS HS RS τ).1 (path xi z θS HS RS τ).2 (z t) ≠ 0 ∧
    actualTheta xi z (path xi z θS HS RS τ).1 (path xi z θS HS RS τ).2 t = ev τ (θS t) ∧
    actualH xi z (path xi z θS HS RS τ).1 (path xi z θS HS RS τ).2 (z t) = ev τ (HS t) ∧
    actualNodeR xi z (path xi z θS HS RS τ).1 (path xi z θS HS RS τ).2 t = ev τ (RS t) := by
  have hu := G.id_U hR hrad t hτ
  have hw := G.id_weight hR hrad t hτ
  have hg := G.id_G hR hrad t hτ
  have hne : actualU xi z (path xi z θS HS RS τ).1 (path xi z θS HS RS τ).2 (z t) ≠ 0 :=
    left_ne_zero_of_mul_eq_one hu
  have hHe : ev τ (HS t) =
      (actualU xi z (path xi z θS HS RS τ).1 (path xi z θS HS RS τ).2 (z t))⁻¹ :=
    eq_inv_of_mul_eq_one_right hu
  refine ⟨hne, ?_, hHe.symm, ?_⟩
  · simp only [actualTheta]
    rw [hw, mul_assoc, mul_comm (ev τ (HS t)), hu, mul_one]
  · simp only [actualNodeR]
    rw [← hg, hHe, div_eq_mul_inv]

end GermSection


end FMSA.Convergence.PureFluidFoldPath

/-- info: 'FMSA.Convergence.PureFluidFoldPath.rhoOf_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.rhoOf_pos
/-- info: 'FMSA.Convergence.PureFluidFoldPath.Germ.path_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.Germ.path_eventuallyEq
/-- info: 'FMSA.Convergence.PureFluidFoldPath.pair_D_an' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.pair_D_an
/-- info: 'FMSA.Convergence.PureFluidFoldPath.pair_G_an' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.pair_G_an
/-- info: 'FMSA.Convergence.PureFluidFoldPath.weight_an' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.weight_an
/-- info: 'FMSA.Convergence.PureFluidFoldPath.nodeU_an' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.nodeU_an
/-- info: 'FMSA.Convergence.PureFluidFoldPath.nodeG_an' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.nodeG_an
/-- info: 'FMSA.Convergence.PureFluidFoldPath.residual_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.residual_zero_iff
/-- info: 'FMSA.Convergence.PureFluidFoldPath.eqOn_of_germ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.eqOn_of_germ
/-- info: 'FMSA.Convergence.PureFluidFoldPath.endpoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.endpoint_eq
/-- info: 'FMSA.Convergence.PureFluidFoldPath.nnnorm_lt_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.nnnorm_lt_ofReal
/-- info: 'FMSA.Convergence.PureFluidFoldPath.Germ.allAbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.Germ.allAbs
/-- info: 'FMSA.Convergence.PureFluidFoldPath.Germ.fac_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.Germ.fac_pos
/-- info: 'FMSA.Convergence.PureFluidFoldPath.Germ.path_an' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.Germ.path_an
/-- info: 'FMSA.Convergence.PureFluidFoldPath.Germ.near_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.Germ.near_zero
/-- info: 'FMSA.Convergence.PureFluidFoldPath.Germ.root_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.Germ.root_on
/-- info: 'FMSA.Convergence.PureFluidFoldPath.Germ.id_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.Germ.id_weight
/-- info: 'FMSA.Convergence.PureFluidFoldPath.Germ.id_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.Germ.id_U
/-- info: 'FMSA.Convergence.PureFluidFoldPath.Germ.id_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.Germ.id_G
/-- info: 'FMSA.Convergence.PureFluidFoldPath.Germ.node_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldPath.Germ.node_on
