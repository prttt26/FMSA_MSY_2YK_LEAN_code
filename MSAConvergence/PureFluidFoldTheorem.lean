import MSAConvergence.PureFluidFoldEnd
import MSAConvergence.PureFluidFoldSigns

set_option linter.style.header false

/-! Pure fluid, arbitrary finite strictly positive tails: the Taylor radius of the original
hard-sphere germ `(Dt, G)` is the point where its real analytic continuation ends in a fold. -/

noncomputable section
open Filter Topology Set PowerSeries
open scoped ENNReal NNReal ContDiff
namespace FMSA.Convergence.PureFluidFoldTheorem
open FMSA.Convergence.PureFluidFoldPath FMSA.Convergence.PureFluidFoldEnd
open FMSA.Convergence.PureFluidFoldCore FMSA.Convergence.PureFluidSeriesEval
open FMSA.Convergence.PureFluidFoldRadius FMSA.Convergence.PureFluidFoldBridge
open FMSA.Convergence.PureFluidFoldSigns
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.Convergence.PureFluidThetaPringsheimRoute FMSA.Convergence.PureFluidThetaCouplingTaylor
open FMSA.Convergence.PureFluidActualNodeGerm
open FMSA.Convergence.PureFluidNodeClosedForm FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.PureFluidExponentialSplit FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Paper.StableIntervalRadius FMSA.Convergence.PureFluidActualAnalyticGerm
open FMSA.ExactMSA FMSA.ExactMSA.BSource

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The Taylor series of `r / (1 - κ r)` satisfies the algebraic relation. -/
theorem quotient_relation {r S : PowerSeries ℝ} {κ : ℝ} (hrad : 0 < rad r) (h0 : coeff 0 r = 0)
    (hS : HasTaylorPowerSeriesAt (fun x => ev x r / (1 - κ * ev x r)) S) :
    S * (1 - C κ * r) = r := by
  have hr := hasTaylor_ev hrad
  have hne : ∀ᶠ x in 𝓝 (0 : ℝ), 1 - κ * ev x r ≠ 0 := by
    have hn0 : (‖(0 : ℝ)‖₊ : ℝ≥0∞) < rad r := by simpa using hrad
    have hc : ContinuousAt (fun x => 1 - κ * ev x r) 0 :=
      continuousAt_const.sub (continuousAt_const.mul (ev_analyticAt hn0).continuousAt)
    refine hc.eventually_ne ?_
    simp [ev_zero_point, h0]
  have hT := hS.mul ((taylor_const 1).add ((taylor_const (-κ)).mul hr))
  have heq := taylorPowerSeries_eq_of_eventually _ _ _ _ hT hr (by
    filter_upwards [hne] with x hx
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [show (1 : ℝ) + -κ * ev x r = 1 - κ * ev x r by ring]
    exact div_mul_cancel₀ _ hx)
  have hform : S * (1 - C κ * r) = S * (C 1 + C (-κ) * r) := by
    simp only [map_one, map_neg]
    ring
  exact hform.trans heq

section GermSection

variable {xi : ℝ} {z K : T → ℝ} {p : ℝ → (T → ℝ) × (T → ℝ)} {θS HS RS : T → PowerSeries ℝ}
  (G : PureFluidFoldPath.Germ xi z K p θS HS RS) {R : ℝ} (hR : 0 < R) (hrad : Reaches θS HS RS R)
include G hR hrad

/-- The series of `D_t`. -/
theorem Germ.amp_D (t : T) {S : PowerSeries ℝ} (hS : HasTaylorPowerSeriesAt (fun x => (p x).1 t) S) :
    Abs R S ∧ (∀ τ ∈ Icc 0 R, ev τ S = (path xi z θS HS RS τ).1 t) ∧ CN S ∧
      rad S ≤ rad (HS t) := by
  have hend := Germ.abs_end G hR hrad t
  have hpos : 0 < ENNReal.ofReal R := ENNReal.ofReal_pos.mpr hR
  have hθ := hasTaylor_ev (hpos.trans_le (hrad t).1)
  have hH := hasTaylor_ev (hpos.trans_le (hrad t).2.1)
  have hr := hasTaylor_ev (hpos.trans_le (hrad t).2.2)
  set κ := hardKappa xi (z t) with hκ
  set c := F0 xi (z t) / rhoOf xi with hc
  have hT := (taylor_const c).mul
    ((hθ.mul hH).mul ((taylor_const 1).add ((taylor_const (-κ)).mul hr)))
  have hSeq := taylorPowerSeries_eq_of_eventually _ _ _ _ hS hT (by
    filter_upwards [G.path_eventuallyEq] with x hx
    rw [← hx]
    simp only [Pi.mul_apply, Pi.add_apply, path, ampD, fac]
    rw [← hκ, hc]
    ring)
  have habs : ∀ τ, |τ| ≤ R → Abs τ S := fun τ hτ => by
    have hR' : |τ| ≤ |R| := by rwa [abs_of_pos hR]
    rw [hSeq]
    exact (abs_C τ _).mul (((hend.1.mono hR').mul (hend.2.1.mono hR')).mul
      ((abs_C τ _).add ((abs_C τ _).mul (hend.2.2.mono hR'))))
  have hF0 : 0 < F0 xi (z t) :=
    lt_trans one_pos (actual_F0_gt_one xi (z t) G.hxi0 G.hxi1 (G.F.hz t))
  have hc0 : 0 < c := div_pos hF0 (rhoOf_pos G.hxi0)
  have hα := G.F.hα t
  have hκ0 := G.F.hκ t
  have hQ := quot_cn hκ0 (G.F.r_cn t) (G.F.r0 t)
  have hform : S = C c * (C (physicalAlpha xi z K t) * (X * HS t) +
      C (physicalAlpha xi z K t * κ) * (X * (HS t * quot κ (RS t)))) := by
    rw [hSeq, ← D_form G.F t]
    simp only [map_one, map_neg]
    ring
  have hXH : CN (X * HS t) := cn_mul cn_X (G.F.H_cn t)
  have hXQ : CN (X * (HS t * quot κ (RS t))) := cn_mul cn_X (cn_mul (G.F.H_cn t) hQ)
  have hSCN : CN S := by
    rw [hform]
    exact cn_mul (cn_C hc0.le) (cn_add (cn_mul (cn_C hα.le) hXH)
      (cn_mul (cn_C (mul_pos hα hκ0).le) hXQ))
  have hdom : rad S ≤ rad (HS t) := by
    refine rad_le_of_dom (c := c * physicalAlpha xi z K t) (m := 1) (mul_pos hc0 hα)
      (G.F.H_cn t) ?_
    have heq : S - C (c * physicalAlpha xi z K t) * (X ^ 1 * HS t) =
        C c * (C (physicalAlpha xi z K t * κ) * (X * (HS t * quot κ (RS t)))) := by
      rw [hform, pow_one, map_mul C c]
      ring
    rw [heq]
    exact cn_mul (cn_C hc0.le) (cn_mul (cn_C (mul_pos hα hκ0).le) hXQ)
  refine ⟨habs R (by rw [abs_of_pos hR]), fun τ hτ => ?_, hSCN, hdom⟩
  have hR' : |τ| ≤ |R| := by rw [abs_of_nonneg hτ.1, abs_of_pos hR]; exact hτ.2
  have a1 := hend.1.mono hR'
  have a2 := hend.2.1.mono hR'
  have a3 := hend.2.2.mono hR'
  have a4 : Abs τ (C (1 : ℝ) + C (-κ) * RS t) := (abs_C τ _).add ((abs_C τ _).mul a3)
  rw [hSeq, ev_mul (abs_C τ _) ((a1.mul a2).mul a4), ev_C, ev_mul (a1.mul a2) a4, ev_mul a1 a2,
    ev_add (abs_C τ _) ((abs_C τ _).mul a3), ev_C, ev_mul (abs_C τ _) a3, ev_C]
  simp only [path, ampD, fac]
  rw [← hκ, hc]
  ring

/-- The series of `G_t`. -/
theorem Germ.amp_G (t : T) {S : PowerSeries ℝ} (hS : HasTaylorPowerSeriesAt (fun x => (p x).2 t) S) :
    Abs R S ∧ (∀ τ ∈ Icc 0 R, ev τ S = (path xi z θS HS RS τ).2 t) ∧
      ∀ n, 1 ≤ n → 0 ≤ coeff n S := by
  have hend := Germ.abs_end G hR hrad t
  have hpos : 0 < ENNReal.ofReal R := ENNReal.ofReal_pos.mpr hR
  have hrr := hpos.trans_le (hrad t).2.2
  have hn0 : (‖(0 : ℝ)‖₊ : ℝ≥0∞) < rad (RS t) := by simpa using hrr
  have hκ0 := G.F.hκ t
  set κ := hardKappa xi (z t) with hκ
  have hfac : ∀ x, fac xi z RS x t = 1 - κ * ev x (RS t) := fun _ => rfl
  have hg0 : AnalyticAt ℝ (fun x => ev x (RS t) / (1 - κ * ev x (RS t))) 0 :=
    (ev_analyticAt hn0).div (analyticAt_const.sub (analyticAt_const.mul (ev_analyticAt hn0)))
      (by simp [ev_zero_point, G.F.r0 t])
  obtain ⟨Q, hQ⟩ := exists_taylorPowerSeries _ hg0
  have hrel := quotient_relation hrr (G.F.r0 t) hQ
  have hcn : CN Q := cn_of_quotient hκ0 (G.F.r_cn t) (G.F.r0 t) hrel
  have hQrad : ENNReal.ofReal R ≤ rad Q :=
    taylor_radius_lower_bound_of_nonnegative_analytic_branch _ Q hQ (fun n => hcn n) R hR
      fun x hx => by
        have hx' := (nnnorm_lt_ofReal hR hx).trans_le (hrad t).2.2
        exact (ev_analyticAt hx').div
          (analyticAt_const.sub (analyticAt_const.mul (ev_analyticAt hx')))
          (G.fac_pos hR hrad hx t).ne'
  have hQval : ∀ τ, τ ∈ Icc 0 R → Abs τ Q → ev τ Q = ev τ (RS t) / fac xi z RS τ t := by
    intro τ hτ ha
    have hR' : |τ| ≤ |R| := by rw [abs_of_nonneg hτ.1, abs_of_pos hR]; exact hτ.2
    have a3 := hend.2.2.mono hR'
    have hv := congrArg (ev τ) hrel
    rw [ev_mul ha ((abs_one τ).sub ((abs_C τ _).mul a3)),
      ev_sub (abs_one τ) ((abs_C τ _).mul a3), ev_one, ev_mul (abs_C τ _) a3, ev_C] at hv
    rw [eq_div_iff (Germ.fac_pos_Icc G hR hrad hτ t).ne', hfac]
    exact hv
  have hfR := Germ.fac_end_pos G hR hrad t
  have hQR : Abs R Q := by
    refine abs_of_summable (summable_at_endpoint hcn hR
      (fun a ha => abs_of_lt_rad ((nnnorm_lt_ofReal hR ha).trans_le hQrad))
      (B := ev R (RS t) / fac xi z RS R t) fun a ha => ?_)
    have ha' : a ∈ Icc 0 R := ⟨ha.1, ha.2.le⟩
    rw [hQval a ha' (abs_of_lt_rad ((nnnorm_lt_ofReal hR ha).trans_le hQrad))]
    have hrm := ev_mono (G.F.r_cn t) ha.1 ha.2.le hend.2.2
    have hfa := G.fac_pos hR hrad ha t
    have hfm : fac xi z RS R t ≤ fac xi z RS a t := by
      simp only [hfac]
      nlinarith
    exact div_le_div₀ (ev_nonneg (G.F.r_cn t) hR.le) hrm hfR hfm
  set d := 2 * Real.pi * rhoOf xi * (F0 xi (z t)) ^ 2 with hd
  have hT := (taylor_const (hardG0Node xi (z t))).add ((taylor_const d⁻¹).mul hQ)
  have hSeq := taylorPowerSeries_eq_of_eventually _ _ _ _ hS hT (by
    filter_upwards [G.path_eventuallyEq] with x hx
    rw [← hx]
    simp only [Pi.mul_apply, Pi.add_apply, path, ampG, fac]
    rw [← hκ, ← hd]
    ring)
  have habs : ∀ τ, |τ| ≤ R → Abs τ S := fun τ hτ => by
    have hR' : |τ| ≤ |R| := by rwa [abs_of_pos hR]
    rw [hSeq]
    exact (abs_C τ _).add ((abs_C τ _).mul (hQR.mono hR'))
  have hd0 : 0 < d := by
    have hF0 : 0 < F0 xi (z t) :=
      lt_trans one_pos (actual_F0_gt_one xi (z t) G.hxi0 G.hxi1 (G.F.hz t))
    have hρ := rhoOf_pos G.hxi0
    rw [hd]
    positivity
  refine ⟨habs R (by rw [abs_of_pos hR]), fun τ hτ => ?_, fun n hn => ?_⟩
  swap
  · rw [hSeq, map_add, coeff_C, if_neg (by omega), zero_add, coeff_C_mul]
    exact mul_nonneg (inv_nonneg.mpr hd0.le) (hcn n)
  have hR' : |τ| ≤ |R| := by rw [abs_of_nonneg hτ.1, abs_of_pos hR]; exact hτ.2
  have aQ := hQR.mono hR'
  rw [hSeq, ev_add (abs_C τ _) ((abs_C τ _).mul aQ), ev_C, ev_mul (abs_C τ _) aQ, ev_C,
    hQval τ hτ aQ]
  simp only [path, ampG]
  rw [← hd]
  ring

end GermSection


/-- Every continuous root germ through the hard-sphere seed is the same germ. -/
theorem seed_germ_unique (xi : ℝ) (hxi : xi ∈ Ioo (0 : ℝ) 1) (z K : T → ℝ) (hz : ∀ u, 0 < z u)
    {p q : ℝ → Pairs T} (hp0 : p 0 = ((fun _ => 0), fun u => G0 xi (z u)))
    (hq0 : q 0 = ((fun _ => 0), fun u => G0 xi (z u)))
    (hp : ContinuousAt p 0) (hq : ContinuousAt q 0)
    (hpr : ∀ᶠ τ : ℝ in 𝓝 0, MultiTail.IsRoot xi z (fun u => τ * K u) (p τ).1 (p τ).2)
    (hqr : ∀ᶠ τ : ℝ in 𝓝 0, MultiTail.IsRoot xi z (fun u => τ * K u) (q τ).1 (q τ).2) :
    p =ᶠ[𝓝 0] q := by
  have hF (u : T) : F0 xi (z u) ≠ 0 := by
    have h := bhF_base_ne_zero hxi (hz u)
    simpa [bhF, F0] using h
  set a : Pairs T := ((fun _ => 0), fun u => G0 xi (z u)) with ha
  have hinv : ((fderiv ℝ (MultiTail.residual xi z K) ((0 : ℝ), a)).comp
      (ContinuousLinearMap.inr ℝ ℝ (Pairs T))).IsInvertible := by
    rw [show a = ((0 : T → ℝ), fun u => G0 xi (z u)) from rfl, MultiTail.residual_partial_triangular]
    exact MultiTail.triangular_isInvertible _ hF _
  have hc : ContDiffAt ℝ ω (MultiTail.residual xi z K) ((0 : ℝ), a) :=
    (residual_analyticAt xi z K ((0 : ℝ), a)).contDiffAt
  have hb : MultiTail.residual xi z K ((0 : ℝ), a) = 0 :=
    MultiTail.residual_base z K hxi hz
  have hlocal := hc.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  have ht : ∀ {r : ℝ → Pairs T}, r 0 = a → ContinuousAt r 0 →
      Tendsto (fun x => (x, r x)) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ), a)) := fun h0 hr =>
    tendsto_id.prodMk_nhds (by rw [← h0]; exact hr.tendsto)
  filter_upwards [(ht hp0 hp).eventually hlocal, (ht hq0 hq).eventually hlocal, hpr, hqr]
    with x h1 h2 h3 h4
  have e1 := h1.mp (((residual_zero_iff xi z K _ _ x).mpr h3).trans hb.symm)
  have e2 := h2.mp (((residual_zero_iff xi z K _ _ x).mpr h4).trans hb.symm)
  exact e1.symm.trans e2

/-- **Pure fluid, arbitrary finite strictly positive tails.** The hard-sphere germ of the original
amplitudes continues as an analytic real root path `P` on `[0,R)`, with a root limit at `R`, a
singular original Jacobian there and no analytic continuation across `R`. Its Taylor series converge
absolutely on `|τ| ≤ R` to `P` on the ray. Every `D_t` series has radius exactly `R`, every `G_t` series
at least `R`, and on the ray their coefficients are nonnegative (those of `G_t` from order one). -/
theorem taylor_radius_is_fold [Nonempty T] (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t) (hK : ∀ t, 0 < K t) :
    ∃ (p P : ℝ → Pairs T) (R : ℝ), 0 < R ∧
      (∀ t, R ≤ z t / (2 * PureFluidThetaCouplingTaylor.physicalAlpha xi z K t)) ∧
      p 0 = ((fun _ => 0), fun t => G0 xi (z t)) ∧ AnalyticAt ℝ p 0 ∧
      (∀ᶠ τ : ℝ in 𝓝 0, MultiTail.IsRoot xi z (fun t => τ * K t) (p τ).1 (p τ).2) ∧
      P =ᶠ[𝓝 0] p ∧
      (∀ τ ∈ Ico 0 R, AnalyticAt ℝ P τ ∧
        MultiTail.IsRoot xi z (fun t => τ * K t) (P τ).1 (P τ).2) ∧
      ContinuousOn P (Icc 0 R) ∧
      MultiTail.IsRoot xi z (fun t => R * K t) (P R).1 (P R).2 ∧
      ¬ ((fderiv ℝ (MultiTail.residual xi z K) (R, P R)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Pairs T))).IsInvertible ∧
      (∀ q : ℝ → Pairs T, AnalyticAt ℝ q R → ¬ q =ᶠ[𝓝[<] R] P) ∧
      ∀ DS GS : T → PowerSeries ℝ,
        (∀ t, HasTaylorPowerSeriesAt (fun x => (p x).1 t) (DS t)) →
        (∀ t, HasTaylorPowerSeriesAt (fun x => (p x).2 t) (GS t)) →
        (∀ t, rad (DS t) = ENNReal.ofReal R ∧ ENNReal.ofReal R ≤ rad (GS t)) ∧
        (∀ t n, 0 ≤ coeff n (DS t)) ∧ (∀ t n, 1 ≤ n → 0 ≤ coeff n (GS t)) ∧
        (∀ t τ, |τ| ≤ R → Abs τ (DS t) ∧ Abs τ (GS t)) ∧
        ∀ τ ∈ Icc 0 R, ∀ t, ev τ (DS t) = (P τ).1 t ∧ ev τ (GS t) = (P τ).2 t := by
  obtain ⟨p, θS, HS, RS, hp0, hpa, hθ, hH, hRS, hF, -, hroot⟩ :=
    exists_germ_nodeFamily xi hxi0 hxi1 z K hz hK
  have G : PureFluidFoldPath.Germ xi z K p θS HS RS :=
    ⟨hxi0, hxi1, hp0, hpa, hθ, hH, hRS, hF, hroot⟩
  let f : T → ℝ≥0∞ := fun t => min (rad (θS t)) (min (rad (HS t)) (rad (RS t)))
  obtain ⟨t0, ht0⟩ := Finite.exists_min f
  have hpos : 0 < f t0 := lt_min (rad_pos_of_taylor (hθ t0))
    (lt_min (rad_pos_of_taylor (hH t0)) (rad_pos_of_taylor (hRS t0)))
  have hreach : ∀ t, f t0 ≤ rad (θS t) ∧ f t0 ≤ rad (HS t) ∧ f t0 ≤ rad (RS t) := fun t =>
    ⟨(ht0 t).trans (min_le_left _ _), (ht0 t).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (ht0 t).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have htop : f t0 ≠ ⊤ := by
    intro htop
    have hα := hF.hα t0
    have hz0 := hz t0
    set B := z t0 / (2 * PureFluidThetaCouplingTaylor.physicalAlpha xi z K t0) + 1 with hB
    have hB0 : 0 < B := by positivity
    have hr : Reaches θS HS RS B := fun t => by
      rw [htop] at hreach
      have h := hreach t
      simp only [top_le_iff] at h
      simp [h.1, h.2.1, h.2.2]
    have := hF.R_le (PureFluidFoldPath.Germ.allAbs hB0 hr) hB0 t0
    linarith
  set R := (f t0).toReal with hRdef
  have hR : 0 < R := ENNReal.toReal_pos hpos.ne' htop
  have hofR : ENNReal.ofReal R = f t0 := ENNReal.ofReal_toReal htop
  have hrad : Reaches θS HS RS R := fun t => by
    rw [hofR]; exact hreach t
  have hmax : ∃ t, rad (θS t) ≤ ENNReal.ofReal R ∨ rad (HS t) ≤ ENNReal.ofReal R ∨
      rad (RS t) ≤ ENNReal.ofReal R := by
    refine ⟨t0, ?_⟩
    rw [hofR]
    simpa only [f, min_le_iff] using (le_refl (f t0))
  refine ⟨p, path xi z θS HS RS, R, hR,
    fun t => hF.R_le (PureFluidFoldPath.Germ.allAbs hR hrad) hR t, hp0, hpa, hroot,
    G.path_eventuallyEq,
    fun τ hτ => ⟨G.path_an hR hrad hτ, G.root_on hR hrad hτ⟩,
    PureFluidFoldEnd.Germ.path_cont G hR hrad, PureFluidFoldEnd.Germ.root_end G hR hrad,
    PureFluidFoldEnd.Germ.jacobian_singular G hR hrad hmax,
    fun q hq hl => PureFluidFoldEnd.Germ.no_extension G hR hrad hmax hq hl, ?_⟩
  intro DS GS hD hGS
  have hDa t := Germ.amp_D G hR hrad t (hD t)
  have hGa t := Germ.amp_G G hR hrad t (hGS t)
  refine ⟨fun t => ⟨le_antisymm ((hDa t).2.2.2.trans (rad_H_le_of_stop hF hmax t))
      (le_rad_of_abs hR (hDa t).1), le_rad_of_abs hR (hGa t).1⟩,
    fun t => (hDa t).2.2.1, fun t => (hGa t).2.2, fun t τ hτ => ?_, fun τ hτ t => ?_⟩
  · have hR' : |τ| ≤ |R| := by rwa [abs_of_pos hR]
    exact ⟨(hDa t).1.mono hR', (hGa t).1.mono hR'⟩
  · exact ⟨(hDa t).2.1 τ hτ, (hGa t).2.1 τ hτ⟩


end FMSA.Convergence.PureFluidFoldTheorem

/-- info: 'FMSA.Convergence.PureFluidFoldTheorem.quotient_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldTheorem.quotient_relation
/-- info: 'FMSA.Convergence.PureFluidFoldTheorem.Germ.amp_D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldTheorem.Germ.amp_D
/-- info: 'FMSA.Convergence.PureFluidFoldTheorem.Germ.amp_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldTheorem.Germ.amp_G
/-- info: 'FMSA.Convergence.PureFluidFoldTheorem.seed_germ_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldTheorem.seed_germ_unique
/-- info: 'FMSA.Convergence.PureFluidFoldTheorem.taylor_radius_is_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldTheorem.taylor_radius_is_fold
