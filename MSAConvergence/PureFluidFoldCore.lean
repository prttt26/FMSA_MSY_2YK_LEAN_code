import MSAConvergence.PureFluidSeriesEval
import MSAConvergence.PureFluidNodeBounds

set_option linter.style.header false

/-! Node families: series with nonnegative coefficients solving the two node equations. Bounds on the ray, finite radius, endpoint summability. -/

noncomputable section
open Finset PowerSeries
namespace FMSA.Convergence.PureFluidFoldCore
open FMSA.Convergence.PureFluidSeriesEval FMSA.Convergence.PureFluidNodeBounds

variable {T : Type*} [Fintype T]

/-- A family of node series: nonnegative coefficients, zero constant terms for `θ, r`, and the two
node equations of the pure-fluid theorem. -/
structure NodeFamily (z α κ : T → ℝ) (θ H r : T → PowerSeries ℝ) : Prop where
  hz : ∀ t, 0 < z t
  hα : ∀ t, 0 < α t
  hκ : ∀ t, 0 < κ t
  θ_cn : ∀ t, CN (θ t)
  H_cn : ∀ t, CN (H t)
  r_cn : ∀ t, CN (r t)
  θ0 : ∀ t, coeff 0 (θ t) = 0
  r0 : ∀ t, coeff 0 (r t) = 0
  eqθ : ∀ t, C (α t) * X = θ t * (1 - C (κ t) * r t) ^ 2
  eqH : ∀ s, H s * (1 - ∑ t, C ((z s + z t)⁻¹) * (θ t * H t)) = 1

variable {z α κ : T → ℝ} {θ H r : T → PowerSeries ℝ}

/-- Absolute convergence of all node series on `[0, R)`. -/
def AllAbs (θ H r : T → PowerSeries ℝ) (R : ℝ) : Prop :=
  ∀ τ ∈ Set.Ico 0 R, ∀ t, Abs τ (θ t) ∧ Abs τ (H t) ∧ Abs τ (r t)

/-- The weights at `τ`. -/
def weight (θ H : T → PowerSeries ℝ) (τ : ℝ) (t : T) : ℝ := ev τ (θ t) * ev τ (H t)

section NodeFamilySection

variable (F : NodeFamily z α κ θ H r) {R : ℝ} (hab : AllAbs θ H r R)
include F hab

theorem NodeFamily.ev_H_mul_nodeU {τ : ℝ} (hτ : τ ∈ Set.Ico 0 R) (s : T) :
    ev τ (H s) * nodeU z (weight θ H τ) (z s) = 1 := by
  have habs : ∀ t ∈ (univ : Finset T), Abs τ (C ((z s + z t)⁻¹) * (θ t * H t)) := fun t _ =>
    (abs_C τ _).mul ((hab τ hτ t).1.mul (hab τ hτ t).2.1)
  have hsumA := abs_sum univ (fun t => C ((z s + z t)⁻¹) * (θ t * H t)) habs
  have hev : ev τ (1 - ∑ t, C ((z s + z t)⁻¹) * (θ t * H t)) = nodeU z (weight θ H τ) (z s) := by
    rw [ev_sub (abs_one τ) hsumA, ev_one, ev_sum univ _ habs]
    simp only [nodeU, weight]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [ev_mul (abs_C τ _) ((hab τ hτ t).1.mul (hab τ hτ t).2.1), ev_C,
      ev_mul (hab τ hτ t).1 (hab τ hτ t).2.1, div_eq_inv_mul]
  have h := congrArg (ev τ) (F.eqH s)
  rw [ev_mul (hab τ hτ s).2.1 ((abs_one τ).sub hsumA), hev, ev_one] at h
  exact h

theorem NodeFamily.theta_eq_weight_mul {τ : ℝ} (hτ : τ ∈ Set.Ico 0 R) (t : T) :
    weight θ H τ t * nodeU z (weight θ H τ) (z t) = ev τ (θ t) := by
  have := F.ev_H_mul_nodeU hab hτ t
  simp only [weight] at *
  rw [mul_assoc, this, mul_one]

theorem NodeFamily.ev_alpha {τ : ℝ} (hτ : τ ∈ Set.Ico 0 R) (t : T) :
    α t * τ = ev τ (θ t) * (1 - κ t * ev τ (r t)) ^ 2 := by
  have h := congrArg (ev τ) (F.eqθ t)
  have hg : Abs τ (1 - C (κ t) * r t) := (abs_one τ).sub ((abs_C τ _).mul (hab τ hτ t).2.2)
  have hgv : ev τ (1 - C (κ t) * r t) = 1 - κ t * ev τ (r t) := by
    rw [ev_sub (abs_one τ) ((abs_C τ _).mul (hab τ hτ t).2.2), ev_one,
      ev_mul (abs_C τ _) (hab τ hτ t).2.2, ev_C]
  rw [ev_mul (abs_C τ _) (abs_X τ), ev_C, ev_X, sq, ev_mul (hab τ hτ t).1 (hg.mul hg),
    ev_mul hg hg, hgv] at h
  rw [h, sq]

theorem NodeFamily.weight_nonneg {τ : ℝ} (hτ : τ ∈ Set.Ico 0 R) (t : T) : 0 ≤ weight θ H τ t :=
  mul_nonneg (ev_nonneg (F.θ_cn t) hτ.1) (ev_nonneg (F.H_cn t) hτ.1)

/-- `U(0)` stays nonnegative on the ray. -/
theorem NodeFamily.nodeU_zero_nonneg (hR : 0 < R) {τ : ℝ} (hτ : τ ∈ Set.Ico 0 R) :
    0 ≤ nodeU z (weight θ H τ) 0 := by
  have hzero : (0 : ℝ) ∈ Set.Ico 0 R := ⟨le_rfl, hR⟩
  have hcont : ContinuousOn (fun a => nodeU z (weight θ H a) 0) (Set.Ico 0 R) := by
    simp only [nodeU, weight]
    refine continuousOn_const.sub (continuousOn_finsetSum _ fun t _ => ?_)
    refine ContinuousOn.div_const ?_ _
    exact (ev_continuousOn_Ico fun a ha => (hab a ha t).1).mul
      (ev_continuousOn_Ico fun a ha => (hab a ha t).2.1)
  have hstart : 0 < nodeU z (weight θ H 0) 0 := by
    have : nodeU z (weight θ H 0) 0 = 1 := by
      simp [nodeU, weight, ev_zero_point, F.θ0]
    rw [this]; exact one_pos
  refine nonneg_of_sq_antitone _ hcont hstart ?_ τ hτ
  intro a ha b hb hab'
  rw [dispersion_at_zero z _ F.hz, dispersion_at_zero z _ F.hz]
  refine sub_le_sub_left (sum_le_sum fun t _ => ?_) 1
  rw [F.theta_eq_weight_mul hab ha, F.theta_eq_weight_mul hab hb]
  refine div_le_div_of_nonneg_right ?_ (F.hz t).le
  have := ev_mono (F.θ_cn t) ha.1 hab' (hab b hb t).1
  linarith

/-- The bound on `θ`. -/
theorem NodeFamily.theta_le_half_ev (hR : 0 < R) {τ : ℝ} (hτ : τ ∈ Set.Ico 0 R) (t : T) :
    ev τ (θ t) ≤ z t / 2 := by
  have h := theta_le_half z (weight θ H τ) F.hz (fun u => by
    rw [F.theta_eq_weight_mul hab hτ]; exact ev_nonneg (F.θ_cn u) hτ.1) t
  rwa [F.theta_eq_weight_mul hab hτ] at h

/-- The bound on `H`, with `Z` above all rates. -/
theorem NodeFamily.H_le (hR : 0 < R) {Z : ℝ} (hZ : ∀ t, z t ≤ Z) {τ : ℝ} (hτ : τ ∈ Set.Ico 0 R) (s : T) :
    ev τ (H s) ≤ (z s + Z) / z s := by
  have hzs := F.hz s
  have hZ0 : 0 < Z := hzs.trans_le (hZ s)
  have hl := nodeU_lower z (weight θ H τ) F.hz (F.weight_nonneg hab hτ)
    (F.nodeU_zero_nonneg hab hR hτ) hZ hZ0 hzs
  have hmul := F.ev_H_mul_nodeU hab hτ s
  have hH0 := ev_nonneg (F.H_cn s) hτ.1
  have hpos : 0 < z s / (z s + Z) := div_pos hzs (by linarith)
  have h1 : ev τ (H s) * (z s / (z s + Z)) ≤ 1 := by
    rw [← hmul]; exact mul_le_mul_of_nonneg_left hl hH0
  have h2 : ev τ (H s) * (z s / (z s + Z)) * ((z s + Z) / z s) = ev τ (H s) := by
    have h3 : z s + Z ≠ 0 := by linarith
    field_simp
  calc ev τ (H s) = ev τ (H s) * (z s / (z s + Z)) * ((z s + Z) / z s) := h2.symm
    _ ≤ 1 * ((z s + Z) / z s) :=
        mul_le_mul_of_nonneg_right h1 (div_nonneg (by linarith) hzs.le)
    _ = (z s + Z) / z s := one_mul _

/-- `1 - κ r` stays positive on the ray. -/
theorem NodeFamily.factor_pos (hR : 0 < R) {τ : ℝ} (hτ : τ ∈ Set.Ico 0 R) (t : T) :
    0 < 1 - κ t * ev τ (r t) := by
  have hcont : ContinuousOn (fun a => 1 - κ t * ev a (r t)) (Set.Ico 0 R) :=
    continuousOn_const.sub (continuousOn_const.mul (ev_continuousOn_Ico fun a ha => (hab a ha t).2.2))
  have hstart : 0 < (fun a => 1 - κ t * ev a (r t)) 0 := by
    simp [ev_zero_point, F.r0]
  rcases eq_or_lt_of_le hτ.1 with h0 | hpos
  · rw [← h0]; exact hstart
  by_contra hneg
  rw [not_lt] at hneg
  have hsub : Set.Icc 0 τ ⊆ Set.Ico 0 R := fun a ha => ⟨ha.1, lt_of_le_of_lt ha.2 hτ.2⟩
  obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc' hτ.1 (hcont.mono hsub)
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨hneg, hstart.le⟩)
  have hc0 : 0 < c := by
    rcases eq_or_lt_of_le hc1.1 with h | h
    · rw [← h] at hc2; exact absurd hc2 hstart.ne'
    · exact h
  have halpha := F.ev_alpha hab (hsub hc1) t
  simp only at hc2
  rw [hc2] at halpha
  have : 0 < α t * c := mul_pos (F.hα t) hc0
  simp at halpha
  rcases halpha with h | h
  · exact absurd h (F.hα t).ne'
  · exact absurd h hc0.ne'

/-- The bound on `r`. -/
theorem NodeFamily.r_le (hR : 0 < R) {τ : ℝ} (hτ : τ ∈ Set.Ico 0 R) (t : T) : ev τ (r t) ≤ (κ t)⁻¹ := by
  have hf := F.factor_pos hab hR hτ t
  have hk := F.hκ t
  rw [inv_eq_one_div, le_div_iff₀ hk]
  linarith [mul_comm (ev τ (r t)) (κ t)]

/-- `α_t τ ≤ θ_t` on the ray, as `0 < 1 - κ r ≤ 1`. -/
theorem NodeFamily.alpha_mul_le_theta (hR : 0 < R) {τ : ℝ} (hτ : τ ∈ Set.Ico 0 R) (t : T) :
    α t * τ ≤ ev τ (θ t) := by
  have hf := F.factor_pos hab hR hτ t
  have hr := ev_nonneg (F.r_cn t) hτ.1
  have hk := F.hκ t
  have hf1 : 1 - κ t * ev τ (r t) ≤ 1 := by nlinarith [mul_nonneg hk.le hr]
  have hθ := ev_nonneg (F.θ_cn t) hτ.1
  rw [F.ev_alpha hab hτ t]
  have hsq : (1 - κ t * ev τ (r t)) ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq hθ]

/-- `R` is finite: `α_t τ ≤ θ_t ≤ z_t/2`. -/
theorem NodeFamily.R_le (hR : 0 < R) (t : T) : R ≤ z t / (2 * α t) := by
  have hα := F.hα t
  have hz := F.hz t
  by_contra hcon
  rw [not_le] at hcon
  set B := z t / (2 * α t) with hB
  have hB0 : 0 < B := by positivity
  have hτ : (B + R) / 2 ∈ Set.Ico 0 R := ⟨by linarith, by linarith⟩
  have h1 := F.alpha_mul_le_theta hab hR hτ t
  have h2 := F.theta_le_half_ev hab hR hτ t
  have h3 : α t * B = z t / 2 := by rw [hB]; field_simp
  have h4 : α t * B < α t * ((B + R) / 2) := mul_lt_mul_of_pos_left (by linarith) hα
  linarith

/-- All node series converge at the endpoint `R`. -/
theorem NodeFamily.endpoint_summable (hR : 0 < R) (t : T) :
    (Summable fun n => coeff n (θ t) * R ^ n) ∧ (Summable fun n => coeff n (H t) * R ^ n) ∧
      Summable fun n => coeff n (r t) * R ^ n := by
  classical
  have hZ : ∀ u, z u ≤ ∑ v, z v := fun u =>
    single_le_sum (f := z) (fun v _ => (F.hz v).le) (mem_univ u)
  exact ⟨summable_at_endpoint (F.θ_cn t) hR (fun a ha => (hab a ha t).1)
      (fun a ha => F.theta_le_half_ev hab hR ha t),
    summable_at_endpoint (F.H_cn t) hR (fun a ha => (hab a ha t).2.1)
      (fun a ha => F.H_le hab hR hZ ha t),
    summable_at_endpoint (F.r_cn t) hR (fun a ha => (hab a ha t).2.2)
      (fun a ha => F.r_le hab hR ha t)⟩

end NodeFamilySection


end FMSA.Convergence.PureFluidFoldCore

/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.ev_H_mul_nodeU' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.ev_H_mul_nodeU
/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.theta_eq_weight_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.theta_eq_weight_mul
/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.ev_alpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.ev_alpha
/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.weight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.weight_nonneg
/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.nodeU_zero_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.nodeU_zero_nonneg
/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.theta_le_half_ev' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.theta_le_half_ev
/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.H_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.H_le
/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.factor_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.factor_pos
/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.r_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.r_le
/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.alpha_mul_le_theta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.alpha_mul_le_theta
/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.R_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.R_le
/-- info: 'FMSA.Convergence.PureFluidFoldCore.NodeFamily.endpoint_summable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldCore.NodeFamily.endpoint_summable
