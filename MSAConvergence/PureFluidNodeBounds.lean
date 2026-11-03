import Mathlib

set_option linter.style.header false

/-! Elementary bounds for the node quantities: the finite identity for `U(0)^2` and what follows from it. -/

noncomputable section
open Finset PowerSeries
namespace FMSA.Convergence.PureFluidNodeBounds

variable {T : Type*} [Fintype T]

/-- `U` from the weights. -/
def nodeU (z w : T → ℝ) (x : ℝ) : ℝ := 1 - ∑ t, w t / (x + z t)

omit [Fintype T] in
theorem pair_identity (a b p q : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    p * q / (a * (a + b)) + q * p / (b * (b + a)) = (p / a) * (q / b) := by
  have hba : b + a ≠ 0 := by rwa [add_comm]
  field_simp
  ring

/-- The value of the dispersion relation at `x = 0`, as a finite identity. -/
theorem dispersion_at_zero (z w : T → ℝ) (hz : ∀ t, 0 < z t) :
    nodeU z w 0 ^ 2 = 1 - ∑ t, 2 * (w t * nodeU z w (z t)) / z t := by
  set S := ∑ t, w t / z t with hS
  have hU0 : nodeU z w 0 = 1 - S := by simp [nodeU, hS]
  set D := ∑ t, ∑ u, w t * w u / (z t * (z t + z u)) with hD
  have hswap : D = ∑ t, ∑ u, w u * w t / (z u * (z u + z t)) := by
    rw [hD, Finset.sum_comm]
  have hsq : D + D = S * S := by
    nth_rewrite 2 [hswap]
    rw [hD, ← sum_add_distrib, hS, Finset.sum_mul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    exact pair_identity _ _ _ _ (hz t).ne' (hz u).ne' (add_pos (hz t) (hz u)).ne'
  have hR : ∑ t, 2 * (w t * nodeU z w (z t)) / z t = 2 * S - (D + D) := by
    have : ∀ t, 2 * (w t * nodeU z w (z t)) / z t =
        2 * (w t / z t) - (∑ u, w t * w u / (z t * (z t + z u)) + ∑ u, w t * w u / (z t * (z t + z u))) := by
      intro t
      have ht := (hz t).ne'
      have hsum : w t * (∑ u, w u / (z t + z u)) / z t = ∑ u, w t * w u / (z t * (z t + z u)) := by
        rw [Finset.mul_sum, Finset.sum_div]
        refine sum_congr rfl fun u _ => ?_
        have hu : z t + z u ≠ 0 := (add_pos (hz t) (hz u)).ne'
        field_simp
      simp only [nodeU]
      rw [← hsum]
      field_simp
      ring
    simp_rw [this]
    rw [sum_sub_distrib, sum_add_distrib, ← Finset.mul_sum]
  rw [hU0, hR]
  nlinarith [hsq]

/-- The lower bound on `U` that replaces any subharmonic estimate. -/
theorem nodeU_lower (z w : T → ℝ) (hz : ∀ t, 0 < z t) (hw : ∀ t, 0 ≤ w t)
    (h0 : 0 ≤ nodeU z w 0) {Z : ℝ} (hZ : ∀ t, z t ≤ Z) (hZ0 : 0 < Z) {x : ℝ} (hx : 0 < x) :
    x / (x + Z) ≤ nodeU z w x := by
  have hxZ : 0 < x + Z := by linarith
  have hS : ∑ t, w t / (0 + z t) ≤ 1 := by
    simp only [nodeU] at h0; linarith
  have hterm : ∀ t, w t / (x + z t) ≤ (w t / (0 + z t)) * (Z / (x + Z)) := by
    intro t
    have hzt := hz t
    have hxt : 0 < x + z t := by linarith
    rw [zero_add, div_mul_div_comm, div_le_div_iff₀ hxt (mul_pos hzt hxZ)]
    have : z t * (x + Z) ≤ Z * (x + z t) := by nlinarith [hZ t]
    nlinarith [mul_le_mul_of_nonneg_left this (hw t)]
  have hsum : ∑ t, w t / (x + z t) ≤ Z / (x + Z) := by
    calc ∑ t, w t / (x + z t) ≤ ∑ t, (w t / (0 + z t)) * (Z / (x + Z)) :=
          sum_le_sum fun t _ => hterm t
      _ = (∑ t, w t / (0 + z t)) * (Z / (x + Z)) := by rw [Finset.sum_mul]
      _ ≤ 1 * (Z / (x + Z)) := by
          exact mul_le_mul_of_nonneg_right hS (div_nonneg hZ0.le hxZ.le)
      _ = Z / (x + Z) := one_mul _
  have hone : x / (x + Z) = 1 - Z / (x + Z) := by field_simp; ring
  rw [hone]; simp only [nodeU]; linarith

/-- `θ_t ≤ z_t/2`, given `θ ≥ 0`. -/
theorem theta_le_half (z w : T → ℝ) (hz : ∀ t, 0 < z t)
    (hθ : ∀ t, 0 ≤ w t * nodeU z w (z t)) (t : T) :
    w t * nodeU z w (z t) ≤ z t / 2 := by
  classical
  have hd := dispersion_at_zero z w hz
  have hs : ∑ t, 2 * (w t * nodeU z w (z t)) / z t ≤ 1 := by nlinarith [sq_nonneg (nodeU z w 0)]
  have hnn : ∀ u ∈ univ, 0 ≤ 2 * (w u * nodeU z w (z u)) / z u := fun u _ =>
    div_nonneg (mul_nonneg (by norm_num) (hθ u)) (hz u).le
  have hsingle := single_le_sum hnn (mem_univ t)
  have := hsingle.trans hs
  rw [div_le_one (hz t)] at this
  linarith

/-- A continuous function, positive at the start, with nonincreasing square, cannot go negative. -/
theorem nonneg_of_sq_antitone (u : ℝ → ℝ) {R : ℝ}
    (hc : ContinuousOn u (Set.Ico 0 R)) (h0 : 0 < u 0)
    (hanti : ∀ a ∈ Set.Ico 0 R, ∀ b ∈ Set.Ico 0 R, a ≤ b → u b ^ 2 ≤ u a ^ 2) :
    ∀ τ ∈ Set.Ico 0 R, 0 ≤ u τ := by
  intro τ hτ
  by_contra hneg
  rw [not_le] at hneg
  have hsub : Set.Icc 0 τ ⊆ Set.Ico 0 R := fun a ha => ⟨ha.1, lt_of_le_of_lt ha.2 hτ.2⟩
  have hzero : (0 : ℝ) ∈ Set.Icc (u τ) (u 0) := ⟨hneg.le, h0.le⟩
  obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc' hτ.1 (hc.mono hsub) hzero
  have := hanti c (hsub hc1) τ hτ hc1.2
  rw [hc2] at this
  nlinarith [sq_nonneg (u τ), sq_pos_of_neg hneg]


end FMSA.Convergence.PureFluidNodeBounds

/-- info: 'FMSA.Convergence.PureFluidNodeBounds.pair_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeBounds.pair_identity
/-- info: 'FMSA.Convergence.PureFluidNodeBounds.dispersion_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeBounds.dispersion_at_zero
/-- info: 'FMSA.Convergence.PureFluidNodeBounds.nodeU_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeBounds.nodeU_lower
/-- info: 'FMSA.Convergence.PureFluidNodeBounds.theta_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeBounds.theta_le_half
/-- info: 'FMSA.Convergence.PureFluidNodeBounds.nonneg_of_sq_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeBounds.nonneg_of_sq_antitone
