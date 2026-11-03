import MSAConvergence.PureFluidFoldRadius

set_option linter.style.header false

/-! Coefficient comparisons between the node series, with nonnegative differences. They give the
sign of the amplitude series on every ray and force all `H` radii to agree. -/

noncomputable section
open Filter Topology Set PowerSeries
open scoped ENNReal NNReal
namespace FMSA.Convergence.PureFluidFoldSigns
open FMSA.Convergence.PureFluidFoldCore FMSA.Convergence.PureFluidSeriesEval
open FMSA.Convergence.PureFluidFoldRadius

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- A convergent point bounds the radius from below. -/
theorem le_rad_of_abs {S : PowerSeries ℝ} {R : ℝ} (hR : 0 < R) (h : Abs R S) :
    ENNReal.ofReal R ≤ rad S := by
  have hs : Summable fun n =>
      ‖(FormalMultilinearSeries.ofScalars ℝ fun n => coeff n S) n‖ * (R.toNNReal : ℝ) ^ n := by
    refine h.congr fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal _ hR.le, norm_mul, norm_pow,
      Real.norm_of_nonneg hR.le]
  exact FormalMultilinearSeries.le_radius_of_summable_norm _ hs

/-- `S (1 - κ r) = r` with nonnegative `r` vanishing at zero has nonnegative coefficients. -/
theorem cn_of_quotient {r S : PowerSeries ℝ} {κ : ℝ} (hκ : 0 < κ) (hr : CN r)
    (h0 : coeff 0 r = 0) (h : S * (1 - C κ * r) = r) : CN S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hS : S = r + (C κ * r) * S := by linear_combination h
    have hn : coeff n S = coeff n r + coeff n ((C κ * r) * S) := by
      conv_lhs => rw [hS]
      rw [map_add]
    rw [hn, coeff_mul]
    refine add_nonneg (hr n) (Finset.sum_nonneg fun q hq => ?_)
    rw [coeff_C_mul]
    have hq' := Finset.mem_antidiagonal.mp hq
    by_cases hi : q.1 = 0
    · rw [hi, h0, mul_zero, zero_mul]
    · exact mul_nonneg (mul_nonneg hκ.le (hr _)) (ih _ (by omega))

theorem cn_add {A B : PowerSeries ℝ} (hA : CN A) (hB : CN B) : CN (A + B) := fun n => by
  rw [map_add]; exact add_nonneg (hA n) (hB n)

theorem cn_mul {A B : PowerSeries ℝ} (hA : CN A) (hB : CN B) : CN (A * B) := fun n => by
  rw [coeff_mul]; exact Finset.sum_nonneg fun _ _ => mul_nonneg (hA _) (hB _)

theorem cn_C {a : ℝ} (h : 0 ≤ a) : CN (C a) := fun n => by
  rw [coeff_C]; split_ifs <;> simp [h]

theorem cn_X : CN (X : PowerSeries ℝ) := fun n => by
  rw [coeff_X]; split_ifs <;> simp

theorem cn_one : CN (1 : PowerSeries ℝ) := by
  simpa using cn_C (a := 1) zero_le_one

theorem cn_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℝ) (h : ∀ i ∈ s, CN (f i)) :
    CN (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]; exact Finset.sum_nonneg fun i hi => h i hi n

/-- A shifted positive multiple of `A` below `B` bounds the radius of `B` by that of `A`. -/
theorem rad_le_of_dom {A B : PowerSeries ℝ} {c : ℝ} (hc : 0 < c) {m : ℕ} (hA : CN A)
    (hE : CN (B - C c * (X ^ m * A))) : rad B ≤ rad A := by
  by_contra hcon
  obtain ⟨τ, hτ0, h1, h2⟩ := ENNReal.lt_iff_exists_real_btwn.mp (not_le.mp hcon)
  have hτ : 0 < τ := by
    rcases hτ0.lt_or_eq with h | h
    · exact h
    · subst h; simp at h1
  have hn : (‖τ‖₊ : ℝ≥0∞) = ENNReal.ofReal τ := by
    rw [Real.nnnorm_of_nonneg hτ.le, ← ENNReal.ofReal_eq_coe_nnreal hτ.le]
  have hB : Abs τ B := abs_of_lt_rad (by rw [hn]; exact h2)
  have hdom : ∀ n, c * coeff n A ≤ coeff (n + m) B := fun n => by
    have := hE (n + m)
    rw [map_sub, coeff_C_mul, coeff_X_pow_mul] at this
    linarith
  have hs : Summable fun n => coeff (n + m) B * τ ^ (n + m) := by
    have h := hB.summable
    exact (summable_nat_add_iff m).mpr h
  have hA' : Abs τ A := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (hs.mul_left ((c * τ ^ m)⁻¹))
    rw [Real.norm_of_nonneg (mul_nonneg (hA n) (pow_nonneg hτ.le n))]
    have hpos : 0 < c * τ ^ m := by positivity
    rw [← div_eq_inv_mul, le_div_iff₀ hpos]
    have := mul_le_mul_of_nonneg_right (hdom n) (pow_nonneg hτ.le (n + m))
    rw [pow_add] at this ⊢
    nlinarith [this]
  exact absurd (le_rad_of_abs hτ hA') (not_le.mpr h1)

/-- `Q = r/(1 - κ r)`. -/
def quot (κ : ℝ) (r : PowerSeries ℝ) : PowerSeries ℝ := r * (1 - C κ * r)⁻¹

theorem quot_mul {κ : ℝ} {r : PowerSeries ℝ} (h0 : coeff 0 r = 0) :
    quot κ r * (1 - C κ * r) = r := by
  have hc : constantCoeff (1 - C κ * r) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, map_sub, coeff_C_mul, h0]
    simp
  unfold quot
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hc, mul_one]

theorem quot_cn {κ : ℝ} {r : PowerSeries ℝ} (hκ : 0 < κ) (hr : CN r) (h0 : coeff 0 r = 0) :
    CN (quot κ r) :=
  cn_of_quotient hκ hr h0 (quot_mul h0)

section Node

variable {z α κ : T → ℝ} {θ H r : T → PowerSeries ℝ} (F : NodeFamily z α κ θ H r)
include F

/-- `θ = α X (1 + κ Q)^2`. -/
theorem theta_form (t : T) :
    θ t = C (α t) * X * (1 + C (κ t) * quot (κ t) (r t)) ^ 2 := by
  have hq := quot_mul (κ := κ t) (F.r0 t)
  have hθ := F.eqθ t
  have hI : (1 + C (κ t) * quot (κ t) (r t)) * (1 - C (κ t) * r t) = 1 := by
    linear_combination C (κ t) * hq
  rw [hθ]
  linear_combination (-θ t * (1 + (1 + C (κ t) * quot (κ t) (r t)) * (1 - C (κ t) * r t))) * hI

theorem H_coeff_zero (s : T) : coeff 0 (H s) = 1 := by
  have h := congrArg constantCoeff (F.eqH s)
  have hz : ∀ t, constantCoeff (θ t) = 0 := fun t => by
    rw [← coeff_zero_eq_constantCoeff_apply]; exact F.θ0 t
  simpa [map_sum, hz] using h

theorem H_sub_one_cn (s : T) : CN (H s - 1) := fun n => by
  rw [map_sub, coeff_one]
  split_ifs with h
  · subst h; rw [(H_coeff_zero F)]; simp
  · simpa using F.H_cn s n

/-- The expansion with the term `u` split off. -/
theorem H_split (s u : T) :
    H s = 1 + H s * (C ((z s + z u)⁻¹) * (θ u * H u) +
      ∑ t ∈ Finset.univ.erase u, C ((z s + z t)⁻¹) * (θ t * H t)) := by
  have h : C ((z s + z u)⁻¹) * (θ u * H u) +
      ∑ t ∈ Finset.univ.erase u, C ((z s + z t)⁻¹) * (θ t * H t) =
      ∑ t, C ((z s + z t)⁻¹) * (θ t * H t) :=
    Finset.add_sum_erase _ (fun t => C ((z s + z t)⁻¹) * (θ t * H t)) (Finset.mem_univ u)
  rw [h]
  linear_combination F.eqH s

theorem rest_cn (s u : T) :
    CN (∑ t ∈ Finset.univ.erase u, C ((z s + z t)⁻¹) * (θ t * H t)) :=
  cn_sum _ _ fun t _ => cn_mul
    (cn_C (inv_nonneg.mpr (add_pos (F.hz s) (F.hz t)).le)) (cn_mul (F.θ_cn t) (F.H_cn t))

/-- `H_s` dominates `θ_t`. -/
theorem rad_H_le_theta (s t : T) : rad (H s) ≤ rad (θ t) := by
  have hc : 0 < (z s + z t)⁻¹ := inv_pos.mpr (add_pos (F.hz s) (F.hz t))
  refine rad_le_of_dom (m := 0) hc (F.θ_cn t) ?_
  have hA := (H_split F s t)
  have hE1 := (H_sub_one_cn F s)
  have hE2 := (H_sub_one_cn F t)
  set Rest := ∑ x ∈ Finset.univ.erase t, C ((z s + z x)⁻¹) * (θ x * H x) with hRest
  have heq : H s - C ((z s + z t)⁻¹) * (X ^ 0 * θ t) = 1 + H s * Rest +
      C ((z s + z t)⁻¹) * (θ t * ((H s - 1) * (H t - 1) + (H s - 1) + (H t - 1))) := by
    rw [pow_zero]
    linear_combination hA
  rw [heq]
  exact cn_add (cn_add cn_one (cn_mul (F.H_cn s) ((rest_cn F s t))))
    (cn_mul (cn_C hc.le) (cn_mul (F.θ_cn t)
      (cn_add (cn_add (cn_mul hE1 hE2) hE1) hE2)))

/-- `θ_t` dominates `X r_t`. -/
theorem rad_theta_le_r (t : T) : rad (θ t) ≤ rad (r t) := by
  have hα := F.hα t
  have hκ := F.hκ t
  have hc : 0 < α t * (2 * κ t) := by positivity
  refine rad_le_of_dom (m := 1) hc (F.r_cn t) ?_
  have hq := quot_mul (κ := κ t) (F.r0 t)
  have hQ := quot_cn hκ (F.r_cn t) (F.r0 t)
  set Q := quot (κ t) (r t) with hQd
  have heq : θ t - C (α t * (2 * κ t)) * (X ^ 1 * r t) =
      C (α t) * (X * (1 + C (κ t) ^ 2 * Q ^ 2 + C 2 * C (κ t) * (C (κ t) * (r t * Q)))) := by
    rw [(theta_form F t), ← hQd, map_mul, map_mul, pow_one]
    have h2 : (C 2 : PowerSeries ℝ) = 2 := map_ofNat C 2
    rw [h2]
    linear_combination (2 * C (α t) * X * C (κ t)) * hq
  rw [heq]
  have hk := cn_C hκ.le
  exact cn_mul (cn_C hα.le) (cn_mul cn_X (cn_add (cn_add cn_one
    (cn_mul (by simpa [sq] using cn_mul hk hk) (by simpa [sq] using cn_mul hQ hQ)))
    (cn_mul (cn_mul (cn_C (by norm_num)) hk) (cn_mul hk (cn_mul (F.r_cn t) hQ)))))

/-- Any two `H` series dominate each other up to a shift, so their radii agree. -/
theorem rad_H_le_H (s u : T) : rad (H s) ≤ rad (H u) := by
  have hzsu := add_pos (F.hz s) (F.hz u)
  have hα := F.hα u
  have hκ := F.hκ u
  have hc : 0 < (z s + z u)⁻¹ * α u := by positivity
  refine rad_le_of_dom (m := 1) hc (F.H_cn u) ?_
  have hA := (H_split F s u)
  have hθ := (theta_form F u)
  have hQ := quot_cn hκ (F.r_cn u) (F.r0 u)
  have hE := (H_sub_one_cn F s)
  set Q := quot (κ u) (r u) with hQd
  set Rest := ∑ x ∈ Finset.univ.erase u, C ((z s + z x)⁻¹) * (θ x * H x) with hRest
  set E1 := C (2 * κ u) * Q + C (κ u) * Q * (C (κ u) * Q) with hE1
  have hE1cn : CN E1 := cn_add (cn_mul (cn_C (by positivity)) hQ)
    (cn_mul (cn_mul (cn_C hκ.le) hQ) (cn_mul (cn_C hκ.le) hQ))
  have hI : (1 + C (κ u) * Q) ^ 2 = 1 + E1 := by
    rw [hE1, map_mul]
    have h2 : (C 2 : PowerSeries ℝ) = 2 := map_ofNat C 2
    rw [h2]; ring
  have heq : H s - C ((z s + z u)⁻¹ * α u) * (X ^ 1 * H u) = 1 + H s * Rest +
      C ((z s + z u)⁻¹) * (H u * (C (α u) * (X * (E1 + (H s - 1) + (H s - 1) * E1)))) := by
    rw [hI] at hθ
    rw [map_mul, pow_one]
    have hA' := hA
    rw [hθ] at hA'
    linear_combination hA'
  rw [heq]
  exact cn_add (cn_add cn_one (cn_mul (F.H_cn s) ((rest_cn F s u))))
    (cn_mul (cn_C (inv_nonneg.mpr hzsu.le)) (cn_mul (F.H_cn u) (cn_mul (cn_C hα.le)
      (cn_mul cn_X (cn_add (cn_add hE1cn hE) (cn_mul hE hE1cn))))))

/-- Where one node radius stops, every `H` radius stops. -/
theorem rad_H_le_of_stop {b : ℝ≥0∞}
    (h : ∃ t, rad (θ t) ≤ b ∨ rad (H t) ≤ b ∨ rad (r t) ≤ b) (s : T) : rad (H s) ≤ b := by
  obtain ⟨t, ht⟩ := h
  rcases ht with h | h | h
  · exact ((rad_H_le_theta F s t)).trans h
  · exact ((rad_H_le_H F s t)).trans h
  · exact ((rad_H_le_theta F s t)).trans (((rad_theta_le_r F t)).trans h)

/-- `θ(1-κ r) = α X (1 + κ Q)`, which gives the positive form of the `D` series. -/
theorem D_form (t : T) :
    θ t * H t * (1 - C (κ t) * r t) =
      C (α t) * (X * H t) + C (α t * κ t) * (X * (H t * quot (κ t) (r t))) := by
  have hq := quot_mul (κ := κ t) (F.r0 t)
  have hI : (1 + C (κ t) * quot (κ t) (r t)) * (1 - C (κ t) * r t) = 1 := by
    linear_combination C (κ t) * hq
  rw [(theta_form F t), map_mul]
  linear_combination (C (α t) * X * H t * (1 + C (κ t) * quot (κ t) (r t))) * hI

end Node


end FMSA.Convergence.PureFluidFoldSigns

/-- info: 'FMSA.Convergence.PureFluidFoldSigns.le_rad_of_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.le_rad_of_abs
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.cn_of_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.cn_of_quotient
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.cn_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.cn_add
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.cn_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.cn_mul
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.cn_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.cn_C
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.cn_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.cn_X
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.cn_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.cn_one
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.cn_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.cn_sum
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.rad_le_of_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.rad_le_of_dom
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.quot_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.quot_mul
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.quot_cn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.quot_cn
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.theta_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.theta_form
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.H_coeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.H_coeff_zero
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.H_sub_one_cn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.H_sub_one_cn
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.H_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.H_split
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.rest_cn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.rest_cn
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.rad_H_le_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.rad_H_le_theta
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.rad_theta_le_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.rad_theta_le_r
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.rad_H_le_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.rad_H_le_H
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.rad_H_le_of_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.rad_H_le_of_stop
/-- info: 'FMSA.Convergence.PureFluidFoldSigns.D_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldSigns.D_form
