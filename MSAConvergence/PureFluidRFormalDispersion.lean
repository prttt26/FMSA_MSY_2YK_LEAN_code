import MSAConvergence.PureFluidRFormalReflection

set_option linter.style.header false

/-! The even dispersion product for the independent-theta formal
H/r system. All denominators in this module are real constants. -/
noncomputable section
open MvPowerSeries
namespace FMSA.Convergence.PureFluidRFormalDispersion
open FMSA.Convergence.PureFluidRFormalReflection
open FMSA.Convergence.PureFluidRFormalSolution
variable {T : Type*} [Fintype T] [DecidableEq T]

omit [DecidableEq T] in
theorem formal_two_pole_sum
    (z : T → ℝ) (w : T → MvPowerSeries T ℝ) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hpair : ∀ t u, z t + z u ≠ 0) :
    formalWeightPlus z w x * formalWeightMinus z w x =
      ∑ t, (C ((x + z t)⁻¹) + C ((z t - x)⁻¹)) * w t *
        formalWeightPlus z w (z t) := by
  classical
  have hterm (t u : T) :
      (w t * C ((x + z t)⁻¹)) * (w u * C ((z u - x)⁻¹)) =
        w t * w u * C ((z t + z u)⁻¹) *
          (C ((x + z t)⁻¹) + C ((z u - x)⁻¹)) := by
    have hscalar : (x + z t)⁻¹ * (z u - x)⁻¹ =
        (z t + z u)⁻¹ * ((x + z t)⁻¹ + (z u - x)⁻¹) := by
      field_simp [hplus t, hminus u, hpair t u]
      ring
    have hm := congrArg (C : ℝ →+* MvPowerSeries T ℝ) hscalar
    simp only [map_mul, map_add] at hm
    calc
      _ = w t * w u *
          (C ((x + z t)⁻¹) * C ((z u - x)⁻¹)) := by ring
      _ = _ := by rw [hm]; ring
  have hswap :
      (∑ t, ∑ u, w t * w u * C ((z t + z u)⁻¹) *
          C ((z u - x)⁻¹)) =
      (∑ t, ∑ u, w t * w u * C ((z t + z u)⁻¹) *
          C ((z t - x)⁻¹)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    rw [add_comm (z u) (z t)]
    ring
  calc
    formalWeightPlus z w x * formalWeightMinus z w x =
        ∑ t, ∑ u, (w t * C ((x + z t)⁻¹)) *
          (w u * C ((z u - x)⁻¹)) := by
            unfold formalWeightPlus formalWeightMinus
            rw [Finset.sum_mul]
            simp_rw [Finset.mul_sum]
    _ = ∑ t, ∑ u, w t * w u * C ((z t + z u)⁻¹) *
          (C ((x + z t)⁻¹) + C ((z u - x)⁻¹)) := by
            apply Finset.sum_congr rfl
            intro t _
            exact Finset.sum_congr rfl (fun u _ => hterm t u)
    _ = (∑ t, ∑ u, w t * w u * C ((z t + z u)⁻¹) *
            C ((x + z t)⁻¹)) +
        (∑ t, ∑ u, w t * w u * C ((z t + z u)⁻¹) *
            C ((z u - x)⁻¹)) := by
              simp_rw [mul_add, Finset.sum_add_distrib]
    _ = (∑ t, ∑ u, w t * w u * C ((z t + z u)⁻¹) *
            C ((x + z t)⁻¹)) +
        (∑ t, ∑ u, w t * w u * C ((z t + z u)⁻¹) *
            C ((z t - x)⁻¹)) := by rw [hswap]
    _ = ∑ t, (C ((x + z t)⁻¹) + C ((z t - x)⁻¹)) * w t *
          formalWeightPlus z w (z t) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro t _
            unfold formalWeightPlus
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro u _
            ring

omit [DecidableEq T] in
theorem formal_U_reflection_dispersion
    (z : T → ℝ) (w : T → MvPowerSeries T ℝ) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hpair : ∀ t u, z t + z u ≠ 0) :
    (1 - formalWeightPlus z w x) * (1 - formalWeightMinus z w x) =
      1 - ∑ t, C (2 * z t / ((z t)^2 - x^2)) * w t *
        (1 - formalWeightPlus z w (z t)) := by
  classical
  let c (t : T) : MvPowerSeries T ℝ :=
    C ((x + z t)⁻¹) + C ((z t - x)⁻¹)
  have hc (t : T) : c t = C (2 * z t / ((z t)^2 - x^2)) := by
    have hsq : (z t)^2 - x^2 ≠ 0 := by
      rw [show (z t)^2 - x^2 = (z t + x) * (z t - x) by ring]
      exact mul_ne_zero (by simpa only [add_comm] using hplus t) (hminus t)
    have hscalar : (x + z t)⁻¹ + (z t - x)⁻¹ =
        2 * z t / ((z t)^2 - x^2) := by
      field_simp [hplus t, hminus t, hsq]
      ring
    exact (map_add (C : ℝ →+* MvPowerSeries T ℝ) _ _).symm.trans
      (congrArg (C : ℝ →+* MvPowerSeries T ℝ) hscalar)
  have hlin : formalWeightPlus z w x + formalWeightMinus z w x =
      ∑ t, c t * w t := by
    unfold formalWeightPlus formalWeightMinus
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    dsimp [c]
    ring
  have hprod : formalWeightPlus z w x * formalWeightMinus z w x =
      ∑ t, c t * w t * formalWeightPlus z w (z t) := by
    simpa only [c] using formal_two_pole_sum z w x hplus hminus hpair
  calc
    (1 - formalWeightPlus z w x) * (1 - formalWeightMinus z w x) =
        1 - (formalWeightPlus z w x + formalWeightMinus z w x) +
          formalWeightPlus z w x * formalWeightMinus z w x := by ring
    _ = 1 - ∑ t, c t * w t *
          (1 - formalWeightPlus z w (z t)) := by
            rw [hlin, hprod]
            simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
            ring
    _ = _ := by simp_rw [hc]

theorem physical_formal_U_dispersion
    (z : T → ℝ) (hz : ∀ t, 0 < z t) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0) :
    (1 - formalWeightPlus z (formalWeight z) x) *
        (1 - formalWeightMinus z (formalWeight z) x) =
      1 - ∑ t, C (2 * z t / ((z t)^2 - x^2)) * X t := by
  classical
  have hpair : ∀ t u, z t + z u ≠ 0 := by
    intro t u
    exact (add_pos (hz t) (hz u)).ne'
  rw [formal_U_reflection_dispersion z (formalWeight z) x
    hplus hminus hpair]
  apply congrArg (fun v : MvPowerSeries T ℝ => 1 - v)
  apply Finset.sum_congr rfl
  intro t _
  have hh := formal_H_node_factor z t
  have hw : formalWeight z t *
      (1 - formalWeightPlus z (formalWeight z) (z t)) = X t := by
    change (X t * physicalH z t) *
      (1 - formalWeightPlus z (formalWeight z) (z t)) = X t
    calc
      _ = X t * (physicalH z t *
          (1 - formalWeightPlus z (formalWeight z) (z t))) := by ring
      _ = _ := by rw [hh, mul_one]
  rw [mul_assoc, hw]

def physicalFormalU (z : T → ℝ) (x : ℝ) : MvPowerSeries T ℝ :=
  1 - formalWeightPlus z (formalWeight z) x

def physicalFormalG (z : T → ℝ) (x : ℝ) : MvPowerSeries T ℝ :=
  formalGPlus z (formalWeight z) (formalNodeQ z) x

def physicalFormalR (z : T → ℝ) (x : ℝ) : MvPowerSeries T ℝ :=
  physicalFormalG z x * (physicalFormalU z x)⁻¹

theorem physicalFormalU_constantCoeff_one (z : T → ℝ) (x : ℝ) :
    MvPowerSeries.constantCoeff (physicalFormalU z x) = 1 := by
  classical
  simp [physicalFormalU, formalWeightPlus, formalWeight,
    MvPowerSeries.constantCoeff_X]

theorem physicalFormalU_mul_inv (z : T → ℝ) (x : ℝ) :
    physicalFormalU z x * (physicalFormalU z x)⁻¹ = 1 := by
  apply MvPowerSeries.mul_inv_cancel
  rw [physicalFormalU_constantCoeff_one]
  exact one_ne_zero

/-- The off-node formal rational coordinate specializes exactly to
the independently constructed r-node series at every positive node. -/
theorem physicalFormalR_at_node (z : T → ℝ) (s : T) :
    physicalFormalR z (z s) =
      FMSA.Convergence.PureFluidRFormalSolution.RSeries z s := by
  have hHU := formal_H_node_factor z s
  change FMSA.Convergence.PureFluidRFormalSolution.physicalH z s *
    physicalFormalU z (z s) = 1 at hHU
  have hUinv := physicalFormalU_mul_inv z (z s)
  have hHinv : FMSA.Convergence.PureFluidRFormalSolution.physicalH z s =
      (physicalFormalU z (z s))⁻¹ := by
    calc
      _ = FMSA.Convergence.PureFluidRFormalSolution.physicalH z s *
          (physicalFormalU z (z s) * (physicalFormalU z (z s))⁻¹) := by
            rw [hUinv, mul_one]
      _ = (FMSA.Convergence.PureFluidRFormalSolution.physicalH z s *
          physicalFormalU z (z s)) * (physicalFormalU z (z s))⁻¹ := by ring
      _ = _ := by rw [hHU, one_mul]
  have hr := formal_R_node_G z s
  unfold physicalFormalR physicalFormalG
  rw [hr, hHinv]
  ring

/-- The formal off-node r coordinate obeys a linear resolvent
fixed-point equation; its X-weighted term lowers coefficient degree. -/
theorem physicalFormalR_fixed_point (z : T → ℝ) (x : ℝ) :
    physicalFormalR z x =
      physicalFormalG z x +
        formalWeightPlus z (formalWeight z) x * physicalFormalR z x := by
  have hUinv := physicalFormalU_mul_inv z x
  have hUR : physicalFormalU z x * physicalFormalR z x =
      physicalFormalG z x := by
    unfold physicalFormalR
    calc
      _ = (physicalFormalU z x * (physicalFormalU z x)⁻¹) *
          physicalFormalG z x := by ring
      _ = _ := by rw [hUinv, one_mul]
  unfold physicalFormalU at hUR
  linear_combination hUR

/-- A degree-lowering off-node recursion with the same original
formal r nodes, suitable for rational coefficient induction. -/
theorem physicalFormalR_series_recursion (z : T → ℝ) (x : ℝ) :
    physicalFormalR z x =
      ∑ t, C ((x + z t)⁻¹) *
        (X t * FMSA.Convergence.PureFluidRFormalSolution.physicalH z t *
          (C (z t) - FMSA.Convergence.PureFluidRFormalSolution.RSeries z t +
            physicalFormalR z x)) := by
  classical
  calc
    physicalFormalR z x = physicalFormalG z x +
        formalWeightPlus z (formalWeight z) x * physicalFormalR z x :=
          physicalFormalR_fixed_point z x
    _ = ∑ t, (formalWeight z t * formalNodeQ z t * C ((x + z t)⁻¹) +
          (formalWeight z t * C ((x + z t)⁻¹)) * physicalFormalR z x) := by
            unfold physicalFormalG formalGPlus formalWeightPlus
            rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      unfold formalWeight formalNodeQ
      ring

theorem physicalFormalR_coeff_recursion
    (z : T → ℝ) (x : ℝ) (m : T →₀ ℕ) :
    MvPowerSeries.coeff m (physicalFormalR z x) =
      ∑ t, (x + z t)⁻¹ * MvPowerSeries.coeff m
        (X t * FMSA.Convergence.PureFluidRFormalSolution.physicalH z t *
          (C (z t) - FMSA.Convergence.PureFluidRFormalSolution.RSeries z t +
            physicalFormalR z x)) := by
  classical
  conv_lhs => rw [physicalFormalR_series_recursion]
  simp only [map_sum, MvPowerSeries.coeff_C_mul]

theorem physicalFormalU_minus (z : T → ℝ) (x : ℝ) :
    1 - formalWeightMinus z (formalWeight z) x = physicalFormalU z (-x) := by
  unfold physicalFormalU formalWeightMinus formalWeightPlus
  apply congrArg (fun v : MvPowerSeries T ℝ => 1 - v)
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  congr 1
  ring

theorem physicalFormalG_minus (z : T → ℝ) (x : ℝ) :
    formalGMinus z (formalWeight z) (formalNodeQ z) x =
      physicalFormalG z (-x) := by
  unfold physicalFormalG formalGMinus formalGPlus
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  congr 1
  ring

/-- The odd part of the formal r rational coordinate is determined by
the explicit linear theta dispersion series. -/
theorem physical_formal_R_odd_dispersion
    (z : T → ℝ) (hz : ∀ t, 0 < z t) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0) :
    physicalFormalR z x - physicalFormalR z (-x) =
      C x * (1 -
        (1 - ∑ t, C (2 * z t / ((z t)^2 - x^2)) * X t)⁻¹) := by
  classical
  let Ux := physicalFormalU z x
  let Um := physicalFormalU z (-x)
  let Gx := physicalFormalG z x
  let Gm := physicalFormalG z (-x)
  let V : MvPowerSeries T ℝ :=
    1 - ∑ t, C (2 * z t / ((z t)^2 - x^2)) * X t
  have hprod : Ux * Um = V := by
    have h := physical_formal_U_dispersion z hz x hplus hminus
    rw [physicalFormalU_minus] at h
    exact h
  have href : Gx * Um - Gm * Ux = C x * (Ux * Um - 1) := by
    have h := physical_formal_R_reflection z hz x hplus hminus
    rw [physicalFormalU_minus, physicalFormalG_minus] at h
    exact h
  have hUx : Ux * Ux⁻¹ = 1 := physicalFormalU_mul_inv z x
  have hUm : Um * Um⁻¹ = 1 := physicalFormalU_mul_inv z (-x)
  have hconst : MvPowerSeries.constantCoeff (Ux * Um) = 1 := by
    rw [map_mul]
    change MvPowerSeries.constantCoeff (physicalFormalU z x) *
      MvPowerSeries.constantCoeff (physicalFormalU z (-x)) = 1
    rw [physicalFormalU_constantCoeff_one,
      physicalFormalU_constantCoeff_one]
    ring
  have hInv : (Ux * Um) * (Ux * Um)⁻¹ = 1 := by
    apply MvPowerSeries.mul_inv_cancel
    rw [hconst]
    exact one_ne_zero
  have hnonzero : Ux * Um ≠ 0 := by
    intro he
    have hc := congrArg MvPowerSeries.constantCoeff he
    rw [hconst] at hc
    simp at hc
  have hL : (Gx * Ux⁻¹ - Gm * Um⁻¹) * (Ux * Um) =
      Gx * Um - Gm * Ux := by
    linear_combination (Gx * Um) * hUx - (Gm * Ux) * hUm
  have hR : (C x * (1 - (Ux * Um)⁻¹)) * (Ux * Um) =
      C x * (Ux * Um - 1) := by
    linear_combination -(C x) * hInv
  change Gx * Ux⁻¹ - Gm * Um⁻¹ = C x * (1 - V⁻¹)
  rw [← hprod]
  apply mul_right_cancel₀ hnonzero
  calc
    (Gx * Ux⁻¹ - Gm * Um⁻¹) * (Ux * Um) =
        Gx * Um - Gm * Ux := hL
    _ = C x * (Ux * Um - 1) := href
    _ = (C x * (1 - (Ux * Um)⁻¹)) * (Ux * Um) := hR.symm

end FMSA.Convergence.PureFluidRFormalDispersion

/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.formal_two_pole_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.formal_two_pole_sum
/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.formal_U_reflection_dispersion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.formal_U_reflection_dispersion
/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.physical_formal_U_dispersion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.physical_formal_U_dispersion
/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalU_constantCoeff_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalU_constantCoeff_one
/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalU_mul_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalU_mul_inv
/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalR_at_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalR_at_node
/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalR_fixed_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalR_fixed_point
/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalR_series_recursion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalR_series_recursion
/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalR_coeff_recursion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalR_coeff_recursion
/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalU_minus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalU_minus
/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalG_minus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.physicalFormalG_minus
/-- info: 'FMSA.Convergence.PureFluidRFormalDispersion.physical_formal_R_odd_dispersion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalDispersion.physical_formal_R_odd_dispersion
