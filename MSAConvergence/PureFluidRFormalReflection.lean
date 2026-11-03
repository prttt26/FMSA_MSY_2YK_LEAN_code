import MSAConvergence.PureFluidRReflectionAlgebra
import MSAConvergence.PureFluidRFormalSolution

set_option linter.style.header false

/-! Lift the finite real rational reflection identity to the
independent multivariate theta power-series ring. -/
noncomputable section
open MvPowerSeries
namespace FMSA.Convergence.PureFluidRFormalReflection
open FMSA.Convergence.PureFluidRReflectionAlgebra
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidHFormalSolution
variable {T : Type*} [Fintype T] [DecidableEq T]

def pairDefect (a b x : ℝ)
    (q p : MvPowerSeries T ℝ) : MvPowerSeries T ℝ :=
  ((p - q - C x) * C (((x + a) * (b - x))⁻¹) +
    (q - p - C x) * C (((x + b) * (a - x))⁻¹)) -
    ((p + C a - q) * C ((a + b)⁻¹) * C (reflectionKernel a x) +
      (q + C b - p) * C ((a + b)⁻¹) * C (reflectionKernel b x))

omit [Fintype T] [DecidableEq T] in
theorem pairDefect_affine (a b x : ℝ)
    (q p : MvPowerSeries T ℝ) :
    pairDefect a b x q p =
      q * pairDefect a b x 1 0 +
      p * pairDefect a b x 0 1 +
      (1 - q - p) * pairDefect a b x 0 0 := by
  unfold pairDefect
  ring

omit [Fintype T] [DecidableEq T] in
theorem pairDefect_scalar_zero (a b x q p : ℝ)
    (hxa : x + a ≠ 0) (hxb : x + b ≠ 0)
    (ham : a - x ≠ 0) (hbm : b - x ≠ 0)
    (hab : a + b ≠ 0) :
    pairDefect a b x (C q : MvPowerSeries T ℝ) (C p) = 0 := by
  have h := reflection_pair_identity a b x q p hxa hxb ham hbm hab
  have hm := congrArg (C : ℝ →+* MvPowerSeries T ℝ) h
  unfold pairDefect
  simp only [div_eq_mul_inv] at hm
  simp only [map_add, map_sub, map_mul] at hm
  linear_combination hm

omit [Fintype T] [DecidableEq T] in
theorem reflection_pair_identity_formal
    (a b x : ℝ) (q p : MvPowerSeries T ℝ)
    (hxa : x + a ≠ 0) (hxb : x + b ≠ 0)
    (ham : a - x ≠ 0) (hbm : b - x ≠ 0)
    (hab : a + b ≠ 0) :
    pairDefect a b x q p = 0 := by
  rw [pairDefect_affine]
  have h00 := pairDefect_scalar_zero (T := T) a b x 0 0
    hxa hxb ham hbm hab
  have h10 := pairDefect_scalar_zero (T := T) a b x 1 0
    hxa hxb ham hbm hab
  have h01 := pairDefect_scalar_zero (T := T) a b x 0 1
    hxa hxb ham hbm hab
  simp only [map_zero, map_one] at h00 h10 h01
  rw [h00, h10, h01]
  ring

omit [DecidableEq T] in
theorem double_sum_of_pair_identity_formal
    (F G : T → T → MvPowerSeries T ℝ)
    (hpair : ∀ t u, F t u + F u t = G t u + G u t) :
    (∑ t, ∑ u, F t u) = ∑ t, ∑ u, G t u := by
  classical
  let SF : MvPowerSeries T ℝ := ∑ t, ∑ u, F t u
  let SG : MvPowerSeries T ℝ := ∑ t, ∑ u, G t u
  have hswapF : (∑ t, ∑ u, F u t) = SF := by
    dsimp [SF]
    rw [Finset.sum_comm]
  have hswapG : (∑ t, ∑ u, G u t) = SG := by
    dsimp [SG]
    rw [Finset.sum_comm]
  have htwice : SF + SF = SG + SG := by
    calc
      SF + SF = ∑ t, ∑ u, (F t u + F u t) := by
        simp only [Finset.sum_add_distrib]
        rw [hswapF]
      _ = ∑ t, ∑ u, (G t u + G u t) := by
        apply Finset.sum_congr rfl
        intro t _
        exact Finset.sum_congr rfl (fun u _ => hpair t u)
      _ = SG + SG := by
        simp only [Finset.sum_add_distrib]
        rw [hswapG]
  ext m
  have hc := congrArg (MvPowerSeries.coeff m) htwice
  simp only [map_add] at hc
  dsimp [SF, SG] at hc
  linarith

def formalCrossTerm (z : T → ℝ)
    (w q : T → MvPowerSeries T ℝ) (x : ℝ) (t u : T) :
    MvPowerSeries T ℝ :=
  w t * w u *
    ((q u - q t - C x) * C (((x + z t) * (z u - x))⁻¹))

def formalNodeTerm (z : T → ℝ)
    (w q : T → MvPowerSeries T ℝ) (x : ℝ) (t u : T) :
    MvPowerSeries T ℝ :=
  w t * w u *
    ((q u + C (z t) - q t) * C ((z t + z u)⁻¹) *
      C (reflectionKernel (z t) x))

omit [DecidableEq T] in
theorem formal_cross_sum_eq_node_sum
    (z : T → ℝ) (w q : T → MvPowerSeries T ℝ) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hpair : ∀ t u, z t + z u ≠ 0) :
    (∑ t, ∑ u, formalCrossTerm z w q x t u) =
      ∑ t, ∑ u, formalNodeTerm z w q x t u := by
  classical
  apply double_sum_of_pair_identity_formal
  intro t u
  have h := reflection_pair_identity_formal
    (z t) (z u) x (q t) (q u)
    (hplus t) (hplus u) (hminus t) (hminus u) (hpair t u)
  have heq := sub_eq_zero.mp h
  unfold formalCrossTerm formalNodeTerm
  have hden : z u + z t = z t + z u := add_comm _ _
  rw [hden]
  calc
    _ = w t * w u *
      ((q u - q t - C x) * C (((x + z t) * (z u - x))⁻¹) +
        (q t - q u - C x) * C (((x + z u) * (z t - x))⁻¹)) := by ring
    _ = w t * w u *
      ((q u + C (z t) - q t) * C ((z t + z u)⁻¹) *
          C (reflectionKernel (z t) x) +
        (q t + C (z u) - q u) * C ((z t + z u)⁻¹) *
          C (reflectionKernel (z u) x)) := by
            rw [heq]
    _ = _ := by ring

def formalWeightPlus (z : T → ℝ)
    (w : T → MvPowerSeries T ℝ) (x : ℝ) : MvPowerSeries T ℝ :=
  ∑ t, w t * C ((x + z t)⁻¹)

def formalWeightMinus (z : T → ℝ)
    (w : T → MvPowerSeries T ℝ) (x : ℝ) : MvPowerSeries T ℝ :=
  ∑ t, w t * C ((z t - x)⁻¹)

def formalGPlus (z : T → ℝ)
    (w q : T → MvPowerSeries T ℝ) (x : ℝ) : MvPowerSeries T ℝ :=
  ∑ t, w t * q t * C ((x + z t)⁻¹)

def formalGMinus (z : T → ℝ)
    (w q : T → MvPowerSeries T ℝ) (x : ℝ) : MvPowerSeries T ℝ :=
  ∑ t, w t * q t * C ((z t - x)⁻¹)

omit [DecidableEq T] in
theorem formal_cross_expansion
    (z : T → ℝ) (w q : T → MvPowerSeries T ℝ) (x : ℝ) :
    -(formalGPlus z w q x * formalWeightMinus z w x) +
        formalGMinus z w q x * formalWeightPlus z w x -
          C x * formalWeightPlus z w x * formalWeightMinus z w x =
      ∑ t, ∑ u, formalCrossTerm z w q x t u := by
  classical
  have hGB : formalGPlus z w q x * formalWeightMinus z w x =
      ∑ t, ∑ u,
        (w t * q t * C ((x + z t)⁻¹)) *
          (w u * C ((z u - x)⁻¹)) := by
    unfold formalGPlus formalWeightMinus
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
  have hHA : formalGMinus z w q x * formalWeightPlus z w x =
      ∑ t, ∑ u,
        (w t * C ((x + z t)⁻¹)) *
          (w u * q u * C ((z u - x)⁻¹)) := by
    rw [mul_comm]
    unfold formalGMinus formalWeightPlus
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
  have hAB : formalWeightPlus z w x * formalWeightMinus z w x =
      ∑ t, ∑ u,
        (w t * C ((x + z t)⁻¹)) *
          (w u * C ((z u - x)⁻¹)) := by
    unfold formalWeightPlus formalWeightMinus
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
  rw [hGB, hHA, mul_assoc (C x) (formalWeightPlus z w x)
    (formalWeightMinus z w x), hAB]
  calc
    _ = ∑ t, ∑ u,
        (-(w t * q t * C ((x + z t)⁻¹) *
            (w u * C ((z u - x)⁻¹))) +
          (w t * C ((x + z t)⁻¹)) *
            (w u * q u * C ((z u - x)⁻¹)) -
          C x * ((w t * C ((x + z t)⁻¹)) *
            (w u * C ((z u - x)⁻¹)))) := by
          simp_rw [Finset.mul_sum, Finset.sum_sub_distrib,
            Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro u _
      unfold formalCrossTerm
      rw [mul_inv_rev, map_mul]
      ring

omit [Fintype T] [DecidableEq T] in
theorem formal_linear_pair
    (z x : ℝ) (q : MvPowerSeries T ℝ)
    (hp : x + z ≠ 0) (hm : z - x ≠ 0) :
    q * C (reflectionKernel z x) +
        C x * (C ((x + z)⁻¹) + C ((z - x)⁻¹)) =
      -(C z - q) * C (reflectionKernel z x) := by
  have h := reflection_linear_pair z x 0 hp hm
  have hmapped := congrArg (C : ℝ →+* MvPowerSeries T ℝ) h
  simp only [map_add, map_sub, map_mul, map_neg, map_zero] at hmapped
  linear_combination hmapped

omit [DecidableEq T] in
theorem formal_linear_sum
    (z : T → ℝ) (w q : T → MvPowerSeries T ℝ) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0) :
    formalGPlus z w q x - formalGMinus z w q x +
        C x * (formalWeightPlus z w x + formalWeightMinus z w x) =
      -(∑ t, w t * (C (z t) - q t) * C (reflectionKernel (z t) x)) := by
  unfold formalGPlus formalGMinus formalWeightPlus formalWeightMinus
  calc
    _ = ∑ t, w t *
        (q t * C (reflectionKernel (z t) x) +
          C x * (C ((x + z t)⁻¹) + C ((z t - x)⁻¹))) := by
            simp only [reflectionKernel, map_sub, mul_add, mul_sub,
              Finset.mul_sum, Finset.sum_sub_distrib,
              Finset.sum_add_distrib]
            ring_nf
    _ = -(∑ t, w t * (C (z t) - q t) *
      C (reflectionKernel (z t) x)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro t _
      rw [formal_linear_pair (z t) x (q t) (hplus t) (hminus t)]
      ring

omit [DecidableEq T] in
theorem formal_node_residual_at
    (z : T → ℝ) (w q : T → MvPowerSeries T ℝ) (t : T) :
    formalGPlus z w q (z t) -
        (1 - formalWeightPlus z w (z t)) * (C (z t) - q t) =
      -(C (z t) - q t) +
        ∑ u, w u * ((q u + C (z t) - q t) *
          C ((z t + z u)⁻¹)) := by
  have hsum :
      formalGPlus z w q (z t) +
          formalWeightPlus z w (z t) * (C (z t) - q t) =
        ∑ u, w u * ((q u + C (z t) - q t) *
          C ((z t + z u)⁻¹)) := by
    unfold formalGPlus formalWeightPlus
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  calc
    _ = -(C (z t) - q t) +
      (formalGPlus z w q (z t) +
        formalWeightPlus z w (z t) * (C (z t) - q t)) := by ring
    _ = _ := by rw [hsum]

omit [DecidableEq T] in
theorem formal_node_residual_sum
    (z : T → ℝ) (w q : T → MvPowerSeries T ℝ) (x : ℝ) :
    (∑ t, w t *
      (formalGPlus z w q (z t) -
        (1 - formalWeightPlus z w (z t)) * (C (z t) - q t)) *
          C (reflectionKernel (z t) x)) =
      -(∑ t, w t * (C (z t) - q t) *
        C (reflectionKernel (z t) x)) +
        ∑ t, ∑ u, formalNodeTerm z w q x t u := by
  simp_rw [formal_node_residual_at]
  simp only [mul_add, Finset.mul_sum]
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  · apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    unfold formalNodeTerm
    ring

omit [DecidableEq T] in
theorem formal_reflection_defect_identity
    (z : T → ℝ) (w q : T → MvPowerSeries T ℝ) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hpair : ∀ t u, z t + z u ≠ 0) :
    formalGPlus z w q x * (1 - formalWeightMinus z w x) -
        formalGMinus z w q x * (1 - formalWeightPlus z w x) -
          C x * ((1 - formalWeightPlus z w x) *
            (1 - formalWeightMinus z w x) - 1) =
      ∑ t, w t *
        (formalGPlus z w q (z t) -
          (1 - formalWeightPlus z w (z t)) * (C (z t) - q t)) *
            C (reflectionKernel (z t) x) := by
  calc
    _ = (formalGPlus z w q x - formalGMinus z w q x +
          C x * (formalWeightPlus z w x + formalWeightMinus z w x)) +
        (-(formalGPlus z w q x * formalWeightMinus z w x) +
          formalGMinus z w q x * formalWeightPlus z w x -
            C x * formalWeightPlus z w x * formalWeightMinus z w x) := by ring
    _ = -(∑ t, w t * (C (z t) - q t) *
          C (reflectionKernel (z t) x)) +
        ∑ t, ∑ u, formalCrossTerm z w q x t u := by
          rw [formal_linear_sum z w q x hplus hminus,
            formal_cross_expansion]
    _ = -(∑ t, w t * (C (z t) - q t) *
          C (reflectionKernel (z t) x)) +
        ∑ t, ∑ u, formalNodeTerm z w q x t u := by
          rw [formal_cross_sum_eq_node_sum z w q x
            hplus hminus hpair]
    _ = _ := (formal_node_residual_sum z w q x).symm

omit [DecidableEq T] in
theorem formal_reflection_of_node_residual_zero
    (z : T → ℝ) (w q : T → MvPowerSeries T ℝ) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hpair : ∀ t u, z t + z u ≠ 0)
    (hnode : ∀ t,
      formalGPlus z w q (z t) =
        (1 - formalWeightPlus z w (z t)) * (C (z t) - q t)) :
    formalGPlus z w q x * (1 - formalWeightMinus z w x) -
        formalGMinus z w q x * (1 - formalWeightPlus z w x) =
      C x * ((1 - formalWeightPlus z w x) *
        (1 - formalWeightMinus z w x) - 1) := by
  have h := formal_reflection_defect_identity z w q x
    hplus hminus hpair
  have hzero : (∑ t, w t *
      (formalGPlus z w q (z t) -
        (1 - formalWeightPlus z w (z t)) * (C (z t) - q t)) *
          C (reflectionKernel (z t) x)) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    rw [hnode t]
    ring
  rw [hzero] at h
  exact sub_eq_zero.mp h

def formalWeight (z : T → ℝ) (t : T) : MvPowerSeries T ℝ :=
  X t * physicalH z t

def formalNodeQ (z : T → ℝ) (t : T) : MvPowerSeries T ℝ :=
  C (z t) - RSeries z t

theorem formal_H_node_factor
    (z : T → ℝ) (s : T) :
    physicalH z s * (1 - formalWeightPlus z (formalWeight z) (z s)) = 1 := by
  classical
  have hh := (HSeries_system (fun s t => (z s + z t)⁻¹) s)
  change physicalH z s = 1 +
    ∑ t, C ((z s + z t)⁻¹) *
      (X t * (physicalH z s * physicalH z t)) at hh
  have hsum :
      physicalH z s * formalWeightPlus z (formalWeight z) (z s) =
        ∑ t, C ((z s + z t)⁻¹) *
          (X t * (physicalH z s * physicalH z t)) := by
    unfold formalWeightPlus formalWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [← hsum] at hh
  linear_combination hh

theorem formal_R_node_G
    (z : T → ℝ) (s : T) :
    RSeries z s = physicalH z s *
      formalGPlus z (formalWeight z) (formalNodeQ z) (z s) := by
  classical
  have hr := RSeries_system z s
  change RSeries z s = ∑ t, C ((z s + z t)⁻¹) *
    (X t * ((physicalH z s * physicalH z t) *
      (C (z t) - RSeries z t))) at hr
  rw [hr]
  unfold formalGPlus formalWeight formalNodeQ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem formal_R_node_residual_zero
    (z : T → ℝ) (s : T) :
    formalGPlus z (formalWeight z) (formalNodeQ z) (z s) =
      (1 - formalWeightPlus z (formalWeight z) (z s)) *
        (C (z s) - formalNodeQ z s) := by
  have hh := formal_H_node_factor z s
  have hr := formal_R_node_G z s
  have hq : C (z s) - formalNodeQ z s = RSeries z s := by
    unfold formalNodeQ
    ring
  rw [hq, hr]
  linear_combination - (congrArg
    (fun v : MvPowerSeries T ℝ =>
      v * formalGPlus z (formalWeight z) (formalNodeQ z) (z s)) hh)

/-- The exact multivariate formal H/r solution satisfies the finite
reflection identity at every real frequency away from its poles. -/
theorem physical_formal_R_reflection
    (z : T → ℝ) (hz : ∀ t, 0 < z t) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0) :
    formalGPlus z (formalWeight z) (formalNodeQ z) x *
        (1 - formalWeightMinus z (formalWeight z) x) -
      formalGMinus z (formalWeight z) (formalNodeQ z) x *
        (1 - formalWeightPlus z (formalWeight z) x) =
      C x * ((1 - formalWeightPlus z (formalWeight z) x) *
        (1 - formalWeightMinus z (formalWeight z) x) - 1) := by
  apply formal_reflection_of_node_residual_zero z
    (formalWeight z) (formalNodeQ z) x hplus hminus
  · intro t u
    exact (add_pos (hz t) (hz u)).ne'
  · exact formal_R_node_residual_zero z

end FMSA.Convergence.PureFluidRFormalReflection

/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.pairDefect_affine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.pairDefect_affine
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.pairDefect_scalar_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.pairDefect_scalar_zero
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.reflection_pair_identity_formal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.reflection_pair_identity_formal
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.double_sum_of_pair_identity_formal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.double_sum_of_pair_identity_formal
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.formal_cross_sum_eq_node_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.formal_cross_sum_eq_node_sum
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.formal_cross_expansion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.formal_cross_expansion
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.formal_linear_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.formal_linear_pair
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.formal_linear_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.formal_linear_sum
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.formal_node_residual_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.formal_node_residual_at
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.formal_node_residual_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.formal_node_residual_sum
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.formal_reflection_defect_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.formal_reflection_defect_identity
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.formal_reflection_of_node_residual_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.formal_reflection_of_node_residual_zero
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.formal_H_node_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.formal_H_node_factor
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.formal_R_node_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.formal_R_node_G
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.formal_R_node_residual_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.formal_R_node_residual_zero
/-- info: 'FMSA.Convergence.PureFluidRFormalReflection.physical_formal_R_reflection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalReflection.physical_formal_R_reflection
