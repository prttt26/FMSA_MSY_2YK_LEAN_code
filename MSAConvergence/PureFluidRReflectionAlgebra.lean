import MSAConvergence.PureFluidHDispersion

set_option linter.style.header false

/-! Finite rational reflection algebra for the pure-fluid g/U/r
coordinates. The target is an exact defect identity controlled by the
node residual, before coefficient extraction. -/
noncomputable section
namespace FMSA.Convergence.PureFluidRReflectionAlgebra
open FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidHDispersion
open FMSA.Convergence.PureFluidActualPerTailWeights
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.PureFluidActualNodeGerm
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.ExactMSA
variable {T : Type*} [Fintype T]

def reflectionKernel (z x : ℝ) : ℝ :=
  (x + z)⁻¹ - (z - x)⁻¹

/-- The symmetric pair cancellation behind the finite g reflection.
The variables q and p will be z-r at two rate nodes. -/
theorem reflection_pair_identity
    (a b x q p : ℝ)
    (hxa : x + a ≠ 0) (hxb : x + b ≠ 0)
    (ham : a - x ≠ 0) (hbm : b - x ≠ 0)
    (hab : a + b ≠ 0) :
    (p - q - x) / ((x + a) * (b - x)) +
      (q - p - x) / ((x + b) * (a - x)) =
      ((p + a - q) / (a + b)) * reflectionKernel a x +
        ((q + b - p) / (a + b)) * reflectionKernel b x := by
  unfold reflectionKernel
  have hba : b + a ≠ 0 := by simpa [add_comm] using hab
  field_simp [hxa, hxb, ham, hbm, hab, hba]
  ring

/-- A symmetric pointwise identity suffices for equality of finite
double sums, with no distinct-rate assumption. -/
theorem double_sum_of_pair_identity
    (F G : T → T → ℝ)
    (hpair : ∀ t u, F t u + F u t = G t u + G u t) :
    (∑ t, ∑ u, F t u) = ∑ t, ∑ u, G t u := by
  classical
  let SF : ℝ := ∑ t, ∑ u, F t u
  let SG : ℝ := ∑ t, ∑ u, G t u
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
  dsimp [SF, SG] at htwice ⊢
  linarith

def reflectionCrossTerm (z w q : T → ℝ) (x : ℝ) (t u : T) : ℝ :=
  w t * w u *
    ((q u - q t - x) / ((x + z t) * (z u - x)))

def reflectionNodeTerm (z w q : T → ℝ) (x : ℝ) (t u : T) : ℝ :=
  w t * w u *
    ((q u + z t - q t) / (z t + z u) * reflectionKernel (z t) x)

/-- Symmetrizing the two-pole cross term gives a node-weighted
reflection kernel. Repeated rates are allowed. -/
theorem reflection_cross_sum_eq_node_sum
    (z w q : T → ℝ) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hpair : ∀ t u, z t + z u ≠ 0) :
    (∑ t, ∑ u, reflectionCrossTerm z w q x t u) =
      ∑ t, ∑ u, reflectionNodeTerm z w q x t u := by
  apply double_sum_of_pair_identity
  intro t u
  have h := reflection_pair_identity (z t) (z u) x (q t) (q u)
    (hplus t) (hplus u) (hminus t) (hminus u) (hpair t u)
  unfold reflectionCrossTerm reflectionNodeTerm
  have hden : z u + z t = z t + z u := add_comm _ _
  rw [hden]
  calc
    _ = w t * w u *
      ((q u - q t - x) / ((x + z t) * (z u - x)) +
        (q t - q u - x) / ((x + z u) * (z t - x))) := by ring
    _ = w t * w u *
      (((q u + z t - q t) / (z t + z u)) * reflectionKernel (z t) x +
        ((q t + z u - q u) / (z t + z u)) * reflectionKernel (z u) x) := by
          rw [h]
    _ = _ := by ring

def weightPlus (z w : T → ℝ) (x : ℝ) : ℝ :=
  ∑ t, w t / (x + z t)

def weightMinus (z w : T → ℝ) (x : ℝ) : ℝ :=
  ∑ t, w t / (z t - x)

def gPlus (z w q : T → ℝ) (x : ℝ) : ℝ :=
  ∑ t, w t * q t / (x + z t)

def gMinus (z w q : T → ℝ) (x : ℝ) : ℝ :=
  ∑ t, w t * q t / (z t - x)

theorem reflection_cross_expansion
    (z w q : T → ℝ) (x : ℝ) :
    -(gPlus z w q x * weightMinus z w x) +
        gMinus z w q x * weightPlus z w x -
          x * weightPlus z w x * weightMinus z w x =
      ∑ t, ∑ u, reflectionCrossTerm z w q x t u := by
  classical
  have hGB : gPlus z w q x * weightMinus z w x =
      ∑ t, ∑ u, (w t * q t / (x + z t)) * (w u / (z u - x)) := by
    unfold gPlus weightMinus
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
  have hHA : gMinus z w q x * weightPlus z w x =
      ∑ t, ∑ u, (w t / (x + z t)) * (w u * q u / (z u - x)) := by
    rw [mul_comm]
    unfold gMinus weightPlus
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
  have hAB : weightPlus z w x * weightMinus z w x =
      ∑ t, ∑ u, (w t / (x + z t)) * (w u / (z u - x)) := by
    unfold weightPlus weightMinus
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
  rw [hGB, hHA, mul_assoc x (weightPlus z w x) (weightMinus z w x), hAB]
  calc
    _ = ∑ t, ∑ u,
        (-(w t * q t / (x + z t) * (w u / (z u - x))) +
          (w t / (x + z t)) * (w u * q u / (z u - x)) -
            x * ((w t / (x + z t)) * (w u / (z u - x)))) := by
          simp_rw [Finset.mul_sum, Finset.sum_sub_distrib,
            Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro u _
      unfold reflectionCrossTerm
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem reflection_linear_pair
    (z x q : ℝ) (hp : x + z ≠ 0) (hm : z - x ≠ 0) :
    q * reflectionKernel z x +
        x * ((x + z)⁻¹ + (z - x)⁻¹) =
      -(z - q) * reflectionKernel z x := by
  unfold reflectionKernel
  field_simp [hp, hm]
  ring

theorem reflection_linear_sum
    (z w q : T → ℝ) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0) :
    gPlus z w q x - gMinus z w q x +
        x * (weightPlus z w x + weightMinus z w x) =
      -(∑ t, w t * (z t - q t) * reflectionKernel (z t) x) := by
  unfold gPlus gMinus weightPlus weightMinus
  calc
    _ = ∑ t, w t *
        (q t * reflectionKernel (z t) x +
          x * ((x + z t)⁻¹ + (z t - x)⁻¹)) := by
            simp only [reflectionKernel, div_eq_mul_inv, mul_add, mul_sub,
              Finset.mul_sum, Finset.sum_sub_distrib,
              Finset.sum_add_distrib]
            ring_nf
    _ = -(∑ t, w t * (z t - q t) * reflectionKernel (z t) x) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro t _
      rw [reflection_linear_pair (z t) x (q t) (hplus t) (hminus t)]
      ring

theorem reflection_node_residual_at
    (z w q : T → ℝ) (t : T) :
    gPlus z w q (z t) -
        (1 - weightPlus z w (z t)) * (z t - q t) =
      -(z t - q t) +
        ∑ u, w u * ((q u + z t - q t) / (z t + z u)) := by
  have hsum :
      gPlus z w q (z t) +
          weightPlus z w (z t) * (z t - q t) =
        ∑ u, w u * ((q u + z t - q t) / (z t + z u)) := by
    unfold gPlus weightPlus
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    simp only [div_eq_mul_inv]
    ring
  calc
    _ = -(z t - q t) +
        (gPlus z w q (z t) +
          weightPlus z w (z t) * (z t - q t)) := by ring
    _ = _ := by rw [hsum]

theorem reflection_node_residual_sum
    (z w q : T → ℝ) (x : ℝ) :
    (∑ t, w t *
      (gPlus z w q (z t) -
        (1 - weightPlus z w (z t)) * (z t - q t)) *
          reflectionKernel (z t) x) =
      -(∑ t, w t * (z t - q t) * reflectionKernel (z t) x) +
        ∑ t, ∑ u, reflectionNodeTerm z w q x t u := by
  simp_rw [reflection_node_residual_at]
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
    unfold reflectionNodeTerm
    ring

/-- The full finite rational reflection defect is exactly the weighted
sum of node residuals. Repeated rates are allowed. -/
theorem reflection_defect_identity
    (z w q : T → ℝ) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hpair : ∀ t u, z t + z u ≠ 0) :
    gPlus z w q x * (1 - weightMinus z w x) -
        gMinus z w q x * (1 - weightPlus z w x) -
          x * ((1 - weightPlus z w x) *
            (1 - weightMinus z w x) - 1) =
      ∑ t, w t *
        (gPlus z w q (z t) -
          (1 - weightPlus z w (z t)) * (z t - q t)) *
            reflectionKernel (z t) x := by
  calc
    _ = (gPlus z w q x - gMinus z w q x +
          x * (weightPlus z w x + weightMinus z w x)) +
        (-(gPlus z w q x * weightMinus z w x) +
          gMinus z w q x * weightPlus z w x -
            x * weightPlus z w x * weightMinus z w x) := by ring
    _ = -(∑ t, w t * (z t - q t) * reflectionKernel (z t) x) +
        ∑ t, ∑ u, reflectionCrossTerm z w q x t u := by
          rw [reflection_linear_sum z w q x hplus hminus,
            reflection_cross_expansion]
    _ = -(∑ t, w t * (z t - q t) * reflectionKernel (z t) x) +
        ∑ t, ∑ u, reflectionNodeTerm z w q x t u := by
          rw [reflection_cross_sum_eq_node_sum z w q x
            hplus hminus hpair]
    _ = _ := (reflection_node_residual_sum z w q x).symm

/-- The finite reflection identity follows when every node residual
vanishes. -/
theorem reflection_of_node_residual_zero
    (z w q : T → ℝ) (x : ℝ)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hpair : ∀ t u, z t + z u ≠ 0)
    (hnode : ∀ t,
      gPlus z w q (z t) =
        (1 - weightPlus z w (z t)) * (z t - q t)) :
    gPlus z w q x * (1 - weightMinus z w x) -
        gMinus z w q x * (1 - weightPlus z w x) =
      x * ((1 - weightPlus z w x) *
        (1 - weightMinus z w x) - 1) := by
  have h := reflection_defect_identity z w q x hplus hminus hpair
  have hzero : (∑ t, w t *
      (gPlus z w q (z t) -
        (1 - weightPlus z w (z t)) * (z t - q t)) *
          reflectionKernel (z t) x) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    rw [hnode t]
    ring
  rw [hzero] at h
  linarith

/-- For the actual candidate U,g coordinates, the established linear
r-node equation makes the reflection defect vanish. -/
theorem candidateG_reflection_of_nodeRLinearEquation
    (z w r : T → ℝ) (x : ℝ)
    (hlin : nodeRLinearEquation z w r)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hpair : ∀ t u, z t + z u ≠ 0) :
    candidateG z w r x * candidateU z w (-x) -
        candidateG z w r (-x) * candidateU z w x =
      x * (candidateU z w x * candidateU z w (-x) - 1) := by
  let q : T → ℝ := fun t => z t - r t
  have hnode (t : T) :
      gPlus z w q (z t) =
        (1 - weightPlus z w (z t)) * (z t - q t) := by
    simpa [q, gPlus, weightPlus, candidateG, candidateU] using
      candidateG_node_eq_U_mul_r z w r hlin t
  have h := reflection_of_node_residual_zero
    z w q x hplus hminus hpair hnode
  simpa [q, gPlus, gMinus, weightPlus, weightMinus,
    candidateG, candidateU, sub_eq_add_neg, add_comm] using h

/-- Dividing the numerator reflection by the two nonzero U factors
gives the odd part of the physical r ratio. -/
theorem candidateR_reflection_of_nodeRLinearEquation
    (z w r : T → ℝ) (x : ℝ)
    (hlin : nodeRLinearEquation z w r)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hpair : ∀ t u, z t + z u ≠ 0)
    (hUx : candidateU z w x ≠ 0)
    (hUmx : candidateU z w (-x) ≠ 0) :
    candidateG z w r x / candidateU z w x -
        candidateG z w r (-x) / candidateU z w (-x) =
      x * (1 - (candidateU z w x * candidateU z w (-x))⁻¹) := by
  have h := candidateG_reflection_of_nodeRLinearEquation
    z w r x hlin hplus hminus hpair
  have hprod : candidateU z w x * candidateU z w (-x) ≠ 0 :=
    mul_ne_zero hUx hUmx
  field_simp [hUx, hUmx, hprod]
  linear_combination h

/-- The r odd part is fixed by the finite even dispersion expression.
This is the real rational identity used to determine arbitrary-order
theta coefficients near the hard-sphere seed. -/
theorem candidateR_reflection_dispersion
    (z w r : T → ℝ) (x : ℝ)
    (hlin : nodeRLinearEquation z w r)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hpair : ∀ t u, z t + z u ≠ 0)
    (hUx : candidateU z w x ≠ 0)
    (hUmx : candidateU z w (-x) ≠ 0) :
    candidateG z w r x / candidateU z w x -
        candidateG z w r (-x) / candidateU z w (-x) =
      x * (1 - (1 - ∑ t, 2 * z t *
        (w t * candidateU z w (z t)) /
          ((z t)^2 - x^2))⁻¹) := by
  rw [candidateR_reflection_of_nodeRLinearEquation z w r x hlin
    hplus hminus hpair hUx hUmx]
  rw [candidate_U_reflection_dispersion z w x hplus hminus hpair]

/-- The same reflection-dispersion identity holds for the original
Blum-Høye/Exact MSA pure-fluid root and its actual dressing coordinates.
The off-node rational formulas require x and -x to avoid the origin and
the finite tail poles. -/
theorem actualR_reflection_dispersion
    (xi : ℝ) (z K D G : T → ℝ) (x : ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, 0 < z t)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ t, MultiTail.factor xi z D G (z t) ≠ 0)
    (hUnode : ∀ t, actualU xi z D G (z t) ≠ 0)
    (hx : x ≠ 0)
    (hplus : ∀ t, x + z t ≠ 0)
    (hminus : ∀ t, z t - x ≠ 0)
    (hUx : actualU xi z D G x ≠ 0)
    (hUmx : actualU xi z D G (-x) ≠ 0) :
    actualG xi z D G x / actualU xi z D G x -
        actualG xi z D G (-x) / actualU xi z D G (-x) =
      x * (1 - (1 - ∑ t, 2 * z t *
        actualTheta xi z D G t / ((z t)^2 - x^2))⁻¹) := by
  let w := actualWeight xi z D G
  let r := actualNodeR xi z D G
  have hlin : nodeRLinearEquation z w r :=
    actualNodeR_solves_linear_system_all_rates
      xi z K D G hxi hz hroot hF hUnode
  have hnegx : -x ≠ 0 := neg_ne_zero.mpr hx
  have hminus' : ∀ t, -x + z t ≠ 0 := by
    intro t
    simpa [sub_eq_add_neg, add_comm] using hminus t
  have hpair : ∀ t u, z t + z u ≠ 0 := by
    intro t u
    exact (add_pos (hz t) (hz u)).ne'
  have hUplus : actualU xi z D G x = candidateU z w x :=
    actualU_eq_candidateU_explicit xi z D G hxi
      (fun t => (hz t).ne') x hx hplus
  have hUminus : actualU xi z D G (-x) = candidateU z w (-x) :=
    actualU_eq_candidateU_explicit xi z D G hxi
      (fun t => (hz t).ne') (-x) hnegx hminus'
  have hGplus : actualG xi z D G x = candidateG z w r x :=
    actualG_eq_candidateG_root_all_rates
      xi z K D G hxi hz hroot hF hUnode x hx hplus
  have hGminus : actualG xi z D G (-x) = candidateG z w r (-x) :=
    actualG_eq_candidateG_root_all_rates
      xi z K D G hxi hz hroot hF hUnode (-x) hnegx hminus'
  have hUcplus : candidateU z w x ≠ 0 := by
    rw [← hUplus]
    exact hUx
  have hUcminus : candidateU z w (-x) ≠ 0 := by
    rw [← hUminus]
    exact hUmx
  have hreflection := candidateR_reflection_dispersion z w r x
    hlin hplus hminus hpair hUcplus hUcminus
  have hUnodeEq (t : T) : candidateU z w (z t) =
      actualU xi z D G (z t) := by
    symm
    exact actualU_eq_candidateU_explicit xi z D G hxi
      (fun u => (hz u).ne') (z t) (hz t).ne'
        (fun u => (add_pos (hz t) (hz u)).ne')
  calc
    _ = candidateG z w r x / candidateU z w x -
        candidateG z w r (-x) / candidateU z w (-x) := by
          rw [hGplus, hGminus, hUplus, hUminus]
    _ = x * (1 - (1 - ∑ t, 2 * z t *
        (w t * candidateU z w (z t)) / ((z t)^2 - x^2))⁻¹) := hreflection
    _ = _ := by
      apply congrArg (fun v : ℝ => x * (1 - (1 - v)⁻¹))
      apply Finset.sum_congr rfl
      intro t _
      rw [hUnodeEq]
      rfl

end FMSA.Convergence.PureFluidRReflectionAlgebra

/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_pair_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_pair_identity
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.double_sum_of_pair_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.double_sum_of_pair_identity
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_cross_sum_eq_node_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_cross_sum_eq_node_sum
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_cross_expansion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_cross_expansion
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_linear_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_linear_pair
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_linear_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_linear_sum
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_node_residual_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_node_residual_at
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_node_residual_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_node_residual_sum
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_defect_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_defect_identity
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_of_node_residual_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.reflection_of_node_residual_zero
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.candidateG_reflection_of_nodeRLinearEquation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.candidateG_reflection_of_nodeRLinearEquation
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.candidateR_reflection_of_nodeRLinearEquation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.candidateR_reflection_of_nodeRLinearEquation
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.candidateR_reflection_dispersion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.candidateR_reflection_dispersion
/-- info: 'FMSA.Convergence.PureFluidRReflectionAlgebra.actualR_reflection_dispersion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRReflectionAlgebra.actualR_reflection_dispersion
