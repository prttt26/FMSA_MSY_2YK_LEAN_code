import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-! The arbitrary-finite distinct-node partial fraction identity for
the rational kernel entering pure-fluid r-coefficient positivity. -/
noncomputable section
namespace FMSA.Convergence.PureFluidRPartialFraction
open Polynomial Finset
variable {ι : Type*} [DecidableEq ι]

/-- Lagrange interpolation of the identity polynomial gives the
partial fraction formula for `x / prod (x-v_i)`. -/
theorem lagrange_linear_partial_fraction
    (s : Finset ι) (v : ι → ℝ) (x : ℝ)
    (hs : 2 ≤ s.card) (hv : Set.InjOn v s)
    (hx : ∀ i ∈ s, x ≠ v i) :
    x / (Lagrange.nodal s v).eval x =
      ∑ i ∈ s, Lagrange.nodalWeight s v i *
        (x - v i)⁻¹ * v i := by
  have hdegree : (Polynomial.X : ℝ[X]).degree < s.card := by
    rw [Polynomial.degree_X, Nat.cast_withBot]
    exact WithBot.coe_lt_coe.mpr (by omega)
  have hpoly : (Polynomial.X : ℝ[X]) =
      Lagrange.interpolate s v v := by
    simpa using (Lagrange.eq_interpolate hv hdegree :
      (Polynomial.X : ℝ[X]) =
        Lagrange.interpolate s v
          (fun i => Polynomial.eval (v i) Polynomial.X))
  have hprod : (Lagrange.nodal s v).eval x ≠ 0 := by
    rw [Lagrange.eval_nodal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr (hx i hi)
  have hinterp : x = (Lagrange.nodal s v).eval x *
      ∑ i ∈ s, Lagrange.nodalWeight s v i * (x - v i)⁻¹ * v i := by
    have h := Lagrange.eval_interpolate_not_at_node
      (s := s) (v := v) (x := x) v hx
    rw [← hpoly] at h
    simpa using h
  apply (div_eq_iff hprod).2
  rw [mul_comm]
  exact hinterp

/-- The companion constant-polynomial interpolation identity. -/
theorem lagrange_constant_partial_fraction
    (s : Finset ι) (v : ι → ℝ) (x : ℝ)
    (hs : s.Nonempty) (hv : Set.InjOn v s)
    (hx : ∀ i ∈ s, x ≠ v i) :
    ((Lagrange.nodal s v).eval x)⁻¹ =
      ∑ i ∈ s, Lagrange.nodalWeight s v i *
        (x - v i)⁻¹ := by
  have hprod : (Lagrange.nodal s v).eval x ≠ 0 := by
    rw [Lagrange.eval_nodal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr (hx i hi)
  have h := Lagrange.eval_interpolate_not_at_node
    (s := s) (v := v) (x := x) (1 : ι → ℝ) hx
  rw [Lagrange.interpolate_one hv hs] at h
  simp only [Polynomial.eval_one, Pi.one_apply, mul_one] at h
  rw [inv_eq_one_div]
  apply (div_eq_iff hprod).2
  rw [mul_comm]
  exact h

/-- The partial fraction identity at positive, distinct squared rates.
This is the algebraic input to the divided-difference integral formula. -/
theorem squared_rate_partial_fraction
    (s : Finset ι) (z : ι → ℝ) (k : ℝ)
    (hs : 2 ≤ s.card)
    (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s) :
    k ^ 2 / ∏ i ∈ s, (k ^ 2 + z i ^ 2) =
      ∑ i ∈ s, (-z i ^ 2) *
        (∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) *
          (k ^ 2 + z i ^ 2)⁻¹ := by
  let v : ι → ℝ := fun i => -(z i ^ 2)
  have hvinj : Set.InjOn v s := by
    intro i hi j hj hij
    have hsq : z i ^ 2 = z j ^ 2 := neg_inj.mp hij
    have hmul : (z i - z j) * (z i + z j) = 0 := by nlinarith
    have hdiff : z i - z j = 0 :=
      (mul_eq_zero.mp hmul).resolve_right
        (ne_of_gt (add_pos (hz i hi) (hz j hj)))
    exact hzinj hi hj (sub_eq_zero.mp hdiff)
  have hkv : ∀ i ∈ s, k ^ 2 ≠ v i := by
    intro i hi
    dsimp [v]
    nlinarith [sq_nonneg k, sq_pos_of_pos (hz i hi)]
  have h := lagrange_linear_partial_fraction s v (k ^ 2) hs hvinj hkv
  simpa [Lagrange.eval_nodal, Lagrange.nodalWeight, v,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- Lagrange interpolation of the constant polynomial gives the
square-difference reciprocal identity used to connect W and A. -/
theorem reciprocal_sq_diff_prod_eq_sum
    (s : Finset ι) (z : ι → ℝ) (x : ℝ)
    (hs : s.Nonempty) (hx : 0 < x)
    (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s)
    (hxn : ∀ i ∈ s, x ≠ z i) :
    (∏ i ∈ s, (z i ^ 2 - x ^ 2))⁻¹ =
      ∑ i ∈ s,
        (∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) *
          (z i ^ 2 - x ^ 2)⁻¹ := by
  let v : ι → ℝ := fun i => -(z i ^ 2)
  have hvinj : Set.InjOn v s := by
    intro i hi j hj hij
    have hsq : z i ^ 2 = z j ^ 2 := neg_inj.mp hij
    exact hzinj hi hj ((sq_eq_sq₀ (hz i hi).le (hz j hj).le).mp hsq)
  have hxv : ∀ i ∈ s, -x ^ 2 ≠ v i := by
    intro i hi heq
    have hsq : x ^ 2 = z i ^ 2 := neg_inj.mp heq
    exact hxn i hi ((sq_eq_sq₀ hx.le (hz i hi).le).mp hsq)
  have h := lagrange_constant_partial_fraction s v (-x ^ 2) hs hvinj hxv
  simpa [Lagrange.eval_nodal, Lagrange.nodalWeight, v,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- The rational W weight is the expanded symmetric divided difference
at the extra positive node x. This is the algebraic identity in Claude's
r-coefficient route, before applying the positive integral. -/
theorem rational_W_core_eq_A_expanded
    (s : Finset ι) (z : ι → ℝ) (x : ℝ)
    (hs : s.Nonempty) (hx : 0 < x)
    (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s)
    (hxn : ∀ i ∈ s, x ≠ z i) :
    (∑ i ∈ s, (x + z i)⁻¹ *
      ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) =
      -x * (∏ i ∈ s, (z i ^ 2 - x ^ 2))⁻¹ -
        ∑ i ∈ s, z i * (x ^ 2 - z i ^ 2)⁻¹ *
          ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹ := by
  let p (i : ι) : ℝ :=
    ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹
  have hpoint (i : ι) (hi : i ∈ s) :
      (x + z i)⁻¹ * p i =
        -x * (p i * (z i ^ 2 - x ^ 2)⁻¹) -
          z i * (x ^ 2 - z i ^ 2)⁻¹ * p i := by
    have hdiff : z i ^ 2 - x ^ 2 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      exact hxn i hi ((sq_eq_sq₀ hx.le (hz i hi).le).mp heq.symm)
    have hplus : x + z i ≠ 0 := (add_pos hx (hz i hi)).ne'
    have hdiff' : x ^ 2 - z i ^ 2 ≠ 0 := by
      rw [← neg_sub (z i ^ 2) (x ^ 2)]
      exact neg_ne_zero.mpr hdiff
    field_simp [hplus, hdiff, hdiff']
    ring
  have hrecip := reciprocal_sq_diff_prod_eq_sum
    s z x hs hx hz hzinj hxn
  calc
    (∑ i ∈ s, (x + z i)⁻¹ * p i) =
        ∑ i ∈ s, (-x * (p i * (z i ^ 2 - x ^ 2)⁻¹) -
          z i * (x ^ 2 - z i ^ 2)⁻¹ * p i) := by
            apply Finset.sum_congr rfl
            exact hpoint
    _ = -x * (∏ i ∈ s, (z i ^ 2 - x ^ 2))⁻¹ -
        ∑ i ∈ s, z i * (x ^ 2 - z i ^ 2)⁻¹ * p i := by
          rw [hrecip, Finset.mul_sum, ← Finset.sum_sub_distrib]

end FMSA.Convergence.PureFluidRPartialFraction

/-- info: 'FMSA.Convergence.PureFluidRPartialFraction.lagrange_linear_partial_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRPartialFraction.lagrange_linear_partial_fraction
/-- info: 'FMSA.Convergence.PureFluidRPartialFraction.lagrange_constant_partial_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRPartialFraction.lagrange_constant_partial_fraction
/-- info: 'FMSA.Convergence.PureFluidRPartialFraction.squared_rate_partial_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRPartialFraction.squared_rate_partial_fraction
/-- info: 'FMSA.Convergence.PureFluidRPartialFraction.reciprocal_sq_diff_prod_eq_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRPartialFraction.reciprocal_sq_diff_prod_eq_sum
/-- info: 'FMSA.Convergence.PureFluidRPartialFraction.rational_W_core_eq_A_expanded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRPartialFraction.rational_W_core_eq_A_expanded
