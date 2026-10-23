import LeanCode.YukawaOZMix.MSAMixtureBreakpointConvDirect

/-!
# Finite exponential-polynomial integration for multi-Yukawa convolutions

The two tail index sets are independent. Rates need only be positive: neither
within-set nor cross-set distinctness is needed. This is the analytic building
block shared by the pure-fluid and mixture multi-tail core calculations.
-/

noncomputable section
open MeasureTheory Real Set
open scoped BigOperators

namespace FMSA.FiniteYukawa

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def expPrimitive (z d0 d1 d2 x : ℝ) : ℝ :=
  ((-d0 / z - d1 / z ^ 2 - 2 * d2 / z ^ 3) +
    (-d1 / z - 2 * d2 / z ^ 2) * x + (-d2 / z) * x ^ 2) * exp (-z * x)

theorem integral_quadratic_exp (a b z d0 d1 d2 : ℝ) (hz : 0 < z) :
    (∫ x in a..b, (d0 + d1 * x + d2 * x ^ 2) * exp (-z * x)) =
      expPrimitive z d0 d1 d2 b - expPrimitive z d0 d1 d2 a := by
  simpa [ExactMSA.Breakpoint.canonAntider, expPrimitive, sub_eq_add_neg] using
    ExactMSA.Breakpoint.integral_canonical a b z 0 0 0 0 d0 d1 d2 0 hz

def polyPrimitive (c0 c1 c2 c3 x : ℝ) : ℝ :=
  c0 * x + c1 * x ^ 2 / 2 + c2 * x ^ 3 / 3 + c3 * x ^ 4 / 4

theorem integral_cubic (a b c0 c1 c2 c3 : ℝ) :
    (∫ x in a..b, c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3) =
      polyPrimitive c0 c1 c2 c3 b - polyPrimitive c0 c1 c2 c3 a := by
  simpa [ExactMSA.Breakpoint.canonAntider, polyPrimitive] using
    ExactMSA.Breakpoint.integral_canonical a b 1 c0 c1 c2 c3 0 0 0 0 one_pos

def kernel (z : ι → ℝ) (w : κ → ℝ) (c0 c1 c2 c3 : ℝ)
    (d0 d1 d2 : ι → ℝ) (e0 e1 e2 : κ → ℝ) (H : ι → κ → ℝ) (x : ℝ) : ℝ :=
  (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3) +
    (∑ u, (d0 u + d1 u * x + d2 u * x ^ 2) * exp (-z u * x)) +
    (∑ t, (e0 t + e1 t * x + e2 t * x ^ 2) * exp (-w t * x)) +
    ∑ u, ∑ t, H u t * exp (-(z u + w t) * x)

def primitive (z : ι → ℝ) (w : κ → ℝ) (c0 c1 c2 c3 : ℝ)
    (d0 d1 d2 : ι → ℝ) (e0 e1 e2 : κ → ℝ) (H : ι → κ → ℝ) (x : ℝ) : ℝ :=
  polyPrimitive c0 c1 c2 c3 x +
    (∑ u, expPrimitive (z u) (d0 u) (d1 u) (d2 u) x) +
    (∑ t, expPrimitive (w t) (e0 t) (e1 t) (e2 t) x) -
    ∑ u, ∑ t, H u t * exp (-(z u + w t) * x) / (z u + w t)

/-- Exact bounded-region integral, for any finite number of tails on either side. -/
theorem integral_kernel (z : ι → ℝ) (w : κ → ℝ) (hz : ∀ u, 0 < z u) (hw : ∀ t, 0 < w t)
    (c0 c1 c2 c3 : ℝ) (d0 d1 d2 : ι → ℝ) (e0 e1 e2 : κ → ℝ)
    (H : ι → κ → ℝ) (a b : ℝ) :
    (∫ x in a..b, kernel z w c0 c1 c2 c3 d0 d1 d2 e0 e1 e2 H x) =
      primitive z w c0 c1 c2 c3 d0 d1 d2 e0 e1 e2 H b -
        primitive z w c0 c1 c2 c3 d0 d1 d2 e0 e1 e2 H a := by
  have hp : IntervalIntegrable (fun x : ℝ => c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hd : IntervalIntegrable (fun x : ℝ => ∑ u,
      (d0 u + d1 u * x + d2 u * x ^ 2) * exp (-z u * x)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he : IntervalIntegrable (fun x : ℝ => ∑ t,
      (e0 t + e1 t * x + e2 t * x ^ 2) * exp (-w t * x)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hh : IntervalIntegrable (fun x : ℝ => ∑ u, ∑ t,
      H u t * exp (-(z u + w t) * x)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have ht (u : ι) (t : κ) : IntervalIntegrable
      (fun x : ℝ => H u t * exp (-(z u + w t) * x)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold kernel
  rw [intervalIntegral.integral_add ((hp.add hd).add he) hh,
    intervalIntegral.integral_add (hp.add hd) he, intervalIntegral.integral_add hp hd,
    integral_cubic]
  rw [intervalIntegral.integral_finsetSum (fun _ _ => Continuous.intervalIntegrable (by fun_prop) a b),
    intervalIntegral.integral_finsetSum (fun _ _ => Continuous.intervalIntegrable (by fun_prop) a b),
    intervalIntegral.integral_finsetSum (fun _ _ => Continuous.intervalIntegrable (by fun_prop) a b)]
  simp_rw [integral_quadratic_exp a b _ _ _ _ (hz _),
    integral_quadratic_exp a b _ _ _ _ (hw _)]
  have hpairs : (∑ u, ∫ x in a..b, ∑ t, H u t * exp (-(z u + w t) * x)) =
      ∑ u, ∑ t, (-(H u t * exp (-(z u + w t) * b) / (z u + w t)) +
        H u t * exp (-(z u + w t) * a) / (z u + w t)) := by
    apply Finset.sum_congr rfl
    intro u _
    rw [intervalIntegral.integral_finsetSum (fun t _ => ht u t)]
    apply Finset.sum_congr rfl
    intro t _
    rw [intervalIntegral.integral_const_mul,
      ExactMSA.Breakpoint.integral_exp_linear a b (-(z u + w t)) (by linarith [hz u, hw t])]
    field_simp [(add_pos (hz u) (hw t)).ne'] <;> ring
  rw [hpairs]
  unfold primitive
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

/-- Bilinearity keeps tail indices symbolic rather than expanding one polynomial per tail count. -/
theorem finite_bilinear (a b : ℝ) (U : ι → ℝ) (V : κ → ℝ) :
    (a + ∑ u, U u) * (b + ∑ t, V t) = a * b +
      (∑ u, U u * b) + (∑ t, a * V t) + ∑ u, ∑ t, U u * V t := by
  have hc : (∑ u, U u) * (∑ t, V t) = ∑ u, ∑ t, U u * V t := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [← hc, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- Product of an affine-plus-exponentials branch with a quadratic-plus-exponentials branch.
This covers the bounded Baxter convolution regions for arbitrary species diameters. -/
theorem branchProduct_eq_kernel (z : ι → ℝ) (w : κ → ℝ)
    (a0 a1 b0 b1 b2 : ℝ) (U : ι → ℝ) (V : κ → ℝ) (x : ℝ) :
    ((a0 + a1 * x) + ∑ u, U u * exp (-z u * x)) *
      ((b0 + b1 * x + b2 * x ^ 2) + ∑ t, V t * exp (-w t * x)) =
      kernel z w (a0 * b0) (a0 * b1 + a1 * b0) (a0 * b2 + a1 * b1) (a1 * b2)
        (fun u => U u * b0) (fun u => U u * b1) (fun u => U u * b2)
        (fun t => a0 * V t) (fun t => a1 * V t) (fun _ => 0)
        (fun u t => U u * V t) x := by
  rw [finite_bilinear]
  unfold kernel
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply congrArg₂ (· + ·)
      · ring
      · apply Finset.sum_congr rfl
        intro u _
        ring
    · apply Finset.sum_congr rfl
      intro t _
      ring
  · apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro t _
    rw [show -(z u + w t) * x = -z u * x + -w t * x by ring, exp_add]
    ring

/-- Closed bounded-region convolution integral, with no bound on the number of tails. -/
theorem integral_branchProduct (z : ι → ℝ) (w : κ → ℝ)
    (hz : ∀ u, 0 < z u) (hw : ∀ t, 0 < w t)
    (a0 a1 b0 b1 b2 : ℝ) (U : ι → ℝ) (V : κ → ℝ) (a b : ℝ) :
    (∫ x in a..b, ((a0 + a1 * x) + ∑ u, U u * exp (-z u * x)) *
      ((b0 + b1 * x + b2 * x ^ 2) + ∑ t, V t * exp (-w t * x))) =
      primitive z w (a0 * b0) (a0 * b1 + a1 * b0) (a0 * b2 + a1 * b1) (a1 * b2)
        (fun u => U u * b0) (fun u => U u * b1) (fun u => U u * b2)
        (fun t => a0 * V t) (fun t => a1 * V t) (fun _ => 0) (fun u t => U u * V t) b -
      primitive z w (a0 * b0) (a0 * b1 + a1 * b0) (a0 * b2 + a1 * b1) (a1 * b2)
        (fun u => U u * b0) (fun u => U u * b1) (fun u => U u * b2)
        (fun t => a0 * V t) (fun t => a1 * V t) (fun _ => 0) (fun u t => U u * V t) a := by
  simp_rw [branchProduct_eq_kernel]
  exact integral_kernel z w hz hw _ _ _ _ _ _ _ _ _ _ _ a b

end FMSA.FiniteYukawa
