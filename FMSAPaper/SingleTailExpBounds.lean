import Mathlib

/-! Elementary exponential inequalities used by the single-tail exact MSA
reduction. With `E = exp (-x)` and `x > 0`:
`E (x + 2) + x - 2 > 0`, `E (2x + 2) + x^2 - 2 > 0`,
`2 - 2x + E (x^2 - 2) < 0` and `E < 1`. Each is proved by multiplying by
`exp x` and integrating a positive derivative from zero. -/
noncomputable section
open Real

namespace FMSA.Paper.SingleTailExpBounds

/-- A differentiable function vanishing at zero with positive derivative on
the positive axis is positive there. -/
theorem pos_of_zero_of_deriv_pos (f : ℝ → ℝ) (hf : Differentiable ℝ f) (h0 : f 0 = 0)
    (hd : ∀ x, 0 < x → 0 < deriv f x) (x : ℝ) (hx : 0 < x) : 0 < f x := by
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hf.continuous.continuousOn
    intro y hy
    rw [interior_Ici] at hy
    exact hd y hy
  have := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr hx.le) hx
  simpa [h0] using this

/-- `(x + 2) + (x - 2) e^x > 0` for `x > 0`. -/
theorem J_scaled_pos (x : ℝ) (hx : 0 < x) : 0 < (x + 2) + (x - 2) * exp x := by
  have hg : ∀ y, HasDerivAt (fun y => 1 + (y - 1) * exp y) (y * exp y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => y - 1) 1 y := (hasDerivAt_id' y).sub_const 1
    exact ((h1.mul (hasDerivAt_exp y)).const_add 1).congr_deriv (by ring)
  have hf : ∀ y, HasDerivAt (fun y => (y + 2) + (y - 2) * exp y) (1 + (y - 1) * exp y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => y + 2) 1 y := (hasDerivAt_id' y).add_const 2
    have h2 : HasDerivAt (fun y : ℝ => y - 2) 1 y := (hasDerivAt_id' y).sub_const 2
    exact (h1.add (h2.mul (hasDerivAt_exp y))).congr_deriv (by ring)
  have hgpos : ∀ y, 0 < y → 0 < 1 + (y - 1) * exp y := by
    intro y hy
    apply pos_of_zero_of_deriv_pos (fun y => 1 + (y - 1) * exp y)
      (fun y => (hg y).differentiableAt) (by simp) _ y hy
    intro w hw
    rw [(hg w).deriv]
    positivity
  apply pos_of_zero_of_deriv_pos (fun y => (y + 2) + (y - 2) * exp y)
    (fun y => (hf y).differentiableAt) (by simp) _ x hx
  intro w hw
  rw [(hf w).deriv]
  exact hgpos w hw

/-- `J = e^{-x} (x + 2) + x - 2 > 0` for `x > 0`. -/
theorem J_pos (x : ℝ) (hx : 0 < x) : 0 < exp (-x) * (x + 2) + x - 2 := by
  have h := J_scaled_pos x hx
  have he : exp (-x) * exp x = 1 := by rw [← exp_add]; simp
  have hpos : 0 < exp (-x) := exp_pos _
  have : exp (-x) * ((x + 2) + (x - 2) * exp x) = exp (-x) * (x + 2) + x - 2 := by
    linear_combination (x - 2) * he
  rw [← this]
  exact mul_pos hpos h

/-- `(2x + 2) + (x^2 - 2) e^x > 0` for `x > 0`. -/
theorem H_scaled_pos (x : ℝ) (hx : 0 < x) : 0 < (2 * x + 2) + (x ^ 2 - 2) * exp x := by
  have hg : ∀ y, HasDerivAt (fun y => 2 + (y ^ 2 + 2 * y - 2) * exp y)
      ((y ^ 2 + 4 * y) * exp y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + 2 * y - 2) (2 * y + 2) y := by
      have := (((hasDerivAt_id' y).pow 2).add ((hasDerivAt_id' y).const_mul 2)).sub_const 2
      exact this.congr_deriv (by simp)
    exact ((h1.mul (hasDerivAt_exp y)).const_add 2).congr_deriv (by ring)
  have hf : ∀ y, HasDerivAt (fun y => (2 * y + 2) + (y ^ 2 - 2) * exp y)
      (2 + (y ^ 2 + 2 * y - 2) * exp y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => 2 * y + 2) 2 y :=
      (((hasDerivAt_id' y).const_mul 2).add_const 2).congr_deriv (by ring)
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 - 2) (2 * y) y := by
      have := ((hasDerivAt_id' y).pow 2).sub_const 2
      exact this.congr_deriv (by simp)
    exact (h1.add (h2.mul (hasDerivAt_exp y))).congr_deriv (by ring)
  have hgpos : ∀ y, 0 < y → 0 < 2 + (y ^ 2 + 2 * y - 2) * exp y := by
    intro y hy
    apply pos_of_zero_of_deriv_pos (fun y => 2 + (y ^ 2 + 2 * y - 2) * exp y)
      (fun y => (hg y).differentiableAt) (by simp) _ y hy
    intro w hw
    rw [(hg w).deriv]
    positivity
  apply pos_of_zero_of_deriv_pos (fun y => (2 * y + 2) + (y ^ 2 - 2) * exp y)
    (fun y => (hf y).differentiableAt) (by simp) _ x hx
  intro w hw
  rw [(hf w).deriv]
  exact hgpos w hw

/-- `H = e^{-x} (2x + 2) + x^2 - 2 > 0` for `x > 0`. -/
theorem H_pos (x : ℝ) (hx : 0 < x) : 0 < exp (-x) * (2 * x + 2) + x ^ 2 - 2 := by
  have h := H_scaled_pos x hx
  have he : exp (-x) * exp x = 1 := by rw [← exp_add]; simp
  have : exp (-x) * ((2 * x + 2) + (x ^ 2 - 2) * exp x) = exp (-x) * (2 * x + 2) + x ^ 2 - 2 := by
    linear_combination (x ^ 2 - 2) * he
  rw [← this]
  exact mul_pos (exp_pos _) h

/-- `(2 - 2x) e^x + x^2 - 2 < 0` for `x > 0`. -/
theorem Hrefl_scaled_neg (x : ℝ) (hx : 0 < x) : (2 - 2 * x) * exp x + x ^ 2 - 2 < 0 := by
  have hf : ∀ y, HasDerivAt (fun y => -((2 - 2 * y) * exp y + y ^ 2 - 2))
      (2 * y * (exp y - 1)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => 2 - 2 * y) (-2) y :=
      ((hasDerivAt_const y (2 : ℝ)).sub ((hasDerivAt_id' y).const_mul 2)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y :=
      ((hasDerivAt_id' y).pow 2).congr_deriv (by simp)
    exact ((((h1.mul (hasDerivAt_exp y)).add h2).sub_const 2).neg).congr_deriv (by ring)
  have := pos_of_zero_of_deriv_pos (fun y => -((2 - 2 * y) * exp y + y ^ 2 - 2))
    (fun y => (hf y).differentiableAt) (by simp) (by
      intro w hw
      rw [(hf w).deriv]
      have : 1 < exp w := one_lt_exp_iff.mpr hw
      nlinarith) x hx
  linarith

/-- `2 - 2x + e^{-x} (x^2 - 2) < 0` for `x > 0`. -/
theorem Hrefl_neg (x : ℝ) (hx : 0 < x) : 2 - 2 * x + exp (-x) * (x ^ 2 - 2) < 0 := by
  have h := Hrefl_scaled_neg x hx
  have he : exp (-x) * exp x = 1 := by rw [← exp_add]; simp
  have : exp (-x) * ((2 - 2 * x) * exp x + x ^ 2 - 2) = 2 - 2 * x + exp (-x) * (x ^ 2 - 2) := by
    linear_combination (2 - 2 * x) * he
  rw [← this]
  exact mul_neg_of_pos_of_neg (exp_pos _) h

theorem expNeg_lt_one (x : ℝ) (hx : 0 < x) : exp (-x) < 1 :=
  Real.exp_lt_one_iff.mpr (by linarith)

end FMSA.Paper.SingleTailExpBounds

/-- info: 'FMSA.Paper.SingleTailExpBounds.pos_of_zero_of_deriv_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailExpBounds.pos_of_zero_of_deriv_pos

/-- info: 'FMSA.Paper.SingleTailExpBounds.J_scaled_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailExpBounds.J_scaled_pos

/-- info: 'FMSA.Paper.SingleTailExpBounds.J_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailExpBounds.J_pos

/-- info: 'FMSA.Paper.SingleTailExpBounds.H_scaled_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailExpBounds.H_scaled_pos

/-- info: 'FMSA.Paper.SingleTailExpBounds.H_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailExpBounds.H_pos

/-- info: 'FMSA.Paper.SingleTailExpBounds.Hrefl_scaled_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailExpBounds.Hrefl_scaled_neg

/-- info: 'FMSA.Paper.SingleTailExpBounds.Hrefl_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailExpBounds.Hrefl_neg

/-- info: 'FMSA.Paper.SingleTailExpBounds.expNeg_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailExpBounds.expNeg_lt_one
