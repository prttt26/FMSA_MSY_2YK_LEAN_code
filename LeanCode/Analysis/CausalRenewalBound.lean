import Mathlib

/-! An explicit weighted small-norm criterion for global causal renewal.
No Wiener-algebra inversion theorem is assumed. -/
noncomputable section
open MeasureTheory Set Real Filter Topology

namespace FMSA

/-- A compact-interval maximum argument gives a uniform weighted estimate
from the actual renewal equation. The kernel need only be continuous on the
nonnegative half-line, and the criterion is sufficient, not necessary. -/
theorem causal_renewal_weighted_bound_of_norm_inequality {q f y : ℝ → ℝ} {δ A B : ℝ}
    (hq : ContinuousOn q (Ici 0)) (hy : ContinuousOn y (Ici 0))
    (hkernel : IntegrableOn (fun t => exp (δ * t) * |q t|) (Ioi 0))
    (hmass : (∫ t in Ioi (0 : ℝ), exp (δ * t) * |q t|) ≤ A)
    (hA : A < 1) (hB : 0 ≤ B)
    (hf : ∀ r, 0 ≤ r → exp (δ * r) * |f r| ≤ B)
    (heq : ∀ r, 0 ≤ r → |y r| ≤ |f r| + |∫ t in (0 : ℝ)..r, q (r - t) * y t|)
    {r : ℝ} (hr : 0 ≤ r) : exp (δ * r) * |y r| ≤ B / (1 - A) := by
  have hc : ContinuousOn (fun t => exp (δ * t) * |y t|) (Icc 0 r) :=
    (by fun_prop : Continuous (fun t : ℝ => exp (δ * t))).continuousOn.mul
      ((hy.mono (fun _ ht => ht.1)).abs)
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, ⟨le_rfl, hr⟩⟩ : (Icc (0 : ℝ) r).Nonempty) hc
  let M := exp (δ * x) * |y x|
  have hM : 0 ≤ M := mul_nonneg (exp_pos _).le (abs_nonneg _)
  have hyt : ∀ t ∈ Icc 0 x, exp (δ * t) * |y t| ≤ M := by
    intro t ht
    exact isMaxOn_iff.mp hmax t ⟨ht.1, le_trans ht.2 hx.2⟩
  have hi : IntervalIntegrable (fun t => q (x - t) * y t) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx.1]
    exact (hq.comp (by fun_prop : Continuous (fun t : ℝ => x - t)).continuousOn
      (fun t ht => show x - t ∈ Ici 0 by change 0 ≤ x - t; linarith [ht.2])).mul
      (hy.mono (fun _ ht => ht.1))
  have hkcont : ContinuousOn (fun t => exp (δ * t) * |q t|) (Ici 0) :=
    (by fun_prop : Continuous (fun t : ℝ => exp (δ * t))).continuousOn.mul hq.abs
  have hib : IntervalIntegrable (fun t => M * (exp (δ * (x - t)) * |q (x - t)|))
      volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx.1]
    exact (hkcont.comp (by fun_prop : Continuous (fun t : ℝ => x - t)).continuousOn
      (fun t ht => show x - t ∈ Ici 0 by change 0 ≤ x - t; linarith [ht.2])).const_mul M
  have hconv : exp (δ * x) * |∫ t in (0 : ℝ)..x, q (x - t) * y t| ≤ M * A := by
    calc
      exp (δ * x) * |∫ t in (0 : ℝ)..x, q (x - t) * y t|
          = ‖∫ t in (0 : ℝ)..x, exp (δ * x) * (q (x - t) * y t)‖ := by
            rw [intervalIntegral.integral_const_mul, norm_mul, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      _ ≤ ∫ t in (0 : ℝ)..x, M * (exp (δ * (x - t)) * |q (x - t)|) := by
        apply intervalIntegral.norm_integral_le_of_norm_le hx.1
        · filter_upwards with t ht
          have htt : t ∈ Icc 0 x := ⟨ht.1.le, ht.2⟩
          have hex : exp (δ * x) = exp (δ * (x - t)) * exp (δ * t) := by
            rw [← exp_add]; congr 1; ring
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), abs_mul, hex]
          calc exp (δ * (x - t)) * exp (δ * t) * (|q (x - t)| * |y t|)
              = (exp (δ * t) * |y t|) * (exp (δ * (x - t)) * |q (x - t)|) := by ring
            _ ≤ M * (exp (δ * (x - t)) * |q (x - t)|) :=
              mul_le_mul_of_nonneg_right (hyt t htt) (by positivity)
        · exact hib
      _ = M * ∫ t in (0 : ℝ)..x, exp (δ * t) * |q t| := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        simpa using intervalIntegral.integral_comp_sub_left
          (f := fun t => exp (δ * t) * |q t|) (a := (0 : ℝ)) (b := x) x
      _ ≤ M * (∫ t in Ioi (0 : ℝ), exp (δ * t) * |q t|) := by
        apply mul_le_mul_of_nonneg_left _ hM
        rw [intervalIntegral.integral_of_le hx.1]
        exact setIntegral_mono_set hkernel (by filter_upwards with t; positivity)
          (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
      _ ≤ M * A := mul_le_mul_of_nonneg_left hmass hM
  have hineq : M ≤ B + M * A := by
    change exp (δ * x) * |y x| ≤ _
    calc exp (δ * x) * |y x|
        ≤ exp (δ * x) * (|f x| + |∫ t in (0 : ℝ)..x, q (x - t) * y t|) :=
          mul_le_mul_of_nonneg_left (heq x hx.1) (exp_pos _).le
      _ ≤ B + M * A := by rw [mul_add]; exact add_le_add (hf x hx.1) hconv
  have hMb : M ≤ B / (1 - A) := (le_div_iff₀ (by linarith)).mpr (by nlinarith)
  exact (isMaxOn_iff.mp hmax r ⟨hr, le_rfl⟩).trans hMb

theorem causal_renewal_weighted_bound {q f y : ℝ → ℝ} {δ A B : ℝ}
    (hq : ContinuousOn q (Ici 0)) (hy : ContinuousOn y (Ici 0))
    (hkernel : IntegrableOn (fun t => exp (δ * t) * |q t|) (Ioi 0))
    (hmass : (∫ t in Ioi (0 : ℝ), exp (δ * t) * |q t|) ≤ A)
    (hA : A < 1) (hB : 0 ≤ B)
    (hf : ∀ r, 0 ≤ r → exp (δ * r) * |f r| ≤ B)
    (heq : ∀ r, 0 ≤ r → y r = f r + ∫ t in (0 : ℝ)..r, q (r-t)*y t)
    {r : ℝ} (hr : 0 ≤ r) : exp (δ*r)*|y r| ≤ B/(1-A) := by
  apply causal_renewal_weighted_bound_of_norm_inequality hq hy hkernel hmass hA hB hf _ hr
  intro t ht
  rw [heq t ht]
  exact abs_add_le _ _

/-- Positive exponential weight proves actual L1 decay from renewal and the
small-norm criterion. No decay conclusion is inserted as a premise. -/
theorem causal_renewal_integrable_of_weighted_norm_inequality {q f y : ℝ → ℝ} {δ A B : ℝ}
    (hδ : 0 < δ) (hq : ContinuousOn q (Ici 0)) (hy : ContinuousOn y (Ici 0))
    (hkernel : IntegrableOn (fun t => exp (δ * t) * |q t|) (Ioi 0))
    (hmass : (∫ t in Ioi (0 : ℝ), exp (δ * t) * |q t|) ≤ A)
    (hA : A < 1) (hB : 0 ≤ B)
    (hf : ∀ r, 0 ≤ r → exp (δ * r) * |f r| ≤ B)
    (heq : ∀ r, 0 ≤ r → |y r| ≤ |f r| + |∫ t in (0 : ℝ)..r, q (r-t)*y t|) :
    IntegrableOn y (Ioi 0) := by
  have hdom : IntegrableOn (fun t => (B / (1 - A)) * exp (-δ * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -δ < 0) 0).const_mul _
  apply hdom.mono' ((hy.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  have hb := causal_renewal_weighted_bound_of_norm_inequality hq hy hkernel hmass hA hB hf heq ht.le
  have he : exp (δ * t) * exp (-δ * t) = 1 := by rw [← exp_add]; simp
  calc |y t| = (exp (δ * t) * |y t|) * exp (-δ * t) := by
        linear_combination -|y t| * he
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (exp_pos (-δ * t)).le

theorem causal_renewal_integrable_of_weighted_bound {q f y : ℝ → ℝ} {δ A B : ℝ}
    (hδ : 0 < δ) (hq : ContinuousOn q (Ici 0)) (hy : ContinuousOn y (Ici 0))
    (hkernel : IntegrableOn (fun t => exp (δ*t)*|q t|) (Ioi 0))
    (hmass : (∫ t in Ioi (0 : ℝ), exp (δ*t)*|q t|) ≤ A)
    (hA : A < 1) (hB : 0 ≤ B)
    (hf : ∀ r, 0 ≤ r → exp (δ*r)*|f r| ≤ B)
    (heq : ∀ r, 0 ≤ r → y r=f r+∫ t in (0 : ℝ)..r, q (r-t)*y t) :
    IntegrableOn y (Ioi 0) := by
  apply causal_renewal_integrable_of_weighted_norm_inequality hδ hq hy hkernel hmass hA hB hf
  intro r hr
  rw [heq r hr]
  exact abs_add_le _ _

end FMSA
