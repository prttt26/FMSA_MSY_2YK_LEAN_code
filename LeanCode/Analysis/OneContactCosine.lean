import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Cosine/sine integration by parts across one contact derivative jump.
Continuity at contact is retained; no differentiability there is assumed. -/
noncomputable section
open MeasureTheory Real Set Filter Topology

namespace FMSA.Analysis

theorem cosine_of_one_contact (P g : ℝ → ℝ) (R k : ℝ) (hR : 0 < R) (hk : k ≠ 0)
    (hP : Continuous P)
    (hd : ∀ x, 0 < x → x ≠ R → HasDerivAt P (-g x) x)
    (hzero : Tendsto P atTop (𝓝 0))
    (hpint : IntegrableOn (fun x => P x*cos (k*x)) (Ioi 0))
    (hgint : IntegrableOn (fun x => g x*sin (k*x)) (Ioi 0)) :
    (∫ x in Ioi (0 : ℝ), P x*cos (k*x)) =
      (1/k) * ∫ x in Ioi (0 : ℝ), g x*sin (k*x) := by
  let F : ℝ → ℝ := fun x => P x*(sin (k*x)/k)
  let dF : ℝ → ℝ := fun x => P x*cos (k*x) - g x*sin (k*x)/k
  have hs : ∀ x : ℝ, HasDerivAt (fun t => sin (k*t)/k) (cos (k*x)) x := by
    intro x
    convert! (((hasDerivAt_id x).const_mul k).sin).div_const k using 1
    simp only [id_eq]
    field_simp
  have hFd : ∀ x, 0 < x → x ≠ R → HasDerivAt F (dF x) x := by
    intro x hx hxR
    convert! (hd x hx hxR).mul (hs x) using 1 <;> dsimp [F, dF] <;> ring
  have hFi : IntervalIntegrable dF volume 0 R := by
    have hi : IntervalIntegrable (fun x => g x*sin (k*x)) volume 0 R :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr
        (hgint.mono_set Ioc_subset_Ioi_self)
    exact (Continuous.intervalIntegrable (by fun_prop) 0 R).sub (hi.div_const k)
  have hc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le
    (show ContinuousOn F (Icc 0 R) by fun_prop)
    (fun x hx => hFd x hx.1 (ne_of_lt hx.2)) hFi
  have hit : IntegrableOn dF (Ioi R) :=
    (hpint.mono_set (Ioi_subset_Ioi hR.le)).sub ((hgint.mono_set (Ioi_subset_Ioi hR.le)).div_const k)
  have hb : ∀ x : ℝ, |sin (k*x)/k| ≤ |k|⁻¹ := by
    intro x
    rw [abs_div, inv_eq_one_div]
    gcongr
    exact abs_sin_le_one _
  have hFt : Tendsto F atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun x => ?_) (?_ : Tendsto (fun x => ‖P x‖ * |k|⁻¹) atTop (𝓝 0))
    · dsimp [F]
      rw [abs_mul]
      gcongr
      exact hb x
    · simpa using hzero.norm.mul_const |k|⁻¹
  have ht := integral_Ioi_of_hasDerivAt_of_tendsto
    (show ContinuousWithinAt F (Ici R) R by fun_prop)
    (fun x hx => hFd x (hR.trans hx) (ne_of_gt hx)) hit hFt
  have split : ∀ (f : ℝ → ℝ), IntegrableOn f (Ioi 0) →
      (∫ x in Ioi (0 : ℝ), f x) = (∫ x in (0 : ℝ)..R, f x) + ∫ x in Ioi R, f x := by
    intro f hf
    have he : Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi R := by
      ext x
      simp only [mem_Ioi, mem_union, mem_Ioc]
      constructor
      · intro hx
        by_cases hxR : x ≤ R
        · exact Or.inl ⟨hx, hxR⟩
        · exact Or.inr (not_le.mp hxR)
      · rintro (⟨hx, _⟩ | hx)
        · exact hx
        · exact hR.trans hx
    have hdis : Disjoint (Ioc (0 : ℝ) R) (Ioi R) := by
      apply disjoint_left.mpr
      intro x hx hy
      exact (not_lt.mpr hx.2) hy
    rw [intervalIntegral.integral_of_le hR.le]
    calc
      (∫ x in Ioi (0 : ℝ), f x) = ∫ x in Ioc 0 R ∪ Ioi R, f x := by rw [← he]
      _ = (∫ x in Ioc 0 R, f x) + ∫ x in Ioi R, f x :=
        setIntegral_union hdis measurableSet_Ioi (hf.mono_set Ioc_subset_Ioi_self)
          (hf.mono_set (Ioi_subset_Ioi hR.le))
  dsimp only [dF, F] at hc ht
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) 0 R)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr
      (hgint.mono_set Ioc_subset_Ioi_self) |>.div_const k), intervalIntegral.integral_div] at hc
  rw [integral_sub (hpint.mono_set (Ioi_subset_Ioi hR.le))
    ((hgint.mono_set (Ioi_subset_Ioi hR.le)).div_const k), integral_div] at ht
  simp only [mul_zero, sin_zero, zero_div, sub_zero, zero_sub] at hc ht
  rw [split _ hpint, split _ hgint]
  linear_combination hc + ht

end FMSA.Analysis
