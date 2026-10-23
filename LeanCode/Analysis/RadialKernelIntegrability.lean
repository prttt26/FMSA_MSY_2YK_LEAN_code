import LeanCode.HardSphere.RadialFourier

/-! Absolute-integrability estimates for the actual radial convolution.
The extra first moment pays for the length of the triangle interval in r. -/
noncomputable section
open MeasureTheory Set Filter
namespace FMSA.HardSphere

abbrev positiveMeasure : Measure ℝ := volume.restrict (Ioi 0)

def radialTriangleKernel (a b : ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  a p.2.1 * (Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator b p.2.2

theorem radialTriangleKernel_measurable {a b : ℝ → ℝ}
    (ha : Measurable a) (hb : Measurable b) : Measurable (radialTriangleKernel a b) := by
  have hs : MeasurableSet {p : ℝ × ℝ × ℝ | p.2.2 ∈ Icc |p.1 - p.2.1| (p.1 + p.2.1)} := by
    exact (measurableSet_le ((measurable_fst.sub (measurable_fst.comp measurable_snd)).abs)
      (measurable_snd.comp measurable_snd)).inter
      (measurableSet_le (measurable_snd.comp measurable_snd)
        (measurable_fst.add (measurable_fst.comp measurable_snd)))
  have hh := (ha.comp (measurable_fst.comp measurable_snd)).mul
    ((hb.comp (measurable_snd.comp measurable_snd)).indicator hs)
  convert hh using 1
  funext p
  simp only [radialTriangleKernel, indicator_apply, mem_setOf_eq, Function.comp_apply]

theorem triangle_mem_symmetric (r t s : ℝ) :
    s ∈ Icc |r - t| (r + t) ↔ r ∈ Icc |t - s| (t + s) := by
  simp only [mem_Icc, abs_le]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

theorem radialTriangleKernel_fixed_integrable {a b : ℝ → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (hai : Integrable a positiveMeasure) (hbi : Integrable b positiveMeasure) (r : ℝ) :
    Integrable (fun p : ℝ × ℝ => a p.1 * (Icc |r - p.1| (r + p.1)).indicator b p.2)
      (positiveMeasure.prod positiveMeasure) := by
  have hm := (radialTriangleKernel_measurable ha hb).comp
    ((measurable_const (a := r)).prodMk (measurable_id (α := ℝ × ℝ)))
  refine (hai.mul_prod hbi).mono hm.aestronglyMeasurable ?_
  filter_upwards with p
  by_cases hp : p.2 ∈ Icc |r - p.1| (r + p.1)
  · simp only [indicator_of_mem hp, le_refl]
  · simp only [indicator_of_notMem hp, mul_zero, norm_zero, norm_nonneg]

theorem triangle_r_integrable (a b : ℝ → ℝ) (t s : ℝ) :
    Integrable (fun r => radialTriangleKernel a b (r, t, s)) positiveMeasure := by
  have he : (fun r => radialTriangleKernel a b (r, t, s)) =
      (Icc |t - s| (t + s)).indicator (fun _ => a t * b s) := by
    funext r
    simp only [radialTriangleKernel, indicator_apply, triangle_mem_symmetric]
    split_ifs <;> simp
  rw [he]
  exact (continuous_const.integrableOn_Icc.integrable_indicator
    measurableSet_Icc).integrableOn

theorem triangle_r_norm_bound (a b : ℝ → ℝ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    (∫ r, ‖radialTriangleKernel a b (r, t, s)‖ ∂positiveMeasure) ≤
      2 * ‖t * a t‖ * ‖b s‖ := by
  have he : (fun r => ‖radialTriangleKernel a b (r, t, s)‖) =
      (Icc |t - s| (t + s)).indicator (fun _ => ‖a t‖ * ‖b s‖) := by
    funext r
    simp only [radialTriangleKernel, indicator_apply, triangle_mem_symmetric]
    split_ifs <;> simp [norm_mul]
  rw [he]
  have hi := (continuous_const.integrableOn_Icc.integrable_indicator
    measurableSet_Icc : Integrable ((Icc |t - s| (t + s)).indicator
      (fun _ => ‖a t‖ * ‖b s‖)))
  have hn : ∀ r, 0 ≤ (Icc |t - s| (t + s)).indicator (fun _ => ‖a t‖ * ‖b s‖) r := by
    intro r; exact indicator_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
  have hle := integral_mono_measure (μ := positiveMeasure) Measure.restrict_le_self (Eventually.of_forall hn) hi
  change (∫ r in Ioi 0, _) ≤ _ at hle
  have hfull : (∫ r, (Icc |t - s| (t + s)).indicator (fun _ => ‖a t‖ * ‖b s‖) r) =
      (t + s - |t - s|) * (‖a t‖ * ‖b s‖) := by
    rw [integral_indicator measurableSet_Icc, integral_const, smul_eq_mul,
      Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal (by
        have hh : |t - s| ≤ t + s := abs_le.mpr ⟨by linarith, by linarith⟩
        linarith)]
  change (∫ r in Ioi 0, _) ≤ _
  refine hle.trans ?_
  rw [hfull, norm_mul, Real.norm_eq_abs (r := t), abs_of_pos ht]
  have hlen : t + s - |t - s| ≤ 2 * t := by
    have hh := neg_le_abs (t - s); linarith
  nlinarith [mul_nonneg (norm_nonneg (a t)) (norm_nonneg (b s))]

theorem radialTriangleKernel_integrable {a b : ℝ → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (ha1 : Integrable (fun t => t * a t) positiveMeasure)
    (hb0 : Integrable b positiveMeasure) :
    Integrable (radialTriangleKernel a b)
      (positiveMeasure.prod (positiveMeasure.prod positiveMeasure)) := by
  have hm := radialTriangleKernel_measurable ha hb
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards with p using triangle_r_integrable a b p.1 p.2
  · have hbound := (ha1.norm.mul_prod hb0.norm).const_mul 2
    refine hbound.mono hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable ?_
    have hmem : ∀ᵐ p ∂(positiveMeasure.prod positiveMeasure), p ∈ Ioi 0 ×ˢ Ioi 0 := by
      rw [positiveMeasure, Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    filter_upwards [hmem] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simpa only [norm_mul, norm_norm, Real.norm_ofNat, mul_assoc] using
      triangle_r_norm_bound a b hp.1 hp.2

/-- The radial convolution theorem's Fubini hypotheses follow from ordinary
weighted L1 moments, rather than an assumed OZ equation. -/
theorem radial_fourier_conv_of_moments {f g : ℝ → ℝ}
    (hf : Measurable (fun t => t * f t)) (hg : Measurable (fun t => t * g t))
    (hf0 : IntegrableOn (fun t => t * f t) (Ioi 0))
    (hf1 : IntegrableOn (fun t => t * (t * f t)) (Ioi 0))
    (hg0 : IntegrableOn (fun t => t * g t) (Ioi 0))
    {k : ℝ} (hk : 0 < k) :
    radial_fourier (radial3d_conv f g) k = radial_fourier f k * radial_fourier g k := by
  apply radial_fourier_conv hk
  · intro r _
    exact radialTriangleKernel_fixed_integrable hf hg hf0 hg0 r
  · exact (radialTriangleKernel_integrable hf hg hf1 hg0).mul_bdd (c := 1)
      (by fun_prop) (Eventually.of_forall (fun p => by
        simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (k * p.1)))

theorem setIntegral_Icc_eq_positive_indicator {a b : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) :
    (∫ s in Icc a b, f s) = ∫ s in Ioi 0, (Icc a b).indicator f s := by
  rw [setIntegral_indicator measurableSet_Icc]
  apply setIntegral_congr_set
  have hn : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := volume.ae_ne 0
  filter_upwards [hn] with s hs
  change (s ∈ Icc a b) = (s ∈ Ioi 0 ∩ Icc a b)
  apply propext
  simp only [mem_inter_iff, mem_Icc, mem_Ioi]
  constructor
  · intro h
    exact ⟨lt_of_le_of_ne (ha.trans h.1) hs.symm, h⟩
  · exact fun h => h.2

theorem radial3d_conv_moment_eq_product_integral {f g : ℝ → ℝ}
    (hf : Measurable (fun t => t * f t)) (hg : Measurable (fun t => t * g t))
    (hf0 : IntegrableOn (fun t => t * f t) (Ioi 0))
    (hg0 : IntegrableOn (fun t => t * g t) (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    r * radial3d_conv f g r = 2 * Real.pi *
      ∫ p, radialTriangleKernel (fun t => t * f t) (fun t => t * g t) (r, p)
        ∂(positiveMeasure.prod positiveMeasure) := by
  unfold radial3d_conv
  rw [if_neg (not_le_of_gt hr)]
  have hc : ∀ X : ℝ, r * (2 * Real.pi / r * X) = 2 * Real.pi * X := by
    intro X; field_simp [hr.ne']
  rw [hc]
  congr 1
  have he : ∀ t : ℝ, t * f t * ∫ s in Icc |r - t| (r + t), s * g s =
      ∫ s in Ioi 0, t * f t * (Icc |r - t| (r + t)).indicator (fun s => s * g s) s := by
    intro t
    rw [setIntegral_Icc_eq_positive_indicator (abs_nonneg _), integral_const_mul]
  simp_rw [he]
  exact integral_integral (radialTriangleKernel_fixed_integrable hf hg hf0 hg0 r)

theorem radial3d_conv_moment_integrable {f g : ℝ → ℝ}
    (hf : Measurable (fun t => t * f t)) (hg : Measurable (fun t => t * g t))
    (hf0 : IntegrableOn (fun t => t * f t) (Ioi 0))
    (hf1 : IntegrableOn (fun t => t * (t * f t)) (Ioi 0))
    (hg0 : IntegrableOn (fun t => t * g t) (Ioi 0)) :
    IntegrableOn (fun r => r * radial3d_conv f g r) (Ioi 0) := by
  have hj := radialTriangleKernel_integrable hf hg hf1 hg0
  have hi : IntegrableOn (fun r => 2 * Real.pi *
      ∫ p, radialTriangleKernel (fun t => t * f t) (fun t => t * g t) (r, p)
        ∂(positiveMeasure.prod positiveMeasure)) (Ioi 0) :=
    hj.integral_prod_left.const_mul (2 * Real.pi)
  refine hi.congr_fun ?_ measurableSet_Ioi
  intro r hr
  exact (radial3d_conv_moment_eq_product_integral hf hg hf0 hg0 hr).symm

end FMSA.HardSphere
