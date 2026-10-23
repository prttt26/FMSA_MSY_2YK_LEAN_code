import LeanCode.Analysis.RadialOZReconstruction

/-! Continuity of the actual radial convolution follows from L1 moments.
The shell integral is a difference of continuous primitives, even when the
RDF has a contact jump. -/
noncomputable section
open MeasureTheory Set Filter Topology
namespace FMSA.HardSphere

theorem radial3d_conv_continuousOn {f g : ℝ → ℝ}
    (hf : Measurable (fun t => t * f t))
    (hfi : IntegrableOn (fun t => t * f t) (Ioi 0))
    (hgi : Integrable (fun s => s * g s)) :
    ContinuousOn (radial3d_conv f g) (Ioi 0) := by
  let B := fun x => ∫ s in (0 : ℝ)..x, s * g s
  have hB : Continuous B := hgi.continuous_primitive 0
  let F := fun r t => t * f t * (B (r + t) - B |r - t|)
  have hshell : ∀ r > 0, ∀ t > 0, B (r + t) - B |r - t| =
      ∫ s in Icc |r - t| (r + t), s * g s := by
    intro r hr t ht
    rw [intervalIntegral.integral_interval_sub_left hgi.intervalIntegrable hgi.intervalIntegrable,
      intervalIntegral.integral_of_le (abs_le.mpr ⟨by linarith, by linarith⟩),
      ← integral_Icc_eq_integral_Ioc]
  have hcont : ContinuousOn (fun r => ∫ t in Ioi 0, F r t) (Ioi 0) := by
    apply continuousOn_of_dominated (bound := fun t => ‖t * f t‖ * ∫ s, ‖s * g s‖)
    · intro r _
      exact (hf.mul ((hB.comp (continuous_const.add continuous_id)).sub
        (hB.comp (continuous_const.sub continuous_id).abs)).measurable).aestronglyMeasurable
    · intro r hr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 0 < r at hr
      change 0 < t at ht
      change ‖t * f t * (B (r + t) - B |r - t|)‖ ≤ _
      rw [norm_mul, hshell r hr t ht]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_integral_le_integral_norm _).trans
        (integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall (fun s => norm_nonneg (s * g s))) hgi.norm)
    · exact hfi.norm.mul_const _
    · filter_upwards with t
      exact continuous_const.mul ((hB.comp (continuous_id.add continuous_const)).sub
        (hB.comp (continuous_id.sub continuous_const).abs)) |>.continuousOn
  have he : EqOn (radial3d_conv f g)
      (fun r => (2 * Real.pi / r) * ∫ t in Ioi 0, F r t) (Ioi 0) := by
    intro r hr
    change 0 < r at hr
    unfold radial3d_conv
    rw [if_neg (not_le_of_gt hr)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    dsimp only [F]
    rw [hshell r hr t ht]
  apply ContinuousOn.congr _ he
  exact (((continuous_const (y := (2 * Real.pi : ℝ))).continuousOn.div
    (continuous_id (X := ℝ)).continuousOn
    (fun r hr => (show 0 < r from hr).ne')).mul hcont)

theorem oddRadialMoment_conv_ae_continuous {f g : ℝ → ℝ}
    (hf : Measurable (fun t => t * f t))
    (hfi : IntegrableOn (fun t => t * f t) (Ioi 0))
    (hgi : Integrable (fun s => s * g s)) :
    ∀ᵐ v, ContinuousAt (oddRadialMoment (radial3d_conv f g)) v := by
  have hc := radial3d_conv_continuousOn hf hfi hgi
  filter_upwards [volume.ae_ne (0 : ℝ)] with v hv
  have hpos : |v| ∈ Ioi (0 : ℝ) := abs_pos.mpr hv
  have hcv := hc.continuousAt (isOpen_Ioi.mem_nhds hpos)
  exact Complex.continuous_ofReal.continuousAt.comp
    ((continuous_id (X := ℝ)).continuousAt.mul (hcv.comp continuous_abs.continuousAt))

theorem oddRadialMoment_ae_continuous_of_junction {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ioo 0 1)) (ht : ContinuousOn f (Ioi 1)) :
    ∀ᵐ v, ContinuousAt (oddRadialMoment f) v := by
  filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (1 : ℝ), volume.ae_ne (-1 : ℝ)]
    with v hv hv1 hvn1
  have hp : 0 < |v| := abs_pos.mpr hv
  have hn : |v| ≠ 1 := by
    rcases le_or_gt 0 v with h | h
    · rwa [abs_of_nonneg h]
    · rw [abs_of_neg h]
      intro hh; apply hvn1; linarith
  have hcv : ContinuousAt f |v| := by
    rcases lt_or_gt_of_ne hn with h | h
    · exact hc.continuousAt (isOpen_Ioo.mem_nhds ⟨hp, h⟩)
    · exact ht.continuousAt (isOpen_Ioi.mem_nhds h)
  exact Complex.continuous_ofReal.continuousAt.comp
    ((continuous_id (X := ℝ)).continuousAt.mul (hcv.comp continuous_abs.continuousAt))

theorem radial_oz_of_moments (h c : ℝ → ℝ) (rho : ℝ)
    (hm : Measurable (fun r => r * h r)) (cm : Measurable (fun r => r * c r))
    (hi : Integrable (fun r => r * h r))
    (ci : IntegrableOn (fun r => r * c r) (Ioi 0))
    (ci1 : IntegrableOn (fun r => r * (r * c r)) (Ioi 0))
    (hc : ∀ᵐ v, ContinuousAt (oddRadialMoment h) v)
    (cc : ∀ᵐ v, ContinuousAt (oddRadialMoment c) v)
    (hFourier : ∀ k ≠ 0, radial_fourier h k = radial_fourier c k +
      rho * radial_fourier c k * radial_fourier h k) :
    h =ᵐ[volume.restrict (Ioi 0)] (fun r => c r + rho * radial3d_conv c h r) := by
  exact radial_oz_of_fourier h c rho
    (oddRadialMoment_integrable hi.integrableOn) (oddRadialMoment_integrable ci)
    (oddRadialMoment_integrable (radial3d_conv_moment_integrable cm hm ci ci1 hi.integrableOn))
    hc cc (oddRadialMoment_conv_ae_continuous cm ci hi)
    (fun r _ => radialTriangleKernel_fixed_integrable cm hm ci hi.integrableOn r)
    (radialTriangleKernel_integrable cm hm ci1 hi.integrableOn) hFourier

end FMSA.HardSphere
