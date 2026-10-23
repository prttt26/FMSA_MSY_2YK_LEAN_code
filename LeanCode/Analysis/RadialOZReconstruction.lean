import LeanCode.HardSphere.RadialFourierInjective
import LeanCode.Analysis.RadialKernelIntegrability

/-! An actual Fourier OZ equation implies the actual radial OZ equation under
explicit analytic hypotheses on the actual functions and convolution.
No hard-core, real-space OZ, or inverse transform conclusion is a premise. -/
noncomputable section
open MeasureTheory Set Filter
namespace FMSA.HardSphere

def oddRadialMoment (f : ℝ → ℝ) (v : ℝ) : ℂ := (v * f |v| : ℝ)

theorem oddRadialMoment_integrable {f : ℝ → ℝ}
    (hf : IntegrableOn (fun r => r * f r) (Ioi 0)) :
    Integrable (oddRadialMoment f) := by
  let m := (Ioi (0 : ℝ)).indicator (fun r => r * f r)
  have hi : Integrable (fun r => (m r : ℂ)) :=
    (hf.integrable_indicator measurableSet_Ioi).ofReal
  have he : oddRadialMoment f = fun r => (m r : ℂ) - (m (-r) : ℂ) := by
    funext r
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · have hm : -r ∈ Ioi (0 : ℝ) := by simpa using neg_pos.mpr hr
      have hn : r ∉ Ioi (0 : ℝ) := not_lt_of_ge hr.le
      simp only [oddRadialMoment, m, indicator_of_mem hm, indicator_of_notMem hn,
        abs_of_neg hr]
      push_cast
      ring
    · simp [oddRadialMoment, m]
    · have hm : r ∈ Ioi (0 : ℝ) := hr
      have hn : -r ∉ Ioi (0 : ℝ) := not_lt_of_ge (neg_nonpos.mpr hr.le)
      simp only [oddRadialMoment, m, indicator_of_mem hm, indicator_of_notMem hn,
        abs_of_pos hr, Complex.ofReal_zero, sub_zero]
  rw [he]
  exact hi.sub hi.comp_neg

theorem radial_fourier_neg (f : ℝ → ℝ) (k : ℝ) :
    radial_fourier f (-k) = radial_fourier f k := by
  unfold radial_fourier
  simp_rw [neg_mul, Real.sin_neg, mul_neg, integral_neg]
  ring

theorem oddRadialMoment_positive_integrable {f : ℝ → ℝ}
    (hf : Integrable (oddRadialMoment f)) :
    IntegrableOn (fun r => r * f r) (Ioi 0) := by
  have hh := hf.re.integrableOn (s := Ioi 0)
  refine hh.congr_fun ?_ measurableSet_Ioi
  intro r hr
  change 0 < r at hr
  change (oddRadialMoment f r).re = r * f r
  simp only [oddRadialMoment, Complex.ofReal_re, abs_of_pos hr]

theorem radial_sine_integrable {f : ℝ → ℝ} (hf : Integrable (oddRadialMoment f)) (k : ℝ) :
    IntegrableOn (fun r => r * f r * Real.sin (k * r)) (Ioi 0) := by
  exact (oddRadialMoment_positive_integrable hf).mul_bdd (c := 1)
    (by fun_prop) (Eventually.of_forall (fun r => by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (k * r)))

/-- All assumptions are regularity/absolute-integrability properties of the
actual functions. In particular, `hFourier` is the only OZ assumption. -/
theorem radial_oz_of_fourier (h c : ℝ → ℝ) (rho : ℝ)
    (hhi : Integrable (oddRadialMoment h))
    (hci : Integrable (oddRadialMoment c))
    (hvi : Integrable (oddRadialMoment (radial3d_conv c h)))
    (hhc : ∀ᵐ v, ContinuousAt (oddRadialMoment h) v)
    (hcc : ∀ᵐ v, ContinuousAt (oddRadialMoment c) v)
    (hvc : ∀ᵐ v, ContinuousAt (oddRadialMoment (radial3d_conv c h)) v)
    (hts : ∀ r ∈ Ioi (0 : ℝ), Integrable
      (fun p : ℝ × ℝ => p.1 * c p.1 *
        (Icc |r - p.1| (r + p.1)).indicator (fun s => s * h s) p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))
    (hjoint : Integrable
      (fun p : ℝ × ℝ × ℝ => (p.2.1 * c p.2.1) *
        (Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator (fun s => s * h s) p.2.2)
      ((volume.restrict (Ioi 0)).prod
        ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))))
    (hFourier : ∀ k ≠ 0, radial_fourier h k = radial_fourier c k +
      rho * radial_fourier c k * radial_fourier h k) :
    h =ᵐ[volume.restrict (Ioi 0)] (fun r => c r + rho * radial3d_conv c h r) := by
  let rhs := fun r => c r + rho * radial3d_conv c h r
  have hre : oddRadialMoment rhs = fun v => oddRadialMoment c v +
      (rho : ℂ) * oddRadialMoment (radial3d_conv c h) v := by
    funext v
    simp only [rhs, oddRadialMoment]
    push_cast
    ring
  have hri : Integrable (oddRadialMoment rhs) := by
    rw [hre]
    exact hci.add (hvi.const_mul (rho : ℂ))
  have hrc : ∀ᵐ v, ContinuousAt (oddRadialMoment rhs) v := by
    filter_upwards [hcc, hvc] with v hc hv
    rw [hre]
    exact hc.add (hv.const_mul (rho : ℂ))
  apply ae_eq_of_radial_fourier_eq h rhs hhi hri hhc hrc
  intro k
  have heven : ∀ k, radial_fourier rhs (-k) = radial_fourier rhs k := radial_fourier_neg rhs
  by_cases hk : k = 0
  · subst k; simp [radial_fourier]
  have hf : radial_fourier (radial3d_conv c h) k = radial_fourier c k * radial_fourier h k := by
    have hpos : ∀ k > 0, radial_fourier (radial3d_conv c h) k =
        radial_fourier c k * radial_fourier h k := by
      intro k hkp
      apply radial_fourier_conv hkp hts
      exact hjoint.mul_bdd (c := 1) (by fun_prop)
        (Eventually.of_forall (fun p => by
          simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (k * p.1)))
    rcases lt_or_gt_of_ne hk with hkn | hkp
    · simpa only [neg_neg, radial_fourier_neg] using hpos (-k) (by linarith)
    · exact hpos k hkp
  rw [hFourier k hk]
  unfold radial_fourier rhs
  have hrpt : (fun r => r * (c r + rho * radial3d_conv c h r) * Real.sin (k * r)) =
      (fun r => r * c r * Real.sin (k * r) +
        rho * (r * radial3d_conv c h r * Real.sin (k * r))) := by funext r; ring
  rw [hrpt, integral_add (radial_sine_integrable hci k)
    ((radial_sine_integrable hvi k).const_mul rho), integral_const_mul]
  change (4 * Real.pi / k) * _ + rho * ((4 * Real.pi / k) * _) * ((4 * Real.pi / k) * _) = _
  unfold radial_fourier at hf
  linear_combination -rho * hf

end FMSA.HardSphere
