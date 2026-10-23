import LeanCode.Analysis.RadialConvolutionContinuity
import Mathlib.Data.Matrix.Basic

/-! Matrix radial OZ transfer using the actual finite species sums and actual
radial convolution integrals. Analytic premises concern the actual functions. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators
namespace FMSA.HardSphere
variable {N : ℕ}

def radialMatrixFourier (f : Fin N → Fin N → ℝ → ℝ) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (radial_fourier (f i j) k : ℂ))

def radialMixtureConv (f g : Fin N → Fin N → ℝ → ℝ) (ρ : Fin N → ℝ)
    (i j : Fin N) (r : ℝ) : ℝ := ∑ m, ρ m*radial3d_conv (f i m) (g m j) r

theorem radial_fourier_ae_congr (f g : ℝ → ℝ)
    (he : f =ᵐ[volume.restrict (Ioi 0)] g) (k : ℝ) :
    radial_fourier f k=radial_fourier g k := by
  unfold radial_fourier
  congr 1
  apply integral_congr_ae
  filter_upwards [he] with r hr
  rw [hr]

theorem radial_fourier_add_of_moments (f g : ℝ → ℝ)
    (hf : IntegrableOn (fun r => r*f r) (Ioi 0))
    (hg : IntegrableOn (fun r => r*g r) (Ioi 0)) (k : ℝ) :
    radial_fourier (fun r => f r+g r) k=radial_fourier f k+radial_fourier g k := by
  unfold radial_fourier
  have he : (fun r => r*(f r+g r)*Real.sin (k*r)) =
      fun r => r*f r*Real.sin (k*r)+r*g r*Real.sin (k*r) := by funext r; ring
  rw [he, integral_add (radial_sine_integrable (oddRadialMoment_integrable hf) k)
    (radial_sine_integrable (oddRadialMoment_integrable hg) k)]
  ring

theorem radial_fourier_const_mul (f : ℝ → ℝ) (a k : ℝ) :
    radial_fourier (fun r => a*f r) k=a*radial_fourier f k := by
  unfold radial_fourier
  have he : (fun r => r*(a*f r)*Real.sin (k*r))=fun r => a*(r*f r*Real.sin (k*r)) := by funext r; ring
  rw [he, integral_const_mul]
  ring

theorem radial_fourier_sum_of_moments (f : Fin N → ℝ → ℝ)
    (hf : ∀ m, IntegrableOn (fun r => r*f m r) (Ioi 0)) (k : ℝ) :
    radial_fourier (fun r => ∑ m, f m r) k=∑ m, radial_fourier (f m) k := by
  unfold radial_fourier
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun m _ => radial_sine_integrable (oddRadialMoment_integrable (hf m)) k)]
  rw [Finset.mul_sum]

theorem radial_fourier_conv_of_moments_nonzero {f g : ℝ → ℝ}
    (hf : Measurable (fun r => r*f r)) (hg : Measurable (fun r => r*g r))
    (hfi : IntegrableOn (fun r => r*f r) (Ioi 0))
    (hfi2 : IntegrableOn (fun r => r*(r*f r)) (Ioi 0))
    (hgi : IntegrableOn (fun r => r*g r) (Ioi 0)) (k : ℝ) (hk : k ≠ 0) :
    radial_fourier (radial3d_conv f g) k=radial_fourier f k*radial_fourier g k := by
  rcases lt_or_gt_of_ne hk with hn | hp
  · simpa only [radial_fourier_neg] using radial_fourier_conv_of_moments hf hg hfi hfi2 hgi (k := -k) (by linarith)
  · exact radial_fourier_conv_of_moments hf hg hfi hfi2 hgi hp

theorem radialMixtureConv_radius_integrable (f g : Fin N → Fin N → ℝ → ℝ) (ρ : Fin N → ℝ)
    (fm : ∀ i j, Measurable (fun r => r*f i j r))
    (gm : ∀ i j, Measurable (fun r => r*g i j r))
    (fi : ∀ i j, IntegrableOn (fun r => r*f i j r) (Ioi 0))
    (fi2 : ∀ i j, IntegrableOn (fun r => r*(r*f i j r)) (Ioi 0))
    (gi : ∀ i j, IntegrableOn (fun r => r*g i j r) (Ioi 0)) (i j : Fin N) :
    IntegrableOn (fun r => r*radialMixtureConv f g ρ i j r) (Ioi 0) := by
  have hi : IntegrableOn (fun r => ∑ m, ρ m*(r*radial3d_conv (f i m) (g m j) r)) (Ioi 0) :=
    integrable_finsetSum Finset.univ (fun m _ =>
    (radial3d_conv_moment_integrable (fm i m) (gm m j) (fi i m) (fi2 i m) (gi m j)).const_mul (ρ m))
  convert! hi using 1
  funext r
  simp only [radialMixtureConv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem radialMixtureConv_actual_fourier (f g : Fin N → Fin N → ℝ → ℝ) (ρ : Fin N → ℝ)
    (fm : ∀ i j, Measurable (fun r => r*f i j r))
    (gm : ∀ i j, Measurable (fun r => r*g i j r))
    (fi : ∀ i j, IntegrableOn (fun r => r*f i j r) (Ioi 0))
    (fi2 : ∀ i j, IntegrableOn (fun r => r*(r*f i j r)) (Ioi 0))
    (gi : ∀ i j, IntegrableOn (fun r => r*g i j r) (Ioi 0)) (k : ℝ) (hk : k ≠ 0) :
    radialMatrixFourier (radialMixtureConv f g ρ) k =
      radialMatrixFourier f k*Matrix.diagonal (fun i => (ρ i : ℂ))*radialMatrixFourier g k := by
  ext i j
  change (radial_fourier (fun r => ∑ m, ρ m*radial3d_conv (f i m) (g m j) r) k : ℂ) = _
  rw [radial_fourier_sum_of_moments _ (fun m => by
    have hi : IntegrableOn (fun r => ρ m*(r*radial3d_conv (f i m) (g m j) r)) (Ioi 0) :=
      (radial3d_conv_moment_integrable (fm i m) (gm m j) (fi i m) (fi2 i m) (gi m j)).const_mul (ρ m)
    convert! hi using 1
    funext r; ring)]
  simp_rw [radial_fourier_const_mul, radial_fourier_conv_of_moments_nonzero
    (fm i _) (gm _ j) (fi i _) (fi2 i _) (gi _ j) k hk]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, radialMatrixFourier, Matrix.of_apply, Complex.ofReal_sum,
    Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem radialMixtureConv_odd_ae_continuous (f g : Fin N → Fin N → ℝ → ℝ) (ρ : Fin N → ℝ)
    (fm : ∀ i j, Measurable (fun r => r*f i j r))
    (fi : ∀ i j, IntegrableOn (fun r => r*f i j r) (Ioi 0))
    (gi : ∀ i j, Integrable (fun r => r*g i j r)) (i j : Fin N) :
    ∀ᵐ v, ContinuousAt (oddRadialMoment (radialMixtureConv f g ρ i j)) v := by
  have hc : ∀ᵐ v, ∀ m : Fin N, ContinuousAt (oddRadialMoment (radial3d_conv (f i m) (g m j))) v :=
    eventually_all.mpr (fun m => oddRadialMoment_conv_ae_continuous (fm i m) (fi i m) (gi m j))
  have he : oddRadialMoment (radialMixtureConv f g ρ i j) =
      fun v => ∑ m, (ρ m : ℂ)*oddRadialMoment (radial3d_conv (f i m) (g m j)) v := by
    funext v
    simp only [oddRadialMoment, radialMixtureConv, Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro m _
    ring
  filter_upwards [hc] with v hv
  rw [he]
  exact tendsto_finsetSum _ (fun m _ => (hv m).const_mul (ρ m : ℂ))

theorem radialMatrixFourier_add (f g : Fin N → Fin N → ℝ → ℝ)
    (fi : ∀ i j, IntegrableOn (fun r => r*f i j r) (Ioi 0))
    (gi : ∀ i j, IntegrableOn (fun r => r*g i j r) (Ioi 0)) (k : ℝ) :
    radialMatrixFourier (fun i j r => f i j r+g i j r) k =
      radialMatrixFourier f k+radialMatrixFourier g k := by
  ext i j
  simp only [radialMatrixFourier, Matrix.of_apply, Matrix.add_apply,
    radial_fourier_add_of_moments _ _ (fi i j) (gi i j) k, Complex.ofReal_add]

theorem radialMixture_reference_fourier_OZ (c h : Fin N → Fin N → ℝ → ℝ) (ρ : Fin N → ℝ)
    (cm : ∀ i j, Measurable (fun r => r*c i j r))
    (hm : ∀ i j, Measurable (fun r => r*h i j r))
    (ci : ∀ i j, IntegrableOn (fun r => r*c i j r) (Ioi 0))
    (ci2 : ∀ i j, IntegrableOn (fun r => r*(r*c i j r)) (Ioi 0))
    (hi : ∀ i j, IntegrableOn (fun r => r*h i j r) (Ioi 0))
    (hOZ : ∀ i j, h i j =ᵐ[volume.restrict (Ioi 0)]
      fun r => c i j r+radialMixtureConv c h ρ i j r) (k : ℝ) (hk : k ≠ 0) :
    radialMatrixFourier h k=radialMatrixFourier c k+
      radialMatrixFourier c k*Matrix.diagonal (fun i => (ρ i : ℂ))*radialMatrixFourier h k := by
  have he : radialMatrixFourier h k =
      radialMatrixFourier (fun i j r => c i j r+radialMixtureConv c h ρ i j r) k := by
    ext i j
    exact congrArg Complex.ofReal (radial_fourier_ae_congr _ _ (hOZ i j) k)
  calc
    _ = radialMatrixFourier (fun i j r => c i j r+radialMixtureConv c h ρ i j r) k := he
    _ = _ := by
      rw [radialMatrixFourier_add c (radialMixtureConv c h ρ) ci
        (radialMixtureConv_radius_integrable c h ρ cm hm ci ci2 hi),
        radialMixtureConv_actual_fourier c h ρ cm hm ci ci2 hi k hk]

/-- Transfer actual first-order matrix Fourier OZ to actual radial OZ.
Weighted moments supply all convolution Fubini, integrability and continuity. -/
theorem radialMixture_firstOrder_OZ_of_moments (c0 h0 c1 h1 : Fin N → Fin N → ℝ → ℝ)
    (ρ : Fin N → ℝ)
    (c0m : ∀ i j, Measurable (fun r => r*c0 i j r))
    (h0m : ∀ i j, Measurable (fun r => r*h0 i j r))
    (c1m : ∀ i j, Measurable (fun r => r*c1 i j r))
    (h1m : ∀ i j, Measurable (fun r => r*h1 i j r))
    (c0i : ∀ i j, IntegrableOn (fun r => r*c0 i j r) (Ioi 0))
    (c0i2 : ∀ i j, IntegrableOn (fun r => r*(r*c0 i j r)) (Ioi 0))
    (c1i : ∀ i j, IntegrableOn (fun r => r*c1 i j r) (Ioi 0))
    (c1i2 : ∀ i j, IntegrableOn (fun r => r*(r*c1 i j r)) (Ioi 0))
    (h0i : ∀ i j, Integrable (fun r => r*h0 i j r))
    (h1i : ∀ i j, Integrable (fun r => r*h1 i j r))
    (c1c : ∀ i j, ∀ᵐ v, ContinuousAt (oddRadialMoment (c1 i j)) v)
    (h1c : ∀ i j, ∀ᵐ v, ContinuousAt (oddRadialMoment (h1 i j)) v)
    (hFourier : ∀ k ≠ 0, radialMatrixFourier h1 k=radialMatrixFourier c1 k+
      radialMatrixFourier c0 k*Matrix.diagonal (fun i => (ρ i : ℂ))*radialMatrixFourier h1 k+
        radialMatrixFourier c1 k*Matrix.diagonal (fun i => (ρ i : ℂ))*radialMatrixFourier h0 k)
    (i j : Fin N) :
    h1 i j =ᵐ[volume.restrict (Ioi 0)] fun r => c1 i j r+
      radialMixtureConv c0 h1 ρ i j r+radialMixtureConv c1 h0 ρ i j r := by
  let A := radialMixtureConv c0 h1 ρ
  let B := radialMixtureConv c1 h0 ρ
  have ai := radialMixtureConv_radius_integrable c0 h1 ρ c0m h1m c0i c0i2 (fun i j => (h1i i j).integrableOn)
  have bi := radialMixtureConv_radius_integrable c1 h0 ρ c1m h0m c1i c1i2 (fun i j => (h0i i j).integrableOn)
  have ac := radialMixtureConv_odd_ae_continuous c0 h1 ρ c0m c0i h1i
  have bc := radialMixtureConv_odd_ae_continuous c1 h0 ρ c1m c1i h0i
  let rhs := fun r => c1 i j r+A i j r+B i j r
  have ri : IntegrableOn (fun r => r*rhs r) (Ioi 0) := by
    convert! ((c1i i j).add (ai i j)).add (bi i j) using 1
    funext r
    simp only [rhs, Pi.add_apply]
    ring
  have rc : ∀ᵐ v, ContinuousAt (oddRadialMoment rhs) v := by
    have he : oddRadialMoment rhs=fun v => oddRadialMoment (c1 i j) v+
        oddRadialMoment (A i j) v+oddRadialMoment (B i j) v := by
      funext v
      simp only [oddRadialMoment, rhs]
      push_cast
      ring
    filter_upwards [c1c i j, ac i j, bc i j] with v hc ha hb
    rw [he]
    exact (hc.add ha).add hb
  apply ae_eq_of_radial_fourier_eq _ rhs
    (oddRadialMoment_integrable (h1i i j).integrableOn) (oddRadialMoment_integrable ri) (h1c i j) rc
  intro k
  by_cases hk : k=0
  · subst k; simp [radial_fourier]
  have he : radialMatrixFourier h1 k=radialMatrixFourier
      (fun i j r => c1 i j r+A i j r+B i j r) k := by
    rw [radialMatrixFourier_add (fun i j r => c1 i j r+A i j r) B
      (fun i j => by convert! (c1i i j).add (ai i j) using 1; funext r; simp only [Pi.add_apply]; ring) bi,
      radialMatrixFourier_add c1 A c1i ai,
      radialMixtureConv_actual_fourier c0 h1 ρ c0m h1m c0i c0i2 (fun i j => (h1i i j).integrableOn) k hk,
      radialMixtureConv_actual_fourier c1 h0 ρ c1m h0m c1i c1i2 (fun i j => (h0i i j).integrableOn) k hk]
    exact hFourier k hk
  have hij := congrFun (congrFun he i) j
  change (radial_fourier (h1 i j) k : ℂ) = (radial_fourier rhs k : ℂ) at hij
  exact_mod_cast hij

end FMSA.HardSphere
