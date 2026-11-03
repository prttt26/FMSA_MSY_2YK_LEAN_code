import MSAConvergence.RadialCovarianceBounds

/-! Actual L2 Plancherel and a positive-real Laplace point bound.
No Hardy-space or reproducing-kernel axiom is introduced. -/
noncomputable section
open MeasureTheory Set Real FourierTransform
open scoped ComplexInnerProductSpace
namespace FMSA.Convergence.CausalLaplaceL2
open FMSA.Paper.FourierL1L2 FMSA.Convergence.ActualHRadialL2

/-- The L2 norm is the integral of the actual representative's squared norm. -/
theorem Lp_norm_sq_integral (F : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖F‖^2 = ∫ t : ℝ, ‖F t‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) F F)]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (F t)

private theorem norm_sq_toLp (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖^2 = ∫ t : ℝ, ‖f t‖^2 := by
  rw [Lp_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]

/-- Honest integral Fourier Plancherel for L1 intersect L2; the Fourier
integral need not itself have been assumed L1. -/
theorem integral_fourier_norm_sq_eq (f : ℝ → ℂ) (hfi : Integrable f) (hf : MemLp f 2 volume) :
    Integrable (fun w : ℝ => ‖𝓕 f w‖^2) ∧
      (∫ w : ℝ, ‖𝓕 f w‖^2) = ∫ t : ℝ, ‖f t‖^2 := by
  let F := hf.toLp f
  have he := L2_fourier_ae_integral f hfi hf
  have hFT : MemLp (fun w : ℝ => (𝓕 F : Lp ℂ 2 volume) w) 2 volume := Lp.memLp (𝓕 F)
  have hi := (memLp_two_iff_integrable_sq_norm hFT.aestronglyMeasurable).mp hFT
  have hs : (fun w : ℝ => ‖(𝓕 F : Lp ℂ 2 volume) w‖^2) =ᵐ[volume] fun w : ℝ => ‖𝓕 f w‖^2 := by
    filter_upwards [he] with w hw
    rw [hw]
  refine ⟨hi.congr hs,?_⟩
  calc
    _ = ∫ w : ℝ, ‖(𝓕 F : Lp ℂ 2 volume) w‖^2 := integral_congr_ae hs.symm
    _ = ‖(𝓕 F : Lp ℂ 2 volume)‖^2 := (Lp_norm_sq_integral _).symm
    _ = ‖F‖^2 := by rw [Lp.norm_fourier_eq]
    _ = _ := norm_sq_toLp f hf

private def positiveKernel (s t : ℝ) : ℂ :=
  (((Ioi (0 : ℝ)).indicator (fun r : ℝ => exp (-s*r)) t : ℝ) : ℂ)

private theorem positiveKernel_integrable (s : ℝ) (hs : 0 < s) : Integrable (positiveKernel s) := by
  exact ((integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0).integrable_indicator measurableSet_Ioi).ofReal

private theorem positiveKernel_memLp (s : ℝ) (hs : 0 < s) : MemLp (positiveKernel s) 2 volume := by
  apply integrable_bounded_memLp_two _ (positiveKernel_integrable s hs) 1
  apply ae_of_all
  intro t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [positiveKernel,indicator_of_mem ht,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    apply exp_le_one_iff.mpr
    change 0 < t at ht
    nlinarith
  · simp [positiveKernel,ht]

private theorem positiveKernel_norm_sq (s : ℝ) (hs : 0 < s) :
    ‖(positiveKernel_memLp s hs).toLp (positiveKernel s)‖^2 = (2*s)⁻¹ := by
  rw [norm_sq_toLp]
  have he : (fun t : ℝ => ‖positiveKernel s t‖^2) =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => exp (-(2*s)*t)) := by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [positiveKernel,indicator_of_mem ht,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (exp_pos _)]
      rw [pow_two,← exp_add]
      congr 1
      ring
    · simp [positiveKernel,ht]
  rw [he,integral_indicator measurableSet_Ioi,integral_exp_mul_Ioi (by linarith : -(2*s) < 0) 0]
  simp

/-- Cauchy–Schwarz controls a genuine positive-real Laplace integral by the
actual whole-line L2 norm. No analyticity or amplitude bound is a premise. -/
theorem laplace_point_sq_le_L2 (f : ℝ → ℂ) (hf : MemLp f 2 volume) (s : ℝ) (hs : 0 < s) :
    ‖∫ t in Ioi (0 : ℝ), f t*Complex.exp (-(s : ℂ)*t)‖^2 ≤
      (2*s)⁻¹*(∫ t : ℝ, ‖f t‖^2) := by
  let F := hf.toLp f
  let E := (positiveKernel_memLp s hs).toLp (positiveKernel s)
  have hi : inner ℂ E F = ∫ t in Ioi (0 : ℝ), f t*Complex.exp (-(s : ℂ)*t) := by
    rw [MeasureTheory.L2.inner_def]
    have he : (fun t : ℝ => inner ℂ (E t) (F t)) =ᵐ[volume]
        (Ioi (0 : ℝ)).indicator (fun t : ℝ => f t*Complex.exp (-(s : ℂ)*t)) := by
      filter_upwards [(positiveKernel_memLp s hs).coeFn_toLp,hf.coeFn_toLp] with t he hf'
      change inner ℂ (((positiveKernel_memLp s hs).toLp (positiveKernel s)) t) ((hf.toLp f) t) = _
      rw [he,hf']
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · simp only [positiveKernel,indicator_of_mem ht,RCLike.inner_apply',Complex.conj_ofReal]
        have hex : Complex.exp (-(s : ℂ)*(t : ℂ)) = (exp (-s*t) : ℂ) := by
          rw [Complex.ofReal_exp]
          congr 1
          push_cast
          ring
        rw [hex]
        ring
      · simp [positiveKernel,ht]
    rw [integral_congr_ae he,integral_indicator measurableSet_Ioi]
  calc
    _ = ‖inner ℂ E F‖^2 := by rw [hi]
    _ ≤ (‖E‖*‖F‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm E F) 2
    _ = _ := by rw [mul_pow,positiveKernel_norm_sq s hs,norm_sq_toLp f hf]

end FMSA.Convergence.CausalLaplaceL2
/-- info: 'FMSA.Convergence.CausalLaplaceL2.Lp_norm_sq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CausalLaplaceL2.Lp_norm_sq_integral
/-- info: 'FMSA.Convergence.CausalLaplaceL2.integral_fourier_norm_sq_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CausalLaplaceL2.integral_fourier_norm_sq_eq
/-- info: 'FMSA.Convergence.CausalLaplaceL2.laplace_point_sq_le_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CausalLaplaceL2.laplace_point_sq_le_L2
