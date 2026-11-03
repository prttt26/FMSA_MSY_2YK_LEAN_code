import MSAConvergence.CanonicalResolventAnalysis

/-! Infinite-rectangle line shifts and causal support of genuine regularized
frequency integrals. Identification with the actual time resolvent is separate. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators

namespace FMSA.Convergence.CanonicalContourShift
open FMSA.Convergence.CanonicalKernelEstimates FMSA.Convergence.CanonicalResolventAnalysis

/-- The unnormalized actual inverse-frequency integral on one vertical line.
Its integrability is established before it is used in the shift theorems. -/
def verticalIntegral (F : ℂ → ℂ) (a t : ℝ) : ℂ :=
  ∫ k : ℝ, Complex.exp (verticalPoint a k*(t : ℂ))*F (verticalPoint a k)

/-- A horizontal edge of the finite inverse-frequency rectangle. -/
def horizontalIntegral (F : ℂ → ℂ) (a0 a1 k t : ℝ) : ℂ :=
  ∫ a : ℝ in a0..a1, Complex.exp (verticalPoint a k*(t : ℂ))*F (verticalPoint a k)

/-- Both time signs are controlled by the larger endpoint exponential. -/
theorem endpoint_exponential_bound (a0 a1 a t : ℝ) (h0 : a0 ≤ a) (h1 : a ≤ a1) :
    exp (a*t) ≤ max (exp (a0*t)) (exp (a1*t)) := by
  by_cases ht : 0 ≤ t
  · exact (exp_le_exp.mpr (mul_le_mul_of_nonneg_right h1 ht)).trans (le_max_right _ _)
  · exact (exp_le_exp.mpr (mul_le_mul_of_nonpos_right h0 (le_of_lt (lt_of_not_ge ht)))).trans (le_max_left _ _)

/-- The already proved quadratic majorant is an actual entry-norm bound. -/
theorem inverse_quadratic_norm_bound (v : ℂ) (k C : ℝ) (h : (1+k^2)*‖v‖ ≤ C) :
    ‖v‖ ≤ C*(1+k^2)⁻¹ := by
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < 1+k^2)).mpr (by simpa only [mul_comm] using h)

/-- The horizontal integral decays quadratically at both imaginary ends,
with an endpoint maximum valid for every real time. -/
theorem horizontal_integral_norm_bound
    (F : ℂ → ℂ) (lower C : ℝ)
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (a0 a1 : ℝ) (h0 : lower ≤ a0) (h01 : a0 ≤ a1) (k t : ℝ) :
    ‖horizontalIntegral F a0 a1 k t‖ ≤
      (max (exp (a0*t)) (exp (a1*t)))*C*(1+k^2)⁻¹*|a1-a0| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro a ha
  rw [uIoc_of_le h01] at ha
  have hFn := inverse_quadratic_norm_bound (F (verticalPoint a k)) k C
    (hmajor a (h0.trans ha.1.le) k)
  rw [norm_mul, vertical_exponential_norm]
  calc
    _ ≤ (max (exp (a0*t)) (exp (a1*t)))*(C*(1+k^2)⁻¹) :=
      mul_le_mul (endpoint_exponential_bound a0 a1 a t ha.1.le ha.2) hFn
        (norm_nonneg _) (le_trans (exp_pos _).le (le_max_left _ _))
    _ = _ := by ring

/-- The finite rectangle's two horizontal edges vanish as its height tends
to infinity. The negative-height edge uses the same all-time majorant. -/
theorem horizontal_integrals_tendsto_zero
    (F : ℂ → ℂ) (lower C : ℝ)
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (a0 a1 : ℝ) (h0 : lower ≤ a0) (h01 : a0 ≤ a1) (t : ℝ) :
    Tendsto (fun K : ℝ => horizontalIntegral F a0 a1 K t) atTop (𝓝 0) ∧
    Tendsto (fun K : ℝ => horizontalIntegral F a0 a1 (-K) t) atTop (𝓝 0) := by
  have hsq : Tendsto (fun K : ℝ => K^2) atTop atTop := tendsto_pow_atTop (by decide)
  have hi : Tendsto (fun K : ℝ => (1+K^2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_const_nhds.add_atTop hsq)
  have hh : Tendsto (fun K : ℝ =>
      (max (exp (a0*t)) (exp (a1*t)))*C*(1+K^2)⁻¹*|a1-a0|) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((show Tendsto (fun _K : ℝ => (max (exp (a0*t)) (exp (a1*t)))*C) atTop
        (𝓝 ((max (exp (a0*t)) (exp (a1*t)))*C)) from tendsto_const_nhds).mul hi).mul_const |a1-a0|
  constructor
  · exact squeeze_zero_norm (fun K => horizontal_integral_norm_bound F lower C hmajor a0 a1 h0 h01 K t) hh
  · apply squeeze_zero_norm _ hh
    intro K
    simpa only [neg_sq] using horizontal_integral_norm_bound F lower C hmajor a0 a1 h0 h01 (-K) t

/-- The exact finite Cauchy-Goursat rectangle identity with matrix-entry
frequency coordinates and the actual inverse-transform exponential. -/
theorem rectangle_vertical_identity
    (F : ℂ → ℂ) (lower : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (a0 a1 : ℝ) (h0 : lower < a0) (h01 : a0 ≤ a1) (K t : ℝ) :
    horizontalIntegral F a0 a1 (-K) t-horizontalIntegral F a0 a1 K t+
      Complex.I*(∫ k : ℝ in (-K)..K, Complex.exp (verticalPoint a1 k*(t : ℂ))*F (verticalPoint a1 k))-
      Complex.I*(∫ k : ℝ in (-K)..K, Complex.exp (verticalPoint a0 k*(t : ℂ))*F (verticalPoint a0 k)) = 0 := by
  have hd : DifferentiableOn ℂ (fun s : ℂ => Complex.exp (s*(t : ℂ))*F s)
      (uIcc (verticalPoint a0 (-K)).re (verticalPoint a1 K).re ×ℂ
        uIcc (verticalPoint a0 (-K)).im (verticalPoint a1 K).im) := by
    intro s hs
    have hre : s.re ∈ uIcc a0 a1 := by simpa [verticalPoint] using hs.1
    rw [uIcc_of_le h01] at hre
    have hFs := (hF s (h0.trans_le hre.1)).differentiableAt
    have he : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w*(t : ℂ))) s := by fun_prop
    exact (he.mul hFs).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun s : ℂ => Complex.exp (s*(t : ℂ))*F s) (verticalPoint a0 (-K)) (verticalPoint a1 K) hd
  simpa [horizontalIntegral, verticalPoint, smul_eq_mul] using hrect

/-- Equality of genuine inverse integrals on ordered interior vertical lines,
proved by the infinite-rectangle limit for all real times. -/
theorem vertical_integrals_eq_of_le
    (F : ℂ → ℂ) (lower C : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (a0 a1 : ℝ) (h0 : lower < a0) (h01 : a0 ≤ a1) (t : ℝ) :
    verticalIntegral F a0 t = verticalIntegral F a1 t := by
  obtain ⟨hp, hn⟩ := horizontal_integrals_tendsto_zero F lower C hmajor a0 a1 h0.le h01 t
  have hv0 := MeasureTheory.intervalIntegral_tendsto_integral
    (vertical_phase_integrable F a0 t (hL1 a0 h0.le)) tendsto_neg_atTop_atBot tendsto_id
  have hv1 := MeasureTheory.intervalIntegral_tendsto_integral
    (vertical_phase_integrable F a1 t (hL1 a1 (h0.le.trans h01))) tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hn.sub hp).add (hv1.const_mul Complex.I)).sub (hv0.const_mul Complex.I)
  have hz := tendsto_nhds_unique hlim (by
    simpa only [id_eq, rectangle_vertical_identity F lower hF a0 a1 h0 h01] using
      (tendsto_const_nhds : Tendsto (fun _K : ℝ => (0 : ℂ)) atTop (𝓝 0)))
  have he : Complex.I*verticalIntegral F a1 t = Complex.I*verticalIntegral F a0 t := by
    apply sub_eq_zero.mp
    simpa only [verticalIntegral, sub_self, zero_add] using hz
  exact (mul_left_cancel₀ Complex.I_ne_zero he).symm

/-- All-time line independence, without ordering the two chosen interior
vertical lines. No equality of totalized divergent integrals is used. -/
theorem vertical_integrals_eq
    (F : ℂ → ℂ) (lower C : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (a0 a1 : ℝ) (h0 : lower < a0) (h1 : lower < a1) (t : ℝ) :
    verticalIntegral F a0 t = verticalIntegral F a1 t := by
  rcases le_total a0 a1 with h01 | h10
  · exact vertical_integrals_eq_of_le F lower C hF hmajor hL1 a0 a1 h0 h01 t
  · exact (vertical_integrals_eq_of_le F lower C hF hmajor hL1 a1 a0 h1 h10 t).symm

/-- The genuine inversion integrand is absolutely integrable and its
unnormalized integral has the explicit uniform pi-times-majorant bound. -/
theorem vertical_integral_integrable_bound
    (F : ℂ → ℂ) (lower C : ℝ)
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (a : ℝ) (ha : lower ≤ a) (t : ℝ) :
    Integrable (fun k : ℝ => Complex.exp (verticalPoint a k*(t : ℂ))*F (verticalPoint a k)) ∧
      ‖verticalIntegral F a t‖ ≤ exp (a*t)*C*π := by
  refine ⟨vertical_phase_integrable F a t (hL1 a ha), ?_⟩
  have hpoint (k : ℝ) : ‖Complex.exp (verticalPoint a k*(t : ℂ))*F (verticalPoint a k)‖ ≤
      exp (a*t)*C*(1+k^2)⁻¹ := by
    rw [norm_mul, vertical_exponential_norm]
    calc
      _ ≤ exp (a*t)*(C*(1+k^2)⁻¹) := mul_le_mul_of_nonneg_left
        (inverse_quadratic_norm_bound _ k C (hmajor a ha k)) (exp_pos _).le
      _ = _ := by ring
  calc
    _ ≤ ∫ k : ℝ, exp (a*t)*C*(1+k^2)⁻¹ :=
      MeasureTheory.norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul (exp (a*t)*C))
        (Eventually.of_forall hpoint)
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- Uniform vertical control and all-time line independence force the
actual inversion integral to vanish at every negative time. This proves
causal support of the frequency integral, not time-resolvent identification. -/
theorem vertical_integral_eq_zero_of_neg
    (F : ℂ → ℂ) (lower C : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (a : ℝ) (ha : lower < a) (t : ℝ) (ht : t < 0) : verticalIntegral F a t = 0 := by
  have hexp : Tendsto (fun A : ℝ => exp (A*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Filter.Tendsto.atTop_mul_const_of_neg ht tendsto_id)
  have hlim : Tendsto (fun A : ℝ => exp (A*t)*C*π) atTop (𝓝 0) := by
    simpa only [zero_mul] using (hexp.mul_const C).mul_const π
  have hz : ‖verticalIntegral F a t‖ ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [eventually_gt_atTop a] with A hA
    rw [vertical_integrals_eq_of_le F lower C hF hmajor hL1 a A ha hA.le t]
    exact (vertical_integral_integrable_bound F lower C hmajor hL1 A (ha.trans hA).le t).2)
  exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))

/-- A genuine vertical L1 symbol yields a continuous inverse integral in
time. The undamped imaginary phase is dominated before the real exponential
factor is restored; no Fourier normalization is presumed. -/
theorem vertical_integral_continuous (F : ℂ → ℂ) (a : ℝ)
    (hL1 : Integrable (fun k : ℝ => F (verticalPoint a k))) :
    Continuous (fun t : ℝ => verticalIntegral F a t) := by
  have hn (k t : ℝ) : ‖Complex.exp ((k : ℂ)*Complex.I*(t : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hG : Continuous (fun t : ℝ => ∫ k : ℝ,
      Complex.exp ((k : ℂ)*Complex.I*(t : ℂ))*F (verticalPoint a k)) := by
    apply continuous_of_dominated (bound := fun k : ℝ => ‖F (verticalPoint a k)‖)
    · intro t
      have hm : AEStronglyMeasurable (fun k : ℝ => Complex.exp ((k : ℂ)*Complex.I*(t : ℂ))) := by
        apply Continuous.aestronglyMeasurable
        fun_prop
      exact hm.mul hL1.aestronglyMeasurable
    · intro t
      exact Eventually.of_forall (fun k => by rw [norm_mul, hn, one_mul])
    · exact hL1.norm
    · exact Eventually.of_forall (fun k => by fun_prop)
  have he (t : ℝ) : verticalIntegral F a t = Complex.exp ((a : ℂ)*(t : ℂ)) *
      ∫ k : ℝ, Complex.exp ((k : ℂ)*Complex.I*(t : ℂ))*F (verticalPoint a k) := by
    unfold verticalIntegral
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro k
    have hp : Complex.exp (verticalPoint a k*(t : ℂ)) =
        Complex.exp ((a : ℂ)*(t : ℂ))*Complex.exp ((k : ℂ)*Complex.I*(t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold verticalPoint
      ring
    change Complex.exp (verticalPoint a k*(t : ℂ))*F (verticalPoint a k) =
      Complex.exp ((a : ℂ)*(t : ℂ))*(Complex.exp ((k : ℂ)*Complex.I*(t : ℂ))*F (verticalPoint a k))
    rw [hp, mul_assoc]
  have hf : (fun t : ℝ => verticalIntegral F a t) = fun t : ℝ => Complex.exp ((a : ℂ)*(t : ℂ)) *
      ∫ k : ℝ, Complex.exp ((k : ℂ)*Complex.I*(t : ℂ))*F (verticalPoint a k) := funext he
  rw [hf]
  exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp ((a : ℂ)*(t : ℂ)))).mul hG

/-- Causal support includes the zero-time endpoint, by the proved time
continuity and the genuine negative-time vanishing theorem. -/
theorem vertical_integral_eq_zero_of_nonpos
    (F : ℂ → ℂ) (lower C : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (a : ℝ) (ha : lower < a) (t : ℝ) (ht : t ≤ 0) : verticalIntegral F a t = 0 := by
  rcases lt_or_eq_of_le ht with ht | rfl
  · exact vertical_integral_eq_zero_of_neg F lower C hF hmajor hL1 a ha t ht
  · have hc := vertical_integral_continuous F a (hL1 a ha.le)
    have hct : Tendsto (fun t : ℝ => verticalIntegral F a t) (𝓝[<] (0 : ℝ))
        (𝓝 (verticalIntegral F a 0)) := hc.continuousAt.mono_left nhdsWithin_le_nhds
    have he : (fun t : ℝ => verticalIntegral F a t) =ᶠ[𝓝[<] (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact vertical_integral_eq_zero_of_neg F lower C hF hmajor hL1 a ha u hu
    exact tendsto_nhds_unique hct (tendsto_const_nhds.congr' he.symm)

/-- The causal inversion integral has a genuine whole-real-line weighted
L1 bound whenever the damping exceeds the chosen vertical real part.
This is a time integral of the frequency inversion, still not an actual RDF. -/
theorem vertical_integral_weighted_integrable
    (F : ℂ → ℂ) (lower C : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (a : ℝ) (ha : lower < a) (gamma : ℝ) (hg : a < gamma) :
    Integrable (fun t : ℝ => Complex.exp (-(gamma : ℂ)*(t : ℂ))*verticalIntegral F a t) := by
  have hBon : IntegrableOn (fun t : ℝ => (C*π)*exp ((a-gamma)*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : a-gamma < 0) 0).const_mul (C*π)
  have hB : Integrable ((Ioi (0 : ℝ)).indicator (fun t : ℝ => (C*π)*exp ((a-gamma)*t))) :=
    hBon.integrable_indicator measurableSet_Ioi
  have hc : Continuous (fun t : ℝ => Complex.exp (-(gamma : ℂ)*(t : ℂ))*verticalIntegral F a t) :=
    (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-(gamma : ℂ)*(t : ℂ)))).mul
      (vertical_integral_continuous F a (hL1 a ha.le))
  apply hB.mono' hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  change ‖Complex.exp (-(gamma : ℂ)*(t : ℂ))*verticalIntegral F a t‖ ≤
    (Ioi (0 : ℝ)).indicator (fun t : ℝ => (C*π)*exp ((a-gamma)*t)) t
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), norm_mul]
    have he : ‖Complex.exp (-(gamma : ℂ)*(t : ℂ))‖ = exp (-gamma*t) := by
      simp [Complex.norm_exp, Complex.mul_re]
    rw [he]
    calc
      _ ≤ exp (-gamma*t)*(exp (a*t)*C*π) := mul_le_mul_of_nonneg_left
        (vertical_integral_integrable_bound F lower C hmajor hL1 a ha.le t).2 (exp_pos _).le
      _ = (C*π)*(exp (-gamma*t)*exp (a*t)) := by ring
      _ = _ := by rw [← exp_add]; congr 1; congr 1; ring
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
      vertical_integral_eq_zero_of_nonpos F lower C hF hmajor hL1 a ha t (le_of_not_gt ht), mul_zero, norm_zero]

/-- The actual canonical regularized MSA frequency integral is independent
of every interior vertical line, vanishes at negative time, and has an
exponential envelope on an internally chosen negative line. It is not yet
identified with the constructed time-domain Volterra resolvent. -/
theorem actual_canonical_contour_integrals
    {N : ℕ} {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i)
    (p : FMSA.ExactMSA.MultiTailMixture.TailMatrix T N × FMSA.ExactMSA.MultiTailMixture.TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-FMSA.ExactMSA.MultiTailMixture.rdfMatrixLaplace
        (FMSA.ExactMSA.MultiTailMixture.nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ delta b C : ℝ, 0 < delta ∧ (∀ u, delta < z u) ∧ delta < b ∧ 0 ≤ C ∧
      ∀ i j : Fin N,
        (∀ a : ℝ, -delta < a → Continuous (fun t : ℝ => verticalIntegral (fun s => regularizedResolvent
          (FMSA.ExactMSA.MultiTailMixture.nonlinearCausalKernel z rho sigma p.1 p.2) b s i j) a t)) ∧
        (∀ a0 a1 : ℝ, -delta < a0 → -delta < a1 → ∀ t : ℝ,
          verticalIntegral (fun s => regularizedResolvent
            (FMSA.ExactMSA.MultiTailMixture.nonlinearCausalKernel z rho sigma p.1 p.2) b s i j) a0 t =
          verticalIntegral (fun s => regularizedResolvent
            (FMSA.ExactMSA.MultiTailMixture.nonlinearCausalKernel z rho sigma p.1 p.2) b s i j) a1 t) ∧
        (∀ a : ℝ, -delta < a → ∀ t : ℝ,
          ‖verticalIntegral (fun s => regularizedResolvent
            (FMSA.ExactMSA.MultiTailMixture.nonlinearCausalKernel z rho sigma p.1 p.2) b s i j) a t‖ ≤ exp (a*t)*C*π) ∧
        (∀ a : ℝ, -delta < a → ∀ t : ℝ, t ≤ 0 →
          verticalIntegral (fun s => regularizedResolvent
            (FMSA.ExactMSA.MultiTailMixture.nonlinearCausalKernel z rho sigma p.1 p.2) b s i j) a t = 0) ∧
        Integrable (fun t : ℝ => verticalIntegral (fun s => regularizedResolvent
          (FMSA.ExactMSA.MultiTailMixture.nonlinearCausalKernel z rho sigma p.1 p.2) b s i j) (-delta/2) t) ∧
        (∀ gamma : ℝ, -delta/2 < gamma → Integrable (fun t : ℝ => Complex.exp (-(gamma : ℂ)*(t : ℂ))*
          verticalIntegral (fun s => regularizedResolvent
            (FMSA.ExactMSA.MultiTailMixture.nonlinearCausalKernel z rho sigma p.1 p.2) b s i j) (-delta/2) t)) ∧
        ∀ t : ℝ,
          ‖verticalIntegral (fun s => regularizedResolvent
            (FMSA.ExactMSA.MultiTailMixture.nonlinearCausalKernel z rho sigma p.1 p.2) b s i j) (-delta/2) t‖ ≤
            exp ((-delta/2)*t)*C*π := by
  obtain ⟨delta, b, R, B, C, hd, hdr, hb, hR, hB, hC, hAn, hcont, hfreq, hlines⟩ :=
    actual_canonical_regularized_resolvent_analysis z hz rho sigma hsigma p hcanon
  refine ⟨delta, b, C, hd, hdr, hb, hC, ?_⟩
  intro i j
  let F := fun s : ℂ => regularizedResolvent
    (FMSA.ExactMSA.MultiTailMixture.nonlinearCausalKernel z rho sigma p.1 p.2) b s i j
  have hmajor (a : ℝ) (ha : -delta ≤ a) (k : ℝ) : (1+k^2)*‖F (verticalPoint a k)‖ ≤ C := by
    exact (mul_le_mul_of_nonneg_left (complexNormSum_entry_le _ i j) (by positivity)).trans ((hlines a ha).1 k)
  have hL1 (a : ℝ) (ha : -delta ≤ a) : Integrable (fun k : ℝ => F (verticalPoint a k)) :=
    ((hlines a ha).2.2 i j).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact vertical_integral_continuous F a (hL1 a ha.le)
  · intro a0 a1 h0 h1 t
    exact vertical_integrals_eq F (-delta) C (hAn i j) hmajor hL1 a0 a1 h0 h1 t
  · intro a ha t
    exact (vertical_integral_integrable_bound F (-delta) C hmajor hL1 a ha.le t).2
  · intro a ha t ht
    exact vertical_integral_eq_zero_of_nonpos F (-delta) C (hAn i j) hmajor hL1 a ha t ht
  · have hi := vertical_integral_weighted_integrable F (-delta) C (hAn i j) hmajor hL1
      (-delta/2) (by linarith) 0 (by linarith)
    simpa only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] using hi
  · intro gamma hg
    exact vertical_integral_weighted_integrable F (-delta) C (hAn i j) hmajor hL1
      (-delta/2) (by linarith) gamma hg
  · intro t
    exact (vertical_integral_integrable_bound F (-delta) C hmajor hL1 (-delta/2) (by linarith) t).2

end FMSA.Convergence.CanonicalContourShift

/-- info: 'FMSA.Convergence.CanonicalContourShift.endpoint_exponential_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.endpoint_exponential_bound

/-- info: 'FMSA.Convergence.CanonicalContourShift.inverse_quadratic_norm_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.inverse_quadratic_norm_bound

/-- info: 'FMSA.Convergence.CanonicalContourShift.horizontal_integral_norm_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.horizontal_integral_norm_bound

/-- info: 'FMSA.Convergence.CanonicalContourShift.horizontal_integrals_tendsto_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.horizontal_integrals_tendsto_zero

/-- info: 'FMSA.Convergence.CanonicalContourShift.rectangle_vertical_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.rectangle_vertical_identity

/-- info: 'FMSA.Convergence.CanonicalContourShift.vertical_integrals_eq_of_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.vertical_integrals_eq_of_le

/-- info: 'FMSA.Convergence.CanonicalContourShift.vertical_integrals_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.vertical_integrals_eq

/-- info: 'FMSA.Convergence.CanonicalContourShift.vertical_integral_integrable_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.vertical_integral_integrable_bound

/-- info: 'FMSA.Convergence.CanonicalContourShift.vertical_integral_eq_zero_of_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.vertical_integral_eq_zero_of_neg

/-- info: 'FMSA.Convergence.CanonicalContourShift.vertical_integral_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.vertical_integral_continuous

/-- info: 'FMSA.Convergence.CanonicalContourShift.vertical_integral_eq_zero_of_nonpos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.vertical_integral_eq_zero_of_nonpos

/-- info: 'FMSA.Convergence.CanonicalContourShift.vertical_integral_weighted_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.vertical_integral_weighted_integrable

/-- info: 'FMSA.Convergence.CanonicalContourShift.actual_canonical_contour_integrals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalContourShift.actual_canonical_contour_integrals
