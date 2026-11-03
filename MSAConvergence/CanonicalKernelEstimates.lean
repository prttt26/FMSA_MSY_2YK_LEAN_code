import MSAConvergence.ActualLaplaceJets

/-! Actual causal-kernel Laplace integrals beyond the Fourier axis and
uniform high-frequency bounds for the later canonical resolvent argument. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Paper FMSA.Convergence.ActualRDFTangent FMSA.Convergence.RDFExponentialOrder
open FMSA.Convergence.ActualLaplaceJets
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture

variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual causal-kernel Laplace integral exists on the full rate domain,
including negative real parts above every negative tail rate. -/
theorem kernel_laplace_integrable_rate_domain
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ)
    (hrate : ∀ u, 0 < s.re + z u) (i j : Fin N) :
    IntegrableOn (fun r : ℝ => (nonlinearCausalKernel z rho sigma p.1 p.2 r i j : ℂ) *
      Complex.exp (-s*r)) (Ioi 0) := by
  have hi : IntegrableOn (fun r : ℝ => exp (-s.re*r) * nonlinearCausalKernel z rho sigma p.1 p.2 r i j) (Ioi 0) := by
    have h := (nonlinearRecenteredQ_weighted_integrable z rho sigma p.1 p.2 hsigma (-s.re)
      (fun u => by linarith [hrate u]) i j).const_mul (rho i)
    change Integrable (fun r : ℝ => exp (-s.re*r) * nonlinearCausalKernel z rho sigma p.1 p.2 r i j) (volume.restrict (Ioi 0))
    simpa only [nonlinearCausalKernel, Matrix.of_apply, mul_assoc, mul_comm, mul_left_comm] using h
  exact FMSA.complex_laplace_integrable _
    ((nonlinearCausalKernel_continuous z rho sigma p.1 p.2).matrix_elem i j).continuousOn s hi

/-- The full Q transform formula needs only actual tail convergence, not a
nonnegative real part. Compact core pieces impose no extra restriction. -/
theorem full_q_integral_rate_domain (z : T → ℝ) (sigma A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N) (hsigma : ∀ i, 0 ≤ sigma i)
    (s : ℂ) (hs : s ≠ 0) (hrate : ∀ u, 0 < s.re + z u) (i j : Fin N) :
    (∫ r : ℝ, (q z sigma A qp W C i j r : ℂ) * Complex.exp (-s*r)) =
      QhatComplex z sigma A qp W C s i j := by
  rw [q_complex_decomposition z sigma A qp W C hsigma s i j,
    integral_add (qComplexPoly_integrable sigma A qp s i j)
      (integrable_finsetSum _ (fun u _ => qComplexRow_integrable z sigma W C s i j u (hrate u))),
    integral_finsetSum _ (fun u _ => qComplexRow_integrable z sigma W C s i j u (hrate u)),
    qComplexPoly_integral sigma A qp s i j hs (hsigma i)]
  simp_rw [qComplexRow_integral z sigma W C s i j _ (hrate _) hs (hsigma i)]
  have he : Complex.exp (-s*(edgeHi sigma i j : ℂ)) =
      Complex.exp (-s*(edgeLo sigma i j : ℂ)) * Complex.exp (-s*(sigma i : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold edgeHi edgeLo
    push_cast
    ring
  have hrows :
      (∑ u, ((W u i j : ℂ) * Complex.exp (-s*(edgeLo sigma i j : ℂ)) / (s+(z u : ℂ)) +
        (C u i j : ℂ) * (Complex.exp (-s*(edgeLo sigma i j : ℂ)) -
          Complex.exp (-s*(edgeHi sigma i j : ℂ))) / s +
        (C u i j : ℂ) * Complex.exp (-s*(edgeHi sigma i j : ℂ)) / (s+(z u : ℂ)))) =
      Complex.exp (-s*(edgeLo sigma i j : ℂ)) *
        (∑ u, ((W u i j : ℂ) / (s+(z u : ℂ)) +
          (C u i j : ℂ) * (1-Complex.exp (-s*(sigma i : ℂ))) / s)) +
        ∑ u, (C u i j : ℂ) * Complex.exp (-s*(edgeHi sigma i j : ℂ)) / (s+(z u : ℂ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [he]
    ring
  rw [hrows]
  unfold QhatComplex
  ring

/-- The actual recentered kernel dictionary transform extends to the full
rate convergence domain, retaining its lower-edge shift exactly. -/
theorem recentered_transform_rate_domain
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (Dt G : TailMatrix T N) (s : ℂ) (hs : s ≠ 0)
    (hrate : ∀ u, 0 < s.re + z u) (i j : Fin N) :
    FMSA.causalComplexLaplace (nonlinearRecenteredQ z rho sigma Dt G i j) s =
      Complex.exp (s*(edgeLo sigma i j : ℂ)) * QhatComplex z sigma
        (amplitudeA z rho sigma Dt G) (amplitudeQp z rho sigma Dt G)
        (W z rho Dt G) (C z rho sigma Dt G) s i j := by
  have hshift := causalShift_complex_laplace (nonlinearRecenteredQ z rho sigma Dt G i j) (edgeLo sigma i j) s
  rw [← nonlinearActualQ_eq_causalShift,
    full_q_integral_rate_domain z sigma _ _ _ _ hsigma s hs hrate] at hshift
  rw [hshift]
  have he : Complex.exp (s*(edgeLo sigma i j : ℂ))*Complex.exp (-s*(edgeLo sigma i j : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [← mul_assoc, he, one_mul]

/-- The actual J/L formula is an integral identity throughout the full rate
domain, not a formal assignment to divergent transforms. -/
theorem recentered_rational_rate_domain
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (Dt G : TailMatrix T N) (s : ℂ) (hs : s ≠ 0)
    (hrate : ∀ u, 0 < s.re + z u) (i j : Fin N) :
    s * FMSA.causalComplexLaplace (nonlinearRecenteredQ z rho sigma Dt G i j) s =
      nonlinearComplexL z rho sigma Dt G s i j -
        Complex.exp (-s*(sigma i : ℂ)) * nonlinearComplexJ z rho sigma Dt G s i j := by
  rw [recentered_transform_rate_domain z rho sigma hsigma Dt G s hs hrate]
  have he0 : Complex.exp (s*(edgeLo sigma i j : ℂ))*Complex.exp (-s*(edgeLo sigma i j : ℂ))=1 := by
    rw [← Complex.exp_add]; simp
  have he1 : Complex.exp (s*(edgeLo sigma i j : ℂ))*Complex.exp (-s*(edgeHi sigma i j : ℂ))=
      Complex.exp (-s*(sigma i : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; unfold edgeLo edgeHi; push_cast; ring
  have he : Complex.exp (s*(edgeLo sigma i j : ℂ))*QhatComplex z sigma
      (amplitudeA z rho sigma Dt G) (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) s i j=
      (1-s*(sigma i : ℂ)-Complex.exp (-s*(sigma i : ℂ)))/s^2*(amplitudeQp z rho sigma Dt G i j : ℂ)+
      (1-s*(sigma i : ℂ)+(s*(sigma i : ℂ))^2/2-Complex.exp (-s*(sigma i : ℂ)))/s^3*(amplitudeA z rho sigma Dt G j : ℂ)+
      (∑ u, ((W z rho Dt G u i j : ℂ)/(s+(z u : ℂ))+
        (C z rho sigma Dt G u i j : ℂ)*(1-Complex.exp (-s*(sigma i : ℂ)))/s))+
      (∑ u, Complex.exp (-s*(sigma i : ℂ))*(C z rho sigma Dt G u i j : ℂ)/(s+(z u : ℂ))) := by
    unfold QhatComplex
    rw [mul_add, ← mul_assoc, he0, one_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    calc
      _ = (Complex.exp (s*(edgeLo sigma i j : ℂ))*Complex.exp (-s*(edgeHi sigma i j : ℂ)))*
          (C z rho sigma Dt G u i j : ℂ)/(s+(z u : ℂ)) := by ring
      _ = _ := by rw [he1]
  rw [he]
  have hzs : ∀ u, s+(z u : ℂ) ≠ 0 := by
    intro u h
    have hRe := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hRe
    linarith [hrate u]
  have hc := nonlinear_complex_recenter_identity (amplitudeA z rho sigma Dt G j)
    (amplitudeQp z rho sigma Dt G i j) (sigma i) (Complex.exp (-s*(sigma i : ℂ))) s
    (fun u => (z u : ℂ)) (fun u => (W z rho Dt G u i j : ℂ)) (fun u => (C z rho sigma Dt G u i j : ℂ)) hs hzs
  simpa only [nonlinearComplexL, nonlinearComplexJ, Matrix.of_apply, nonlinearLowerQValue,
    Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_sum,
    sub_eq_add_neg, add_assoc, neg_mul] using hc

/-- The existing density-weighted causal kernel has the same exact J/L
integral formula on the extended rate domain. -/
theorem kernel_rational_rate_domain
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : s ≠ 0)
    (hrate : ∀ u, 0 < s.re + z u) (i j : Fin N) :
    s * rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j =
      (rho i : ℂ) * (nonlinearComplexL z rho sigma p.1 p.2 s i j -
        Complex.exp (-s*(sigma i : ℂ)) * nonlinearComplexJ z rho sigma p.1 p.2 s i j) := by
  have hk : rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j =
      (rho i : ℂ) * FMSA.causalComplexLaplace (nonlinearRecenteredQ z rho sigma p.1 p.2 i j) s := by
    unfold rdfMatrixLaplace FMSA.causalComplexLaplace nonlinearCausalKernel
    simp only [Matrix.of_apply]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    push_cast
    ring
  rw [hk, mul_left_comm s (rho i : ℂ), recentered_rational_rate_domain z rho sigma hsigma p.1 p.2 s hs hrate i j]

/-- The actual kernel's origin value is the existing lower-value coefficient,
including the row density. -/
theorem kernel_zero_value (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    nonlinearCausalKernel z rho sigma p.1 p.2 0 i j = rho i * nonlinearLowerQValue z rho sigma p.1 p.2 i j := by
  simp only [nonlinearCausalKernel, Matrix.of_apply, nonlinearRecenteredQ,
    min_eq_left (hsigma i), max_eq_right (hsigma i), sub_self, mul_zero,
    exp_zero, mul_one, zero_sub, nonlinearLowerQValue]
  ring

/-- Large complex frequency controls every shifted tail denominator without
restricting its real part to be nonnegative. -/
theorem norm_add_real_lower_bound (s : ℂ) (z : ℝ) (hz : 2 * |z| ≤ ‖s‖) :
    ‖s‖ ≤ 2 * ‖s+(z : ℂ)‖ := by
  have ht : ‖s‖ ≤ ‖s+(z : ℂ)‖ + |z| := by
    simpa only [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs] using norm_sub_le (s+(z : ℂ)) (z : ℂ)
  linarith

/-- One denominator power exactly cancels one frequency norm. -/
theorem scaled_norm_div (s a : ℂ) (hs : s ≠ 0) : ‖s‖ * ‖a/s‖ = ‖a‖ := by
  rw [norm_div]
  have hx : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  field_simp

/-- A double denominator retains at least one frequency factor at |s|>=1. -/
theorem scaled_norm_div_sq (s a : ℂ) (hs : 1 ≤ ‖s‖) : ‖s‖ * ‖a/s^2‖ ≤ ‖a‖ := by
  have hx : 0 < ‖s‖ := lt_of_lt_of_le zero_lt_one hs
  have he : ‖s‖ * ‖a/s^2‖ = ‖a‖ / ‖s‖ := by
    rw [norm_div, norm_pow]
    field_simp
  rw [he]
  exact div_le_self (norm_nonneg _) hs

/-- Shifted tail denominators lose at most a factor two at large frequency. -/
theorem scaled_norm_div_shift (s a : ℂ) (z : ℝ) (hs : 1 ≤ ‖s‖) (hz : 2 * |z| ≤ ‖s‖) :
    ‖s‖ * ‖a/(s+(z : ℂ))‖ ≤ 2*‖a‖ := by
  have hden := norm_add_real_lower_bound s z hz
  have hp : 0 < ‖s+(z : ℂ)‖ := by linarith
  rw [norm_div, ← mul_div_assoc]
  apply (div_le_iff₀ hp).mpr
  nlinarith [norm_nonneg a]

/-- A finite dictionary norm sum retains one common nonnegative scale. -/
theorem scaled_norm_add_add_sum {I : Type*} [Fintype I]
    (x : ℝ) (hx : 0 ≤ x) (a b : ℂ) (c : I → ℂ) :
    x * ‖a+b+∑ u, c u‖ ≤ x*‖a‖ + x*‖b‖ + ∑ u, x*‖c u‖ := by
  have ht := (norm_add_le (a+b) (∑ u, c u)).trans
    (add_le_add (norm_add_le a b) (norm_sum_le _ _))
  simpa only [mul_add, Finset.mul_sum] using mul_le_mul_of_nonneg_left ht hx

def jDecayBound (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) : ℝ :=
  |amplitudeA z rho sigma p.1 p.2 j| + |amplitudeQp z rho sigma p.1 p.2 i j| +
    ∑ u, 2 * |z u * C z rho sigma p.1 p.2 u i j|

def lDecayBound (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) : ℝ :=
  |amplitudeA z rho sigma p.1 p.2 j| +
    |amplitudeQp z rho sigma p.1 p.2 i j - sigma i * amplitudeA z rho sigma p.1 p.2 j| +
    ∑ u, 2 * |z u * W z rho p.1 p.2 u i j|

def leadingErrorBound (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (i j : Fin N) : ℝ :=
  |rho i| * (lDecayBound z rho sigma p i j + exp (delta*sigma i) * jDecayBound z rho sigma p i j)

/-- All finite high-frequency constants are computed nonnegative quantities. -/
theorem decayBounds_nonneg (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (i j : Fin N) :
    0 ≤ jDecayBound z rho sigma p i j ∧ 0 ≤ lDecayBound z rho sigma p i j ∧
      0 ≤ leadingErrorBound z rho sigma p delta i j := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [leadingErrorBound, lDecayBound, jDecayBound] <;> positivity

/-- The actual complex source J has one inverse-frequency bound, including
all finite tail terms, uniformly over directions in complex frequency. -/
theorem complexJ_scaled_bound (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ)
    (hs : 1 ≤ ‖s‖) (hz : ∀ u, 2 * |z u| ≤ ‖s‖) (i j : Fin N) :
    ‖s‖ * ‖nonlinearComplexJ z rho sigma p.1 p.2 s i j‖ ≤ jDecayBound z rho sigma p i j := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have hA := scaled_norm_div_sq s (amplitudeA z rho sigma p.1 p.2 j : ℂ) hs
  have hq := scaled_norm_div s (amplitudeQp z rho sigma p.1 p.2 i j : ℂ) hs0
  have hu (u : T) := scaled_norm_div_shift s ((z u : ℂ)*(C z rho sigma p.1 p.2 u i j : ℂ)) (z u) hs (hz u)
  unfold jDecayBound
  simp only [nonlinearComplexJ, Matrix.of_apply]
  apply (scaled_norm_add_add_sum ‖s‖ (norm_nonneg _) _ _ _).trans
  apply add_le_add
  · apply add_le_add
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hA
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hq.le
  · apply Finset.sum_le_sum
    intro u _
    simpa only [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs] using hu u

/-- The actual complex L factor minus its true lower value decays as one
inverse frequency; the contact derivative jump has not been discarded. -/
theorem complexL_scaled_remainder_bound (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ)
    (hs : 1 ≤ ‖s‖) (hz : ∀ u, 2 * |z u| ≤ ‖s‖) (i j : Fin N) :
    ‖s‖ * ‖nonlinearComplexL z rho sigma p.1 p.2 s i j -
      (nonlinearLowerQValue z rho sigma p.1 p.2 i j : ℂ)‖ ≤ lDecayBound z rho sigma p i j := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have he : nonlinearComplexL z rho sigma p.1 p.2 s i j -
      (nonlinearLowerQValue z rho sigma p.1 p.2 i j : ℂ) =
      (amplitudeA z rho sigma p.1 p.2 j : ℂ)/s^2 +
        ((amplitudeQp z rho sigma p.1 p.2 i j - sigma i*amplitudeA z rho sigma p.1 p.2 j : ℝ) : ℂ)/s +
        ∑ u, -((z u : ℂ)*(W z rho p.1 p.2 u i j : ℂ)/(s+(z u : ℂ))) := by
    simp only [nonlinearComplexL, Matrix.of_apply, Finset.sum_neg_distrib]
    push_cast
    ring
  rw [he]
  have hA := scaled_norm_div_sq s (amplitudeA z rho sigma p.1 p.2 j : ℂ) hs
  have hq := scaled_norm_div s
    ((amplitudeQp z rho sigma p.1 p.2 i j - sigma i*amplitudeA z rho sigma p.1 p.2 j : ℝ) : ℂ) hs0
  unfold lDecayBound
  apply (scaled_norm_add_add_sum ‖s‖ (norm_nonneg _) _ _ _).trans
  apply add_le_add
  · apply add_le_add
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hA
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hq.le
  · apply Finset.sum_le_sum
    intro u _
    simpa only [norm_neg, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs] using
      scaled_norm_div_shift s ((z u : ℂ)*(W z rho p.1 p.2 u i j : ℂ)) (z u) hs (hz u)

/-- The existing contact exponential is uniformly bounded on a closed
negative-real-part half-plane; no imaginary-frequency restriction is used. -/
theorem contact_phase_norm_bound (sigma delta : ℝ) (hsigma : 0 ≤ sigma)
    (s : ℂ) (hs : -delta ≤ s.re) :
    ‖Complex.exp (-s*(sigma : ℂ))‖ ≤ exp (delta*sigma) := by
  rw [Complex.norm_exp]
  apply exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_right (by linarith : -s.re ≤ delta) hsigma

/-- The actual scaled kernel minus its origin coefficient has an explicit
inverse-frequency bound throughout the convergent closed half-plane. -/
theorem kernel_scaled_origin_remainder
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hdelta : ∀ u, delta < z u)
    (s : ℂ) (hsre : -delta ≤ s.re) (hs : 1 ≤ ‖s‖)
    (hz : ∀ u, 2 * |z u| ≤ ‖s‖) (i j : Fin N) :
    ‖s‖ * ‖s * rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j -
      (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ)‖ ≤ leadingErrorBound z rho sigma p delta i j := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have hrate (u : T) : 0 < s.re + z u := by linarith [hdelta u]
  have hJ := complexJ_scaled_bound z rho sigma p s hs hz i j
  have hL := complexL_scaled_remainder_bound z rho sigma p s hs hz i j
  have hE := contact_phase_norm_bound (sigma i) delta (hsigma i) s hsre
  have hEJ : ‖s‖ * ‖Complex.exp (-s*(sigma i : ℂ)) * nonlinearComplexJ z rho sigma p.1 p.2 s i j‖ ≤
      exp (delta*sigma i) * jDecayBound z rho sigma p i j := by
    rw [norm_mul]
    calc
      _ = ‖Complex.exp (-s*(sigma i : ℂ))‖ * (‖s‖ * ‖nonlinearComplexJ z rho sigma p.1 p.2 s i j‖) := by ring
      _ ≤ _ := mul_le_mul hE hJ (by positivity) (exp_pos _).le
  have he : s * rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j -
      (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ) =
      (rho i : ℂ) * ((nonlinearComplexL z rho sigma p.1 p.2 s i j -
        (nonlinearLowerQValue z rho sigma p.1 p.2 i j : ℂ)) -
        Complex.exp (-s*(sigma i : ℂ)) * nonlinearComplexJ z rho sigma p.1 p.2 s i j) := by
    rw [kernel_rational_rate_domain z rho sigma hsigma p s hs0 hrate i j,
      kernel_zero_value z rho sigma hsigma p i j]
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold leadingErrorBound
  calc
    _ = |rho i| * (‖s‖ * ‖(nonlinearComplexL z rho sigma p.1 p.2 s i j -
        (nonlinearLowerQValue z rho sigma p.1 p.2 i j : ℂ)) -
        Complex.exp (-s*(sigma i : ℂ)) * nonlinearComplexJ z rho sigma p.1 p.2 s i j‖) := by ring
    _ ≤ |rho i| * (‖s‖ * ‖nonlinearComplexL z rho sigma p.1 p.2 s i j -
        (nonlinearLowerQValue z rho sigma p.1 p.2 i j : ℂ)‖ +
        ‖s‖ * ‖Complex.exp (-s*(sigma i : ℂ)) * nonlinearComplexJ z rho sigma p.1 p.2 s i j‖) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [mul_add] using mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg s)
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hL hEJ) (abs_nonneg _)

/-- The actual kernel has a full inverse-square leading-term remainder;
its leading coefficient is the actual kernel value at the origin. -/
theorem kernel_leading_remainder_bound
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hdelta : ∀ u, delta < z u)
    (s : ℂ) (hsre : -delta ≤ s.re) (hs : 1 ≤ ‖s‖)
    (hz : ∀ u, 2 * |z u| ≤ ‖s‖) (i j : Fin N) :
    ‖s‖^2 * ‖rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j -
      (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ)/s‖ ≤ leadingErrorBound z rho sigma p delta i j := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  let Q := rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j
  let q0 : ℂ := nonlinearCausalKernel z rho sigma p.1 p.2 0 i j
  have he : s*(Q-q0/s) = s*Q-q0 := by field_simp [hs0]
  have hn : ‖s‖^2 * ‖Q-q0/s‖ = ‖s‖ * ‖s*Q-q0‖ := by
    rw [← he, norm_mul]
    ring
  rw [hn]
  exact kernel_scaled_origin_remainder z rho sigma hsigma p delta hdelta s hsre hs hz i j

/-- The actual kernel itself has one inverse-frequency norm bound, with
its true origin coefficient and the proved inverse-square remainder. -/
theorem kernel_scaled_bound
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hdelta : ∀ u, delta < z u)
    (s : ℂ) (hsre : -delta ≤ s.re) (hs : 1 ≤ ‖s‖)
    (hz : ∀ u, 2 * |z u| ≤ ‖s‖) (i j : Fin N) :
    ‖s‖ * ‖rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j‖ ≤
      |nonlinearCausalKernel z rho sigma p.1 p.2 0 i j| + leadingErrorBound z rho sigma p delta i j := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  let Q := rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j
  let q0 : ℂ := nonlinearCausalKernel z rho sigma p.1 p.2 0 i j
  have hlead : ‖s‖^2 * ‖Q-q0/s‖ ≤ leadingErrorBound z rho sigma p delta i j :=
    kernel_leading_remainder_bound z rho sigma hsigma p delta hdelta s hsre hs hz i j
  have herr : ‖s‖ * ‖Q-q0/s‖ ≤ ‖s‖^2 * ‖Q-q0/s‖ :=
    mul_le_mul_of_nonneg_right (by nlinarith : ‖s‖ ≤ ‖s‖^2) (norm_nonneg _)
  calc
    _ ≤ ‖s‖ * ‖Q-q0/s‖ + ‖s‖ * ‖q0/s‖ := by
      simpa only [sub_add_cancel, mul_add] using mul_le_mul_of_nonneg_left
        (norm_add_le (Q-q0/s) (q0/s)) (norm_nonneg s)
    _ = ‖s‖ * ‖Q-q0/s‖ + ‖q0‖ := by rw [scaled_norm_div s q0 hs0]
    _ ≤ ‖s‖^2 * ‖Q-q0/s‖ + ‖q0‖ := add_le_add herr le_rfl
    _ ≤ leadingErrorBound z rho sigma p delta i j + ‖q0‖ := add_le_add hlead le_rfl
    _ = _ := by simp only [q0, Complex.norm_real, Real.norm_eq_abs]; ring

/-- The full actual matrix kernel has computable uniform high-frequency
bounds throughout a convergent closed negative-real-part half-plane. -/
theorem kernel_halfplane_high_frequency
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hdelta : ∀ u, delta < z u) :
    ∃ R B : ℝ, 1 ≤ R ∧ 0 ≤ B ∧ ∀ s : ℂ, -delta ≤ s.re → R ≤ ‖s‖ →
      ‖s‖^2 * (∑ i, ∑ j, ‖rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j -
        (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ)/s‖) ≤ B ∧
      ‖s‖ * (∑ i, ∑ j, ‖rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j‖) ≤
        FMSA.matrixAbsSum (nonlinearCausalKernel z rho sigma p.1 p.2 0) + B := by
  let R : ℝ := 1+2*∑ u, |z u|
  let B : ℝ := ∑ i, ∑ j, leadingErrorBound z rho sigma p delta i j
  have hn : 0 ≤ ∑ u, |z u| := Finset.sum_nonneg (fun u _ => abs_nonneg _)
  have hR : 1 ≤ R := by dsimp [R]; linarith
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    (decayBounds_nonneg z rho sigma p delta i j).2.2))
  refine ⟨R, B, hR, hB, ?_⟩
  intro s hsre hsR
  have hs : 1 ≤ ‖s‖ := hR.trans hsR
  have hz (u : T) : 2 * |z u| ≤ ‖s‖ := by
    have hu := Finset.single_le_sum (f := fun u : T => |z u|) (fun u _ => abs_nonneg (z u)) (Finset.mem_univ u)
    dsimp only [R] at hsR
    linarith
  constructor
  · simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
      kernel_leading_remainder_bound z rho sigma hsigma p delta hdelta s hsre hs hz i j))
  · simpa only [Finset.mul_sum, FMSA.matrixAbsSum, B, Finset.sum_add_distrib] using
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        kernel_scaled_bound z rho sigma hsigma p delta hdelta s hsre hs hz i j))

/-- Even off-root, the actual kernel renewal factor is a unit outside a
computed compact region of a convergent closed half-plane. This does not
assert canonicity inside that compact region. -/
theorem kernel_halfplane_unit_outside
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hdelta : ∀ u, delta < z u) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : ℂ, -delta ≤ s.re → R ≤ ‖s‖ →
      IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s) := by
  obtain ⟨R, B, hR, hB, hb⟩ := kernel_halfplane_high_frequency z rho sigma hsigma p delta hdelta
  let A := FMSA.matrixAbsSum (nonlinearCausalKernel z rho sigma p.1 p.2 0)
  have hA : 0 ≤ A := FMSA.matrixAbsSum_nonneg _
  refine ⟨R+A+B+1, by linarith, ?_⟩
  intro s hsre hsR
  have hs0 : R ≤ ‖s‖ := by linarith
  have hx : 0 < ‖s‖ := by linarith
  have ht := (hb s hsre hs0).2
  have hc : A+B < ‖s‖ := by linarith
  apply complex_matrix_one_sub_isUnit_of_normSum
  by_contra hn
  have h1 : (1 : ℝ) ≤ ∑ i, ∑ j, ‖rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j‖ := le_of_not_gt hn
  have hm := mul_le_mul_of_nonneg_left h1 hx.le
  rw [mul_one] at hm
  exact not_lt_of_ge hm (ht.trans_lt hc)

/-- The actual integral kernel symbol is continuous on a whole closed
half-plane extending left of the Fourier axis, including frequency zero. -/
theorem kernel_laplace_entry_continuous_halfplane
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hdelta : ∀ u, delta < z u) (i j : Fin N) :
    ContinuousOn (fun s : ℂ => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j)
      {s : ℂ | -delta ≤ s.re} := by
  unfold rdfMatrixLaplace FMSA.causalComplexLaplace
  simp only [Matrix.of_apply]
  apply continuousOn_of_dominated (bound := fun r : ℝ => exp (delta*r) * |nonlinearCausalKernel z rho sigma p.1 p.2 r i j|)
  · intro s _
    exact ((Complex.continuous_ofReal.comp ((nonlinearCausalKernel_continuous z rho sigma p.1 p.2).matrix_elem i j)).mul
      (by fun_prop : Continuous (fun r : ℝ => Complex.exp (-s*r)))).aestronglyMeasurable
  · intro s hsre
    change -delta ≤ s.re at hsre
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change ‖(nonlinearCausalKernel z rho sigma p.1 p.2 r i j : ℂ) * Complex.exp (-s*r)‖ ≤ _
    simp only [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re,
      Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.norm_eq_abs]
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith : -s.re ≤ delta) hr.le)
  · exact nonlinearCausalKernel_weighted_entry_integrable z rho sigma p.1 p.2 hsigma delta hdelta i j
  · exact Eventually.of_forall (fun r => (by fun_prop : Continuous (fun s : ℂ =>
      (nonlinearCausalKernel z rho sigma p.1 p.2 r i j : ℂ) * Complex.exp (-s*r))).continuousOn)

omit [Fintype T] in
/-- A finite positive rate family has an internally chosen strictly positive
left-strip margin; the empty family is allowed. -/
theorem exists_positive_rate_margin [Finite T] (z : T → ℝ) (hz : ∀ u, 0 < z u) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ u, delta < z u := by
  classical
  letI := Fintype.ofFinite T
  have haux (S : Finset T) : (∀ u ∈ S, 0 < z u) → ∃ delta : ℝ, 0 < delta ∧ ∀ u ∈ S, delta < z u := by
    induction S using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, zero_lt_one, fun u hu => False.elim (Finset.notMem_empty u hu)⟩
    | @insert u S hu ih =>
      intro hp
      obtain ⟨delta, hd, hb⟩ := ih (fun v hv => hp v (Finset.mem_insert_of_mem hv))
      have hzu := hp u (Finset.mem_insert_self u S)
      refine ⟨min delta (z u/2), lt_min hd (by linarith), ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (hb v hv)
  obtain ⟨delta, hd, hb⟩ := haux Finset.univ (fun u _ => hz u)
  exact ⟨delta, hd, fun u => hb u (Finset.mem_univ u)⟩

/-- Positive actual rates give an honest negative-real-part half-plane of
integral continuity and uniform high-frequency bounds, with a computed
unit renewal factor outside a compact region. No canonicity is assumed. -/
theorem actual_kernel_negative_halfplane_control
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N) :
    ∃ delta R B : ℝ, 0 < delta ∧ (∀ u, delta < z u) ∧ 1 ≤ R ∧ 0 ≤ B ∧
      ContinuousOn (fun s : ℂ => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)
        {s : ℂ | -delta ≤ s.re} ∧
      ∀ s : ℂ, -delta ≤ s.re →
        (∀ i j, IntegrableOn (fun r : ℝ => (nonlinearCausalKernel z rho sigma p.1 p.2 r i j : ℂ) *
          Complex.exp (-s*r)) (Ioi 0)) ∧
        (R ≤ ‖s‖ →
          ‖s‖^2 * (∑ i, ∑ j, ‖rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j -
            (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ)/s‖) ≤ B ∧
          ‖s‖ * (∑ i, ∑ j, ‖rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j‖) ≤
            FMSA.matrixAbsSum (nonlinearCausalKernel z rho sigma p.1 p.2 0) + B ∧
          IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) := by
  obtain ⟨delta, hd, hdr⟩ := exists_positive_rate_margin z hz
  obtain ⟨R0, B, hR0, hB, hest⟩ := kernel_halfplane_high_frequency z rho sigma hsigma p delta hdr
  obtain ⟨R1, hR1, hunit⟩ := kernel_halfplane_unit_outside z rho sigma hsigma p delta hdr
  have hc : ContinuousOn (fun s : ℂ => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)
      {s : ℂ | -delta ≤ s.re} := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact kernel_laplace_entry_continuous_halfplane z rho sigma hsigma p delta hdr i j
  refine ⟨delta, max R0 R1, B, hd, hdr, hR0.trans (le_max_left _ _), hB, hc, ?_⟩
  intro s hsre
  constructor
  · intro i j
    exact kernel_laplace_integrable_rate_domain z rho sigma hsigma p s
      (fun u => by linarith [hdr u]) i j
  · intro hsR
    have h0 : R0 ≤ ‖s‖ := (le_max_left _ _).trans hsR
    have h1 : R1 ≤ ‖s‖ := (le_max_right _ _).trans hsR
    exact ⟨(hest s hsre h0).1, (hest s hsre h0).2, hunit s hsre h1⟩

/-- The true zero-frequency transform is the actual zeroth kernel moment.
It is separate from the time-origin coefficient in the high-frequency expansion. -/
theorem kernel_laplace_at_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) 0 i j =
      ((rho i * nonlinearQMoment0 z rho sigma p.1 p.2 i j : ℝ) : ℂ) := by
  unfold rdfMatrixLaplace FMSA.causalComplexLaplace
  simp only [Matrix.of_apply, neg_zero, zero_mul, Complex.exp_zero, mul_one, nonlinearCausalKernel]
  rw [integral_complex_ofReal, integral_const_mul,
    ← nonlinearQMoment0_eq_integral z rho sigma p.1 p.2 hz hsigma i j]

/-- Continuity and exterior unit control turn full closed-right-half-plane
canonicity into a genuine left-strip gap. No real-axis stability substitute
for the stated full half-plane premise is used. -/
theorem continuous_canonical_strip_gap
    (F : ℂ → Matrix (Fin N) (Fin N) ℂ) (delta0 R : ℝ) (hd0 : 0 < delta0)
    (hF : ContinuousOn F {s : ℂ | -delta0 ≤ s.re})
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (F s))
    (hout : ∀ s : ℂ, -delta0 ≤ s.re → R ≤ ‖s‖ → IsUnit (F s)) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta0 ∧
      ∀ s : ℂ, -delta ≤ s.re → IsUnit (F s) := by
  classical
  let clamp : ℂ → ℂ := fun s => ⟨max (-delta0) s.re, s.im⟩
  have hclamp : Continuous clamp := by
    have he : clamp = fun s : ℂ => ((max (-delta0) s.re : ℝ) : ℂ) + (s.im : ℂ)*Complex.I := by
      funext s
      apply Complex.ext <;> simp [clamp]
    rw [he]
    fun_prop
  have hmem (s : ℂ) : -delta0 ≤ (clamp s).re := le_max_left _ _
  have heq (s : ℂ) (hs : -delta0 ≤ s.re) : clamp s = s := by
    apply Complex.ext <;> simp [clamp, max_eq_right hs]
  let G := F ∘ clamp
  have hG : Continuous G := hF.comp_continuous hclamp hmem
  have hentry (i j : Fin N) : Continuous (fun s => G s i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hG)
  have hdet : Continuous (fun s => (G s).det) := by
    simp only [Matrix.det_apply']
    fun_prop
  let S : Set ℂ := Metric.closedBall 0 R ∩ {s | (G s).det = 0}
  have hS : IsCompact S := (isCompact_closedBall (0 : ℂ) R).inter_right
    (isClosed_eq hdet continuous_const)
  have hneg (s : ℂ) (hs : s ∈ S) : s.re < 0 := by
    by_contra hn
    have hnonneg : 0 ≤ s.re := le_of_not_gt hn
    have hu : IsUnit (G s) := by
      change IsUnit (F (clamp s))
      rw [heq s (by linarith)]
      exact hcanon s hnonneg
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)) hs.2
  have hbad (delta : ℝ) (hdle : delta ≤ delta0) (s : ℂ) (hs : -delta ≤ s.re)
      (hn : ¬ IsUnit (F s)) : s ∈ S := by
    have hs0 : -delta0 ≤ s.re := by linarith
    have hnR : ‖s‖ ≤ R := by
      by_contra h
      exact hn (hout s hs0 (le_of_lt (lt_of_not_ge h)))
    refine ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hnR, ?_⟩
    change (F (clamp s)).det = 0
    rw [heq s hs0]
    by_contra hd
    exact hn ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  by_cases hne : S.Nonempty
  · obtain ⟨s0, hs0, hmax⟩ := hS.exists_isMaxOn hne Complex.continuous_re.continuousOn
    have hn0 : s0.re < 0 := hneg s0 hs0
    refine ⟨min delta0 (-s0.re/2), lt_min hd0 (by linarith), min_le_left _ _, ?_⟩
    intro s hs
    by_contra hn
    have hle := isMaxOn_iff.mp hmax s (hbad _ (min_le_left _ _) s hs hn)
    have hm := min_le_right delta0 (-s0.re/2)
    linarith
  · refine ⟨delta0/2, by linarith, by linarith, ?_⟩
    intro s hs
    by_contra hn
    exact hne ⟨s, hbad _ (by linarith) s hs hn⟩

/-- Full closed-right-half-plane canonicity of the actual integral renewal
factor implies a positive, internally obtained zero-free strip, inside all
actual tail rates. Pointwise Fourier stability is not the premise. -/
theorem actual_canonical_kernel_strip_gap
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re →
      IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ delta : ℝ, 0 < delta ∧ (∀ u, delta < z u) ∧
      ∀ s : ℂ, -delta ≤ s.re →
        IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s) := by
  obtain ⟨delta0, hd0, hdr⟩ := exists_positive_rate_margin z hz
  obtain ⟨R, _, hout⟩ := kernel_halfplane_unit_outside z rho sigma hsigma p delta0 hdr
  have hQ : ContinuousOn (fun s : ℂ =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)
      {s : ℂ | -delta0 ≤ s.re} := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact kernel_laplace_entry_continuous_halfplane z rho sigma hsigma p delta0 hdr i j
  obtain ⟨delta, hd, hdle, hu⟩ := continuous_canonical_strip_gap _ delta0 R hd0
    (continuousOn_const.sub hQ) hcanon hout
  exact ⟨delta, hd, fun u => hdle.trans_lt (hdr u), hu⟩

/-- Entry norm sum for finite complex matrices, without changing any norm
instance on matrices or the actual amplitude space. -/
def complexNormSum (A : Matrix (Fin N) (Fin N) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖

theorem complexNormSum_nonneg (A : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ complexNormSum A :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg (A i j)

theorem complexNormSum_add_le (A B : Matrix (Fin N) (Fin N) ℂ) :
    complexNormSum (A+B) ≤ complexNormSum A + complexNormSum B := by
  simpa only [complexNormSum, Matrix.add_apply, Finset.sum_add_distrib] using
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => norm_add_le (A i j) (B i j)))

theorem complexNormSum_mul_le (A B : Matrix (Fin N) (Fin N) ℂ) :
    complexNormSum (A*B) ≤ complexNormSum A * complexNormSum B := by
  classical
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [Matrix.mul_apply, norm_mul] using norm_sum_le (s := Finset.univ) (f := fun k => A i k * B k j)
    _ = ∑ i, ∑ k, ‖A i k‖ * (∑ j, ‖B k j‖) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, ‖A i k‖ * complexNormSum B := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg (B i j))) (Finset.mem_univ k)
    _ = _ := by simp only [complexNormSum, Finset.sum_mul]

theorem complexNormSum_one : complexNormSum (1 : Matrix (Fin N) (Fin N) ℂ) = (N : ℝ) := by
  classical
  have hh (i j : Fin N) : ‖(if i=j then (1 : ℂ) else 0)‖ = if i=j then (1 : ℝ) else 0 := by
    split_ifs <;> simp
  simp only [complexNormSum, Matrix.one_apply, hh]
  simp

/-- A half-size entry norm budget yields a quantitative inverse bound by
its actual inverse identity; no inverse-series axiom is supplied. -/
theorem one_sub_inverse_normSum_bound (Q : Matrix (Fin N) (Fin N) ℂ)
    (hQ : complexNormSum Q ≤ 1 / 2) :
    IsUnit (1-Q) ∧ complexNormSum ((1-Q)⁻¹) ≤ 2*(N : ℝ) := by
  have hu : IsUnit (1-Q) := complex_matrix_one_sub_isUnit_of_normSum Q (by
    change complexNormSum Q < 1
    linarith)
  have hmul := Matrix.nonsing_inv_mul (1-Q) ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have he : (1-Q)⁻¹ = 1 + (1-Q)⁻¹*Q := by
    rw [mul_sub, mul_one] at hmul
    exact sub_eq_iff_eq_add.mp hmul
  have hb : complexNormSum ((1-Q)⁻¹) ≤ (N : ℝ) +
      complexNormSum ((1-Q)⁻¹)*complexNormSum Q := by
    calc
      _ = complexNormSum (1+(1-Q)⁻¹*Q) := congrArg complexNormSum he
      _ ≤ complexNormSum 1 + complexNormSum ((1-Q)⁻¹*Q) := complexNormSum_add_le _ _
      _ ≤ _ := by rw [complexNormSum_one]; exact add_le_add le_rfl (complexNormSum_mul_le _ _)
  have hh := mul_le_mul_of_nonneg_left hQ (complexNormSum_nonneg ((1-Q)⁻¹))
  exact ⟨hu, by nlinarith⟩

/-- The actual matrix inverse has a quadratic small-kernel remainder. -/
theorem one_sub_inverse_remainder_bound (Q : Matrix (Fin N) (Fin N) ℂ)
    (hQ : complexNormSum Q ≤ 1 / 2) :
    complexNormSum ((1-Q)⁻¹-1-Q) ≤ 2*(N : ℝ)*(complexNormSum Q)^2 := by
  obtain ⟨hu, hb⟩ := one_sub_inverse_normSum_bound Q hQ
  have hmul := Matrix.nonsing_inv_mul (1-Q) ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have he : (1-Q)⁻¹-1 = (1-Q)⁻¹*Q := by
    rw [mul_sub, mul_one] at hmul
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hmul).trans (add_comm _ _))
  have he2 : (1-Q)⁻¹-1-Q = (1-Q)⁻¹*Q*Q := by
    calc
      _ = (1-Q)⁻¹*Q-Q := by rw [he]
      _ = ((1-Q)⁻¹-1)*Q := by noncomm_ring
      _ = _ := by rw [he]
  rw [he2]
  calc
    _ ≤ complexNormSum ((1-Q)⁻¹*Q) * complexNormSum Q := complexNormSum_mul_le _ _
    _ ≤ (complexNormSum ((1-Q)⁻¹)*complexNormSum Q)*complexNormSum Q :=
      mul_le_mul_of_nonneg_right (complexNormSum_mul_le _ _) (complexNormSum_nonneg _)
    _ ≤ (2*(N : ℝ)*complexNormSum Q)*complexNormSum Q := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb (complexNormSum_nonneg _)) (complexNormSum_nonneg _)
    _ = _ := by ring

/-- Continuity of the genuine nonsingular inverse on a unit-valued domain. -/
theorem matrix_inverse_continuousOn (F : ℂ → Matrix (Fin N) (Fin N) ℂ) (S : Set ℂ)
    (hF : ContinuousOn F S) (hu : ∀ s ∈ S, IsUnit (F s)) :
    ContinuousOn (fun s => (F s)⁻¹) S := by
  intro s hs
  have hd : (F s).det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (hu s hs))
  have hi : ContinuousAt Ring.inverse (F s).det := by
    change ContinuousAt (fun c : ℂ => Ring.inverse c) (F s).det
    simpa only [Ring.inverse_eq_inv] using (continuousAt_inv₀ hd)
  exact (continuousAt_matrix_inv (F s) hi).comp_continuousWithinAt (hF s hs)

/-- The true finite canonical resolvent has a uniform inverse-square
high-frequency remainder on a convergent negative-real-part half-plane.
This is a frequency estimate, not yet a time-domain decay theorem. -/
theorem actual_resolvent_halfplane_high_frequency
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hdelta : ∀ u, delta < z u) :
    ∃ R B : ℝ, 1 ≤ R ∧ 0 ≤ B ∧ ∀ s : ℂ, -delta ≤ s.re → R ≤ ‖s‖ →
      IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s) ∧
      complexNormSum ((1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹) ≤ 2*(N : ℝ) ∧
      ‖s‖^2 * complexNormSum
        ((1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹-1-
          Matrix.of (fun i j => (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ)/s)) ≤ B := by
  obtain ⟨R0, B0, hR0, hB0, hb⟩ := kernel_halfplane_high_frequency z rho sigma hsigma p delta hdelta
  let C0 := FMSA.matrixAbsSum (nonlinearCausalKernel z rho sigma p.1 p.2 0) + B0
  have hC0 : 0 ≤ C0 := add_nonneg (FMSA.matrixAbsSum_nonneg _) hB0
  refine ⟨R0+2*C0, B0+2*(N : ℝ)*C0^2, by linarith, by positivity, ?_⟩
  intro s hsre hsR
  have hsR0 : R0 ≤ ‖s‖ := by linarith
  have hs : 1 ≤ ‖s‖ := hR0.trans hsR0
  let Q := rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s
  let K := Matrix.of (fun i j => (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ)/s)
  have hscale : ‖s‖*complexNormSum Q ≤ C0 := (hb s hsre hsR0).2
  have hhalf : complexNormSum Q ≤ 1 / 2 := by
    have hx : 2*C0 ≤ ‖s‖ := by linarith
    have ht := mul_le_mul_of_nonneg_right hx (complexNormSum_nonneg Q)
    nlinarith [complexNormSum_nonneg Q]
  obtain ⟨hu, hinv⟩ := one_sub_inverse_normSum_bound Q hhalf
  refine ⟨hu, hinv, ?_⟩
  have hk : ‖s‖^2 * complexNormSum (Q-K) ≤ B0 := (hb s hsre hsR0).1
  have hr := one_sub_inverse_remainder_bound Q hhalf
  have herr : ‖s‖^2 * complexNormSum ((1-Q)⁻¹-1-Q) ≤ 2*(N : ℝ)*C0^2 := by
    have hp : (‖s‖*complexNormSum Q)^2 ≤ C0^2 := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (complexNormSum_nonneg Q)) hscale 2
    calc
      _ ≤ ‖s‖^2*(2*(N : ℝ)*(complexNormSum Q)^2) := mul_le_mul_of_nonneg_left hr (sq_nonneg _)
      _ = 2*(N : ℝ)*(‖s‖*complexNormSum Q)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have he : (1-Q)⁻¹-1-K = (Q-K)+((1-Q)⁻¹-1-Q) := by abel
  change ‖s‖^2*complexNormSum ((1-Q)⁻¹-1-K) ≤ _
  rw [he]
  calc
    _ ≤ ‖s‖^2*(complexNormSum (Q-K)+complexNormSum ((1-Q)⁻¹-1-Q)) :=
      mul_le_mul_of_nonneg_left (complexNormSum_add_le _ _) (sq_nonneg _)
    _ = ‖s‖^2*complexNormSum (Q-K)+‖s‖^2*complexNormSum ((1-Q)⁻¹-1-Q) := by ring
    _ ≤ _ := add_le_add hk herr

/-- Closed-right-half-plane canonicity gives an actual negative half-plane
on which the finite resolvent inverse is continuous and uniformly bounded.
The actual high-frequency resolvent remainder is simultaneously controlled. -/
theorem actual_canonical_resolvent_control
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re →
      IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ delta R B C : ℝ, 0 < delta ∧ (∀ u, delta < z u) ∧ 1 ≤ R ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ContinuousOn (fun s : ℂ => (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹)
        {s : ℂ | -delta ≤ s.re} ∧
      ∀ s : ℂ, -delta ≤ s.re →
        IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s) ∧
        complexNormSum ((1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹) ≤ C ∧
        (R ≤ ‖s‖ → ‖s‖^2 * complexNormSum
          ((1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹-1-
            Matrix.of (fun i j => (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ)/s)) ≤ B) := by
  classical
  obtain ⟨delta, hd, hdr, hu⟩ := actual_canonical_kernel_strip_gap z hz rho sigma hsigma p hcanon
  obtain ⟨R, B, hR, hB, hb⟩ := actual_resolvent_halfplane_high_frequency z rho sigma hsigma p delta hdr
  let H := {s : ℂ | -delta ≤ s.re}
  let U := fun s : ℂ => (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹
  have hQ : ContinuousOn (fun s : ℂ =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s) H := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact kernel_laplace_entry_continuous_halfplane z rho sigma hsigma p delta hdr i j
  have hU : ContinuousOn U H := matrix_inverse_continuousOn _ H
    (continuousOn_const.sub hQ) hu
  let K := Metric.closedBall (0 : ℂ) R ∩ H
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hS : ContinuousOn (fun s => complexNormSum (U s)) K := by
    unfold complexNormSum
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact (continuousOn_pi.mp (continuousOn_pi.mp (hU.mono (fun s (hs : s ∈ K) => hs.2)) i) j).norm
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hS
  refine ⟨delta, R, B, max 0 (max C0 (2*(N : ℝ))), hd, hdr, hR, hB, le_max_left _ _, hU, ?_⟩
  intro s hs
  refine ⟨hu s hs, ?_, fun hsR => (hb s hs hsR).2.2⟩
  by_cases hsR : R ≤ ‖s‖
  · exact (hb s hs hsR).2.1.trans ((le_max_right _ _).trans (le_max_right _ _))
  · have hsK : s ∈ K := ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using (le_of_lt (lt_of_not_ge hsR)), hs⟩
    have hc : complexNormSum (U s) ≤ C0 := le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hC0 s hsK)
    exact hc.trans ((le_max_left _ _).trans (le_max_right _ _))

end FMSA.Convergence.CanonicalKernelEstimates

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.kernel_laplace_integrable_rate_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.kernel_laplace_integrable_rate_domain

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.full_q_integral_rate_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.full_q_integral_rate_domain

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.recentered_transform_rate_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.recentered_transform_rate_domain

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.recentered_rational_rate_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.recentered_rational_rate_domain

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.kernel_rational_rate_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.kernel_rational_rate_domain

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.kernel_zero_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.kernel_zero_value

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.norm_add_real_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.norm_add_real_lower_bound

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.scaled_norm_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.scaled_norm_div

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.scaled_norm_div_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.scaled_norm_div_sq

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.scaled_norm_div_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.scaled_norm_div_shift

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.scaled_norm_add_add_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.scaled_norm_add_add_sum

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.decayBounds_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.decayBounds_nonneg

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.complexJ_scaled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.complexJ_scaled_bound

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.complexL_scaled_remainder_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.complexL_scaled_remainder_bound

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.contact_phase_norm_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.contact_phase_norm_bound

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.kernel_scaled_origin_remainder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.kernel_scaled_origin_remainder

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.kernel_leading_remainder_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.kernel_leading_remainder_bound

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.kernel_scaled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.kernel_scaled_bound

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.kernel_halfplane_high_frequency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.kernel_halfplane_high_frequency

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.kernel_halfplane_unit_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.kernel_halfplane_unit_outside

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.kernel_laplace_entry_continuous_halfplane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.kernel_laplace_entry_continuous_halfplane

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.exists_positive_rate_margin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.exists_positive_rate_margin

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.actual_kernel_negative_halfplane_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.actual_kernel_negative_halfplane_control

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.kernel_laplace_at_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.kernel_laplace_at_zero

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.continuous_canonical_strip_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.continuous_canonical_strip_gap

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.actual_canonical_kernel_strip_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.actual_canonical_kernel_strip_gap

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.complexNormSum_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.complexNormSum_nonneg

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.complexNormSum_add_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.complexNormSum_add_le

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.complexNormSum_mul_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.complexNormSum_mul_le

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.complexNormSum_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.complexNormSum_one

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.one_sub_inverse_normSum_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.one_sub_inverse_normSum_bound

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.one_sub_inverse_remainder_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.one_sub_inverse_remainder_bound

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.matrix_inverse_continuousOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.matrix_inverse_continuousOn

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.actual_resolvent_halfplane_high_frequency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.actual_resolvent_halfplane_high_frequency

/-- info: 'FMSA.Convergence.CanonicalKernelEstimates.actual_canonical_resolvent_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalKernelEstimates.actual_canonical_resolvent_control
