import MSAConvergence.ActualExcessDecay

/-! Genuine amplitude derivatives of the cancelled excess source and its
finite exponential tail; all derivative interchanges use fixed dictionaries. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Convergence.ActualExcessSourceTangent
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.ActualRDFTangent FMSA.Convergence.RDFExponentialOrder
open FMSA.Convergence.CanonicalRenewalFormula FMSA.Convergence.ActualExcessDecay

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Fixed scalar background convolution dictionary. -/
def backgroundBasis (z : T → ℝ) (sigma : Fin N → ℝ)
    (b : BasisIndex T) (i m : Fin N) : ℝ → ℝ :=
  causalIntervalConv (recenteredBasis z sigma b m) (fun t => t+edgeHi sigma i m)

/-- Each fixed background convolution is genuinely continuous. -/
theorem background_basis_continuous (z : T → ℝ) (sigma : Fin N → ℝ)
    (b : BasisIndex T) (i m : Fin N) : Continuous (backgroundBasis z sigma b i m) :=
  causal_convolution_continuous _ _ (recenteredBasis_continuous z sigma b m) (by fun_prop)

/-- The actual background integral has a finite fixed dictionary, so its
amplitude differentiation needs no unproved integral interchange. -/
theorem background_convolution_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i m j : Fin N) (r : ℝ) :
    (∫ t in (0 : ℝ)..r, nonlinearRecenteredQ z rho sigma p.1 p.2 m j (r-t)*(t+edgeHi sigma i m)) =
      ∑ b : BasisIndex T, bhCoefficient z rho sigma p m j b*backgroundBasis z sigma b i m r := by
  simp_rw [recentered_eq_basis, Finset.sum_mul]
  have hi (b : BasisIndex T) : IntervalIntegrable
      (fun t : ℝ => bhCoefficient z rho sigma p m j b*recenteredBasis z sigma b m (r-t)*(t+edgeHi sigma i m)) volume 0 r :=
    ((continuous_const.mul ((recenteredBasis_continuous z sigma b m).comp
      (continuous_const.sub continuous_id))).mul (continuous_id.add_const _)).intervalIntegrable 0 r
  rw [intervalIntegral.integral_finsetSum (fun b _ => hi b)]
  apply Finset.sum_congr rfl
  intro b _
  simp only [backgroundBasis, causalIntervalConv]
  rw [show (fun t : ℝ => (bhCoefficient z rho sigma p m j b*recenteredBasis z sigma b m (r-t))*(t+edgeHi sigma i m)) =
    fun t : ℝ => bhCoefficient z rho sigma p m j b*(recenteredBasis z sigma b m (r-t)*(t+edgeHi sigma i m)) by funext t; ring,
    intervalIntegral.integral_const_mul]

/-- Actual cancelled source dictionary before any differentiation. -/
theorem excess_source_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    nonlinearExcessSource z rho sigma p.1 p.2 r i j =
      nonlinearGSource z rho sigma p.1 p.2 r i j-(r+edgeHi sigma i j)+
        ∑ m, rho m*∑ b : BasisIndex T, bhCoefficient z rho sigma p m j b*backgroundBasis z sigma b i m r := by
  simp only [nonlinearExcessSource, Matrix.of_apply, background_convolution_eq_basis]

/-- Genuine smoothness of the actual affine/exponential source in amplitudes. -/
theorem g_source_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N => nonlinearGSource z rho sigma p.1 p.2 r i j) := by
  have he : (fun p : TailMatrix T N × TailMatrix T N => nonlinearGSource z rho sigma p.1 p.2 r i j) =
      fun p => ∑ b : BasisIndex T, bhCoefficient z rho sigma p i j b*gSourceBasis z b r := by
    funext p
    exact gSource_eq_basis z rho sigma p i j r
  rw [he]
  fun_prop

/-- The actual cancelled source is smooth at every fixed real radius. -/
theorem excess_source_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ) (i j : Fin N) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N => nonlinearExcessSource z rho sigma p.1 p.2 r i j) := by
  have he : (fun p : TailMatrix T N × TailMatrix T N => nonlinearExcessSource z rho sigma p.1 p.2 r i j) =
      fun p => nonlinearGSource z rho sigma p.1 p.2 r i j-(r+edgeHi sigma i j)+
        ∑ m, rho m*∑ b : BasisIndex T, bhCoefficient z rho sigma p m j b*backgroundBasis z sigma b i m r := by
    funext p
    exact excess_source_eq_basis z rho sigma p i j r
  rw [he]
  exact ((g_source_contDiff z rho sigma i j r).sub contDiff_const).add (by fun_prop)

/-- The genuine Frechet derivative of the actual cancelled source. -/
def excessSourceVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearExcessSource z rho sigma a.1 a.2 r i j) p v

/-- Actual source differentiation is reduced to the proved fixed dictionary. -/
theorem excess_source_variation_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    excessSourceVariation z rho sigma p v i j r = sourceVariation z rho sigma p v i j r+
      ∑ m, rho m*∑ b : BasisIndex T, fderiv ℝ (fun a => bhCoefficient z rho sigma a m j b) p v*
        backgroundBasis z sigma b i m r := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearExcessSource z rho sigma a.1 a.2 r i j) =
      fun a => nonlinearGSource z rho sigma a.1 a.2 r i j-(r+edgeHi sigma i j)+
        ∑ m, rho m*∑ b : BasisIndex T, bhCoefficient z rho sigma a m j b*backgroundBasis z sigma b i m r := by
    funext a
    exact excess_source_eq_basis z rho sigma a i j r
  have hdc (m : Fin N) (b : BasisIndex T) :=
    ((bhCoefficient_contDiff z rho sigma m j b).differentiable (by simp) p).hasFDerivAt.mul_const
      (backgroundBasis z sigma b i m r)
  have hd := (((g_source_contDiff z rho sigma i j r).differentiable (by simp) p).hasFDerivAt.sub_const
    (r+edgeHi sigma i j)).add (HasFDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
      (HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => hdc m b)).const_mul (rho m)))
  change HasFDerivAt (fun a : TailMatrix T N × TailMatrix T N =>
    nonlinearGSource z rho sigma a.1 a.2 r i j-(r+edgeHi sigma i j)+
      ∑ m, rho m*∑ b : BasisIndex T, bhCoefficient z rho sigma a m j b*backgroundBasis z sigma b i m r) _ p at hd
  rw [excessSourceVariation, he, hd.fderiv]
  simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, sourceVariation]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The genuine cancelled-source derivative is globally continuous in time. -/
theorem excess_source_variation_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    Continuous (excessSourceVariation z rho sigma p v i j) := by
  have he : excessSourceVariation z rho sigma p v i j = fun r => sourceVariation z rho sigma p v i j r+
      ∑ m, rho m*∑ b : BasisIndex T, fderiv ℝ (fun a => bhCoefficient z rho sigma a m j b) p v*
        backgroundBasis z sigma b i m r := funext (excess_source_variation_eq_basis z rho sigma p v i j)
  rw [he]
  exact (sourceVariation_continuous z rho sigma p v i j).add
    (continuous_finsetSum _ (fun m _ => (continuous_finsetSum _ (fun b _ =>
      (background_basis_continuous z sigma b i m).const_mul _)).const_mul _))

/-- The finite actual excess tail coefficients are smooth off root. -/
theorem excess_tail_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ) (u : T) (i j : Fin N) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N => nonlinearExcessTail z rho sigma p.1 p.2 u i j) := by
  unfold nonlinearExcessTail nonlinearTailAmplitude
  fun_prop

/-- Differentiating an off-root finite tail identity proves the actual
cancelled-source tangent tail, rather than differentiating an inequality. -/
theorem excess_source_variation_tail (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) (hr : rdfHSSupportCeiling sigma ≤ r) :
    excessSourceVariation z rho sigma p v i j r = ∑ u : T,
      fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearExcessTail z rho sigma a.1 a.2 u i j) p v*exp (-z u*r) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearExcessSource z rho sigma a.1 a.2 r i j) =
      fun a => ∑ u : T, nonlinearExcessTail z rho sigma a.1 a.2 u i j*exp (-z u*r) := by
    funext a
    exact nonlinearExcessSource_tail z rho sigma a.1 a.2 hz hsigma hv r hr i j
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun u _ =>
    ((excess_tail_contDiff z rho sigma u i j).differentiable (by simp) p).hasFDerivAt.mul_const (exp (-z u*r)))
  rw [excessSourceVariation, he, hd.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- A continuous field with an actual finite exponential tail has a global
positive-axis exponential weight bound, with the compact constant obtained
internally. Empty tail families are allowed. -/
theorem finite_exponential_tail_weighted_bound
    (f : ℝ → ℝ) (hf : Continuous f) (z c : T → ℝ) (R delta : ℝ) (hR : 0 ≤ R)
    (hdz : ∀ u, delta ≤ z u) (htail : ∀ t, R ≤ t → f t = ∑ u, c u*exp (-z u*t)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 ≤ t → exp (delta*t)*|f t| ≤ B := by
  have hc : Continuous (fun t : ℝ => exp (delta*t)*|f t|) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf.abs
  obtain ⟨x, _hx, hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) R).Nonempty from ⟨0, le_rfl, hR⟩) hc.continuousOn
  refine ⟨exp (delta*x)*|f x|+∑ u, |c u|, by positivity, ?_⟩
  intro t ht
  by_cases h : t ≤ R
  · exact (hm ⟨ht, h⟩).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
  · have hb : exp (delta*t)*|f t| ≤ ∑ u, |c u| := by
      rw [htail t (not_le.mp h).le]
      calc
        _ ≤ exp (delta*t)*∑ u, |c u*exp (-z u*t)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (exp_pos _).le
        _ = ∑ u, |c u| *exp ((delta-z u)*t) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          rw [abs_mul, abs_of_pos (exp_pos _), mul_left_comm, ← exp_add]
          congr 2
          ring
        _ ≤ ∑ u, |c u| := Finset.sum_le_sum (fun u _ => by
          have he : exp ((delta-z u)*t) ≤ 1 := exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hdz u)) ht)
          simpa only [mul_one] using mul_le_mul_of_nonneg_left he (abs_nonneg (c u)))
    exact hb.trans (le_add_of_nonneg_left (mul_nonneg (exp_pos _).le (abs_nonneg _)))

/-- Finitely many entrywise exponential weight bounds give one genuine
matrix absolute-sum bound. -/
theorem matrix_weighted_bound_of_entries (f : ℝ → Matrix (Fin N) (Fin N) ℝ) (delta : ℝ)
    (h : ∀ i j, ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 ≤ t → exp (delta*t)*|f t i j| ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 ≤ t → exp (delta*t)*FMSA.matrixAbsSum (f t) ≤ B := by
  choose B hB hb using h
  refine ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hB i j)), ?_⟩
  intro t ht
  simp only [FMSA.matrixAbsSum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j t ht))

/-- Global exponential weight control of the genuine cancelled-source
derivative, obtained from its actual tail and compact continuity. -/
theorem excess_source_variation_weighted_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hdz : ∀ u, delta ≤ z u) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 ≤ t → exp (delta*t)*FMSA.matrixAbsSum
      (Matrix.of (fun i j => excessSourceVariation z rho sigma p v i j t)) ≤ B := by
  apply matrix_weighted_bound_of_entries
  intro i j
  exact finite_exponential_tail_weighted_bound _ (excess_source_variation_continuous z rho sigma p v i j)
    z _ (rdfHSSupportCeiling sigma) delta (rdfHSSupportCeiling_nonneg sigma) hdz
    (fun t ht => excess_source_variation_tail z hz rho sigma hsigma hv p v i j t ht)

/-- The genuine actual kernel derivative is globally continuous in time. -/
theorem kernel_variation_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    Continuous (kernelVariation z rho sigma p v i j) := by
  have he : kernelVariation z rho sigma p v i j = fun r => rho i*
      ∑ b : BasisIndex T, fderiv ℝ (fun a => bhCoefficient z rho sigma a i j b) p v*recenteredBasis z sigma b i r :=
    funext (kernelVariation_eq_basis z rho sigma p v i j)
  rw [he]
  exact continuous_const.mul (continuous_finsetSum _ (fun b _ =>
    (recenteredBasis_continuous z sigma b i).const_mul _))

/-- The actual nonlinear kernel tail identity holds off root and may be
differentiated at fixed parameters. Row density is retained. -/
theorem kernel_variation_tail (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) (hr : sigma i ≤ r) :
    kernelVariation z rho sigma p v i j r = ∑ u : T,
      (rho i*fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearTailAmplitude z rho sigma a.1 a.2 u i j) p v)*exp (-z u*r) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearCausalKernel z rho sigma a.1 a.2 r i j) =
      fun a => rho i*∑ u : T, nonlinearTailAmplitude z rho sigma a.1 a.2 u i j*exp (-z u*r) := by
    funext a
    simp only [nonlinearCausalKernel, Matrix.of_apply, nonlinearRecenteredQ_tail z rho sigma a.1 a.2 i j r hr]
  have hdc (u : T) : ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => nonlinearTailAmplitude z rho sigma a.1 a.2 u i j) := by
    unfold nonlinearTailAmplitude
    fun_prop
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ) (fun u _ =>
    ((hdc u).differentiable (by simp) p).hasFDerivAt.mul_const (exp (-z u*r)))).const_mul (rho i)
  rw [kernelVariation, he, hd.fderiv]
  simp only [smul_apply, smul_eq_mul, sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- A true exponential weight bound for the actual kernel derivative,
without a BH-root, nearby canonicity or kernel-budget premise. -/
theorem kernel_variation_weighted_bounded (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hdz : ∀ u, delta ≤ z u) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 ≤ t → exp (delta*t)*FMSA.matrixAbsSum
      (Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) ≤ B := by
  apply matrix_weighted_bound_of_entries
  intro i j
  apply finite_exponential_tail_weighted_bound _ (kernel_variation_continuous z rho sigma p v i j)
    z _ (rdfHSSupportCeiling sigma) delta (rdfHSSupportCeiling_nonneg sigma) hdz
  intro t ht
  exact kernel_variation_tail z rho sigma p v i j t ((le_abs_self _).trans
    ((Finset.single_le_sum (f := fun m : Fin N => |sigma m|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)).trans ht))

/-- The actual kernel derivative convoluted with the affine background
has the same fixed dictionary used in the genuine source derivative. -/
theorem background_kernel_variation_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i m j : Fin N) (r : ℝ) :
    causalIntervalConv (kernelVariation z rho sigma p v m j) (fun t => t+edgeHi sigma i m) r =
      rho m*∑ b : BasisIndex T, fderiv ℝ (fun a => bhCoefficient z rho sigma a m j b) p v*
        backgroundBasis z sigma b i m r := by
  have he : (fun t : ℝ => kernelVariation z rho sigma p v m j (r-t)*(t+edgeHi sigma i m)) =
      fun t : ℝ => rho m*∑ b : BasisIndex T,
        fderiv ℝ (fun a => bhCoefficient z rho sigma a m j b) p v*
          (recenteredBasis z sigma b m (r-t)*(t+edgeHi sigma i m)) := by
    funext t
    rw [kernelVariation_eq_basis, mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hi (b : BasisIndex T) : IntervalIntegrable (fun t : ℝ =>
      fderiv ℝ (fun a => bhCoefficient z rho sigma a m j b) p v*
        (recenteredBasis z sigma b m (r-t)*(t+edgeHi sigma i m))) volume 0 r :=
    ((((recenteredBasis_continuous z sigma b m).comp (continuous_const.sub continuous_id)).mul
      (continuous_id.add_const _)).const_mul _).intervalIntegrable 0 r
  unfold causalIntervalConv
  rw [he, intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun b _ => hi b)]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- The actual cancelled-source derivative contains exactly the affine
background convolution with the actual kernel derivative. -/
theorem excess_source_variation_eq_background (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    excessSourceVariation z rho sigma p v i j r = sourceVariation z rho sigma p v i j r+
      ∑ m, causalIntervalConv (kernelVariation z rho sigma p v m j) (fun t => t+edgeHi sigma i m) r := by
  simp only [background_kernel_variation_eq_basis, excess_source_variation_eq_basis]

/-- Actual linearized excess renewal, with its affine background genuinely
removed. The derivative is the existing Frechet derivative, not independent
tangent data and not a derivative along a presumed curve of BH roots. -/
theorem actual_excess_tangent_renewal (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    excessVariation z rho sigma p v i j r = excessSourceVariation z rho sigma p v i j r+
      (∑ m, causalIntervalConv (fun t => nonlinearCausalKernel z rho sigma p.1 p.2 t m j)
        (excessVariation z rho sigma p v i m) r)+
      ∑ m, causalIntervalConv (kernelVariation z rho sigma p v m j)
        (fun t => nonlinearRDFExcess z rho sigma p.1 p.2 t i m) r := by
  have hsplit (m : Fin N) :
      causalIntervalConv (kernelVariation z rho sigma p v m j)
        (fun t => nonlinearCausalG z rho sigma p.1 p.2 t i m) r =
      causalIntervalConv (kernelVariation z rho sigma p v m j)
        (fun t => nonlinearRDFExcess z rho sigma p.1 p.2 t i m) r+
      causalIntervalConv (kernelVariation z rho sigma p v m j) (fun t => t+edgeHi sigma i m) r := by
    have hiX := (((kernel_variation_continuous z rho sigma p v m j).comp
      ((continuous_const (y := r)).sub continuous_id)).mul
      ((nonlinearRDFExcess_continuous z rho sigma p.1 p.2).matrix_elem i m)).intervalIntegrable (μ := volume) 0 r
    have hiB := (((kernel_variation_continuous z rho sigma p v m j).comp
      ((continuous_const (y := r)).sub continuous_id)).mul (continuous_id.add_const (edgeHi sigma i m))).intervalIntegrable (μ := volume) 0 r
    unfold causalIntervalConv
    rw [show (fun t : ℝ => kernelVariation z rho sigma p v m j (r-t)*nonlinearCausalG z rho sigma p.1 p.2 t i m) =
      fun t : ℝ => kernelVariation z rho sigma p v m j (r-t)*nonlinearRDFExcess z rho sigma p.1 p.2 t i m+
        kernelVariation z rho sigma p v m j (r-t)*(t+edgeHi sigma i m) by
      funext t; simp only [nonlinearCausalG, Matrix.of_apply]; ring]
    exact intervalIntegral.integral_add hiX hiB
  have h := actual_tangent_renewal z rho sigma p v i j r hr
  change causalVariation z rho sigma p v i j r = sourceVariation z rho sigma p v i j r+
    (∑ m, causalIntervalConv (fun t => nonlinearCausalKernel z rho sigma p.1 p.2 t m j)
      (causalVariation z rho sigma p v i m) r)+
    ∑ m, causalIntervalConv (kernelVariation z rho sigma p v m j)
      (fun t => nonlinearCausalG z rho sigma p.1 p.2 t i m) r at h
  simp_rw [hsplit] at h
  rw [Finset.sum_add_distrib] at h
  have hfun (a b : Fin N) : excessVariation z rho sigma p v a b = causalVariation z rho sigma p v a b :=
    funext (excessVariation_eq_causalVariation z rho sigma p v a b)
  simp only [hfun, excess_source_variation_eq_background]
  exact h.trans (by abel)

end FMSA.Convergence.ActualExcessSourceTangent

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.background_basis_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.background_basis_continuous

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.background_convolution_eq_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.background_convolution_eq_basis

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.excess_source_eq_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.excess_source_eq_basis

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.g_source_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.g_source_contDiff

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.excess_source_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.excess_source_contDiff

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.excess_source_variation_eq_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.excess_source_variation_eq_basis

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.excess_source_variation_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.excess_source_variation_continuous

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.excess_tail_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.excess_tail_contDiff

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.excess_source_variation_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.excess_source_variation_tail

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.finite_exponential_tail_weighted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.finite_exponential_tail_weighted_bound

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.matrix_weighted_bound_of_entries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.matrix_weighted_bound_of_entries

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.excess_source_variation_weighted_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.excess_source_variation_weighted_bounded

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.kernel_variation_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.kernel_variation_continuous

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.kernel_variation_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.kernel_variation_tail

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.kernel_variation_weighted_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.kernel_variation_weighted_bounded

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.background_kernel_variation_eq_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.background_kernel_variation_eq_basis

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.excess_source_variation_eq_background' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.excess_source_variation_eq_background

/-- info: 'FMSA.Convergence.ActualExcessSourceTangent.actual_excess_tangent_renewal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessSourceTangent.actual_excess_tangent_renewal
