import MSAConvergence.RDFExponentialOrder

/-! Actual amplitude derivatives of global causal Laplace families.
All integral and local representation inputs are established off-root. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Convergence.ActualLaplaceJets
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.Convergence.ActualRDFTangent
open FMSA.Convergence.RDFExponentialOrder FMSA.Convergence.ComplexWronskianJets
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture

section General
variable {P I : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype I]

/-- A fixed integrable complex dictionary integrates exactly as a finite sum. -/
theorem finite_complex_integral (mu : Measure ℝ) (a : I → ℝ) (phi : I → ℝ → ℂ)
    (hi : ∀ b, Integrable (phi b) mu) :
    (∫ r, ∑ b, (a b : ℂ) * phi b r ∂mu) = ∑ b, (a b : ℂ) * ∫ r, phi b r ∂mu := by
  rw [integral_finsetSum _ (fun b _ => (hi b).const_mul _)]
  simp only [integral_const_mul]

/-- Smooth real coefficients give genuine smoothness of the whole integral. -/
theorem finite_complex_integral_contDiff (mu : Measure ℝ) (c : P → I → ℝ)
    (hc : ∀ b, ContDiff ℝ ∞ (fun a => c a b)) (phi : I → ℝ → ℂ)
    (hi : ∀ b, Integrable (phi b) mu) :
    ContDiff ℝ ∞ (fun a => ∫ r, ∑ b, (c a b : ℂ) * phi b r ∂mu) := by
  have he : (fun a => ∫ r, ∑ b, (c a b : ℂ) * phi b r ∂mu) =
      fun a => ∑ b, (c a b : ℂ) * ∫ r, phi b r ∂mu := by
    funext a
    exact finite_complex_integral mu (c a) phi hi
  rw [he]
  exact ContDiff.sum fun b _ => (complex_ofReal_contDiff _ (hc b)).mul contDiff_const

/-- Genuine Frechet differentiation commutes with a fixed finite complex
integrable dictionary, with all integrability supplied by the basis. -/
theorem finite_complex_integral_fderiv (mu : Measure ℝ) (c : P → I → ℝ)
    (hc : ∀ b, ContDiff ℝ ∞ (fun a => c a b)) (phi : I → ℝ → ℂ)
    (hi : ∀ b, Integrable (phi b) mu) (p v : P) :
    fderiv ℝ (fun a => ∫ r, ∑ b, (c a b : ℂ) * phi b r ∂mu) p v =
      ∫ r, ∑ b, (fderiv ℝ (fun a => c a b) p v : ℂ) * phi b r ∂mu := by
  have he : (fun a => ∫ r, ∑ b, (c a b : ℂ) * phi b r ∂mu) =
      fun a => ∑ b, (c a b : ℂ) * ∫ r, phi b r ∂mu := by
    funext a
    exact finite_complex_integral mu (c a) phi hi
  have hd (b : I) : HasFDerivAt (fun a => (c a b : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun a => c a b) p)) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p ((hc b).differentiable (by simp) p).hasFDerivAt
  rw [he, fderiv_fun_sum (fun b _ => (hd b).differentiableAt.mul_const _),
    finite_complex_integral _ _ _ hi]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [((hd b).mul_const (∫ r, phi b r ∂mu)).fderiv]
  simp [mul_comm]
end General

/-- At most affine positive-axis growth gives an honest complex Laplace
integral at every strictly positive real part, not just at a large cutoff. -/
theorem affine_complex_laplace_integrable (f : ℝ → ℝ) (hf : Continuous f) (B : ℝ)
    (hb : ∀ r, 0 ≤ r → |f r| ≤ B * (1+r)) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun r : ℝ => (f r : ℂ) * Complex.exp (-s*r)) (Ioi 0) := by
  have hi : IntegrableOn (fun r : ℝ => B * (exp (-s.re*r) + r*exp (-s.re*r))) (Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (by linarith : -s.re < 0) 0).add
      (FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg hs)).const_mul B
  have hiw : IntegrableOn (fun r : ℝ => exp (-s.re*r) * f r) (Ioi 0) := by
    apply hi.mono' (by apply Continuous.aestronglyMeasurable; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change ‖exp (-s.re*r) * f r‖ ≤ B * (exp (-s.re*r) + r*exp (-s.re*r))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    have he := mul_le_mul_of_nonneg_left (hb r hr.le) (exp_pos (-s.re*r)).le
    nlinarith
  exact FMSA.complex_laplace_integrable f hf.continuousOn s hiw

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Every fixed source basis has a Laplace integral on the whole open right
half-plane, with its affine term controlled explicitly. -/
theorem source_basis_laplace_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (s : ℂ) (hs : 0 < s.re) (b : BasisIndex T) :
    IntegrableOn (fun r : ℝ => (gSourceBasis z b r : ℂ) * Complex.exp (-s*r)) (Ioi 0) := by
  obtain ⟨B, _, hb⟩ := gSourceBasis_affine_bound z hz b
  exact affine_complex_laplace_integrable _ (gSourceBasis_continuous z b) B hb s hs

/-- Every fixed kernel basis, including its density coefficient, has an
honest Laplace integral on the open right half-plane. -/
theorem kernel_basis_laplace_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (s : ℂ) (hs : 0 < s.re) (b : BasisIndex T) (i : Fin N) :
    IntegrableOn (fun r : ℝ => (rho i * recenteredBasis z sigma b i r : ℝ) *
      Complex.exp (-s*r)) (Ioi 0) := by
  obtain ⟨M, _, hb⟩ := recenteredBasis_bounded_positive z hz sigma hsigma b i
  apply exp_order_complex_integrable _ (by apply Continuous.aestronglyMeasurable; fun_prop)
    0 (|rho i| * M) _ s hs
  intro r hr
  simp only [neg_zero, zero_mul, exp_zero, one_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hb r hr.le) (abs_nonneg _)

/-- The actual G-source transform is a full finite coefficient expansion
at arbitrary amplitudes, without a root or budget premise. -/
theorem source_laplace_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (i j : Fin N) :
    rdfMatrixLaplace (nonlinearGSource z rho sigma p.1 p.2) s i j =
      ∫ r in Ioi (0 : ℝ), ∑ b : BasisIndex T, (bhCoefficient z rho sigma p i j b : ℂ) *
        ((gSourceBasis z b r : ℂ) * Complex.exp (-s*r)) := by
  unfold rdfMatrixLaplace FMSA.causalComplexLaplace
  simp only [Matrix.of_apply]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  rw [gSource_eq_basis z rho sigma p i j r]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_assoc]

/-- The actual causal kernel transform retains its entire fixed dictionary. -/
theorem kernel_laplace_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (i j : Fin N) :
    rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j =
      ∫ r in Ioi (0 : ℝ), ∑ b : BasisIndex T, (bhCoefficient z rho sigma p i j b : ℂ) *
        ((rho i * recenteredBasis z sigma b i r : ℝ) * Complex.exp (-s*r)) := by
  unfold rdfMatrixLaplace FMSA.causalComplexLaplace
  simp only [nonlinearCausalKernel, Matrix.of_apply, recentered_eq_basis]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  simp only [Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The actual global G-source Laplace family is amplitude-smooth off-root. -/
theorem source_laplace_contDiff (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (s : ℂ) (hs : 0 < s.re) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearGSource z rho sigma a.1 a.2) s i j) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearGSource z rho sigma a.1 a.2) s i j) =
      fun a => ∫ r in Ioi (0 : ℝ), ∑ b : BasisIndex T, (bhCoefficient z rho sigma a i j b : ℂ) *
        ((gSourceBasis z b r : ℂ) * Complex.exp (-s*r)) := by
    funext a
    exact source_laplace_basis z rho sigma a s i j
  rw [he]
  exact finite_complex_integral_contDiff _ _ (bhCoefficient_contDiff z rho sigma i j) _
    (source_basis_laplace_integrable z hz s hs)

/-- The actual causal-kernel Laplace family is amplitude-smooth off-root. -/
theorem kernel_laplace_contDiff (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (s : ℂ) (hs : 0 < s.re) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s i j) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s i j) =
      fun a => ∫ r in Ioi (0 : ℝ), ∑ b : BasisIndex T, (bhCoefficient z rho sigma a i j b : ℂ) *
        ((rho i * recenteredBasis z sigma b i r : ℝ) * Complex.exp (-s*r)) := by
    funext a
    exact kernel_laplace_basis z rho sigma a s i j
  rw [he]
  exact finite_complex_integral_contDiff _ _ (bhCoefficient_contDiff z rho sigma i j) _
    (fun b => kernel_basis_laplace_integrable z hz rho sigma hsigma s hs b i)

/-- The genuine G-source variation commutes with the full Laplace integral. -/
theorem sourceVariation_laplace (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : 0 < s.re) (i j : Fin N) :
    rdfMatrixLaplace (fun r => Matrix.of (fun a b => sourceVariation z rho sigma p v a b r)) s i j =
      fderiv ℝ (fun a => rdfMatrixLaplace (nonlinearGSource z rho sigma a.1 a.2) s i j) p v := by
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearGSource z rho sigma a.1 a.2) s i j) =
      fun a => ∫ r in Ioi (0 : ℝ), ∑ b : BasisIndex T, (bhCoefficient z rho sigma a i j b : ℂ) *
        ((gSourceBasis z b r : ℂ) * Complex.exp (-s*r)) := by
    funext a
    exact source_laplace_basis z rho sigma a s i j
  rw [he, finite_complex_integral_fderiv _ _ (bhCoefficient_contDiff z rho sigma i j) _
    (source_basis_laplace_integrable z hz s hs) p v]
  unfold rdfMatrixLaplace FMSA.causalComplexLaplace
  simp only [Matrix.of_apply]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  rw [sourceVariation_eq_basis z rho sigma p v i j r]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_assoc]

/-- The genuine kernel variation commutes with the full Laplace integral. -/
theorem kernelVariation_laplace (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : 0 < s.re) (i j : Fin N) :
    rdfMatrixLaplace (fun r => Matrix.of (fun a b => kernelVariation z rho sigma p v a b r)) s i j =
      fderiv ℝ (fun a => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s i j) p v := by
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s i j) =
      fun a => ∫ r in Ioi (0 : ℝ), ∑ b : BasisIndex T, (bhCoefficient z rho sigma a i j b : ℂ) *
        ((rho i * recenteredBasis z sigma b i r : ℝ) * Complex.exp (-s*r)) := by
    funext a
    exact kernel_laplace_basis z rho sigma a s i j
  rw [he, finite_complex_integral_fderiv _ _ (bhCoefficient_contDiff z rho sigma i j) _
    (fun b => kernel_basis_laplace_integrable z hz rho sigma hsigma s hs b i) p v]
  unfold rdfMatrixLaplace FMSA.causalComplexLaplace
  simp only [Matrix.of_apply]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  rw [kernelVariation_eq_basis z rho sigma p v i j r]
  simp only [Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Uniform coefficient envelopes in a finite dictionary give one fixed
growth constant for every coefficient array in that envelope. -/
theorem matrix_dictionary_uniform_bound {B : Type*} [Fintype B]
    (A : Fin N → Fin N → B → ℝ) (hA : ∀ i j b, 0 ≤ A i j b)
    (phi : B → Fin N → ℝ → ℝ) (g : ℝ → ℝ)
    (hphi : ∀ b i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, 0 ≤ r → |phi b i r| ≤ M * g r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : Fin N → Fin N → B → ℝ,
      (∀ i j b, |c i j b| ≤ A i j b) → ∀ r, 0 ≤ r →
      FMSA.matrixAbsSum (Matrix.of (fun i j => ∑ b, c i j b * phi b i r)) ≤ M * g r := by
  obtain ⟨M, hM, hb⟩ := matrix_dictionary_bound A (fun b i r => |phi b i r|) g
    (fun b i => by simpa only [abs_abs] using hphi b i)
  refine ⟨M, hM, ?_⟩
  intro c hc r hr
  apply le_trans _ (hb r hr)
  simp only [FMSA.matrixAbsSum, Matrix.of_apply]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [abs_of_nonneg (Finset.sum_nonneg (fun b _ => mul_nonneg (hA i j b) (abs_nonneg _)))]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hc i j b) (abs_nonneg _)

/-- All actual finite amplitude coefficients share one bounded envelope on
a neighbourhood of any fixed amplitude point, from genuine smoothness. -/
theorem coefficients_locally_bounded (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ a in 𝓝 p, ∀ i j b, |bhCoefficient z rho sigma a i j b| ≤ L := by
  let c : (TailMatrix T N × TailMatrix T N) → Fin N → Fin N → BasisIndex T → ℝ :=
    fun a i j b => bhCoefficient z rho sigma a i j b
  have hc : Continuous c := continuous_pi fun i => continuous_pi fun j => continuous_pi fun b =>
    (bhCoefficient_contDiff z rho sigma i j b).continuous
  refine ⟨‖c p‖+1, by positivity, ?_⟩
  have hn : ∀ᶠ a in 𝓝 p, ‖c a‖ < ‖c p‖+1 :=
    hc.norm.continuousAt.eventually (gt_mem_nhds (by linarith : ‖c p‖ < ‖c p‖+1))
  filter_upwards [hn] with a ha
  intro i j b
  exact ((norm_le_pi_norm (c a i j) b).trans
    ((norm_le_pi_norm (c a i) j).trans (norm_le_pi_norm (c a) i))).trans ha.le

/-- The actual kernel/source dictionaries give one global bound on a
parameter neighbourhood, before solving the actual renewal. -/
theorem actual_kernel_source_local_bounds (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ ∀ᶠ a in 𝓝 p, ∀ r, 0 ≤ r →
      FMSA.matrixAbsSum (nonlinearCausalKernel z rho sigma a.1 a.2 r) ≤ M ∧
      FMSA.matrixAbsSum (nonlinearGSource z rho sigma a.1 a.2 r) ≤ C * (1+r) := by
  obtain ⟨L, hL, hc⟩ := coefficients_locally_bounded z rho sigma p
  obtain ⟨M, hM, hk⟩ := matrix_dictionary_uniform_bound
    (fun i _ _ => |rho i| * L) (fun i _ _ => mul_nonneg (abs_nonneg _) hL)
    (recenteredBasis z sigma) (fun _ => (1 : ℝ))
    (fun b i => by simpa only [mul_one] using recenteredBasis_bounded_positive z hz sigma hsigma b i)
  obtain ⟨C, hC, hf⟩ := matrix_dictionary_uniform_bound (fun _ _ _ => L) (fun _ _ _ => hL)
    (fun b (_ : Fin N) => gSourceBasis z b) (fun r => 1+r)
    (fun b _ => gSourceBasis_affine_bound z hz b)
  refine ⟨M, C, hM, hC, ?_⟩
  filter_upwards [hc] with a ha
  intro r hr
  constructor
  · have hb := hk (fun i j b => rho i * bhCoefficient z rho sigma a i j b)
      (fun i j b => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (ha i j b) (abs_nonneg _)) r hr
    simpa only [mul_one, nonlinearCausalKernel, recentered_eq_basis, Finset.mul_sum, mul_assoc] using hb
  · have he : nonlinearGSource z rho sigma a.1 a.2 r =
        Matrix.of (fun i j => ∑ b : BasisIndex T, bhCoefficient z rho sigma a i j b * gSourceBasis z b r) := by
      ext i j
      exact gSource_eq_basis z rho sigma a i j r
    rw [he]
    exact hf (bhCoefficient z rho sigma a) ha r hr

/-- The actual base G family has one global exponential-order bound
throughout a neighbourhood of any amplitude point, with no root premise. -/
theorem actual_causal_local_exponential_order (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) :
    ∃ gamma B : ℝ, 0 < gamma ∧ 0 ≤ B ∧ ∀ᶠ a in 𝓝 p, ∀ r, 0 ≤ r →
      exp (-gamma*r) * FMSA.matrixAbsSum (nonlinearCausalG z rho sigma a.1 a.2 r) ≤ B := by
  obtain ⟨M, C, hM, hC, hb⟩ := actual_kernel_source_local_bounds z hz rho sigma hsigma p
  refine ⟨M+1, C*(M+1), by linarith, by positivity, ?_⟩
  filter_upwards [hb] with a ha
  have hq : Continuous (fun r => (nonlinearCausalKernel z rho sigma a.1 a.2 r).transpose) :=
    continuous_matrix fun i j => (nonlinearCausalKernel_continuous z rho sigma a.1 a.2).matrix_elem j i
  have hy : Continuous (fun r => (nonlinearCausalG z rho sigma a.1 a.2 r).transpose) :=
    continuous_matrix fun i j => (nonlinearCausalG_continuous z rho sigma a.1 a.2).matrix_elem j i
  have h := matrix_renewal_exponential_order
    (fun r => (nonlinearCausalKernel z rho sigma a.1 a.2 r).transpose)
    (fun r => (nonlinearGSource z rho sigma a.1 a.2 r).transpose)
    (fun r => (nonlinearCausalG z rho sigma a.1 a.2 r).transpose) hq hy M C hM hC
    (fun r hr => by simpa only [FMSA.matrixAbsSum_transpose] using (ha r hr).1)
    (fun r hr => by simpa only [FMSA.matrixAbsSum_transpose] using (ha r hr).2)
    (fun i j r hr => by simpa only [Matrix.transpose_apply, mul_comm] using
      nonlinearCausalG_renewal z rho sigma a.1 a.2 j i r hr)
  simpa only [FMSA.matrixAbsSum_transpose] using h

section MatrixRegularity
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Determinant smoothness is proved from its finite permutation expansion,
without changing the norm on the actual amplitude space. -/
theorem matrix_det_contDiffAt (A : P → Matrix (Fin N) (Fin N) ℂ) (p : P)
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun a => A a i j) p) :
    ContDiffAt ℝ ∞ (fun a => (A a).det) p := by
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun s _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hA (s i) i)

/-- The actual nonsingular matrix inverse is entrywise smooth at a unit,
proved via the scalar reciprocal determinant and finite adjugate formula. -/
theorem matrix_inv_entry_contDiffAt (A : P → Matrix (Fin N) (Fin N) ℂ) (p : P)
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun a => A a i j) p) (hu : IsUnit (A p)) (i j : Fin N) :
    ContDiffAt ℝ ∞ (fun a => (A a)⁻¹ i j) p := by
  have hd : (A p).det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hdet := matrix_det_contDiffAt A p hA
  have hadj : ContDiffAt ℝ ∞ (fun a => (A a).adjugate i j) p := by
    simp only [Matrix.adjugate_apply]
    apply matrix_det_contDiffAt
    intro k l
    by_cases hk : k = j
    · subst k
      simp only [Matrix.updateRow_self]
      exact contDiffAt_const (c := ((Pi.single i (1 : ℂ) : Fin N → ℂ) l))
    · simpa only [Matrix.updateRow_ne hk] using hA k l
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact (hdet.inv hd).mul hadj
end MatrixRegularity

/-- A bounded causal matrix has a computably small Laplace norm sum far
in the right half-plane, with no physical kernel-budget assumption. -/
theorem bounded_matrix_laplace_norm_sum
    (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q) (M : ℝ)
    (hk : ∀ r, 0 ≤ r → FMSA.matrixAbsSum (q r) ≤ M) (s : ℂ) (hs : 0 < s.re) :
    (∑ i, ∑ j, ‖rdfMatrixLaplace q s i j‖) ≤ M / s.re := by
  have hc (i j : Fin N) : IntegrableOn
      (fun r : ℝ => (q r i j : ℂ) * Complex.exp (-s*r)) (Ioi 0) := by
    apply exp_order_complex_integrable _ (hq.matrix_elem i j).aestronglyMeasurable 0 M _ s hs
    intro r hr
    simpa only [neg_zero, zero_mul, exp_zero, one_mul] using
      (FMSA.matrixAbsSum_entry_le (q r) i j).trans (hk r hr.le)
  have hn (i j : Fin N) : IntegrableOn (fun r => exp (-s.re*r) * |q r i j|) (Ioi 0) := by
    change Integrable (fun r => exp (-s.re*r) * |q r i j|) (volume.restrict (Ioi 0))
    simpa only [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re,
      Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.norm_eq_abs,
      mul_comm] using (hc i j).norm
  have hi : IntegrableOn (fun r => exp (-s.re*r) * FMSA.matrixAbsSum (q r)) (Ioi 0) := by
    simp only [FMSA.matrixAbsSum, Finset.mul_sum]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hn i j))
  have hM : IntegrableOn (fun r : ℝ => M * exp (-s.re*r)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -s.re < 0) 0).const_mul M
  calc
    _ ≤ ∑ i, ∑ j, ∫ r in Ioi (0 : ℝ), exp (-s.re*r) * |q r i j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [rdfMatrixLaplace, Matrix.of_apply, FMSA.causalComplexLaplace,
        norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re,
        Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.norm_eq_abs,
        mul_comm] using norm_integral_le_integral_norm
          (fun r : ℝ => (q r i j : ℂ) * Complex.exp (-s*r)) (μ := volume.restrict (Ioi 0))
    _ = ∫ r in Ioi (0 : ℝ), exp (-s.re*r) * FMSA.matrixAbsSum (q r) := by
      simp only [FMSA.matrixAbsSum, Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hn i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hn i j)]
    _ ≤ ∫ r in Ioi (0 : ℝ), M * exp (-s.re*r) := by
      apply integral_mono_ae hi hM
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hk r hr.le) (exp_pos (-s.re*r)).le
    _ = M / s.re := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -s.re < 0)]
      simp only [mul_zero, exp_zero]
      field_simp

/-- The actual renewal factor is invertible after sufficiently strong
computed damping, independently of a canonical-state assumption. -/
theorem bounded_matrix_laplace_isUnit
    (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q) (M : ℝ)
    (hk : ∀ r, 0 ≤ r → FMSA.matrixAbsSum (q r) ≤ M) (s : ℂ)
    (hs : 0 < s.re) (hMs : M < s.re) : IsUnit (1-rdfMatrixLaplace q s) := by
  apply complex_matrix_one_sub_isUnit_of_normSum
  exact (bounded_matrix_laplace_norm_sum q hq M hk s hs).trans_lt
    ((div_lt_one hs).mpr hMs)

/-- On a parameter neighbourhood the actual whole Laplace family satisfies
its off-root renewal identity with an invertible far-right renewal factor. -/
theorem actual_local_laplace_renewal_unit
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ s : ℂ, cutoff < s.re → ∀ᶠ a in 𝓝 p,
      rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s *
        (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s) =
          rdfMatrixLaplace (nonlinearGSource z rho sigma a.1 a.2) s ∧
      IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s) := by
  obtain ⟨M, C, hM, hC, hkf⟩ := actual_kernel_source_local_bounds z hz rho sigma hsigma p
  obtain ⟨gamma, B, hg, _, hyb⟩ := actual_causal_local_exponential_order z hz rho sigma hsigma p
  refine ⟨gamma+M+2, by linarith, ?_⟩
  intro s hs
  filter_upwards [hkf, hyb] with a ha hya
  have hsr : 0 < s.re := by linarith
  have hq := nonlinearCausalKernel_continuous z rho sigma a.1 a.2
  have hf := nonlinearGSource_continuous z rho sigma a.1 a.2
  have hy := nonlinearCausalG_continuous z rho sigma a.1 a.2
  constructor
  · apply complexMatrixLaplace_right_renewal _ _ _ hq hf hy s
    · intro i j
      apply exp_order_real_integrable _ (hq.matrix_elem i j).aestronglyMeasurable 0 M s.re _ hsr
      intro r hr
      simpa only [neg_zero, zero_mul, exp_zero, one_mul] using
        (FMSA.matrixAbsSum_entry_le _ i j).trans (ha r hr.le).1
    · intro i j
      apply exp_order_real_integrable _ (hf.matrix_elem i j).aestronglyMeasurable 1 C s.re _ (by linarith)
      intro r hr
      simpa only [neg_mul, one_mul] using affine_damping_bound _ C hC
        (fun r hr => (FMSA.matrixAbsSum_entry_le _ i j).trans (ha r hr).2) r hr.le
    · intro i j
      apply exp_order_real_integrable _ (hy.matrix_elem i j).aestronglyMeasurable gamma B s.re _ (by linarith)
      intro r hr
      exact (mul_le_mul_of_nonneg_left (FMSA.matrixAbsSum_entry_le _ i j) (exp_pos _).le).trans (hya r hr.le)
    · intro i j r hr
      simpa only [causalIntervalConv, mul_comm] using nonlinearCausalG_renewal z rho sigma a.1 a.2 i j r hr
  · exact bounded_matrix_laplace_isUnit _ hq M (fun r hr => (ha r hr).1) s hsr (by linarith)

section MatrixDerivatives
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A locally valid off-root renewal and a unit factor give a genuine
smooth local representation of the entire parameter Laplace family. -/
theorem matrix_renewal_family_contDiffAt
    (q f y : P → Matrix (Fin N) (Fin N) ℂ) (p : P)
    (hq : ∀ i j, ContDiffAt ℝ ∞ (fun a => q a i j) p)
    (hf : ∀ i j, ContDiffAt ℝ ∞ (fun a => f a i j) p)
    (he : ∀ᶠ a in 𝓝 p, y a * (1-q a) = f a ∧ IsUnit (1-q a)) (i j : Fin N) :
    ContDiffAt ℝ ∞ (fun a => y a i j) p := by
  have hunit : IsUnit (1-q p) := he.self_of_nhds.2
  have hT (k l : Fin N) : ContDiffAt ℝ ∞ (fun a => (1-q a) k l) p :=
    contDiffAt_const.sub (hq k l)
  have hinv (k l : Fin N) := matrix_inv_entry_contDiffAt (fun a => 1-q a) p hT hunit k l
  have hreg : ContDiffAt ℝ ∞ (fun a => (f a * (1-q a)⁻¹) i j) p := by
    simp only [Matrix.mul_apply]
    exact ContDiffAt.sum fun k _ => (hf i k).mul (hinv k j)
  apply hreg.congr_of_eventuallyEq
  filter_upwards [he] with a ha
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp ha.2
  have hh : y a = f a * (1-q a)⁻¹ := by
    calc
      _ = (y a * (1-q a)) * (1-q a)⁻¹ := (Matrix.mul_nonsing_inv_cancel_right _ _ hd).symm
      _ = _ := by rw [ha.1]
  exact congrFun (congrFun hh i) j

/-- Entrywise Frechet differentiation of a locally valid matrix renewal
retains the two noncommutative product orders. -/
theorem matrix_renewal_family_fderiv
    (q f y : P → Matrix (Fin N) (Fin N) ℂ) (p v : P)
    (hq : ∀ i j, DifferentiableAt ℝ (fun a => q a i j) p)
    (_hf : ∀ i j, DifferentiableAt ℝ (fun a => f a i j) p)
    (hy : ∀ i j, DifferentiableAt ℝ (fun a => y a i j) p)
    (he : ∀ᶠ a in 𝓝 p, y a * (1-q a) = f a) :
    Matrix.of (fun i j => fderiv ℝ (fun a => y a i j) p v) * (1-q p) =
      Matrix.of (fun i j => fderiv ℝ (fun a => f a i j) p v) +
        y p * Matrix.of (fun i j => fderiv ℝ (fun a => q a i j) p v) := by
  have hentry (i j : Fin N) :
      fderiv ℝ (fun a => y a i j) p v -
        (∑ k, ((fderiv ℝ (fun a => y a i k) p v) * q p k j +
          y p i k * fderiv ℝ (fun a => q a k j) p v)) =
      fderiv ℝ (fun a => f a i j) p v := by
    have hscalar : (fun a => y a i j - ∑ k, y a i k * q a k j) =ᶠ[𝓝 p] fun a => f a i j := by
      filter_upwards [he] with a ha
      rw [Matrix.mul_sub, Matrix.mul_one] at ha
      have hh := congrFun (congrFun ha i) j
      simpa only [Matrix.sub_apply, Matrix.mul_apply] using hh
    have hd := (hy i j).hasFDerivAt.sub
      (HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hy i k).hasFDerivAt.mul (hq k j).hasFDerivAt))
    have hp := congrArg (fun L : P →L[ℝ] ℂ => L v)
      (hscalar.fderiv_eq.symm.trans hd.fderiv)
    simpa only [sub_apply, sum_apply, smul_apply, smul_eq_mul, add_apply, mul_comm, add_comm] using hp.symm
  rw [Matrix.mul_sub, Matrix.mul_one]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
  have hh := hentry i j
  rw [Finset.sum_add_distrib] at hh
  linear_combination hh

/-- Invertibility of the actual fixed renewal factor makes its linearized
matrix response unique; it does not assume Jacobian invertibility. -/
theorem matrix_tangent_response_unique (T A B F : Matrix (Fin N) (Fin N) ℂ)
    (hu : IsUnit T) (hA : A*T=F) (hB : B*T=F) : A=B :=
  (IsUnit.mul_left_injective hu) (hA.trans hB.symm)
end MatrixDerivatives

/-- The entire actual G Laplace family is genuinely amplitude-smooth near
any point throughout a constructed right half-plane, with no root premise. -/
theorem actual_causal_laplace_contDiffAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ s : ℂ, cutoff < s.re → ∀ i j,
      ContDiffAt ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
        rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j) p := by
  obtain ⟨cutoff, hc, he⟩ := actual_local_laplace_renewal_unit z hz rho sigma hsigma p
  refine ⟨cutoff, hc, ?_⟩
  intro s hs i j
  have hsr : 0 < s.re := hc.trans hs
  exact matrix_renewal_family_contDiffAt
    (fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s)
    (fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearGSource z rho sigma a.1 a.2) s)
    (fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s) p
    (fun k l => (kernel_laplace_contDiff z hz rho sigma hsigma s hsr k l).contDiffAt)
    (fun k l => (source_laplace_contDiff z hz rho sigma s hsr k l).contDiffAt) (he s hs) i j

/-- Genuine amplitude differentiation commutes with the whole actual causal
G Laplace transform in a constructed right half-plane. The proof uses
neighbourhood off-root representation and actual tangent integral uniqueness. -/
theorem actual_causalVariation_laplace_fderiv
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p v : TailMatrix T N × TailMatrix T N) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ s : ℂ, cutoff < s.re → ∀ i j,
      rdfMatrixLaplace (fun r => Matrix.of (fun a b => causalVariation z rho sigma p v a b r)) s i j =
        fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N =>
          rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j) p v := by
  obtain ⟨c0, hc0, hrep⟩ := actual_local_laplace_renewal_unit z hz rho sigma hsigma p
  obtain ⟨c1, hc1, hsmooth⟩ := actual_causal_laplace_contDiffAt z hz rho sigma hsigma p
  obtain ⟨c2, hc2, htan⟩ := actual_tangent_laplace_renewal z hz rho sigma hsigma p v
  refine ⟨max c0 (max c1 c2), lt_of_lt_of_le hc0 (le_max_left _ _), ?_⟩
  intro s hs i j
  have hs0 : c0 < s.re := (le_max_left _ _).trans_lt hs
  have hs1 : c1 < s.re := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hs
  have hs2 : c2 < s.re := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hs
  have hsr : 0 < s.re := hc0.trans hs0
  let q := fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s
  let f := fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearGSource z rho sigma a.1 a.2) s
  let y := fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s
  have he : ∀ᶠ a in 𝓝 p, y a * (1-q a) = f a := (hrep s hs0).mono fun _ h => h.1
  have hd := matrix_renewal_family_fderiv q f y p v
    (fun k l => (kernel_laplace_contDiff z hz rho sigma hsigma s hsr k l).differentiable (by simp) p)
    (fun k l => (source_laplace_contDiff z hz rho sigma s hsr k l).differentiable (by simp) p)
    (fun k l => (hsmooth s hs1 k l).differentiableAt (by simp)) he
  have hq : Matrix.of (fun k l => fderiv ℝ (fun a => q a k l) p v) =
      rdfMatrixLaplace (fun r => Matrix.of (fun a b => kernelVariation z rho sigma p v a b r)) s := by
    ext k l
    exact (kernelVariation_laplace z hz rho sigma hsigma p v s hsr k l).symm
  have hf : Matrix.of (fun k l => fderiv ℝ (fun a => f a k l) p v) =
      rdfMatrixLaplace (fun r => Matrix.of (fun a b => sourceVariation z rho sigma p v a b r)) s := by
    ext k l
    exact (sourceVariation_laplace z hz rho sigma p v s hsr k l).symm
  rw [hq, hf] at hd
  have hm := matrix_tangent_response_unique _ _ _ _ ((hrep s hs0).self_of_nhds.2)
    (htan s hs2) hd
  exact congrFun (congrFun hm i) j

/-- The true integrated source variation is the derivative of the existing
complex J factor, with the exact 2*pi normalization. -/
theorem sourceVariation_laplace_eq_J_fderiv
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : 0 < s.re) (i j : Fin N) :
    rdfMatrixLaplace (fun r => Matrix.of (fun a b => sourceVariation z rho sigma p v a b r)) s i j =
      fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 s i j) p v /
        (2*(π : ℂ)) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearGSource z rho sigma a.1 a.2) s i j) =
      fun a => nonlinearComplexJ z rho sigma a.1 a.2 s i j / (2*(π : ℂ)) := by
    funext a
    exact nonlinearGSource_actual_complex_laplace z rho sigma a.1 a.2 hz s hs i j
  rw [sourceVariation_laplace z hz rho sigma p v s hs i j, he]
  simp only [div_eq_mul_inv]
  rw [(((complexJ_entry_contDiff z rho sigma s i j).differentiable (by simp) p).hasFDerivAt.mul_const
    (2*(π : ℂ))⁻¹).fderiv]
  simp only [smul_apply, smul_eq_mul, mul_comm]

/-- The existing causal kernel integral has the exact rational J/L form at
all amplitudes, with the row-density and fixed contact phase retained. -/
theorem kernel_laplace_rational
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N)
    (s : ℂ) (hs : 0 < s.re) (i j : Fin N) :
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
  rw [hk, mul_left_comm s (rho i : ℂ),
    nonlinearRecenteredQ_complex_laplace_rational z rho sigma p.1 p.2 hz hsigma s
      (by intro h; subst s; simp at hs) hs.le i j]

/-- The actual integrated kernel variation equals the genuine derivative
of the rational J/L factor formula; this is an off-root differentiation. -/
theorem kernelVariation_laplace_rational
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p v : TailMatrix T N × TailMatrix T N)
    (s : ℂ) (hs : 0 < s.re) (i j : Fin N) :
    s * rdfMatrixLaplace (fun r => Matrix.of (fun a b => kernelVariation z rho sigma p v a b r)) s i j =
      (rho i : ℂ) *
        (fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexL z rho sigma a.1 a.2 s i j) p v -
          Complex.exp (-s*(sigma i : ℂ)) *
            fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 s i j) p v) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      s * rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s i j) =
      fun a => (rho i : ℂ) * (nonlinearComplexL z rho sigma a.1 a.2 s i j -
        Complex.exp (-s*(sigma i : ℂ)) * nonlinearComplexJ z rho sigma a.1 a.2 s i j) := by
    funext a
    exact kernel_laplace_rational z hz rho sigma hsigma a s hs i j
  have hl := ((kernel_laplace_contDiff z hz rho sigma hsigma s hs i j).differentiable (by simp) p).hasFDerivAt.const_mul s
  have hJ := ((complexJ_entry_contDiff z rho sigma s i j).differentiable (by simp) p).hasFDerivAt
  have hL := ((complexL_entry_contDiff z rho sigma s i j).differentiable (by simp) p).hasFDerivAt
  have hr := (hL.fun_sub (hJ.const_mul (Complex.exp (-s*(sigma i : ℂ))))).const_mul (rho i : ℂ)
  have hd := congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ => L v)
    ((congrArg (fun f : (TailMatrix T N × TailMatrix T N) → ℂ => fderiv ℝ f p) he).trans hr.fderiv)
  rw [hl.fderiv] at hd
  rw [kernelVariation_laplace z hz rho sigma hsigma p v s hs i j]
  simpa only [smul_apply, smul_eq_mul, sub_apply] using hd

/-- Finite-dimensional linearity gives a single far-right cutoff for every
amplitude direction, with actual integrability and derivative interchange.
The frequency bound depends on the amplitude point, not on the direction. -/
theorem actual_causal_laplace_fderiv_all_directions
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ s : ℂ, cutoff < s.re →
      (∀ i j, ContDiffAt ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
        rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j) p) ∧
      ∀ (v : TailMatrix T N × TailMatrix T N) (i j : Fin N),
        IntegrableOn (fun r : ℝ => (causalVariation z rho sigma p v i j r : ℂ) *
          Complex.exp (-s*r)) (Ioi 0) ∧
        rdfMatrixLaplace (fun r => Matrix.of (fun a b => causalVariation z rho sigma p v a b r)) s i j =
          fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N =>
            rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j) p v := by
  classical
  let P := TailMatrix T N × TailMatrix T N
  let b := Module.finBasis ℝ P
  obtain ⟨c0, hc0, hsmooth⟩ := actual_causal_laplace_contDiffAt z hz rho sigma hsigma p
  choose c1 hc1 hswap using fun k => actual_causalVariation_laplace_fderiv z hz rho sigma hsigma p (b k)
  choose c2 hc2 hint using fun k => actual_causal_laplace_integrable z hz rho sigma hsigma p (b k)
  let C := c0 + ∑ k, (c1 k+c2 k)
  have hn : 0 ≤ ∑ k, (c1 k+c2 k) := Finset.sum_nonneg (fun k _ => add_nonneg (hc1 k).le (hc2 k).le)
  have hbnd (k : Fin (Module.finrank ℝ P)) : c1 k+c2 k ≤ ∑ l, (c1 l+c2 l) :=
    Finset.single_le_sum (fun l _ => add_nonneg (hc1 l).le (hc2 l).le) (Finset.mem_univ k)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro s hs
  have hs0 : c0 < s.re := by dsimp [C] at hs; linarith
  have hs1 (k : Fin (Module.finrank ℝ P)) : c1 k < s.re := by
    have := hbnd k
    have := hc2 k
    dsimp [C] at hs
    linarith
  have hs2 (k : Fin (Module.finrank ℝ P)) : c2 k < s.re := by
    have := hbnd k
    have := hc1 k
    dsimp [C] at hs
    linarith
  refine ⟨hsmooth s hs0, ?_⟩
  intro v i j
  let phi : Fin (Module.finrank ℝ P) → ℝ → ℂ := fun k r =>
    (causalVariation z rho sigma p (b k) i j r : ℂ) * Complex.exp (-s*r)
  have hi (k : Fin (Module.finrank ℝ P)) : IntegrableOn (phi k) (Ioi 0) :=
    (hint k s (hs2 k) i j).2
  have hv (r : ℝ) : causalVariation z rho sigma p v i j r =
      ∑ k, (b.repr v) k * causalVariation z rho sigma p (b k) i j r := by
    have hh := congrArg (fun w : P => fderiv ℝ (fun a : P =>
      nonlinearCausalG z rho sigma a.1 a.2 r i j) p w) (b.sum_repr v)
    simpa only [causalVariation, map_sum, map_smul, smul_eq_mul] using hh.symm
  have he : (fun r : ℝ => (causalVariation z rho sigma p v i j r : ℂ) * Complex.exp (-s*r)) =
      fun r => ∑ k, ((b.repr v) k : ℂ) * phi k r := by
    funext r
    rw [hv r]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, phi, mul_assoc]
  constructor
  · rw [he]
    exact integrable_finsetSum _ (fun k _ => (hi k).const_mul _)
  · change (∫ r in Ioi (0 : ℝ), (causalVariation z rho sigma p v i j r : ℂ) * Complex.exp (-s*r)) = _
    rw [he, finite_complex_integral _ _ _ hi]
    have hder : fderiv ℝ (fun a : P =>
        rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j) p v =
        ∑ k, ((b.repr v) k : ℂ) * fderiv ℝ (fun a : P =>
          rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j) p (b k) := by
      have hh := congrArg (fun w : P => fderiv ℝ (fun a : P =>
        rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j) p w) (b.sum_repr v)
      simpa only [map_sum, map_smul, Complex.real_smul] using hh.symm
    rw [hder]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun w : ℂ => ((b.repr v) k : ℂ) * w) (hswap k s (hs1 k) i j)

end FMSA.Convergence.ActualLaplaceJets

/-- info: 'FMSA.Convergence.ActualLaplaceJets.finite_complex_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.finite_complex_integral

/-- info: 'FMSA.Convergence.ActualLaplaceJets.finite_complex_integral_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.finite_complex_integral_contDiff

/-- info: 'FMSA.Convergence.ActualLaplaceJets.finite_complex_integral_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.finite_complex_integral_fderiv

/-- info: 'FMSA.Convergence.ActualLaplaceJets.affine_complex_laplace_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.affine_complex_laplace_integrable

/-- info: 'FMSA.Convergence.ActualLaplaceJets.source_basis_laplace_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.source_basis_laplace_integrable

/-- info: 'FMSA.Convergence.ActualLaplaceJets.kernel_basis_laplace_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.kernel_basis_laplace_integrable

/-- info: 'FMSA.Convergence.ActualLaplaceJets.source_laplace_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.source_laplace_basis

/-- info: 'FMSA.Convergence.ActualLaplaceJets.kernel_laplace_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.kernel_laplace_basis

/-- info: 'FMSA.Convergence.ActualLaplaceJets.source_laplace_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.source_laplace_contDiff

/-- info: 'FMSA.Convergence.ActualLaplaceJets.kernel_laplace_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.kernel_laplace_contDiff

/-- info: 'FMSA.Convergence.ActualLaplaceJets.sourceVariation_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.sourceVariation_laplace

/-- info: 'FMSA.Convergence.ActualLaplaceJets.kernelVariation_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.kernelVariation_laplace

/-- info: 'FMSA.Convergence.ActualLaplaceJets.matrix_dictionary_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.matrix_dictionary_uniform_bound

/-- info: 'FMSA.Convergence.ActualLaplaceJets.coefficients_locally_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.coefficients_locally_bounded

/-- info: 'FMSA.Convergence.ActualLaplaceJets.actual_kernel_source_local_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.actual_kernel_source_local_bounds

/-- info: 'FMSA.Convergence.ActualLaplaceJets.actual_causal_local_exponential_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.actual_causal_local_exponential_order

/-- info: 'FMSA.Convergence.ActualLaplaceJets.matrix_det_contDiffAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.matrix_det_contDiffAt

/-- info: 'FMSA.Convergence.ActualLaplaceJets.matrix_inv_entry_contDiffAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.matrix_inv_entry_contDiffAt

/-- info: 'FMSA.Convergence.ActualLaplaceJets.bounded_matrix_laplace_norm_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.bounded_matrix_laplace_norm_sum

/-- info: 'FMSA.Convergence.ActualLaplaceJets.bounded_matrix_laplace_isUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.bounded_matrix_laplace_isUnit

/-- info: 'FMSA.Convergence.ActualLaplaceJets.actual_local_laplace_renewal_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.actual_local_laplace_renewal_unit

/-- info: 'FMSA.Convergence.ActualLaplaceJets.matrix_renewal_family_contDiffAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.matrix_renewal_family_contDiffAt

/-- info: 'FMSA.Convergence.ActualLaplaceJets.matrix_renewal_family_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.matrix_renewal_family_fderiv

/-- info: 'FMSA.Convergence.ActualLaplaceJets.matrix_tangent_response_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.matrix_tangent_response_unique

/-- info: 'FMSA.Convergence.ActualLaplaceJets.actual_causal_laplace_contDiffAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.actual_causal_laplace_contDiffAt

/-- info: 'FMSA.Convergence.ActualLaplaceJets.actual_causalVariation_laplace_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.actual_causalVariation_laplace_fderiv

/-- info: 'FMSA.Convergence.ActualLaplaceJets.sourceVariation_laplace_eq_J_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.sourceVariation_laplace_eq_J_fderiv

/-- info: 'FMSA.Convergence.ActualLaplaceJets.kernel_laplace_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.kernel_laplace_rational

/-- info: 'FMSA.Convergence.ActualLaplaceJets.kernelVariation_laplace_rational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.kernelVariation_laplace_rational

/-- info: 'FMSA.Convergence.ActualLaplaceJets.actual_causal_laplace_fderiv_all_directions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualLaplaceJets.actual_causal_laplace_fderiv_all_directions
