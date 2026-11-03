import MSAConvergence.ActualCanonicalBranch

/-! Initial full canonicity from a genuine finite HS kernel budget. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.LowDensityCanonicalSeed
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.MatrixQ0
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.ActualLaplaceJets FMSA.Convergence.ActualCanonicalBranch
open FMSA.Paper.ActualAnalyticTaylor FMSA.Paper.FoldRadius FMSA.Paper.TaylorRoot
variable {N : ℕ} {T : Type*} [Fintype T]

/-- HS polynomial coefficients in the same finite dictionary as the actual kernel. -/
theorem hs_coefficient (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (G : TailMatrix T N) (i j : Fin N) (b : BasisIndex T) :
    bhCoefficient z rho sigma (0,G) i j b =
      match b with
      | .inl a => if a = 0 then Q0phys rho sigma i j else Qppphys rho sigma j j
      | .inr _ => 0 := by
  rcases b with b | (u | u)
  · simp [bhCoefficient, coefficient]
  · simp [bhCoefficient, coefficient, W, Wt]
  · simp [bhCoefficient, coefficient, C, Ct]

/-- A real scalar density can be moved outside an actual complex Laplace integral. -/
theorem causal_laplace_real_const_mul (f : ℝ → ℝ) (c : ℝ) (s : ℂ) :
    FMSA.causalComplexLaplace (fun r => c*f r) s = (c : ℂ)*FMSA.causalComplexLaplace f s := by
  unfold FMSA.causalComplexLaplace
  simp_rw [Complex.ofReal_mul, mul_assoc]
  exact integral_const_mul _ _

/-- The actual HS kernel has only the two compact polynomial basis symbols.
No inverse, root, tail-rate restriction or value at a formal removable pole is used. -/
theorem hs_kernel_symbol (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (G : TailMatrix T N)
    (s : ℂ) (hs : 0 ≤ s.re) (i j : Fin N) :
    rdfMatrixLaplace (nonlinearCausalKernel z rho sigma 0 G) s i j =
      ((rho i*Q0phys rho sigma i j : ℝ) : ℂ)*
        FMSA.causalComplexLaplace (recenteredBasis z sigma (.inl 0) i) s +
      ((rho i*Qppphys rho sigma j j : ℝ) : ℂ)*
        FMSA.causalComplexLaplace (recenteredBasis z sigma (.inl 1) i) s := by
  rw [kernel_laplace_coefficient_sum z hz rho sigma (0,G) s hs i j]
  simp_rw [hs_coefficient, causal_laplace_real_const_mul]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.isValue, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false, Complex.ofReal_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Complex.ofReal_mul]
  ring

/-- The linear compact basis mass is exactly sigma squared over two. -/
theorem hs_linear_basis_mass (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (i : Fin N) (hsigma : 0 ≤ sigma i) :
    kernelBasisMass z (fun _ => 1) sigma (.inl 0) i = sigma i^2/2 := by
  let f : ℝ → ℝ := fun r => |recenteredBasis z sigma (.inl 0) i r|
  have hi : IntegrableOn f (Ioi 0) := by
    simpa only [one_mul] using kernel_basis_mass_integrable z hz (fun _ => 1) sigma (.inl 0) i
  have ht : (∫ r in Ioi (sigma i), f r) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    change sigma i < r at hr
    simp [f, recenteredBasis, basisQp, basisA, basisW, basisC, min_eq_right hr.le]
  have he := intervalIntegral.integral_Ioi_sub_Ioi hi hsigma
  rw [ht, sub_zero] at he
  simp only [kernelBasisMass, one_mul]
  change (∫ r in Ioi (0 : ℝ), f r) = _
  rw [he]
  have hc : (∫ r in (0 : ℝ)..sigma i, f r) = ∫ r in (0 : ℝ)..sigma i, sigma i-r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hsigma] at hr
    simp [f, recenteredBasis, basisQp, basisA, basisW, basisC, min_eq_left hr.2,
      abs_of_nonpos (sub_nonpos.mpr hr.2)]
  rw [hc]
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => sigma i*y-y^2/2) (sigma i-x) x := by
    exact (((hasDerivAt_id x).const_mul (sigma i)).sub
      (((hasDerivAt_id x).pow 2).div_const 2)).congr_deriv (by norm_num)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- The quadratic compact basis mass is exactly sigma cubed over six. -/
theorem hs_quadratic_basis_mass (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (i : Fin N) (hsigma : 0 ≤ sigma i) :
    kernelBasisMass z (fun _ => 1) sigma (.inl 1) i = sigma i^3/6 := by
  let f : ℝ → ℝ := fun r => |recenteredBasis z sigma (.inl 1) i r|
  have hi : IntegrableOn f (Ioi 0) := by
    simpa only [one_mul] using kernel_basis_mass_integrable z hz (fun _ => 1) sigma (.inl 1) i
  have ht : (∫ r in Ioi (sigma i), f r) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    change sigma i < r at hr
    simp [f, recenteredBasis, basisQp, basisA, basisW, basisC, min_eq_right hr.le]
  have he := intervalIntegral.integral_Ioi_sub_Ioi hi hsigma
  rw [ht, sub_zero] at he
  simp only [kernelBasisMass, one_mul]
  change (∫ r in Ioi (0 : ℝ), f r) = _
  rw [he]
  have hc : (∫ r in (0 : ℝ)..sigma i, f r) = ∫ r in (0 : ℝ)..sigma i, (r-sigma i)^2/2 := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hsigma] at hr
    simp [f, recenteredBasis, basisQp, basisA, basisW, basisC, min_eq_left hr.2,
      div_eq_mul_inv, mul_comm]
  rw [hc]
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => (y-sigma i)^3/6) ((x-sigma i)^2/2) x := by
    exact ((((hasDerivAt_id x).sub_const (sigma i)).pow 3).div_const 6).congr_deriv (by norm_num; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- An exact finite coefficient/L1 majorant for the actual HS kernel.
The two basis masses are independent of the density and of G. -/
def hsKernelBudget (z : T → ℝ) (rho sigma : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, (
    |rho i*Q0phys rho sigma i j| *kernelBasisMass z (fun _ => 1) sigma (.inl 0) i +
    |rho i*Qppphys rho sigma j j| *kernelBasisMass z (fun _ => 1) sigma (.inl 1) i)

/-- The L1 majorant is a finite explicit rational expression in physical data. -/
theorem hs_kernel_budget_eq (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) :
    hsKernelBudget z rho sigma = ∑ i, ∑ j, (
      |rho i*Q0phys rho sigma i j| * (sigma i^2/2) +
      |rho i*Qppphys rho sigma j j| * (sigma i^3/6)) := by
  simp only [hsKernelBudget, hs_linear_basis_mass z hz sigma _ (hsigma _),
    hs_quadratic_basis_mass z hz sigma _ (hsigma _)]

/-- One genuine budget uniformly controls EVERY closed-right-half-plane frequency. -/
theorem hs_kernel_symbol_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (G : TailMatrix T N) (s : ℂ) (hs : 0 ≤ s.re) :
    complexNormSum (rdfMatrixLaplace (nonlinearCausalKernel z rho sigma 0 G) s) ≤
      hsKernelBudget z rho sigma := by
  unfold complexNormSum hsKernelBudget
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [hs_kernel_symbol z hz rho sigma G s hs i j]
  apply (norm_add_le _ _).trans
  apply add_le_add
  all_goals rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [one_mul] using kernel_basis_laplace_uniform_bound z hz (fun _ => 1) sigma (.inl 0) i s hs
  · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [one_mul] using kernel_basis_laplace_uniform_bound z hz (fun _ => 1) sigma (.inl 1) i s hs

/-- The actual HS seed is fully canonical whenever its genuine L1 budget is below one.
The assertion includes s=0 and every zero-density species. -/
theorem hs_canonical_of_budget (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (G : TailMatrix T N)
    (hb : hsKernelBudget z rho sigma < 1) : (0,G) ∈ canonicalAmplitudes z rho sigma := by
  intro s hs
  exact complex_matrix_one_sub_isUnit_of_normSum _ ((hs_kernel_symbol_bound z hz rho sigma G s hs).trans_lt hb)

/-- Directly checkable physical-data criterion, with no remaining improper
integral or complex-frequency quantifier in the sufficient hypothesis. -/
theorem hs_canonical_of_explicit_budget (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (G : TailMatrix T N)
    (hb : (∑ i, ∑ j, (|rho i*Q0phys rho sigma i j| *(sigma i^2/2) +
      |rho i*Qppphys rho sigma j j| *(sigma i^3/6))) < 1) :
    (0,G) ∈ canonicalAmplitudes z rho sigma := by
  apply hs_canonical_of_budget z hz rho sigma G
  rwa [hs_kernel_budget_eq z hz rho sigma hsigma]

/-- The zero-Dt actual kernel is independent of the finite-tail presentation
and of the unused G amplitudes. This is equality of genuine kernels. -/
theorem hs_kernel_independent_tails {U : Type*} [Fintype U]
    (z : T → ℝ) (w : U → ℝ) (rho sigma : Fin N → ℝ)
    (G : TailMatrix T N) (H : TailMatrix U N) :
    nonlinearCausalKernel z rho sigma 0 G = nonlinearCausalKernel w rho sigma 0 H := by
  funext r i j
  simp [nonlinearCausalKernel, nonlinearRecenteredQ, W, Wt, C, Ct]

/-- The HS budget on physical diameter data is independent of all tail rates
and the number of finite tails, as is the actual initial kernel. -/
theorem hs_kernel_budget_independent_tails {U : Type*} [Fintype U]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (w : U → ℝ) (hw : ∀ u, 0 < w u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) :
    hsKernelBudget z rho sigma = hsKernelBudget w rho sigma := by
  rw [hs_kernel_budget_eq z hz rho sigma hsigma, hs_kernel_budget_eq w hw rho sigma hsigma]

omit [Fintype T] in
/-- The finite HS budget is continuous at every density with nonzero vacancy. -/
theorem hs_kernel_budget_continuousAt (z : T → ℝ) (sigma rho : Fin N → ℝ)
    (hv : vacMix rho sigma ≠ 0) : ContinuousAt (fun r => hsKernelBudget z r sigma) rho := by
  have hvac : Continuous (fun r : Fin N → ℝ => vacMix r sigma) := by
    unfold vacMix etaMix
    fun_prop
  have hxi : Continuous (fun r : Fin N → ℝ => xi2 r sigma) := by
    unfold xi2
    fun_prop
  have hQ (i j : Fin N) : ContinuousAt (fun r : Fin N → ℝ => Q0phys r sigma i j) rho := by
    have hc : ContinuousAt (fun r : Fin N → ℝ => vacMix r sigma) rho := hvac.continuousAt
    have hx : ContinuousAt (fun r : Fin N → ℝ => xi2 r sigma) rho := hxi.continuousAt
    have h4 : 4*vacMix rho sigma ≠ 0 := mul_ne_zero (by norm_num) hv
    unfold Q0phys
    fun_prop
  have hA (j : Fin N) : ContinuousAt (fun r : Fin N → ℝ => Qppphys r sigma j j) rho := by
    have hc : ContinuousAt (fun r : Fin N → ℝ => vacMix r sigma) rho := hvac.continuousAt
    have hx : ContinuousAt (fun r : Fin N → ℝ => xi2 r sigma) rho := hxi.continuousAt
    have h2 : 2*vacMix rho sigma ≠ 0 := mul_ne_zero (by norm_num) hv
    unfold Qppphys
    fun_prop
  unfold hsKernelBudget
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact (((continuousAt_apply i rho).mul (hQ i j)).abs.mul_const _).add
    (((continuousAt_apply i rho).mul (hA j)).abs.mul_const _)

omit [Fintype T] in
/-- At vacuum the true HS budget vanishes exactly, for any diameter data. -/
theorem hs_kernel_budget_zero (z : T → ℝ) (sigma : Fin N → ℝ) :
    hsKernelBudget z 0 sigma = 0 := by simp [hsKernelBudget]

/-- Full HS canonicity holds on a genuine density neighbourhood of vacuum.
The low-density condition is proved to exist rather than supplied as an axiom. -/
theorem hs_canonical_eventually_zero_density (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) :
    ∀ᶠ rho : Fin N → ℝ in 𝓝 0, ∀ G : TailMatrix T N,
      (0,G) ∈ canonicalAmplitudes z rho sigma := by
  have hv : vacMix (0 : Fin N → ℝ) sigma ≠ 0 := by simp [vacMix, etaMix]
  have h := (hs_kernel_budget_continuousAt z sigma 0 hv).eventually_lt continuousAt_const
    (by rw [hs_kernel_budget_zero]; norm_num : hsKernelBudget z 0 sigma < 1)
  filter_upwards [h] with rho hr
  exact fun G => hs_canonical_of_budget z hz rho sigma G hr

/-- An explicit nonzero radius in the ORIGINAL density norm exists. Positive
vacancy and full canonicity are both conclusions at every density in this ball. -/
theorem exists_hs_canonical_density_ball (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ rho : Fin N → ℝ, ‖rho‖ < epsilon →
      0 < vacMix rho sigma ∧ hsKernelBudget z rho sigma < 1 ∧
        ∀ G : TailMatrix T N, (0,G) ∈ canonicalAmplitudes z rho sigma := by
  have hv0 : vacMix (0 : Fin N → ℝ) sigma = 1 := by simp [vacMix, etaMix]
  have hv : Continuous (fun r : Fin N → ℝ => vacMix r sigma) := by unfold vacMix etaMix; fun_prop
  have he : ∀ᶠ r : Fin N → ℝ in 𝓝 0, 0 < vacMix r sigma :=
    continuousAt_const.eventually_lt hv.continuousAt (by rw [hv0]; norm_num : 0 < vacMix (0 : Fin N → ℝ) sigma)
  have hb := (hs_kernel_budget_continuousAt z sigma 0 (by rw [hv0]; norm_num)).eventually_lt continuousAt_const
    (by rw [hs_kernel_budget_zero]; norm_num : hsKernelBudget z 0 sigma < 1)
  obtain ⟨epsilon,hepsilon,hball⟩ := Metric.eventually_nhds_iff.mp (he.and hb)
  refine ⟨epsilon,hepsilon,?_⟩
  intro rho hrho
  have h := hball (by simpa only [dist_zero_right] using hrho)
  exact ⟨h.1,h.2,fun G => hs_canonical_of_budget z hz rho sigma G h.2⟩

/-- A physical HS seed with budget below one generates an ACTUAL two-sided
analytic canonical root germ and a positive common Taylor radius. The branch
and its local roots are constructed; K symmetry is unnecessary here. -/
theorem exists_analytic_canonical_hs_seed_of_budget
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (hv : 0 < vacMix rho sigma) (K : TailMatrix T N)
    (hb : hsKernelBudget z rho sigma < 1) :
    ∃ p : ℝ → TailMatrix T N × TailMatrix T N,
      p 0 = (0,baseSeed z rho sigma) ∧ AnalyticAt ℝ p 0 ∧
      0 < amplitudeRadius (branchCoefficients p) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), p t ∈ canonicalAmplitudes z rho sigma) := by
  obtain ⟨p,hp0,hr,ha,hR⟩ := exists_analytic_seed_positive_radius z rho sigma K hz hv hrho hsigma
  have hc := hs_canonical_of_budget z hz rho sigma (baseSeed z rho sigma) hb
  have ht : Tendsto p (𝓝 0) (𝓝 (0,baseSeed z rho sigma)) := by rw [← hp0]; exact ha.continuousAt.tendsto
  exact ⟨p,hp0,ha,hR,hr,ht.eventually
    (actual_canonicity_eventually z hz rho sigma (fun i => (hsigma i).le) _ hc)⟩

/-- For every finite positive diameter vector, sufficiently small nonnegative
densities have an actual analytic canonical HS-seeded branch. No canonical,
Jacobian-inverse or local-root premise is supplied by the caller. -/
theorem exists_low_density_analytic_canonical_hs_branch
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ rho : Fin N → ℝ,
      (∀ i, 0 ≤ rho i) → ‖rho‖ < epsilon → ∀ K : TailMatrix T N,
      ∃ p : ℝ → TailMatrix T N × TailMatrix T N,
        p 0 = (0,baseSeed z rho sigma) ∧ AnalyticAt ℝ p 0 ∧
        0 < amplitudeRadius (branchCoefficients p) ∧
        (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) ∧
        (∀ᶠ t in 𝓝 (0 : ℝ), p t ∈ canonicalAmplitudes z rho sigma) := by
  obtain ⟨epsilon,he,hball⟩ := exists_hs_canonical_density_ball z hz sigma
  refine ⟨epsilon,he,?_⟩
  intro rho hrho hr K
  have h := hball rho hr
  exact exists_analytic_canonical_hs_seed_of_budget z hz rho sigma hsigma hrho h.1 K h.2.1

/-- Every finite-dimensional analytic amplitude germ has one common
neighbourhood on which ALL its Taylor series sum to the actual amplitudes. -/
theorem analytic_amplitudes_eventually_hasSum
    (p : ℝ → TailMatrix T N × TailMatrix T N) (ha : AnalyticAt ℝ p 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j*t^n) ((p t).1 u i j)) ∧
      (∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j*t^n) ((p t).2 u i j)) := by
  obtain ⟨hD,hG⟩ := analyticAt_components p 0 ha
  apply Filter.Eventually.and
  · apply eventually_all.mpr
    intro u
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    simpa only [branchCoefficients, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul, zero_add] using
      (FMSA.Paper.AnalyticTaylor.hasFPowerSeriesAt_jet _ (hD u i j)).eventually_hasSum
  · apply eventually_all.mpr
    intro u
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    simpa only [branchCoefficients, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul, zero_add] using
      (FMSA.Paper.AnalyticTaylor.hasFPowerSeriesAt_jet _ (hG u i j)).eventually_hasSum

/-- A checked HS budget constructs an actual interval of analytic canonical
MSA roots on which all amplitude Taylor series converge TO THOSE ROOTS.
Only a local interval is claimed; its size is not the full stable interval. -/
theorem exists_convergent_canonical_hs_interval_of_budget
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (hv : 0 < vacMix rho sigma) (K : TailMatrix T N)
    (hb : hsKernelBudget z rho sigma < 1) :
    ∃ p : ℝ → TailMatrix T N × TailMatrix T N, ∃ b : ℝ,
      0 < b ∧ p 0 = (0,baseSeed z rho sigma) ∧
      0 < amplitudeRadius (branchCoefficients p) ∧ ∀ t : ℝ, |t| < b →
        AnalyticAt ℝ p t ∧ IsRoot z rho sigma (t • K) (p t).1 (p t).2 ∧
        p t ∈ canonicalAmplitudes z rho sigma ∧
        (∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j*t^n) ((p t).1 u i j)) ∧
        (∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j*t^n) ((p t).2 u i j)) := by
  obtain ⟨p,hp0,ha,hR,hr,hc⟩ := exists_analytic_canonical_hs_seed_of_budget z hz rho sigma hsigma hrho hv K hb
  have hs := analytic_amplitudes_eventually_hasSum p ha
  have he := ha.eventually_analyticAt.and (hr.and (hc.and hs))
  obtain ⟨b,hb,hball⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨p,b,hb,hp0,hR,fun t ht => hball (by simpa only [Real.dist_eq,sub_zero] using ht)⟩

end FMSA.Convergence.LowDensityCanonicalSeed

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_coefficient

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.causal_laplace_real_const_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.causal_laplace_real_const_mul

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_symbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_symbol

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_linear_basis_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_linear_basis_mass

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_quadratic_basis_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_quadratic_basis_mass

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_budget_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_budget_eq

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_symbol_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_symbol_bound

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_canonical_of_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_canonical_of_budget

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_canonical_of_explicit_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_canonical_of_explicit_budget

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_independent_tails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_independent_tails

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_budget_independent_tails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_budget_independent_tails

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_budget_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_budget_continuousAt

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_budget_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_kernel_budget_zero

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.hs_canonical_eventually_zero_density' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.hs_canonical_eventually_zero_density

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.exists_hs_canonical_density_ball' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.exists_hs_canonical_density_ball

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.exists_analytic_canonical_hs_seed_of_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.exists_analytic_canonical_hs_seed_of_budget

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.exists_low_density_analytic_canonical_hs_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.exists_low_density_analytic_canonical_hs_branch

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.analytic_amplitudes_eventually_hasSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.analytic_amplitudes_eventually_hasSum

/-- info: 'FMSA.Convergence.LowDensityCanonicalSeed.exists_convergent_canonical_hs_interval_of_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.LowDensityCanonicalSeed.exists_convergent_canonical_hs_interval_of_budget
