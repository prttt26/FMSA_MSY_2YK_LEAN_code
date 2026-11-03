import MSAConvergence.CanonicalFirstLoss

/-! The actual finite kernel determines the scalar second BH source linearly.
Repeated rates are retained; no coefficient independence is assumed. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.ScalarKernelSource
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.ActualLaplaceJets FMSA.Convergence.ActualSourceBoundary
variable {T : Type*} [Fintype T]

abbrev Coeff (T : Type*) := BasisIndex T → ℝ

def field (z : T → ℝ) (sigma : ℝ) (c : Coeff T) (t : ℝ) : ℝ :=
  ∑ b, c b * recenteredBasis z (fun _ : Fin 1 => sigma) b 0 t

def core (z : T → ℝ) (sigma : ℝ) (c : Coeff T) (t : ℝ) : ℝ :=
  ∑ b, c b * (basisQp b*(t-sigma)+basisA b/2*(t-sigma)^2+
    basisW b*exp (-basisRate z b*t)+basisC b)

def tail (z : T → ℝ) (sigma : ℝ) (c : Coeff T) (t : ℝ) : ℝ :=
  ∑ b, c b * (basisW b*exp (-basisRate z b*t)+
    basisC b*exp (-basisRate z b*(t-sigma)))

def bridge (z : T → ℝ) (c : Coeff T) (t : ℝ) : ℝ :=
  ∑ b, c b * (basisQp b*t+basisA b/2*t^2+
    basisC b*(1-exp (-basisRate z b*t)))

def sourceNumerator (z : T → ℝ) (c : Coeff T) (t : ℝ) : ℝ :=
  ∑ b, c b * (basisQp b+basisA b*t+
    basisRate z b*basisC b*exp (-basisRate z b*t))

/-- All coefficient combinations retain a continuous actual kernel field. -/
theorem field_continuous (z : T → ℝ) (sigma : ℝ) (c : Coeff T) :
    Continuous (field z sigma c) := by
  unfold field
  exact continuous_finsetSum _ (fun b _ => continuous_const.mul (recenteredBasis_continuous _ _ _ _))

/-- On the core, the honest kernel equals its entire exponential polynomial. -/
theorem field_eq_core (z : T → ℝ) (sigma : ℝ) (c : Coeff T) (t : ℝ) (ht : t ≤ sigma) :
    field z sigma c t = core z sigma c t := by
  simp only [field,core,recenteredBasis,min_eq_left ht,max_eq_right ht,sub_self,mul_zero,
    exp_zero,mul_one]

/-- Beyond the edge, it equals the entire exponential tail polynomial. -/
theorem field_eq_tail (z : T → ℝ) (sigma : ℝ) (c : Coeff T) (t : ℝ) (ht : sigma ≤ t) :
    field z sigma c t = tail z sigma c t := by
  simp only [field,tail,recenteredBasis,min_eq_right ht,max_eq_left ht,sub_self,mul_zero,
    zero_pow (by decide : 2 ≠ 0),add_zero,zero_add]

/-- Actual core and tail analytic continuations give the source primitive. -/
theorem core_sub_tail_eq_bridge (z : T → ℝ) (sigma : ℝ) (c : Coeff T) (t : ℝ) :
    core z sigma c (sigma+t)-tail z sigma c (sigma+t) = bridge z c t := by
  unfold core tail bridge
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [show sigma+t-sigma=t by ring]
  ring

/-- The source is the genuine derivative of this primitive, at every t. -/
theorem bridge_hasDerivAt (z : T → ℝ) (c : Coeff T) (t : ℝ) :
    HasDerivAt (bridge z c) (sourceNumerator z c t) t := by
  unfold bridge sourceNumerator
  apply HasDerivAt.fun_sum
  intro b _
  have he := (Real.hasDerivAt_exp (-basisRate z b*t)).comp t
    ((hasDerivAt_id t).const_mul (-basisRate z b))
  have h := (((hasDerivAt_id t).const_mul (basisQp b)).add
    (((hasDerivAt_id t).pow 2).const_mul (basisA b/2))).add
      (((hasDerivAt_const t (1 : ℝ)).sub he).const_mul (basisC b)) |>.const_mul (c b)
  exact h.congr_deriv (by dsimp; ring)

/-- Positive core length determines both analytic continuations from a
finite compact interval, with no distinct-rate or basis-independence premise. -/
theorem core_tail_zero_of_field_zero
    (z : T → ℝ) (sigma : ℝ) (hsigma : 0 < sigma) (c : Coeff T)
    (hzero : ∀ t ∈ Icc (0 : ℝ) (2*sigma), field z sigma c t = 0) :
    (∀ t, core z sigma c t = 0) ∧ (∀ t, tail z sigma c t = 0) := by
  have hcore : ContDiff ℝ ω (core z sigma c) := by unfold core; fun_prop
  have htail : ContDiff ℝ ω (tail z sigma c) := by unfold tail; fun_prop
  have hca : AnalyticOnNhd ℝ (core z sigma c) univ := fun _ _ => hcore.contDiffAt.analyticAt
  have hta : AnalyticOnNhd ℝ (tail z sigma c) univ := fun _ _ => htail.contDiffAt.analyticAt
  have hce : core z sigma c =ᶠ[𝓝 (sigma/2)] 0 := by
    filter_upwards [Ioo_mem_nhds (by linarith : (0:ℝ)<sigma/2) (by linarith : sigma/2<sigma)] with t ht
    exact (field_eq_core z sigma c t ht.2.le).symm.trans (hzero t ⟨ht.1.le,by linarith [ht.2]⟩)
  have hte : tail z sigma c =ᶠ[𝓝 (3*sigma/2)] 0 := by
    filter_upwards [Ioo_mem_nhds (by linarith : sigma<3*sigma/2) (by linarith : 3*sigma/2<2*sigma)] with t ht
    exact (field_eq_tail z sigma c t ht.1.le).symm.trans (hzero t ⟨by linarith [ht.1],ht.2.le⟩)
  exact ⟨fun t => hca.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _) hce (mem_univ t),
    fun t => hta.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _) hte (mem_univ t)⟩

/-- A zero compact kernel forces its source to vanish EVERYWHERE, not just
at selected rates. This kills all redundant coefficient directions. -/
theorem source_zero_of_field_zero
    (z : T → ℝ) (sigma : ℝ) (hsigma : 0 < sigma) (c : Coeff T)
    (hzero : ∀ t ∈ Icc (0 : ℝ) (2*sigma), field z sigma c t = 0) :
    ∀ t, sourceNumerator z c t = 0 := by
  obtain ⟨hc,ht⟩ := core_tail_zero_of_field_zero z sigma hsigma c hzero
  have he : bridge z c = 0 := by
    funext t
    rw [← core_sub_tail_eq_bridge z sigma c t,hc,ht,sub_self]
    rfl
  intro t
  have hd := (bridge_hasDerivAt z c t).deriv
  simpa [he] using hd.symm

/-- Zero compact data in fact determine the whole nonnegative kernel. -/
theorem field_zero_of_compact_zero
    (z : T → ℝ) (sigma : ℝ) (hsigma : 0 < sigma) (c : Coeff T)
    (hzero : ∀ t ∈ Icc (0 : ℝ) (2*sigma), field z sigma c t = 0) :
    ∀ t : ℝ, 0 ≤ t → field z sigma c t = 0 := by
  obtain ⟨hc,ht⟩ := core_tail_zero_of_field_zero z sigma hsigma c hzero
  intro t _
  rcases le_total t sigma with h | h
  · exact (field_eq_core z sigma c t h).trans (hc t)
  · exact (field_eq_tail z sigma c t h).trans (ht t)

/-- Compact actual-kernel map in a genuine sup norm. -/
def compactKernel (z : T → ℝ) (sigma : ℝ) :
    Coeff T →ₗ[ℝ] C(Icc (0 : ℝ) (2*sigma),ℝ) where
  toFun c := ⟨fun t => field z sigma c t,(field_continuous z sigma c).comp continuous_subtype_val⟩
  map_add' c d := by
    ext t
    simp [field,add_mul,Finset.sum_add_distrib]
  map_smul' a c := by
    ext t
    change (∑ b, (a*c b)*recenteredBasis z (fun _ : Fin 1 => sigma) b 0 t) =
      a*∑ b, c b*recenteredBasis z (fun _ : Fin 1 => sigma) b 0 t
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Same compact kernel data give the SAME entire nonnegative actual field,
including beyond the observed compact interval. -/
theorem field_eq_of_compact_eq
    (z : T → ℝ) (sigma : ℝ) (hsigma : 0 < sigma) (c d : Coeff T)
    (heq : compactKernel z sigma c = compactKernel z sigma d) :
    ∀ t : ℝ, 0 ≤ t → field z sigma c t = field z sigma d t := by
  have hzero : ∀ t ∈ Icc (0 : ℝ) (2*sigma), field z sigma (c-d) t = 0 := by
    intro t ht
    have h := congrArg (fun f : C(Icc (0 : ℝ) (2*sigma),ℝ) => f ⟨t,ht⟩) heq
    change field z sigma c t = field z sigma d t at h
    simpa [field,sub_mul,Finset.sum_sub_distrib] using sub_eq_zero.mpr h
  intro t ht
  have h := field_zero_of_compact_zero z sigma hsigma (c-d) hzero t ht
  apply sub_eq_zero.mp
  simpa only [field,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib] using h

/-- A linear section on the FINITE actual-kernel image removes redundant
coefficient directions. Its continuity follows from finite dimension. -/
def kernelSection (z : T → ℝ) (sigma : ℝ) :
    (compactKernel z sigma).range →L[ℝ] Coeff T :=
  (Classical.choose ((compactKernel z sigma).rangeRestrict.exists_rightInverse_of_surjective
    (compactKernel z sigma).range_rangeRestrict)).toContinuousLinearMap

/-- The section reproduces every compact actual kernel exactly. -/
theorem kernel_section_rightInverse (z : T → ℝ) (sigma : ℝ)
    (q : (compactKernel z sigma).range) :
    compactKernel z sigma (kernelSection z sigma q) = q.1 := by
  have h := LinearMap.congr_fun (Classical.choose_spec
    ((compactKernel z sigma).rangeRestrict.exists_rightInverse_of_surjective
      (compactKernel z sigma).range_rangeRestrict)) q
  exact congrArg Subtype.val h

/-- The section is bounded by the observed kernel norm, in the ORIGINAL
finite coefficient norm. -/
theorem kernel_section_norm_bound (z : T → ℝ) (sigma : ℝ)
    (q : (compactKernel z sigma).range) :
    ‖kernelSection z sigma q‖ ≤ ‖kernelSection z sigma‖*‖q.1‖ :=
  (kernelSection z sigma).le_opNorm q

/-- Chosen reduced coefficients reproduce the whole actual field, not merely
its samples or its compact restriction. -/
theorem kernel_section_full_field (z : T → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (q : (compactKernel z sigma).range) (c : Coeff T)
    (hc : compactKernel z sigma c = q.1) :
    ∀ t : ℝ, 0 ≤ t → field z sigma (kernelSection z sigma q) t = field z sigma c t :=
  field_eq_of_compact_eq z sigma hsigma _ _ ((kernel_section_rightInverse z sigma q).trans hc.symm)

/-- The actual source basis numerator, before any amplitude specialization. -/
theorem source_numerator_basis (z : T → ℝ) (c : Coeff T) (t : ℝ) :
    sourceNumerator z c t = 2*Real.pi*∑ b, c b*gSourceBasis z b t := by
  unfold sourceNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  unfold gSourceBasis
  field_simp
  ring

/-- Each source basis has an honest positively damped REAL Laplace integral. -/
theorem source_basis_real_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (s : ℝ) (hs : 0 < s) (b : BasisIndex T) :
    IntegrableOn (fun t : ℝ => exp (-s*t)*(basisQp b+basisA b*t+
      basisRate z b*basisC b*exp (-basisRate z b*t))) (Ioi 0) := by
  obtain ⟨B,_hB,hb⟩ := FMSA.Convergence.RDFExponentialOrder.gSourceBasis_affine_bound z hz b
  have hi := (real_affine_damped_integrable (gSourceBasis z b) (gSourceBasis_continuous z b) B s hb hs).const_mul (2*Real.pi)
  have he : (fun t : ℝ => exp (-s*t)*(basisQp b+basisA b*t+
      basisRate z b*basisC b*exp (-basisRate z b*t))) =
      fun t => 2*Real.pi*(exp (-s*t)*gSourceBasis z b t) := by
    funext t
    unfold gSourceBasis
    field_simp
    ring
  rw [he]
  exact hi

/-- Honest source integral as a linear functional of the finite dictionary. -/
def sourceMap (z : T → ℝ) (s : ℝ) : Coeff T →ₗ[ℝ] ℝ where
  toFun c := ∑ b, c b*(∫ t in Ioi (0 : ℝ), exp (-s*t)*(basisQp b+basisA b*t+
    basisRate z b*basisC b*exp (-basisRate z b*t)))
  map_add' c d := by simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc,RingHom.id_apply]

/-- All finite source integrals are exchanged only after integrability. -/
theorem source_map_eq_integral (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (s : ℝ) (hs : 0 < s) (c : Coeff T) :
    sourceMap z s c = ∫ t in Ioi (0 : ℝ), exp (-s*t)*sourceNumerator z c t := by
  have he : (fun t => exp (-s*t)*sourceNumerator z c t) =
      fun t => ∑ b, c b*(exp (-s*t)*(basisQp b+basisA b*t+
        basisRate z b*basisC b*exp (-basisRate z b*t))) := by
    funext t
    unfold sourceNumerator
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he,integral_finsetSum _ (fun b _ => (source_basis_real_integrable z hz s hs b).const_mul (c b))]
  simp only [sourceMap,LinearMap.coe_mk,AddHom.coe_mk,integral_const_mul]

/-- The source map kills ALL directions invisible to the actual compact
kernel, including duplicate-rate coefficient cancellations. -/
theorem source_map_zero_of_compact_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ) (hsigma : 0 < sigma)
    (s : ℝ) (hs : 0 < s) (c : Coeff T)
    (hzero : compactKernel z sigma c = 0) : sourceMap z s c = 0 := by
  have hf : ∀ t ∈ Icc (0 : ℝ) (2*sigma), field z sigma c t = 0 := by
    intro t ht
    exact congrArg (fun f : C(Icc (0 : ℝ) (2*sigma),ℝ) => f ⟨t,ht⟩) hzero
  rw [source_map_eq_integral z hz s hs c]
  simp_rw [source_zero_of_field_zero z sigma hsigma c hf,mul_zero]
  simp

/-- Same actual compact kernel gives the SAME source transform at every
positive damping, not a supplied source equality. -/
theorem source_map_eq_of_compact_eq
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ) (hsigma : 0 < sigma)
    (s : ℝ) (hs : 0 < s) (c d : Coeff T)
    (heq : compactKernel z sigma c = compactKernel z sigma d) : sourceMap z s c = sourceMap z s d := by
  have hzero : compactKernel z sigma (c-d) = 0 := by rw [map_sub,heq,sub_self]
  have h := source_map_zero_of_compact_zero z hz sigma hsigma s hs (c-d) hzero
  exact sub_eq_zero.mp (by simpa only [map_sub] using h)

/-- The actual source functional is bounded PURELY LINEARLY by the genuine
compact kernel norm. No smallness, distinct rates or field norm is assumed. -/
theorem source_map_bound_by_compact_kernel
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ) (hsigma : 0 < sigma)
    (s : ℝ) (hs : 0 < s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : Coeff T, |sourceMap z s c| ≤ B*‖compactKernel z sigma c‖ := by
  let L := (sourceMap z s).toContinuousLinearMap.comp (kernelSection z sigma)
  refine ⟨‖L‖,norm_nonneg _,?_⟩
  intro c
  let q : (compactKernel z sigma).range := ⟨compactKernel z sigma c,⟨c,rfl⟩⟩
  have he : sourceMap z s c = L q := source_map_eq_of_compact_eq z hz sigma hsigma s hs c
    (kernelSection z sigma q) (kernel_section_rightInverse z sigma q).symm
  rw [he,← Real.norm_eq_abs]
  exact L.le_opNorm q

/-- The actual BH coefficient map is identified before specializing the
honest source integral. This is an off-root equality. -/
theorem actual_source_numerator (z : T → ℝ) {N : ℕ} (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (t : ℝ) :
    sourceNumerator z (bhCoefficient z rho sigma p i j) t =
      2*Real.pi*nonlinearGSource z rho sigma p.1 p.2 t i j := by
  rw [source_numerator_basis,gSource_eq_basis]

/-- The source functional is exactly secondRHS at every actual tail rate,
without a root premise, a formal transform or a supplied source bound. -/
theorem source_map_at_actual_rate (z : T → ℝ) (hz : ∀ u, 0 < z u)
    {N : ℕ} (rho sigma : Fin N → ℝ) (p : TailMatrix T N × TailMatrix T N)
    (u : T) (i j : Fin N) :
    sourceMap z (z u) (bhCoefficient z rho sigma p i j) = secondRHS z rho sigma p.1 p.2 u i j := by
  rw [source_map_eq_integral z hz (z u) (hz u)]
  simp_rw [actual_source_numerator]
  have he : (fun t => exp (-z u*t)*(2*Real.pi*nonlinearGSource z rho sigma p.1 p.2 t i j)) =
      fun t => 2*Real.pi*(exp (-z u*t)*nonlinearGSource z rho sigma p.1 p.2 t i j) := by funext t; ring
  rw [he,integral_const_mul]
  change 2*Real.pi*realMatrixLaplace (nonlinearGSource z rho sigma p.1 p.2) (z u) i j = _
  rw [nonlinearGSource_actual_laplace z rho sigma p.1 p.2 hz (z u) (hz u)]
  rw [← FMSA.Convergence.ActualBHSecondAmplitudeRecovery.rational_J_at_rate_eq_second_rhs z hz rho sigma p u i j]
  simp only [nonlinearRationalJ,Matrix.of_apply]
  field_simp

/-- Row-density weighted compact data of the ACTUAL causal kernel. -/
def actualCompactKernel {N : ℕ} (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) : C(Icc (0 : ℝ) (2*sigma i),ℝ) :=
  compactKernel z (sigma i) (rho i • bhCoefficient z rho sigma p i j)

/-- Compact data are the honest physical kernel values, not formal samples. -/
theorem actual_compact_kernel_apply {N : ℕ} (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (t : Icc (0 : ℝ) (2*sigma i)) :
    actualCompactKernel z rho sigma p i j t = nonlinearCausalKernel z rho sigma p.1 p.2 t i j := by
  change field z (sigma i) (rho i • bhCoefficient z rho sigma p i j) t = _
  simp only [field,Pi.smul_apply,smul_eq_mul,nonlinearCausalKernel,Matrix.of_apply,
    recentered_eq_basis,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [recenteredBasis]
  ring

/-- The actual SECOND BH source has a pure linear bound by the honest
row-density weighted compact kernel. No root/curve/smallness is supplied.
Every positive-density row and all repeated tail rates are covered. -/
theorem actual_second_source_bound {N : ℕ}
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (i j : Fin N) (hsigma : 0 < sigma i) (hrho : 0 < rho i) (u : T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : TailMatrix T N × TailMatrix T N,
      |secondRHS z rho sigma p.1 p.2 u i j| ≤ B*‖actualCompactKernel z rho sigma p i j‖ := by
  obtain ⟨B,hB,hbound⟩ := source_map_bound_by_compact_kernel z hz (sigma i) hsigma (z u) (hz u)
  refine ⟨B/rho i,div_nonneg hB hrho.le,?_⟩
  intro p
  have h := hbound (rho i • bhCoefficient z rho sigma p i j)
  rw [map_smul,smul_eq_mul,source_map_at_actual_rate z hz rho sigma p u i j,
    abs_mul,abs_of_pos hrho] at h
  change rho i*|secondRHS z rho sigma p.1 p.2 u i j| ≤ B*‖actualCompactKernel z rho sigma p i j‖ at h
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hrho).mpr (by simpa only [mul_comm] using h)

/-- Honest compact kernel data vary continuously with the actual amplitudes,
in their original finite-dimensional norm. No root equation is needed. -/
theorem actual_compact_kernel_continuous {N : ℕ} (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (i j : Fin N) : Continuous (fun p : TailMatrix T N × TailMatrix T N =>
      actualCompactKernel z rho sigma p i j) := by
  have hc : Continuous (fun p : TailMatrix T N × TailMatrix T N =>
      rho i • bhCoefficient z rho sigma p i j) :=
    continuous_const.smul (continuous_pi (fun b => (bhCoefficient_contDiff z rho sigma i j b).continuous))
  exact (compactKernel z (sigma i)).continuous_of_finiteDimensional.comp hc

end FMSA.Convergence.ScalarKernelSource

/-- info: 'FMSA.Convergence.ScalarKernelSource.field_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.field_continuous

/-- info: 'FMSA.Convergence.ScalarKernelSource.field_eq_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.field_eq_core

/-- info: 'FMSA.Convergence.ScalarKernelSource.field_eq_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.field_eq_tail

/-- info: 'FMSA.Convergence.ScalarKernelSource.core_sub_tail_eq_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.core_sub_tail_eq_bridge

/-- info: 'FMSA.Convergence.ScalarKernelSource.bridge_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.bridge_hasDerivAt

/-- info: 'FMSA.Convergence.ScalarKernelSource.core_tail_zero_of_field_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.core_tail_zero_of_field_zero

/-- info: 'FMSA.Convergence.ScalarKernelSource.source_zero_of_field_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.source_zero_of_field_zero

/-- info: 'FMSA.Convergence.ScalarKernelSource.field_zero_of_compact_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.field_zero_of_compact_zero

/-- info: 'FMSA.Convergence.ScalarKernelSource.field_eq_of_compact_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.field_eq_of_compact_eq

/-- info: 'FMSA.Convergence.ScalarKernelSource.kernel_section_rightInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.kernel_section_rightInverse

/-- info: 'FMSA.Convergence.ScalarKernelSource.kernel_section_norm_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.kernel_section_norm_bound

/-- info: 'FMSA.Convergence.ScalarKernelSource.kernel_section_full_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.kernel_section_full_field

/-- info: 'FMSA.Convergence.ScalarKernelSource.source_numerator_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.source_numerator_basis

/-- info: 'FMSA.Convergence.ScalarKernelSource.source_basis_real_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.source_basis_real_integrable

/-- info: 'FMSA.Convergence.ScalarKernelSource.source_map_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.source_map_eq_integral

/-- info: 'FMSA.Convergence.ScalarKernelSource.source_map_zero_of_compact_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.source_map_zero_of_compact_zero

/-- info: 'FMSA.Convergence.ScalarKernelSource.source_map_eq_of_compact_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.source_map_eq_of_compact_eq

/-- info: 'FMSA.Convergence.ScalarKernelSource.source_map_bound_by_compact_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.source_map_bound_by_compact_kernel

/-- info: 'FMSA.Convergence.ScalarKernelSource.actual_source_numerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.actual_source_numerator

/-- info: 'FMSA.Convergence.ScalarKernelSource.source_map_at_actual_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.source_map_at_actual_rate

/-- info: 'FMSA.Convergence.ScalarKernelSource.actual_compact_kernel_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.actual_compact_kernel_apply

/-- info: 'FMSA.Convergence.ScalarKernelSource.actual_second_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.actual_second_source_bound

/-- info: 'FMSA.Convergence.ScalarKernelSource.actual_compact_kernel_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarKernelSource.actual_compact_kernel_continuous
