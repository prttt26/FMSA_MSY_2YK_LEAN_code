import MSAConvergence.HolomorphicZeroPersistence
import MSAConvergence.ActualCanonicalBranch
import MSAConvergence.CanonicalResolventAnalysis

/-! A finite continuous first loss of full actual canonicity occurs on the
Fourier axis. No Hurwitz/Rouche axiom, winding detector or sampled grid is used. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.CanonicalFirstLoss
open FMSA.Paper FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture
open FMSA.Paper.StableIntervalRadius FMSA.Paper.TaylorRoot FMSA.Paper.FoldRadius
open FMSA.MatrixQ0 FMSA.Convergence.CanonicalNeighborhood
open FMSA.Convergence.CanonicalKernelEstimates FMSA.Convergence.CanonicalResolventAnalysis
open FMSA.Convergence.ActualCanonicalBranch FMSA.Convergence.HolomorphicZeroPersistence
open FMSA.Convergence.ActualRadialTangentOZ FMSA.Convergence.ActualCanonicalKernelTangent
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The genuine finite renewal determinant, with honest Laplace integrals. -/
def renewalDet (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) : ℂ :=
  (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s).det

/-- Uniform actual coefficient-distance control gives true joint amplitude/
frequency continuity at every strictly-right frequency. -/
theorem kernel_entry_joint_continuousAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : 0 < s.re) (i j : Fin N) :
    ContinuousAt (fun x : (TailMatrix T N × TailMatrix T N) × ℂ =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma x.1.1 x.1.2) x.2 i j) (p,s) := by
  have hRe : ∀ᶠ x : (TailMatrix T N × TailMatrix T N) × ℂ in 𝓝 (p,s), 0 < x.2.re :=
    continuousAt_const.eventually_lt (Complex.continuous_re.comp continuous_snd).continuousAt hs
  have hdist : Tendsto (fun x : (TailMatrix T N × TailMatrix T N) × ℂ =>
      kernelCoefficientDistance z rho sigma x.1 p) (𝓝 (p,s)) (𝓝 0) := by
    have hc : Continuous (fun x : (TailMatrix T N × TailMatrix T N) × ℂ =>
        kernelCoefficientDistance z rho sigma x.1 p) :=
      (kernel_coefficient_distance_continuous z rho sigma p).comp continuous_fst
    simpa only [kernel_coefficient_distance_self] using hc.continuousAt.tendsto (x := (p,s))
  have hdiff : Tendsto (fun x : (TailMatrix T N × TailMatrix T N) × ℂ =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma x.1.1 x.1.2) x.2 i j-
        rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) x.2 i j) (𝓝 (p,s)) (𝓝 0) := by
    apply squeeze_zero_norm' _ hdist
    filter_upwards [hRe] with x hx
    exact (complexNormSum_entry_le _ i j).trans (kernel_laplace_difference_bound z hz rho sigma x.1 p x.2 hx.le)
  have hH : {w : ℂ | -(0 : ℝ) ≤ w.re} ∈ 𝓝 s := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    simpa only [neg_zero] using hw.le
  have hfixed := (kernel_laplace_entry_continuous_halfplane z rho sigma hsigma p 0 hz i j).continuousAt hH
  have hsnd : Tendsto (fun x : (TailMatrix T N × TailMatrix T N) × ℂ => x.2) (𝓝 (p,s)) (𝓝 s) :=
    continuous_snd.tendsto (p,s)
  have hsum := hdiff.add (hfixed.tendsto.comp hsnd)
  change Tendsto (fun x : (TailMatrix T N × TailMatrix T N) × ℂ =>
    rdfMatrixLaplace (nonlinearCausalKernel z rho sigma x.1.1 x.1.2) x.2 i j)
      (𝓝 (p,s)) (𝓝 (rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j))
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hsum

/-- The true determinant is jointly continuous in amplitudes and strictly-
right frequency, in the existing finite-entry topology. -/
theorem renewal_det_joint_continuousAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : 0 < s.re) :
    ContinuousAt (fun x : (TailMatrix T N × TailMatrix T N) × ℂ => renewalDet z rho sigma x.1 x.2) (p,s) := by
  have hM : ContinuousAt (fun x : (TailMatrix T N × TailMatrix T N) × ℂ =>
      1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma x.1.1 x.1.2) x.2) (p,s) := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact continuousAt_const.sub (kernel_entry_joint_continuousAt z hz rho sigma hsigma p s hs i j)
  have hD : Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => A.det) := continuous_id.matrix_det
  exact ContinuousAt.comp (f := fun x : (TailMatrix T N × TailMatrix T N) × ℂ =>
    1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma x.1.1 x.1.2) x.2) (x := (p,s)) hD.continuousAt hM

/-- Actual determinant holomorphy on the open right half-plane is proved
from the honest integral dictionary, not assumed from a rational definition. -/
theorem renewal_det_analytic_right (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) :
    AnalyticOnNhd ℂ (renewalDet z rho sigma p) {s : ℂ | 0 < s.re} := by
  have hd : DifferentiableOn ℂ (renewalDet z rho sigma p) {s : ℂ | 0 < s.re} := by
    intro s hs
    change 0 < s.re at hs
    have hs0 : s ≠ 0 := by intro h; simpa only [h,Complex.zero_re,lt_self_iff_false] using hs
    exact (matrix_det_frequency_differentiableAt _ s (fun i j => differentiableAt_const _ |>.sub
      (actual_kernel_frequency_differentiableAt_off_zero z rho sigma hsigma p 0 hz s (by simpa only [neg_zero] using hs) hs0 i j))).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- The actual determinant is NEVER identically zero on the right half-
plane: a fixed limit-amplitude high-frequency cutoff supplies a nonzero value. -/
theorem renewal_det_exists_nonzero_right (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) :
    ∃ s : ℂ, 0 < s.re ∧ renewalDet z rho sigma p s ≠ 0 := by
  obtain ⟨R,hR,hu⟩ := kernel_halfplane_unit_outside z rho sigma hsigma p 0 hz
  refine ⟨(R+1 : ℝ),by simpa using (show 0 < R+1 by linarith),?_⟩
  have hunit := hu ((R+1 : ℝ) : ℂ) (by simp; linarith) (by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0 < R+1 by linarith)]
    linarith)
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-- Closure of actual full canonical amplitudes has NO strictly-right
frequency zero, proved by reciprocal maximum modulus and actual joint continuity. -/
theorem canonical_closure_no_strict_right_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (hp : p ∈ closure (canonicalAmplitudes z rho sigma)) :
    ∀ s : ℂ, 0 < s.re → renewalDet z rho sigma p s ≠ 0 := by
  apply zero_free_at_closure (renewalDet z rho sigma) (canonicalAmplitudes z rho sigma) p
    {s : ℂ | 0 < s.re} (isOpen_lt continuous_const Complex.continuous_re)
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected hp
    (renewal_det_analytic_right z hz rho sigma hsigma p)
    (renewal_det_exists_nonzero_right z hz rho sigma hsigma p)
    (fun s hs => renewal_det_joint_continuousAt z hz rho sigma hsigma p s hs)
    (fun q _ => (renewal_det_analytic_right z hz rho sigma hsigma q).differentiableOn)
  intro q hq s hs
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (hq s hs.le))

/-- A noncanonical limit of actual canonical amplitudes has a true zero
on the imaginary axis. No assumption of an already known first axis zero. -/
theorem noncanonical_closure_exists_axis_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (hp : p ∈ closure (canonicalAmplitudes z rho sigma))
    (hn : p ∉ canonicalAmplitudes z rho sigma) :
    ∃ s : ℂ, s.re = 0 ∧ renewalDet z rho sigma p s = 0 := by
  obtain ⟨s,hs,hzero⟩ := (not_canonical_iff_exists_closed_right_zero z rho sigma p).mp hn
  refine ⟨s,le_antisymm ?_ hs,hzero⟩
  by_contra hpos
  exact canonical_closure_no_strict_right_zero z hz rho sigma hsigma p hp s (lt_of_not_ge hpos) hzero

/-- The actual imaginary-axis zero is an honest real physical wave number,
including zero. -/
theorem noncanonical_closure_exists_real_frequency (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (hp : p ∈ closure (canonicalAmplitudes z rho sigma))
    (hn : p ∉ canonicalAmplitudes z rho sigma) :
    ∃ k : ℝ, renewalDet z rho sigma p (Complex.I*k) = 0 := by
  obtain ⟨s,hs,hzero⟩ := noncanonical_closure_exists_axis_zero z hz rho sigma hsigma p hp hn
  refine ⟨s.im,?_⟩
  have he : Complex.I*(s.im : ℂ) = s := by apply Complex.ext <;> simp [hs]
  rw [he]
  exact hzero

/-- Any finite continuous limit of a nonempty canonical prefix belongs to
the closure of the actual canonical amplitude set. No root equation is needed. -/
theorem canonical_prefix_endpoint_mem_closure (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (tstar : ℝ) (ht : 0 < tstar)
    (hp : ContinuousOn p (Icc 0 tstar))
    (hcanon : ∀ t ∈ Ico 0 tstar, p t ∈ canonicalAmplitudes z rho sigma) :
    p tstar ∈ closure (canonicalAmplitudes z rho sigma) := by
  have hclose : tstar ∈ closure (Ico (0 : ℝ) tstar) := by
    rw [closure_Ico ht.ne]
    exact ⟨ht.le,le_rfl⟩
  letI : NeBot (𝓝[Ico (0 : ℝ) tstar] tstar) := mem_closure_iff_nhdsWithin_neBot.mp hclose
  have hT := ((hp tstar ⟨ht.le,le_rfl⟩).mono Ico_subset_Icc_self).tendsto
  apply mem_closure_of_tendsto hT
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hcanon t ht

/-- FIRST loss of full actual canonicity along a finite continuous branch
occurs on the Fourier axis. A positive prefix length is explicit. -/
theorem actual_first_loss_exists_real_frequency (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (tstar : ℝ) (ht : 0 < tstar)
    (hp : ContinuousOn p (Icc 0 tstar))
    (hcanon : ∀ t ∈ Ico 0 tstar, p t ∈ canonicalAmplitudes z rho sigma)
    (hn : p tstar ∉ canonicalAmplitudes z rho sigma) :
    ∃ k : ℝ, renewalDet z rho sigma (p tstar) (Complex.I*k) = 0 :=
  noncanonical_closure_exists_real_frequency z hz rho sigma hsigma (p tstar)
    (canonical_prefix_endpoint_mem_closure z rho sigma p tstar ht hp hcanon) hn

/-- Honest kernel renewal units and physical Baxter Fourier-factor units
are EQUIVALENT, including k=0 and zero-density species. -/
theorem kernel_unit_iff_physical_factor_unit (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hrho : ∀ i, 0 ≤ rho i) (p : TailMatrix T N × TailMatrix T N) (k : ℝ) :
    IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) (Complex.I*k)) ↔
      IsUnit (fourierFactor z rho sigma (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) k) := by
  classical
  constructor
  · exact physical_fourier_factor_unit_of_kernel_unit z rho sigma hrho p k
  · intro hphys
    let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
    let R := Matrix.diagonal (fun i => (rho i : ℂ))
    let Q := nonlinearActualFourierQ z rho sigma p.1 p.2 k
    let P := rdfPhase sigma (Complex.I*k)
    let A := 1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) (Complex.I*k)
    let F := 1-Q.transpose*R
    have hR : S*S = R := by
      rw [show S = Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) from rfl, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact_mod_cast mul_self_sqrt (hrho i)
    rw [physical_factor_eq_weighted_Q z rho sigma p k] at hphys
    change IsUnit (1-S*Q*S) at hphys
    have hswap : (1-S*Q*S).det = (1-R*Q).det := by
      rw [Matrix.det_one_sub_mul_comm (S*Q) S, ← Matrix.mul_assoc, hR]
    have hRQ : IsUnit (1-R*Q) := (Matrix.isUnit_iff_isUnit_det _).mpr (by
      rw [← hswap]
      exact (Matrix.isUnit_iff_isUnit_det _).mp hphys)
    have hF : IsUnit F := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      have he : F = (1-R*Q).transpose := by
        simp only [F, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
          R, Matrix.diagonal_transpose]
      rw [he, Matrix.det_transpose]
      exact (Matrix.isUnit_iff_isUnit_det _).mp hRQ
    have hp : IsUnit P := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      dsimp only [P, rdfPhase]
      rw [Matrix.det_diagonal]
      exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => Complex.exp_ne_zero _))
    have hphase : F*P = P*A.transpose := nonlinear_actual_recentered_factor_phase z rho sigma p.1 p.2 k
    have hprod : IsUnit (P*A.transpose) := by rw [← hphase]; exact hF.mul hp
    have hprodD : IsUnit (P.det*A.transpose.det) := by
      simpa only [Matrix.det_mul] using (Matrix.isUnit_iff_isUnit_det _).mp hprod
    have hAT : IsUnit A.transpose.det := isUnit_of_mul_isUnit_right hprodD
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simpa only [Matrix.det_transpose] using hAT

/-- A finite continuous first full-canonicity loss is a genuine physical
Fourier-factor determinant zero at SOME real wave number, possibly zero. -/
theorem actual_first_loss_physical_fourier_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (tstar : ℝ) (ht : 0 < tstar)
    (hp : ContinuousOn p (Icc 0 tstar))
    (hcanon : ∀ t ∈ Ico 0 tstar, p t ∈ canonicalAmplitudes z rho sigma)
    (hn : p tstar ∉ canonicalAmplitudes z rho sigma) :
    ∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma (p tstar).1 (p tstar).2)
      (amplitudeQp z rho sigma (p tstar).1 (p tstar).2) (W z rho (p tstar).1 (p tstar).2)
        (C z rho sigma (p tstar).1 (p tstar).2) k).det = 0 := by
  obtain ⟨k,hk⟩ := actual_first_loss_exists_real_frequency z hz rho sigma hsigma p tstar ht hp hcanon hn
  refine ⟨k,?_⟩
  by_contra hd
  have hphys := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  have hkernel := (kernel_unit_iff_physical_factor_unit z rho sigma hrho (p tstar) k).mpr hphys
  exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hkernel)) hk

/-- At a finite first loss, the physical Fourier factor vanishes and the
loss coupling is no greater than any specified nonnegative transverse fold
on the same supplied branch. Strictness is NOT inferred. -/
theorem actual_first_loss_zero_and_le_transverse_fold
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (tstar : ℝ) (ht : 0 < tstar)
    (hp : ContinuousOn p (Icc 0 tstar))
    (hcanon : ∀ t ∈ Ico 0 tstar, p t ∈ canonicalAmplitudes z rho sigma)
    (hn : p tstar ∉ canonicalAmplitudes z rho sigma)
    (f : ℝ) (hf : 0 ≤ f) (hroot : IsRoot z rho sigma (f • K) (p f).1 (p f).2)
    (htransverse : (fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (f,p f)) (1,0) ∉
      Set.range (fun w => (fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (f,p f)) (0,w))) :
    (∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma (p tstar).1 (p tstar).2)
      (amplitudeQp z rho sigma (p tstar).1 (p tstar).2) (W z rho (p tstar).1 (p tstar).2)
        (C z rho sigma (p tstar).1 (p tstar).2) k).det = 0) ∧ tstar ≤ f := by
  refine ⟨actual_first_loss_physical_fourier_zero z hz rho sigma (fun i => (hsigma i).le) hrho p tstar ht hp hcanon hn,?_⟩
  by_contra hlt
  exact (actual_transverse_root_not_canonical z hz rho sigma hsigma hrho K hK hv f (p f) hroot htransverse)
    (hcanon f ⟨hf,lt_of_not_ge hlt⟩)

/-- A continuous actual amplitude path on a connected parameter set stays
fully canonical if it starts canonical and has no Fourier-axis zero anywhere.
The entire half-plane conclusion is not inferred from one isolated axis check. -/
theorem canonical_path_of_no_axis_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (s : Set ℝ) (t0 : ℝ)
    (hs : IsPreconnected s) (ht0 : t0 ∈ s) (hp : ContinuousOn p s)
    (hseed : p t0 ∈ canonicalAmplitudes z rho sigma)
    (haxis : ∀ t ∈ s, ∀ k : ℝ, renewalDet z rho sigma (p t) (Complex.I*k) ≠ 0) :
    ∀ t ∈ s, p t ∈ canonicalAmplitudes z rho sigma := by
  letI : PreconnectedSpace s := Subtype.preconnectedSpace hs
  let A : Set s := {t | p t ∈ canonicalAmplitudes z rho sigma}
  have ho : IsOpen A := (canonical_amplitudes_isOpen z hz rho sigma hsigma).preimage hp.restrict
  have hc : IsClosed A := by
    apply isClosed_of_closure_subset
    intro t ht
    have hfreq : ∃ᶠ u : s in 𝓝 t, p u ∈ canonicalAmplitudes z rho sigma :=
      mem_closure_iff_frequently.mp ht
    have hclose : p t ∈ closure (canonicalAmplitudes z rho sigma) :=
      mem_closure_of_frequently_of_tendsto hfreq hp.restrict.continuousAt.tendsto
    change p t ∈ canonicalAmplitudes z rho sigma
    by_contra hn
    obtain ⟨k,hk⟩ := noncanonical_closure_exists_real_frequency z hz rho sigma hsigma (p t) hclose hn
    exact haxis t t.property k hk
  have hall : A = Set.univ := (show IsClopen A from ⟨hc,ho⟩).eq_univ ⟨⟨t0,ht0⟩,hseed⟩
  intro t ht
  have hm : (⟨t,ht⟩ : s) ∈ A := by rw [hall]; trivial
  exact hm

/-- The actual physical Fourier detector targets full canonicity ALONG a
continuous connected path from a canonical seed. Every real k is quantified;
a finite sign/winding sample is not substituted for that premise. -/
theorem canonical_path_of_physical_factor_units (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (s : Set ℝ) (t0 : ℝ)
    (hs : IsPreconnected s) (ht0 : t0 ∈ s) (hp : ContinuousOn p s)
    (hseed : p t0 ∈ canonicalAmplitudes z rho sigma)
    (hF : ∀ t ∈ s, ∀ k : ℝ, IsUnit
      (fourierFactor z rho sigma (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2) (W z rho (p t).1 (p t).2)
          (C z rho sigma (p t).1 (p t).2) k)) :
    ∀ t ∈ s, p t ∈ canonicalAmplitudes z rho sigma := by
  apply canonical_path_of_no_axis_zero z hz rho sigma hsigma p s t0 hs ht0 hp hseed
  intro t ht k
  have hu := (kernel_unit_iff_physical_factor_unit z rho sigma hrho (p t) k).mpr (hF t ht k)
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

/-- The actual initial coupling set is connected for every extended
endpoint, including zero and infinity. -/
theorem initial_couplings_isPreconnected (bound : ENNReal) : IsPreconnected (initialCouplings bound) := by
  have hc : Set.OrdConnected (initialCouplings bound) := by
    constructor
    intro x hx y hy t ht
    exact ⟨hx.1.trans ht.1,(ENNReal.ofReal_le_ofReal ht.2).trans_lt hy.2⟩
  exact hc.isPreconnected

/-- Actual all-wave-number physical factor units on the initial branch,
together with one full canonical seed, suffice for the EXACT Taylor-radius
criterion. A two-sided analytic germ is constructed, not assumed of p. -/
theorem exists_series_extension_of_physical_axis_units
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (bound : ENNReal) (hbound : 0 < bound)
    (hp : ContinuousOn p (initialCouplings bound))
    (hroot : ∀ t ∈ initialCouplings bound, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hseed : p 0 ∈ canonicalAmplitudes z rho sigma)
    (hF : ∀ t ∈ initialCouplings bound, ∀ k : ℝ, IsUnit
      (fourierFactor z rho sigma (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2) (W z rho (p t).1 (p t).2)
          (C z rho sigma (p t).1 (p t).2) k)) :
    ∃ e : ℝ → TailMatrix T N × TailMatrix T N,
      Set.EqOn e p (initialCouplings bound) ∧ AnalyticOnNhd ℝ e (initialCouplings bound) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (e t).1 (e t).2) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), e t ∈ canonicalAmplitudes z rho sigma) ∧
      0 < amplitudeRadius (branchCoefficients e) ∧
      (AmplitudeHasSumTo e p bound ↔ bound ≤ amplitudeRadius (branchCoefficients e)) := by
  have h0 : (0 : ℝ) ∈ initialCouplings bound := ⟨le_rfl,by simpa using hbound⟩
  have hc := canonical_path_of_physical_factor_units z hz rho sigma (fun i => (hsigma i).le) hrho p
    (initialCouplings bound) 0 (initial_couplings_isPreconnected bound) h0 hp hseed hF
  exact exists_canonical_series_extension z hz rho sigma hsigma hrho K hK hv p bound hbound hp hroot hc

end FMSA.Convergence.CanonicalFirstLoss

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.kernel_entry_joint_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.kernel_entry_joint_continuousAt

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.renewal_det_joint_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.renewal_det_joint_continuousAt

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.renewal_det_analytic_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.renewal_det_analytic_right

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.renewal_det_exists_nonzero_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.renewal_det_exists_nonzero_right

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.canonical_closure_no_strict_right_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.canonical_closure_no_strict_right_zero

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.noncanonical_closure_exists_axis_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.noncanonical_closure_exists_axis_zero

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.noncanonical_closure_exists_real_frequency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.noncanonical_closure_exists_real_frequency

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.canonical_prefix_endpoint_mem_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.canonical_prefix_endpoint_mem_closure

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.actual_first_loss_exists_real_frequency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.actual_first_loss_exists_real_frequency

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.kernel_unit_iff_physical_factor_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.kernel_unit_iff_physical_factor_unit

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.actual_first_loss_physical_fourier_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.actual_first_loss_physical_fourier_zero

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.actual_first_loss_zero_and_le_transverse_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.actual_first_loss_zero_and_le_transverse_fold

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.canonical_path_of_no_axis_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.canonical_path_of_no_axis_zero

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.canonical_path_of_physical_factor_units' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.canonical_path_of_physical_factor_units

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.initial_couplings_isPreconnected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.initial_couplings_isPreconnected

/-- info: 'FMSA.Convergence.CanonicalFirstLoss.exists_series_extension_of_physical_axis_units' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFirstLoss.exists_series_extension_of_physical_axis_units
