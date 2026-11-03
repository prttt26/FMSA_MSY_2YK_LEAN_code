import MSAConvergence.ActualTracerAmplitudeRecovery
import MSAConvergence.CanonicalNeighborhood
import FMSAPaper.StableIntervalRadius
import FMSAPaper.RegularContinuation

/-! Actual canonical-root local analytic branches, continuation uniqueness
and correct initial-interval Taylor-radius criteria. -/
noncomputable section
open Filter Topology Set
open scoped ContDiff BigOperators
namespace FMSA.Convergence.ActualCanonicalBranch
open FMSA.Paper FMSA.Paper.JacobianExterior FMSA.MatrixQ0
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.BSource
open FMSA.Convergence.ActualTracerAmplitudeRecovery FMSA.Convergence.CanonicalNeighborhood
open FMSA.Paper.ActualAnalyticBranch FMSA.Paper.ActualAnalyticTaylor
open FMSA.Paper.StableIntervalRadius FMSA.Paper.TaylorRoot FMSA.Paper.FoldRadius
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Every continuous actual root germ through a canonical root is analytic;
its actual Jacobian inverse is internally discharged. -/
theorem actual_canonical_root_analyticAt
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (t0 : ℝ)
    (hp : ContinuousAt p t0)
    (hroot : ∀ᶠ t in 𝓝 t0, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : p t0 ∈ canonicalAmplitudes z rho sigma) : AnalyticAt ℝ p t0 := by
  exact actual_regular_root_analyticAt z rho sigma K p t0 hp hroot
    (actual_residual_partial_isInvertible z hz rho sigma hsigma hrho K hK t0 (p t0) hv hroot.self_of_nhds hcanon)

/-- Any actual canonical root generates a true two-sided local analytic
canonical root branch. Nearby roots AND canonicity are constructed. -/
theorem exists_analytic_canonical_root
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (t0 : ℝ) (a : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t0 • K) a.1 a.2)
    (hcanon : a ∈ canonicalAmplitudes z rho sigma) :
    ∃ p : ℝ → TailMatrix T N × TailMatrix T N,
      p t0 = a ∧ AnalyticAt ℝ p t0 ∧
      (∀ᶠ t in 𝓝 t0, IsRoot z rho sigma (t • K) (p t).1 (p t).2) ∧
      (∀ᶠ t in 𝓝 t0, p t ∈ canonicalAmplitudes z rho sigma) := by
  let R := FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K
  have hc : ContDiffAt ℝ ω R (t0,a) := (residual_analyticAt z rho sigma K (t0,a)).contDiffAt
  have hi := actual_residual_partial_isInvertible z hz rho sigma hsigma hrho K hK t0 a hv hroot hcanon
  let p := hc.implicitFunction (by simp) hi
  have hp0 : p t0 = a := hc.implicitFunction_apply_self (by simp) hi
  have ha : AnalyticAt ℝ p t0 := (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  have hR0 : R (t0,a) = 0 := (residual_eq_zero_iff z rho sigma K a.1 a.2 t0).mpr hroot
  have hr : ∀ᶠ t in 𝓝 t0, IsRoot z rho sigma (t • K) (p t).1 (p t).2 := by
    filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with t ht
    exact (residual_eq_zero_iff z rho sigma K (p t).1 (p t).2 t).mp (ht.trans hR0)
  have ht : Tendsto p (𝓝 t0) (𝓝 a) := by rw [← hp0]; exact ha.continuousAt.tendsto
  exact ⟨p,hp0,ha,hr,ht.eventually (actual_canonicity_eventually z hz rho sigma (fun i => (hsigma i).le) a hcanon)⟩

/-- Actual root uniqueness also holds for relative germs, including a
one-sided germ at an endpoint. No inverse or canonicity of the second germ is supplied. -/
theorem canonical_root_germs_eventuallyEqWithin
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p q : ℝ → TailMatrix T N × TailMatrix T N) (s : Set ℝ) (t0 : ℝ)
    (hp : ContinuousWithinAt p s t0) (hq : ContinuousWithinAt q s t0)
    (heq : p t0 = q t0) (hbase : IsRoot z rho sigma (t0 • K) (p t0).1 (p t0).2)
    (hpr : ∀ᶠ t in 𝓝[s] t0, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hqr : ∀ᶠ t in 𝓝[s] t0, IsRoot z rho sigma (t • K) (q t).1 (q t).2)
    (hcanon : p t0 ∈ canonicalAmplitudes z rho sigma) : p =ᶠ[𝓝[s] t0] q := by
  let R := FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K
  have hc : ContDiffAt ℝ ∞ R (t0,p t0) := (residual_contDiff z rho sigma K).contDiffAt
  have hi := actual_residual_partial_isInvertible z hz rho sigma hsigma hrho K hK t0 (p t0) hv hbase hcanon
  have htP : Tendsto (fun t => (t,p t)) (𝓝[s] t0) (𝓝 (t0,p t0)) := (continuousWithinAt_id.prodMk hp).tendsto
  have htQ : Tendsto (fun t => (t,q t)) (𝓝[s] t0) (𝓝 (t0,p t0)) := by
    simpa only [heq, id_eq] using (continuousWithinAt_id.prodMk hq).tendsto
  have hu := hc.eventually_apply_eq_iff_implicitFunction (by simp) hi
  have hR0 : R (t0,p t0) = 0 := (residual_eq_zero_iff _ _ _ _ _ _ _).mpr hbase
  filter_upwards [htP.eventually hu,htQ.eventually hu,hpr,hqr] with t hP hQ hPr hQr
  exact (hP.mp (((residual_eq_zero_iff _ _ _ _ _ _ _).mpr hPr).trans hR0.symm)).symm.trans
    (hQ.mp (((residual_eq_zero_iff _ _ _ _ _ _ _).mpr hQr).trans hR0.symm))

/-- Every relative actual root germ with a canonical base extends locally
to a TWO-SIDED analytic canonical root germ. -/
theorem exists_analytic_extension_of_relative_root
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (s : Set ℝ) (t0 : ℝ)
    (hp : ContinuousWithinAt p s t0)
    (hbase : IsRoot z rho sigma (t0 • K) (p t0).1 (p t0).2)
    (hpr : ∀ᶠ t in 𝓝[s] t0, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : p t0 ∈ canonicalAmplitudes z rho sigma) :
    ∃ q : ℝ → TailMatrix T N × TailMatrix T N,
      q t0 = p t0 ∧ AnalyticAt ℝ q t0 ∧
      (∀ᶠ t in 𝓝 t0, IsRoot z rho sigma (t • K) (q t).1 (q t).2) ∧
      (∀ᶠ t in 𝓝 t0, q t ∈ canonicalAmplitudes z rho sigma) ∧ p =ᶠ[𝓝[s] t0] q := by
  obtain ⟨q,hq0,hqa,hqr,hqc⟩ := exists_analytic_canonical_root z hz rho sigma hsigma hrho K hK hv t0 (p t0) hbase hcanon
  have he := canonical_root_germs_eventuallyEqWithin z hz rho sigma hsigma hrho K hK hv p q s t0 hp hqa.continuousAt.continuousWithinAt
    hq0.symm hbase hpr (hqr.filter_mono nhdsWithin_le_nhds) hcanon
  exact ⟨q,hq0,hqa,hqr,hqc,he⟩

/-- A connected continuous actual root branch agreeing with a canonical
branch once agrees everywhere; the second branch need not be canonical. -/
theorem actual_canonical_roots_eqOn_of_preconnected
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p q : ℝ → TailMatrix T N × TailMatrix T N) (s : Set ℝ) (t0 : ℝ)
    (hs : IsPreconnected s) (ht0 : t0 ∈ s) (hp : ContinuousOn p s) (hq : ContinuousOn q s)
    (heq : p t0 = q t0)
    (hpr : ∀ t ∈ s, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hqr : ∀ t ∈ s, IsRoot z rho sigma (t • K) (q t).1 (q t).2)
    (hcanon : ∀ t ∈ s, p t ∈ canonicalAmplitudes z rho sigma) : Set.EqOn p q s := by
  apply RegularContinuation.roots_eqOn_of_preconnected
    (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) p q s t0 hs ht0 hp hq heq
    (fun t ht => (residual_eq_zero_iff _ _ _ _ _ _ _).mpr (hpr t ht))
    (fun t ht => (residual_eq_zero_iff _ _ _ _ _ _ _).mpr (hqr t ht))
    (fun t ht => (residual_contDiff z rho sigma K).contDiffAt)
  exact fun t ht => actual_residual_partial_isInvertible z hz rho sigma hsigma hrho K hK t (p t) hv (hpr t ht) (hcanon t ht)

/-- Canonical regularity before an endpoint matches both continuous limiting
roots, without assuming canonicity or uniqueness at the endpoint itself. -/
theorem actual_canonical_roots_eq_at_endpoint
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p q : ℝ → TailMatrix T N × TailMatrix T N) (f : ℝ) (hf : 0 < f)
    (hp : ContinuousOn p (Icc 0 f)) (hq : ContinuousOn q (Icc 0 f)) (heq : p 0 = q 0)
    (hpr : ∀ t ∈ Ico 0 f, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hqr : ∀ t ∈ Ico 0 f, IsRoot z rho sigma (t • K) (q t).1 (q t).2)
    (hcanon : ∀ t ∈ Ico 0 f, p t ∈ canonicalAmplitudes z rho sigma) : p f = q f := by
  apply RegularContinuation.roots_eq_at_endpoint
    (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) p q f hf hp hq heq
    (fun t ht => (residual_eq_zero_iff _ _ _ _ _ _ _).mpr (hpr t ht))
    (fun t ht => (residual_eq_zero_iff _ _ _ _ _ _ _).mpr (hqr t ht))
    (fun t ht => (residual_contDiff z rho sigma K).contDiffAt)
  exact fun t ht => actual_residual_partial_isInvertible z hz rho sigma hsigma hrho K hK t (p t) hv (hpr t ht) (hcanon t ht)

/-- Genuine canonical-root hypotheses replace the supplied Jacobian inverse
in the full extended-endpoint initial-interval analytic criterion. -/
theorem actual_canonical_branch_analytic_before
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (bound : ENNReal)
    (hp0 : ContinuousAt p 0) (hp : ContinuousOn p (initialCouplings bound))
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hroot : ∀ t ∈ initialCouplings bound, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ initialCouplings bound, p t ∈ canonicalAmplitudes z rho sigma) :
    AnalyticOnNhd ℝ p (initialCouplings bound) := by
  apply actual_regular_branch_analytic_before z rho sigma K p bound hp0 hp hlocal hroot
  exact fun t ht => actual_residual_partial_isInvertible z hz rho sigma hsigma hrho K hK t (p t) hv (hroot t ht) (hcanon t ht)

/-- Correct actual canonical-branch convergence criterion. Full canonicity
alone does not imply the required complex Taylor-radius lower bound. -/
theorem actual_canonical_branch_converges_before_iff
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (bound : ENNReal)
    (hp0 : ContinuousAt p 0) (hp : ContinuousOn p (initialCouplings bound))
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hroot : ∀ t ∈ initialCouplings bound, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ initialCouplings bound, p t ∈ canonicalAmplitudes z rho sigma) :
    AmplitudeHasSumBefore p bound ↔ bound ≤ amplitudeRadius (branchCoefficients p) :=
  analytic_branch_converges_before_iff p bound
    (actual_canonical_branch_analytic_before z hz rho sigma hsigma hrho K hK hv p bound hp0 hp hlocal hroot hcanon)

/-- Infinite initial interval requires an ENTIRE common Taylor germ. -/
theorem actual_canonical_branch_entire_iff
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp0 : ContinuousAt p 0) (hp : ContinuousOn p (initialCouplings ⊤))
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hroot : ∀ t ∈ initialCouplings ⊤, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ initialCouplings ⊤, p t ∈ canonicalAmplitudes z rho sigma) :
    AmplitudeHasSumBefore p ⊤ ↔ amplitudeRadius (branchCoefficients p) = ⊤ := by
  simpa only [top_le_iff] using actual_canonical_branch_converges_before_iff z hz rho sigma hsigma hrho K hK hv p ⊤ hp0 hp hlocal hroot hcanon

/-- A canonical actual root cannot satisfy the frozen transverse-fold
obstruction: its parameter derivative lies in the amplitude derivative range. -/
theorem actual_canonical_root_parameter_derivative_in_range
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2) (hcanon : p ∈ canonicalAmplitudes z rho sigma) :
    (fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (t,p)) (1,0) ∈
      Set.range (fun w => (fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (t,p)) (0,w)) := by
  obtain ⟨w,hw⟩ := (actual_amplitude_jacobian_bijective z hz rho sigma hsigma hrho K hK t p hv hroot hcanon).2
    ((fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (t,p)) (1,0))
  exact ⟨w,hw⟩

/-- Any genuine real transverse BH fold root fails full canonicity. -/
theorem actual_transverse_root_not_canonical
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (htransverse : (fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (t,p)) (1,0) ∉
      Set.range (fun w => (fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (t,p)) (0,w))) :
    p ∉ canonicalAmplitudes z rho sigma := by
  intro hc
  exact htransverse (actual_canonical_root_parameter_derivative_in_range z hz rho sigma hsigma hrho K hK hv t p hroot hc)

/-- Failure of actual full canonicity means an actual determinant zero in
the closed right half-plane, not necessarily a Fourier-axis zero. -/
theorem not_canonical_iff_exists_closed_right_zero (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) :
    p ∉ canonicalAmplitudes z rho sigma ↔ ∃ s : ℂ, 0 ≤ s.re ∧
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s).det = 0 := by
  classical
  simp [canonicalAmplitudes, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- A real actual transverse fold has a genuine closed-right-half-plane
renewal-factor zero; no firstness or purely imaginary location is inferred. -/
theorem actual_transverse_root_exists_closed_right_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (htransverse : (fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (t,p)) (1,0) ∉
      Set.range (fun w => (fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (t,p)) (0,w))) :
    ∃ s : ℂ, 0 ≤ s.re ∧ (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s).det = 0 :=
  (not_canonical_iff_exists_closed_right_zero z rho sigma p).mp
    (actual_transverse_root_not_canonical z hz rho sigma hsigma hrho K hK hv t p hroot htransverse)

/-- A canonical initial prefix cannot extend strictly past an actual
nonnegative transverse fold. This gives only a NONSTRICT endpoint bound. -/
theorem transverse_fold_bounds_initial_canonical_prefix
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (bound : ENNReal) (f : ℝ) (hf : 0 ≤ f)
    (hcanon : ∀ t ∈ initialCouplings bound, p t ∈ canonicalAmplitudes z rho sigma)
    (hroot : IsRoot z rho sigma (f • K) (p f).1 (p f).2)
    (htransverse : (fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (f,p f)) (1,0) ∉
      Set.range (fun w => (fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (f,p f)) (0,w))) :
    bound ≤ ENNReal.ofReal f := by
  by_contra hn
  exact (actual_transverse_root_not_canonical z hz rho sigma hsigma hrho K hK hv f (p f) hroot htransverse)
    (hcanon f ⟨hf,lt_of_not_ge hn⟩)

/-- Taylor coefficients depend only on the actual local amplitude germ. -/
theorem branch_coefficients_eq_of_eventuallyEq
    (p q : ℝ → TailMatrix T N × TailMatrix T N) (he : p =ᶠ[𝓝 (0 : ℝ)] q) :
    branchCoefficients p = branchCoefficients q := by
  funext n
  apply Prod.ext
  all_goals funext u i j
  all_goals simp only [branchCoefficients, jet]
  all_goals congr 1
  all_goals apply Filter.EventuallyEq.iteratedDeriv_eq
  all_goals filter_upwards [he] with t ht
  all_goals rw [ht]

/-- Taylor coefficients are taken from a genuine analytic germ, while the
series sums to the separately specified physical nonnegative branch. -/
def AmplitudeHasSumTo (germ branch : ℝ → TailMatrix T N × TailMatrix T N)
    (bound : ENNReal) : Prop :=
  ∀ t ∈ initialCouplings bound,
    (∀ u i j, HasSum (fun n => (branchCoefficients germ n).1 u i j*t^n) ((branch t).1 u i j)) ∧
    (∀ u i j, HasSum (fun n => (branchCoefficients germ n).2 u i j*t^n) ((branch t).2 u i j))

/-- Matching the actual nonnegative branch transfers the exact series limit,
without imposing analytic values on its arbitrary negative-time definition. -/
theorem amplitude_hasSumTo_iff_before_of_eqOn
    (germ branch : ℝ → TailMatrix T N × TailMatrix T N) (bound : ENNReal)
    (heq : Set.EqOn germ branch (initialCouplings bound)) :
    AmplitudeHasSumTo germ branch bound ↔ AmplitudeHasSumBefore germ bound := by
  constructor
  · intro h t ht
    simpa only [heq ht] using h t ht
  · intro h t ht
    simpa only [heq ht] using h t ht

/-- A continuous canonical branch specified ONLY on the initial nonnegative
interval has a genuine analytic extension germ and the correct radius criterion.
No two-sided root germ or whole-line continuity at zero is assumed of p. -/
theorem exists_canonical_series_extension
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (bound : ENNReal) (hbound : 0 < bound)
    (hp : ContinuousOn p (initialCouplings bound))
    (hroot : ∀ t ∈ initialCouplings bound, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ initialCouplings bound, p t ∈ canonicalAmplitudes z rho sigma) :
    ∃ e : ℝ → TailMatrix T N × TailMatrix T N,
      Set.EqOn e p (initialCouplings bound) ∧ AnalyticOnNhd ℝ e (initialCouplings bound) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (e t).1 (e t).2) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), e t ∈ canonicalAmplitudes z rho sigma) ∧
      0 < amplitudeRadius (branchCoefficients e) ∧
      (AmplitudeHasSumTo e p bound ↔ bound ≤ amplitudeRadius (branchCoefficients e)) := by
  classical
  have h0 : (0 : ℝ) ∈ initialCouplings bound := ⟨le_rfl,by simpa using hbound⟩
  have hpr : ∀ᶠ t in 𝓝[initialCouplings bound] (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hroot t ht
  obtain ⟨q,hq0,hqa,hqr,hqc,he⟩ := exists_analytic_extension_of_relative_root z hz rho sigma hsigma hrho K hK hv
    p (initialCouplings bound) 0 (hp 0 h0) (hroot 0 h0) hpr (hcanon 0 h0)
  let e := fun t : ℝ => if 0 ≤ t then p t else q t
  have hEqOn : Set.EqOn e p (initialCouplings bound) := by
    intro t ht
    change (if 0 ≤ t then p t else q t) = p t
    exact if_pos ht.1
  have hupper : ∀ᶠ t in 𝓝 (0 : ℝ), ENNReal.ofReal t < bound :=
    (isOpen_lt ENNReal.continuous_ofReal continuous_const).mem_nhds (by simpa using hbound)
  have heq : e =ᶠ[𝓝 (0 : ℝ)] q := by
    filter_upwards [eventually_nhdsWithin_iff.mp he,hupper] with t ht hu
    change (if 0 ≤ t then p t else q t) = q t
    split_ifs with ht0
    · exact ht ⟨ht0,hu⟩
    · rfl
  have hea : AnalyticAt ℝ e 0 := hqa.congr heq.symm
  have her : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (e t).1 (e t).2 := by
    filter_upwards [heq,hqr] with t ht hr
    rw [ht]
    exact hr
  have hec : ∀ᶠ t in 𝓝 (0 : ℝ), e t ∈ canonicalAmplitudes z rho sigma := by
    filter_upwards [heq,hqc] with t ht hc
    rw [ht]
    exact hc
  have hep : ContinuousOn e (initialCouplings bound) := hp.congr hEqOn
  have heR : ∀ t ∈ initialCouplings bound, IsRoot z rho sigma (t • K) (e t).1 (e t).2 := by
    intro t ht
    rw [hEqOn ht]
    exact hroot t ht
  have heC : ∀ t ∈ initialCouplings bound, e t ∈ canonicalAmplitudes z rho sigma := by
    intro t ht
    rw [hEqOn ht]
    exact hcanon t ht
  have heA := actual_canonical_branch_analytic_before z hz rho sigma hsigma hrho K hK hv e bound hea.continuousAt hep her heR heC
  exact ⟨e,hEqOn,heA,her,hec,amplitudeRadius_pos e hea,
    (amplitude_hasSumTo_iff_before_of_eqOn e p bound hEqOn).trans
      (analytic_branch_converges_before_iff e bound heA)⟩

/-- Actual canonical root germ uniqueness makes the common Taylor
coefficients independent of the chosen analytic extension representative. -/
theorem actual_canonical_root_coefficients_unique
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p q : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContinuousAt p 0) (hq : ContinuousAt q 0) (heq : p 0 = q 0)
    (hpr : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hqr : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (q t).1 (q t).2)
    (hcanon : p 0 ∈ canonicalAmplitudes z rho sigma) : branchCoefficients p = branchCoefficients q := by
  have he := canonical_root_germs_eventuallyEqWithin z hz rho sigma hsigma hrho K hK hv p q Set.univ 0
    hp.continuousWithinAt hq.continuousWithinAt heq hpr.self_of_nhds
    (hpr.filter_mono nhdsWithin_le_nhds) (hqr.filter_mono nhdsWithin_le_nhds) hcanon
  apply branch_coefficients_eq_of_eventuallyEq p q
  simpa only [nhdsWithin_univ] using he

/-- The common Taylor radius is intrinsic to the chosen actual canonical
root germ; arbitrary extension values away from that germ do not alter it. -/
theorem actual_canonical_root_radius_unique
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0)
    (p q : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContinuousAt p 0) (hq : ContinuousAt q 0) (heq : p 0 = q 0)
    (hpr : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hqr : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (q t).1 (q t).2)
    (hcanon : p 0 ∈ canonicalAmplitudes z rho sigma) :
    amplitudeRadius (branchCoefficients p) = amplitudeRadius (branchCoefficients q) := by
  rw [actual_canonical_root_coefficients_unique z hz rho sigma hsigma hrho K hK hv p q hp hq heq hpr hqr hcanon]

end FMSA.Convergence.ActualCanonicalBranch

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.actual_canonical_root_analyticAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.actual_canonical_root_analyticAt

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.exists_analytic_canonical_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.exists_analytic_canonical_root

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.canonical_root_germs_eventuallyEqWithin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.canonical_root_germs_eventuallyEqWithin

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.exists_analytic_extension_of_relative_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.exists_analytic_extension_of_relative_root

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.actual_canonical_roots_eqOn_of_preconnected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.actual_canonical_roots_eqOn_of_preconnected

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.actual_canonical_roots_eq_at_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.actual_canonical_roots_eq_at_endpoint

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.actual_canonical_branch_analytic_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.actual_canonical_branch_analytic_before

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.actual_canonical_branch_converges_before_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.actual_canonical_branch_converges_before_iff

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.actual_canonical_branch_entire_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.actual_canonical_branch_entire_iff

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.actual_canonical_root_parameter_derivative_in_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.actual_canonical_root_parameter_derivative_in_range

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.actual_transverse_root_not_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.actual_transverse_root_not_canonical

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.not_canonical_iff_exists_closed_right_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.not_canonical_iff_exists_closed_right_zero

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.actual_transverse_root_exists_closed_right_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.actual_transverse_root_exists_closed_right_zero

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.transverse_fold_bounds_initial_canonical_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.transverse_fold_bounds_initial_canonical_prefix

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.branch_coefficients_eq_of_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.branch_coefficients_eq_of_eventuallyEq

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.amplitude_hasSumTo_iff_before_of_eqOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.amplitude_hasSumTo_iff_before_of_eqOn

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.exists_canonical_series_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.exists_canonical_series_extension

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.actual_canonical_root_coefficients_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.actual_canonical_root_coefficients_unique

/-- info: 'FMSA.Convergence.ActualCanonicalBranch.actual_canonical_root_radius_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalBranch.actual_canonical_root_radius_unique
