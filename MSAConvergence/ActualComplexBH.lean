import MSAConvergence.MixtureHSCanonicity
import MSAConvergence.ComplexPolynomialSystem
import MSAConvergence.ComplexPathMonodromy
import MSAConvergence.BHPolynomialJacobian

/-! Genuine complexification of the ORIGINAL finite BH residual, preserving
all Dt/G coordinates, actual real roots, true Jacobians and intrinsic common
Taylor radii. A changed complex root lift bounds the ORIGINAL real radius;
numerical root/path certificates remain explicit premises. -/
noncomputable section
open Filter Topology Set
open scoped BigOperators ContDiff
namespace FMSA.Convergence.ActualComplexBH
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.BHPolynomialJacobian
open FMSA.Convergence.ComplexPolynomialSystem FMSA.Convergence.ComplexPathMonodromy
open FMSA.Convergence.RegularEndpointContinuation FMSA.Convergence.CanonicalNeighborhood
open FMSA.Convergence.ActualTracerAmplitudeRecovery
open FMSA.Convergence.ActualCanonicalBranch FMSA.Convergence.MixtureHSCanonicity
open FMSA.Paper.ActualAnalyticBranch
variable {N : ℕ} {T : Type*} [Fintype T]
local instance : DecidableEq (AmpIndex T N) := Classical.decEq _

def complexBHResidual (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N) :
    ℂ × (AmpIndex T N → ℂ) → (AmpIndex T N → ℂ) :=
  complexResidual (residualPoly z rho sigma K)

/-- The whole ORIGINAL real residual embeds exactly, for every state,
coupling and amplitude, including nonroots and singular points. -/
theorem real_slice_residual_eq
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    complexBHResidual z rho sigma K ((t : ℂ),amplitudeEmbedding (amplitudeValues a))=
      amplitudeEmbedding (amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (t,a))) := by
  change complexResidual (residualPoly z rho sigma K)
    ((t : ℂ),fun i => (amplitudeValues a i : ℂ))=_
  rw [complexResidual_ofReal]
  funext i
  rw [amplitudeEmbedding_apply]
  exact congrArg (fun x : ℝ => (x : ℂ)) (eval_residualPoly z rho sigma K (t,a) i)

/-- On the real slice, complex zeros are EXACTLY ORIGINAL BH roots. -/
theorem real_slice_root_iff
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    complexBHResidual z rho sigma K ((t : ℂ),amplitudeEmbedding (amplitudeValues a))=0 ↔
      IsRoot z rho sigma (t • K) a.1 a.2 := by
  change (complexResidual (residualPoly z rho sigma K)
    ((t : ℂ),fun i => (amplitudeValues a i : ℂ))=0) ↔ IsRoot z rho sigma (t • K) a.1 a.2
  rw [complexResidual_ofReal,actual_root_iff_polynomial_zeros]
  constructor
  · intro h i
    exact Complex.ofReal_eq_zero.mp (congrFun h i)
  · intro h
    funext i
    exact Complex.ofReal_eq_zero.mpr (h i)

/-- The traditional ORIGINAL amplitude Jacobian is the real polynomial
Jacobian used to construct the complex analytic germ. -/
theorem real_jacobian_eq_actual
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    realJacobian (residualPoly z rho sigma K) t (amplitudeValues a)=jacobian z rho sigma K t a := by
  rw [realJacobian_eq_specialized]
  rfl

/-- The TRUE complex amplitude Jacobian embeds the ORIGINAL one entrywise. -/
theorem complex_jacobian_real_eq_actual_map
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    complexJacobian (residualPoly z rho sigma K) ((t : ℂ),amplitudeEmbedding (amplitudeValues a))=
      (jacobian z rho sigma K t a).map Complex.ofRealHom := by
  change complexJacobian (residualPoly z rho sigma K)
    ((t : ℂ),fun i => (amplitudeValues a i : ℂ))=_
  rw [complexJacobian_ofReal,real_jacobian_eq_actual]

/-- Real regularity is exactly the required nonzero complex determinant. -/
theorem complex_jacobian_det_real_eq_actual
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    (complexJacobian (residualPoly z rho sigma K)
      ((t : ℂ),amplitudeEmbedding (amplitudeValues a))).det=((jacobian z rho sigma K t a).det : ℂ) := by
  change (complexJacobian (residualPoly z rho sigma K)
    ((t : ℂ),fun i => (amplitudeValues a i : ℂ))).det=_
  rw [complexJacobian_det_ofReal,real_jacobian_eq_actual]

/-- The complex inverse is CONSTRUCTED from the true ORIGINAL regularity;
no independent complex inverse or complexification axiom is given. -/
theorem complex_partial_isInvertible_of_endpointRegular
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (a : TailMatrix T N × TailMatrix T N)
    (hreg : EndpointRegular z rho sigma K t a) :
    (complexPartial (residualPoly z rho sigma K)
      ((t : ℂ),amplitudeEmbedding (amplitudeValues a))).IsInvertible := by
  have hd : (realJacobian (residualPoly z rho sigma K) t (amplitudeValues a)).det≠0 := by
    rw [real_jacobian_eq_actual]
    exact (endpoint_regular_iff_jacobian_det_ne_zero z rho sigma K t a).mp hreg
  exact complex_partial_isInvertible_of_real_det_ne_zero
    (residualPoly z rho sigma K) t (amplitudeValues a) hd

/-- Physical canonicity internally discharges original and complex inverse
premises at a canonical root, with arbitrary tracers and finite tails. -/
theorem complex_partial_isInvertible_at_canonical
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (a : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) a.1 a.2) (hcanon : a ∈ canonicalAmplitudes z rho sigma) :
    (complexPartial (residualPoly z rho sigma K)
      ((t : ℂ),amplitudeEmbedding (amplitudeValues a))).IsInvertible := by
  apply complex_partial_isInvertible_of_endpointRegular z rho sigma K t a
  exact actual_residual_partial_isInvertible z hz rho sigma hsigma hrho K hK t a hv hroot hcanon

/-- An honest ORIGINAL real BH power-series germ CONSTRUCTS a complex BH
germ with exactly the same intrinsic common radius. Coordinate equivalence,
complex inverse, matching coefficients and radius identity are all proved. -/
theorem exists_complex_germ_of_actual_regular_real_series
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (a : FormalMultilinearSeries ℝ ℝ (TailMatrix T N × TailMatrix T N))
    (ha : HasFPowerSeriesAt p a (0 : ℝ))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hreg : EndpointRegular z rho sigma K 0 (p 0)) :
    ∃ (g : ℂ → (AmpIndex T N → ℂ)) (b : FormalMultilinearSeries ℂ ℂ (AmpIndex T N → ℂ)),
      g 0=amplitudeEmbedding (amplitudeValues (p 0)) ∧ HasFPowerSeriesAt g b 0 ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), complexBHResidual z rho sigma K (w,g w)=0) ∧
      ((fun t => amplitudeEmbedding (amplitudeValues (p t)))=ᶠ[𝓝 (0 : ℝ)](fun t => g (t : ℂ))) ∧
      a.radius=b.radius := by
  let e := amplitudeCoordinates (T := T) (N := N)
  let pc := e ∘ p
  let ac := e.toContinuousLinearMap.compFormalMultilinearSeries a
  have hpc : HasFPowerSeriesAt pc ac (0 : ℝ) := by
    obtain ⟨r,hr⟩ := ha
    exact ⟨r,e.toContinuousLinearMap.comp_hasFPowerSeriesOnBall hr⟩
  have hpr : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i,
      MvPolynomial.eval (realPoint t (pc t)) (residualPoly z rho sigma K i)=0 := by
    filter_upwards [hroot] with t ht
    change ∀ i, MvPolynomial.eval (pointValues (t,p t)) (residualPoly z rho sigma K i)=0
    exact (actual_root_iff_polynomial_zeros z rho sigma K t (p t)).mp ht
  have hd : (realJacobian (residualPoly z rho sigma K) 0 (pc 0)).det≠0 := by
    change (realJacobian (residualPoly z rho sigma K) 0 (amplitudeValues (p 0))).det≠0
    rw [real_jacobian_eq_actual]
    exact (endpoint_regular_iff_jacobian_det_ne_zero z rho sigma K 0 (p 0)).mp hreg
  obtain ⟨g,b,hg0,hb,hgr,heq,hR⟩ := exists_complex_germ_with_same_radius
    (residualPoly z rho sigma K) pc ac hpc hpr hd
  have hcoord : ac.radius=a.radius := radius_eq_of_continuousLinearEquiv e a
  exact ⟨g,b,hg0,hb,hgr,heq,hcoord.symm.trans hR⟩

/-- For a physical canonical ORIGINAL germ all inverse premises are
internally discharged; the complex germ and TRUE equal radius are constructed. -/
theorem exists_complex_germ_of_actual_canonical_real_series
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (a : FormalMultilinearSeries ℝ ℝ (TailMatrix T N × TailMatrix T N))
    (ha : HasFPowerSeriesAt p a (0 : ℝ))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : p 0 ∈ canonicalAmplitudes z rho sigma) :
    ∃ (g : ℂ → (AmpIndex T N → ℂ)) (b : FormalMultilinearSeries ℂ ℂ (AmpIndex T N → ℂ)),
      g 0=amplitudeEmbedding (amplitudeValues (p 0)) ∧ HasFPowerSeriesAt g b 0 ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), complexBHResidual z rho sigma K (w,g w)=0) ∧
      ((fun t => amplitudeEmbedding (amplitudeValues (p t)))=ᶠ[𝓝 (0 : ℝ)](fun t => g (t : ℂ))) ∧
      a.radius=b.radius := by
  apply exists_complex_germ_of_actual_regular_real_series z rho sigma K p a ha hroot
  exact actual_residual_partial_isInvertible z hz rho sigma hsigma hrho K hK 0 (p 0) hv
    hroot.self_of_nhds hcanon

variable {S : Type*} [TopologicalSpace S] [PreconnectedSpace S]

/-- A seed-linked changed complex lift bounds the TRUE ORIGINAL real BH
common Taylor radius. The complex germ, entire residual, exact derivative,
seed matching and real/complex radius equality are INTERNALLY discharged.
The actual complex path/root/determinant certificates remain explicit. -/
theorem actual_radius_le_of_changed_complex_lift
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (a : FormalMultilinearSeries ℝ ℝ (TailMatrix T N × TailMatrix T N))
    (ha : HasFPowerSeriesAt p a (0 : ℝ))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : p 0 ∈ canonicalAmplitudes z rho sigma)
    (gamma : S → ℂ) (q : S → (AmpIndex T N → ℂ)) (seed t0 t1 : S)
    (hgamma : Continuous gamma) (hq : Continuous q)
    (hqr : ∀ t, complexBHResidual z rho sigma K (gamma t, q t) = 0)
    (hdet : ∀ t, (complexJacobian (residualPoly z rho sigma K) (gamma t, q t)).det ≠ 0)
    (hloop : gamma t0 = gamma t1) (hchange : q t0 ≠ q t1)
    (r : ℝ) (hr : 0 < r) (hpath : ∀ t, ‖gamma t‖ < r)
    (hstart : gamma seed = 0) (hseed : q seed = amplitudeEmbedding (amplitudeValues (p 0))) :
    a.radius≤ENNReal.ofReal r := by
  obtain ⟨g,b,hg0,hb,hgr,_heq,hR⟩ := exists_complex_germ_of_actual_canonical_real_series
    z hz rho sigma hsigma hrho K hK hv p a ha hroot hcanon
  rw [hR]
  refine radius_le_of_changed_lift (complexBHResidual z rho sigma K) gamma q seed t0 t1
    hgamma hq hqr ?_ ?_ hloop hchange r hr hpath ?_ b g hb hgr hstart (hseed.trans hg0.symm)
  · intro t
    exact (complexResidual_analyticAt (residualPoly z rho sigma K) (gamma t, q t)).contDiffAt
  · intro t
    exact (complex_partial_isInvertible_iff_det_ne_zero (residualPoly z rho sigma K) _).mpr (hdet t)
  · intro x _
    exact complexResidual_analyticAt (residualPoly z rho sigma K) x

/-- Beyond any disc containing a certified changed complex lift, the
ORIGINAL real amplitude vector series cannot converge even conditionally. -/
theorem actual_not_summable_of_changed_complex_lift
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (a : FormalMultilinearSeries ℝ ℝ (TailMatrix T N × TailMatrix T N))
    (ha : HasFPowerSeriesAt p a (0 : ℝ))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : p 0 ∈ canonicalAmplitudes z rho sigma)
    (gamma : S → ℂ) (q : S → (AmpIndex T N → ℂ)) (seed t0 t1 : S)
    (hgamma : Continuous gamma) (hq : Continuous q)
    (hqr : ∀ t, complexBHResidual z rho sigma K (gamma t, q t) = 0)
    (hdet : ∀ t, (complexJacobian (residualPoly z rho sigma K) (gamma t, q t)).det ≠ 0)
    (hloop : gamma t0 = gamma t1) (hchange : q t0 ≠ q t1)
    (r : ℝ) (hr : 0 < r) (hpath : ∀ t, ‖gamma t‖ < r)
    (hstart : gamma seed = 0) (hseed : q seed = amplitudeEmbedding (amplitudeValues (p 0)))
    (tau : ℝ) (htau : r < |tau|) : ¬Summable (fun n => tau^n • a.coeff n) := by
  apply real_not_summable_of_radius_lt_norm a tau
  apply lt_of_le_of_lt (actual_radius_le_of_changed_complex_lift z hz rho sigma hsigma hrho K hK hv
    p a ha hroot hcanon gamma q seed t0 t1 hgamma hq hqr hdet hloop hchange r hr hpath hstart hseed)
  rw [← enorm_eq_nnnorm,← ofReal_norm,Real.norm_eq_abs]
  exact (ENNReal.ofReal_lt_ofReal_iff (hr.trans htau)).mpr htau

/-- From physical HS mixture DATA at eta<1, construct genuine original real
and complex canonical root germs with the SAME positive intrinsic radius.
No real/complex root curve, seed canonicity, series or inverse is supplied. -/
theorem exists_hs_real_complex_germs_from_data
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : 0 < vacMix rho sigma) :
    ∃ (p : ℝ → TailMatrix T N × TailMatrix T N)
      (a : FormalMultilinearSeries ℝ ℝ (TailMatrix T N × TailMatrix T N))
      (g : ℂ → (AmpIndex T N → ℂ)) (b : FormalMultilinearSeries ℂ ℂ (AmpIndex T N → ℂ)),
      p 0=(0, baseSeed z rho sigma) ∧ HasFPowerSeriesAt p a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), p t ∈ canonicalAmplitudes z rho sigma) ∧
      g 0=amplitudeEmbedding (amplitudeValues (0, baseSeed z rho sigma)) ∧
      HasFPowerSeriesAt g b 0 ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), complexBHResidual z rho sigma K (w,g w)=0) ∧
      ((fun t => amplitudeEmbedding (amplitudeValues (p t)))=ᶠ[𝓝 (0 : ℝ)](fun t => g (t : ℂ))) ∧
      a.radius=b.radius ∧ 0<a.radius := by
  have heta : etaMix rho sigma<1 := by unfold vacMix at hv; linarith
  have hc : (0, baseSeed z rho sigma) ∈ canonicalAmplitudes z rho sigma :=
    actual_mixture_hs_canonical z rho sigma hrho (fun i => (hsigma i).le) heta (baseSeed z rho sigma)
  have hseed : IsRoot z rho sigma ((0 : ℝ) • K) 0 (baseSeed z rho sigma) := by
    simpa only [zero_smul] using baseSeed_isRoot z rho sigma hz hv hrho hsigma
  obtain ⟨p,hp0,hpa,hpr,hpc⟩ := exists_analytic_canonical_root z hz rho sigma hsigma hrho K hK hv.ne'
    0 (0, baseSeed z rho sigma) hseed hc
  obtain ⟨a,ha⟩ := hpa
  have hc0 : p 0 ∈ canonicalAmplitudes z rho sigma := hpc.self_of_nhds
  obtain ⟨g,b,hg0,hb,hgr,heq,hR⟩ := exists_complex_germ_of_actual_canonical_real_series
    z hz rho sigma hsigma hrho K hK hv.ne' p a ha hpr hc0
  have hgseed : g 0=amplitudeEmbedding (amplitudeValues (0, baseSeed z rho sigma)) := by
    rw [hg0,hp0]
  exact ⟨p,a,g,b,hp0,ha,hpr,hpc,hgseed,hb,hgr,heq,hR,ha.radius_pos⟩

/-- A changed certified complex lift at physical HS mixture DATA constructs
the ORIGINAL real Taylor germ and proves its radius bound and ordinary
nonconvergence outside the disc. No seed/germ/inverse/radius premise remains;
only the actual numerical path/root/determinant witness is still supplied. -/
theorem exists_hs_real_series_radius_bound_of_changed_complex_lift
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : 0 < vacMix rho sigma)
    (gamma : S → ℂ) (q : S → (AmpIndex T N → ℂ)) (seed t0 t1 : S)
    (hgamma : Continuous gamma) (hq : Continuous q)
    (hqr : ∀ t, complexBHResidual z rho sigma K (gamma t, q t) = 0)
    (hdet : ∀ t, (complexJacobian (residualPoly z rho sigma K) (gamma t, q t)).det ≠ 0)
    (hloop : gamma t0 = gamma t1) (hchange : q t0 ≠ q t1)
    (r : ℝ) (hr : 0 < r) (hpath : ∀ t, ‖gamma t‖ < r)
    (hstart : gamma seed = 0)
    (hseed : q seed = amplitudeEmbedding (amplitudeValues (0, baseSeed z rho sigma))) :
    ∃ (p : ℝ → TailMatrix T N × TailMatrix T N)
      (a : FormalMultilinearSeries ℝ ℝ (TailMatrix T N × TailMatrix T N)),
      p 0=(0, baseSeed z rho sigma) ∧ HasFPowerSeriesAt p a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), p t ∈ canonicalAmplitudes z rho sigma) ∧
      a.radius≤ENNReal.ofReal r ∧ ∀ tau : ℝ, r < |tau| → ¬Summable (fun n => tau^n • a.coeff n) := by
  obtain ⟨p,a,_g,_b,hp0,ha,hpr,hpc,_hg0,_hb,_hgr,_heq,_hR,_ha0⟩ :=
    exists_hs_real_complex_germs_from_data z hz rho sigma hsigma hrho K hK hv
  have hqseed : q seed = amplitudeEmbedding (amplitudeValues (p 0)) := by rw [hp0]; exact hseed
  have hR := actual_radius_le_of_changed_complex_lift z hz rho sigma hsigma hrho K hK hv.ne'
    p a ha hpr hpc.self_of_nhds gamma q seed t0 t1 hgamma hq hqr hdet hloop hchange r hr hpath hstart hqseed
  refine ⟨p,a,hp0,ha,hpr,hpc,hR,?_⟩
  intro tau htau
  exact actual_not_summable_of_changed_complex_lift z hz rho sigma hsigma hrho K hK hv.ne'
    p a ha hpr hpc.self_of_nhds gamma q seed t0 t1 hgamma hq hqr hdet hloop hchange r hr hpath hstart hqseed tau htau

/-- info: 'FMSA.Convergence.ActualComplexBH.real_slice_residual_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.real_slice_residual_eq
/-- info: 'FMSA.Convergence.ActualComplexBH.real_slice_root_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.real_slice_root_iff
/-- info: 'FMSA.Convergence.ActualComplexBH.real_jacobian_eq_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.real_jacobian_eq_actual
/-- info: 'FMSA.Convergence.ActualComplexBH.complex_jacobian_real_eq_actual_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.complex_jacobian_real_eq_actual_map
/-- info: 'FMSA.Convergence.ActualComplexBH.complex_jacobian_det_real_eq_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.complex_jacobian_det_real_eq_actual
/-- info: 'FMSA.Convergence.ActualComplexBH.complex_partial_isInvertible_of_endpointRegular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.complex_partial_isInvertible_of_endpointRegular
/-- info: 'FMSA.Convergence.ActualComplexBH.complex_partial_isInvertible_at_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.complex_partial_isInvertible_at_canonical
/-- info: 'FMSA.Convergence.ActualComplexBH.exists_complex_germ_of_actual_regular_real_series' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.exists_complex_germ_of_actual_regular_real_series
/-- info: 'FMSA.Convergence.ActualComplexBH.exists_complex_germ_of_actual_canonical_real_series' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.exists_complex_germ_of_actual_canonical_real_series
/-- info: 'FMSA.Convergence.ActualComplexBH.actual_radius_le_of_changed_complex_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.actual_radius_le_of_changed_complex_lift
/-- info: 'FMSA.Convergence.ActualComplexBH.actual_not_summable_of_changed_complex_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.actual_not_summable_of_changed_complex_lift
/-- info: 'FMSA.Convergence.ActualComplexBH.exists_hs_real_complex_germs_from_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.exists_hs_real_complex_germs_from_data
/-- info: 'FMSA.Convergence.ActualComplexBH.exists_hs_real_series_radius_bound_of_changed_complex_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualComplexBH.exists_hs_real_series_radius_bound_of_changed_complex_lift
end FMSA.Convergence.ActualComplexBH
