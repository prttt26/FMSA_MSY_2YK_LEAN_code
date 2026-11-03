import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring

/-! Literal real-coefficient polynomial complexification and its true
Jacobian. Real regularity constructs a genuine holomorphic root germ;
local root uniqueness will identify its real restrictions. -/

noncomputable section
open Filter Topology Set
open scoped BigOperators ContDiff
namespace FMSA.Convergence.ComplexPolynomialSystem

/-- Coefficient complexification recovers exact real polynomial values at
EVERY real point, including nonroots, with no positivity assumptions. -/
theorem complex_eval_ofReal {J : Type*} (P : MvPolynomial J ℝ) (v : J → ℝ) :
    MvPolynomial.eval₂Hom Complex.ofRealHom (fun j => (v j : ℂ)) P=
      (MvPolynomial.eval v P : ℂ) := by
  simpa using (MvPolynomial.map_eval₂Hom (RingHom.id ℝ) v Complex.ofRealHom P).symm

/-- The exact coefficient complexification is entire in all coordinates. -/
theorem complex_eval_analyticAt {J : Type*} [Fintype J]
    (P : MvPolynomial J ℝ) (v : J → ℂ) :
    AnalyticAt ℂ (fun w : J → ℂ => MvPolynomial.eval₂Hom Complex.ofRealHom w P) v := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval₂Hom_C] using analyticAt_const
  | add p q hp hq =>
    convert! hp.add hq using 1
    ext w
    simp
  | mul_X p j hp =>
    convert! hp.mul ((ContinuousLinearMap.proj j).analyticAt v) using 1
    ext w
    simp

/-- Formal partials are the GENUINE complex directional derivative. -/
theorem complex_polynomial_line_hasDerivAt {J : Type*} [Fintype J]
    (P : MvPolynomial J ℝ) (v w : J → ℂ) :
    HasDerivAt (fun t : ℂ => MvPolynomial.eval₂Hom Complex.ofRealHom (v+t • w) P)
      (∑ j, MvPolynomial.eval₂Hom Complex.ofRealHom v (MvPolynomial.pderiv j P)*w j) 0 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simpa [MvPolynomial.pderiv_C] using hasDerivAt_const (0 : ℂ) (c : ℂ)
  | add p q hp hq =>
    convert! hp.add hq using 1 <;> simp [map_add,Finset.sum_add_distrib,add_mul]
    rfl
  | mul_X p j hp =>
    have hx : HasDerivAt (fun t : ℂ => v j+t*w j) (w j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (w j)).const_add (v j)
    have hd := hp.mul hx
    convert! hd using 1
    · ext t; simp [map_mul]
    · simp [Pi.single_apply,Finset.sum_add_distrib,mul_add,
        Finset.mul_sum,apply_ite,mul_left_comm,mul_comm]
      ring

variable {I : Type*} [Fintype I]
local instance : DecidableEq I := Classical.decEq _

def point (x : ℂ × (I → ℂ)) : Option I → ℂ := fun j => j.elim x.1 x.2

def pointMap : (ℂ × (I → ℂ)) →L[ℂ] (Option I → ℂ) :=
  ContinuousLinearMap.pi fun j => j.elim (ContinuousLinearMap.fst ℂ ℂ (I → ℂ))
    (fun i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (I → ℂ)))

omit [Fintype I] in
/-- Coupling and EVERY amplitude coordinate are retained by a true complex
linear map; no reduced or rational surrogate is introduced. -/
theorem pointMap_apply (x : ℂ × (I → ℂ)) : pointMap x=point x := by
  funext j
  cases j <;> rfl

def complexResidual (F : I → MvPolynomial (Option I) ℝ) (x : ℂ × (I → ℂ)) : I → ℂ :=
  fun i => MvPolynomial.eval₂Hom Complex.ofRealHom (point x) (F i)

def realPoint (t : ℝ) (a : I → ℝ) : Option I → ℝ := fun j => j.elim t a

omit [Fintype I] in
/-- Exact real-slice equality for the whole square complex system. -/
theorem complexResidual_ofReal (F : I → MvPolynomial (Option I) ℝ) (t : ℝ) (a : I → ℝ) :
    complexResidual F ((t : ℂ),fun i => (a i : ℂ))=
      fun i => (MvPolynomial.eval (realPoint t a) (F i) : ℂ) := by
  funext i
  change MvPolynomial.eval₂Hom Complex.ofRealHom (point ((t : ℂ),fun i => (a i : ℂ))) (F i)=_
  have hp : point ((t : ℂ),fun i => (a i : ℂ))=fun j => (realPoint t a j : ℂ) := by
    funext j
    cases j <;> rfl
  rw [hp,complex_eval_ofReal]

/-- The literal square polynomial complex residual is entire jointly in
coupling and all complex amplitudes. -/
theorem complexResidual_analyticAt (F : I → MvPolynomial (Option I) ℝ) (x : ℂ × (I → ℂ)) :
    AnalyticAt ℂ (complexResidual F) x := by
  apply AnalyticAt.pi
  intro i
  have h := (complex_eval_analyticAt (F i) (pointMap x)).comp
    ((pointMap : (ℂ × (I → ℂ)) →L[ℂ] (Option I → ℂ)).analyticAt x)
  simpa only [Function.comp_def,pointMap_apply,complexResidual] using h

def complexJacobian (F : I → MvPolynomial (Option I) ℝ) (x : ℂ × (I → ℂ)) : Matrix I I ℂ :=
  fun i j => MvPolynomial.eval₂Hom Complex.ofRealHom (point x) (MvPolynomial.pderiv (some j) (F i))

def realJacobian (F : I → MvPolynomial (Option I) ℝ) (t : ℝ) (a : I → ℝ) : Matrix I I ℝ :=
  fun i j => MvPolynomial.eval (realPoint t a) (MvPolynomial.pderiv (some j) (F i))

def complexPartial (F : I → MvPolynomial (Option I) ℝ) (x : ℂ × (I → ℂ)) :
    (I → ℂ) →L[ℂ] (I → ℂ) :=
  (fderiv ℂ (complexResidual F) x).comp (ContinuousLinearMap.inr ℂ ℂ (I → ℂ))

/-- The full complex amplitude partial is EXACTLY formal matrix multiplication
at every point, including nonroots and singular points. -/
theorem complex_partial_coordinates (F : I → MvPolynomial (Option I) ℝ)
    (t : ℂ) (a h : I → ℂ) (i : I) :
    complexPartial F (t,a) h i=∑ j, complexJacobian F (t,a) i j*h j := by
  let R := complexResidual F
  let c : (I → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  have hl : HasDerivAt (fun u : ℂ => (t,a+u • h)) (0,h) 0 := by
    simpa using HasDerivAt.prodMk (hasDerivAt_const (0 : ℂ) t)
      (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add a)
  have hr : HasFDerivAt R (fderiv ℂ R (t,a)) (t,a) :=
    (complexResidual_analyticAt F (t,a)).differentiableAt.hasFDerivAt
  have hr' : HasFDerivAt R (fderiv ℂ R (t,a)) (t,a+(0 : ℂ) • h) := by simpa using hr
  have hd := c.hasFDerivAt.comp_hasDerivAt 0 (hr'.comp_hasDerivAt 0 hl)
  have hp := complex_polynomial_line_hasDerivAt (F i) (point (t,a)) (point (0,h))
  have he : (fun u : ℂ => MvPolynomial.eval₂Hom Complex.ofRealHom
      (point (t,a)+u • point (0,h)) (F i))=(fun u : ℂ => c (R (t,a+u • h))) := by
    funext u
    change MvPolynomial.eval₂Hom Complex.ofRealHom (point (t,a)+u • point (0,h)) (F i)=
      MvPolynomial.eval₂Hom Complex.ofRealHom (point (t,a+u • h)) (F i)
    apply congrArg (fun w => MvPolynomial.eval₂Hom Complex.ofRealHom w (F i))
    funext j
    cases j <;> simp [point]
  rw [he] at hp
  simpa [complexPartial,complexJacobian,point,Fintype.sum_option,c,R,Function.comp_def] using hd.unique hp

/-- Matrix multiplication is the whole genuine partial, not a coordinate
formula merely at roots. -/
theorem complex_partial_mulVec (F : I → MvPolynomial (Option I) ℝ)
    (x : ℂ × (I → ℂ)) (h : I → ℂ) :
    (complexJacobian F x).mulVec h=complexPartial F x h := by
  funext i
  exact (complex_partial_coordinates F x.1 x.2 h i).symm

omit [Fintype I] in
/-- Exact real Jacobian embeds entrywise into the true complex Jacobian. -/
theorem complexJacobian_ofReal (F : I → MvPolynomial (Option I) ℝ) (t : ℝ) (a : I → ℝ) :
    complexJacobian F ((t : ℂ),fun i => (a i : ℂ))=
      (realJacobian F t a).map Complex.ofRealHom := by
  funext i j
  unfold complexJacobian realJacobian
  have hp : point ((t : ℂ),fun i => (a i : ℂ))=fun j => (realPoint t a j : ℂ) := by
    funext j
    cases j <;> rfl
  rw [hp,complex_eval_ofReal]
  rfl

/-- The determinant is the literal real determinant, with no absolute-value
or conjugation surrogate and no nonsingularity assumption. -/
theorem complexJacobian_det_ofReal (F : I → MvPolynomial (Option I) ℝ) (t : ℝ) (a : I → ℝ) :
    (complexJacobian F ((t : ℂ),fun i => (a i : ℂ))).det=
      ((realJacobian F t a).det : ℂ) := by
  classical
  rw [complexJacobian_ofReal]
  exact (RingHom.map_det Complex.ofRealHom (realJacobian F t a)).symm

/-- Matrix nonsingularity is equivalent to invertibility of the TRUE complex
amplitude derivative, including an empty coordinate family. -/
theorem complex_partial_isInvertible_iff_det_ne_zero
    (F : I → MvPolynomial (Option I) ℝ) (x : ℂ × (I → ℂ)) :
    (complexPartial F x).IsInvertible ↔ (complexJacobian F x).det≠0 := by
  classical
  have he : (complexPartial F x : (I → ℂ) → (I → ℂ))=(complexJacobian F x).mulVec := by
    funext h
    exact (complex_partial_mulVec F x h).symm
  have hinj : Function.Injective (complexPartial F x) ↔ Function.Injective (complexJacobian F x).mulVec := by
    rw [he]
  rw [← isUnit_iff_ne_zero,← Matrix.isUnit_iff_isUnit_det,← Matrix.mulVec_injective_iff_isUnit,← hinj]
  constructor
  · rintro ⟨e,heq⟩
    rw [← heq]
    exact e.injective
  · intro hi
    let L := complexPartial F x
    have hk : L.ker=⊥ := LinearMap.ker_eq_bot.mpr hi
    have hs : L.range=⊤ := LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi)
    exact ⟨ContinuousLinearEquiv.ofBijective L hk hs,ContinuousLinearEquiv.coe_ofBijective L hk hs⟩

/-- Real regularity internally constructs the complex inverse needed by the
complex analytic IFT. No independent complex inverse is supplied. -/
theorem complex_partial_isInvertible_of_real_det_ne_zero
    (F : I → MvPolynomial (Option I) ℝ) (t : ℝ) (a : I → ℝ)
    (hdet : (realJacobian F t a).det≠0) :
    (complexPartial F ((t : ℂ),fun i => (a i : ℂ))).IsInvertible := by
  apply (complex_partial_isInvertible_iff_det_ne_zero F _).mpr
  rw [complexJacobian_det_ofReal]
  exact Complex.ofReal_ne_zero.mpr hdet

/-- Every regular REAL root constructs a genuine COMPLEX analytic root germ
of the exact polynomial complexification. No complex germ or inverse is given. -/
theorem exists_complex_analytic_root_of_real_regular
    (F : I → MvPolynomial (Option I) ℝ) (t : ℝ) (a : I → ℝ)
    (hroot : ∀ i, MvPolynomial.eval (realPoint t a) (F i)=0)
    (hdet : (realJacobian F t a).det≠0) :
    ∃ g : ℂ → (I → ℂ), g (t : ℂ)=(fun i => (a i : ℂ)) ∧ AnalyticAt ℂ g (t : ℂ) ∧
      ∀ᶠ z in 𝓝 (t : ℂ), complexResidual F (z,g z)=0 := by
  let x : ℂ × (I → ℂ) := ((t : ℂ),fun i => (a i : ℂ))
  have hc : ContDiffAt ℂ ω (complexResidual F) x := (complexResidual_analyticAt F x).contDiffAt
  have hi : ((fderiv ℂ (complexResidual F) x).comp
      (ContinuousLinearMap.inr ℂ ℂ (I → ℂ))).IsInvertible :=
    complex_partial_isInvertible_of_real_det_ne_zero F t a hdet
  let g := hc.implicitFunction (by simp) hi
  have hg0 : g (t : ℂ)=(fun i => (a i : ℂ)) := hc.implicitFunction_apply_self (by simp) hi
  have hga : AnalyticAt ℂ g (t : ℂ) := (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  have hzero : complexResidual F x=0 := by
    rw [complexResidual_ofReal]
    funext i
    simp [hroot i]
  refine ⟨g,hg0,hga,?_⟩
  filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with z hz
  exact hz.trans hzero

def amplitudeEmbedding : (I → ℝ) →L[ℝ] (I → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

omit [Fintype I] in
/-- Real amplitudes are embedded componentwise, without a normalization. -/
theorem amplitudeEmbedding_apply (a : I → ℝ) (i : I) : amplitudeEmbedding a i=(a i : ℂ) := rfl

/-- The original finite coordinate norm is preserved, including empty I.
This is the norm dictionary required for common Taylor radii. -/
theorem amplitudeEmbedding_norm (a : I → ℝ) : ‖amplitudeEmbedding a‖=‖a‖ := by
  have hn i : ‖amplitudeEmbedding a i‖=‖a i‖ := by simp [amplitudeEmbedding_apply]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
    intro i
    rw [hn]
    exact norm_le_pi_norm a i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (amplitudeEmbedding a))).mpr
    intro i
    rw [← hn]
    exact norm_le_pi_norm (amplitudeEmbedding a) i

/-- Local complex IFT uniqueness matches EVERY approaching real root lift,
even with a one-sided filter and only a supplied real continuity limit.
No complex extension or analyticity of the real lift is assumed. -/
theorem real_lift_matches_complex_germ
    (F : I → MvPolynomial (Option I) ℝ) (t : ℝ) (a : I → ℝ)
    (hroot : ∀ i, MvPolynomial.eval (realPoint t a) (F i)=0)
    (hdet : (realJacobian F t a).det≠0)
    (g : ℂ → (I → ℂ)) (hg0 : g (t : ℂ)=amplitudeEmbedding a)
    (hg : ContinuousAt g (t : ℂ))
    (hgr : ∀ᶠ z in 𝓝 (t : ℂ), complexResidual F (z,g z)=0)
    (p : ℝ → (I → ℝ)) (l : Filter ℝ) (hl : l≤𝓝 t) (hp : Tendsto p l (𝓝 a))
    (hpr : ∀ᶠ s in l, ∀ i, MvPolynomial.eval (realPoint s (p s)) (F i)=0) :
    (fun s => amplitudeEmbedding (p s))=ᶠ[l](fun s => g (s : ℂ)) := by
  let x : ℂ × (I → ℂ) := ((t : ℂ),amplitudeEmbedding a)
  have hc : ContDiffAt ℂ ∞ (complexResidual F) x := (complexResidual_analyticAt F x).contDiffAt
  have hi : ((fderiv ℂ (complexResidual F) x).comp
      (ContinuousLinearMap.inr ℂ ℂ (I → ℂ))).IsInvertible :=
    complex_partial_isInvertible_of_real_det_ne_zero F t a hdet
  have htime : Tendsto (fun s : ℝ => (s : ℂ)) l (𝓝 (t : ℂ)) :=
    (Complex.continuous_ofReal.tendsto t).mono_left hl
  have hpt : Tendsto (fun s => amplitudeEmbedding (p s)) l (𝓝 (amplitudeEmbedding a)) :=
    amplitudeEmbedding.continuous.continuousAt.tendsto.comp hp
  have hgt : Tendsto (fun s : ℝ => g (s : ℂ)) l (𝓝 (amplitudeEmbedding a)) := by
    rw [← hg0]
    exact hg.tendsto.comp htime
  have hpointp : Tendsto (fun s : ℝ => ((s : ℂ),amplitudeEmbedding (p s))) l (𝓝 x) :=
    htime.prodMk_nhds hpt
  have hpointg : Tendsto (fun s : ℝ => ((s : ℂ),g (s : ℂ))) l (𝓝 x) :=
    htime.prodMk_nhds hgt
  have hzero : complexResidual F x=0 := by
    change complexResidual F ((t : ℂ),fun i => (a i : ℂ))=0
    rw [complexResidual_ofReal]
    funext i
    simp [hroot i]
  have hrootp : ∀ᶠ s : ℝ in l, complexResidual F ((s : ℂ),amplitudeEmbedding (p s))=0 := by
    filter_upwards [hpr] with s hs
    change complexResidual F ((s : ℂ),fun i => (p s i : ℂ))=0
    rw [complexResidual_ofReal]
    funext i
    simp [hs i]
  have hu := hc.eventually_apply_eq_iff_implicitFunction (by simp) hi
  filter_upwards [hpointp.eventually hu,hpointg.eventually hu,hrootp,htime.eventually hgr] with s hP hG hPr hGr
  exact (hP.mp (hPr.trans hzero.symm)).symm.trans (hG.mp (hGr.trans hzero.symm))

/-- Real regularity CONSTRUCTS a genuine complex analytic germ that agrees
with any supplied approaching real lift. A one-sided real germ suffices. -/
theorem exists_complex_analytic_root_matching_real_lift
    (F : I → MvPolynomial (Option I) ℝ) (t : ℝ) (a : I → ℝ)
    (hroot : ∀ i, MvPolynomial.eval (realPoint t a) (F i)=0)
    (hdet : (realJacobian F t a).det≠0)
    (p : ℝ → (I → ℝ)) (l : Filter ℝ) (hl : l≤𝓝 t) (hp : Tendsto p l (𝓝 a))
    (hpr : ∀ᶠ s in l, ∀ i, MvPolynomial.eval (realPoint s (p s)) (F i)=0) :
    ∃ g : ℂ → (I → ℂ), g (t : ℂ)=amplitudeEmbedding a ∧ AnalyticAt ℂ g (t : ℂ) ∧
      (∀ᶠ z in 𝓝 (t : ℂ), complexResidual F (z,g z)=0) ∧
      (fun s => amplitudeEmbedding (p s))=ᶠ[l](fun s => g (s : ℂ)) := by
  obtain ⟨g,hg0,hga,hgr⟩ := exists_complex_analytic_root_of_real_regular F t a hroot hdet
  exact ⟨g,hg0,hga,hgr,real_lift_matches_complex_germ F t a hroot hdet g hg0
    hga.continuousAt hgr p l hl hp hpr⟩

def specializeCoupling (t : ℝ) : MvPolynomial (Option I) ℝ →+* MvPolynomial I ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => j.elim (MvPolynomial.C t) MvPolynomial.X)

omit [Fintype I] in
/-- Formal amplitude partials commute with literal coupling specialization. -/
theorem pderiv_specializeCoupling (P : MvPolynomial (Option I) ℝ) (t : ℝ) (i : I) :
    MvPolynomial.pderiv i (specializeCoupling t P)=
      specializeCoupling t (MvPolynomial.pderiv (some i) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [specializeCoupling]
  | add p q hp hq => simp [hp,hq]
  | mul_X p j hp =>
    cases j with
    | none =>
      simp [specializeCoupling]
      exact Or.inl hp
    | some j =>
      simp [specializeCoupling,Pi.single_apply,apply_ite]
      exact hp

omit [Fintype I] in
/-- Literal specialization and point evaluation commute for every real value. -/
theorem eval_specializeCoupling (P : MvPolynomial (Option I) ℝ) (t : ℝ) (a : I → ℝ) :
    MvPolynomial.eval a (specializeCoupling t P)=MvPolynomial.eval (realPoint t a) P := by
  have hh : (MvPolynomial.eval a).comp (specializeCoupling t)=MvPolynomial.eval (realPoint t a) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [specializeCoupling]
    · intro j
      cases j <;> simp [specializeCoupling,realPoint]
  exact RingHom.congr_fun hh P

omit [Fintype I] in
/-- The real Jacobian is exactly the traditional specialized-polynomial
Jacobian, with its standard equation-row/variable-column order. -/
theorem realJacobian_eq_specialized (F : I → MvPolynomial (Option I) ℝ) (t : ℝ) (a : I → ℝ) :
    realJacobian F t a=fun i j => MvPolynomial.eval a
      (MvPolynomial.pderiv j (specializeCoupling t (F i))) := by
  funext i j
  rw [pderiv_specializeCoupling,eval_specializeCoupling]
  rfl

/-- Actual real/complex analytic germs that agree near zero have the EXACT
embedded Taylor coefficients. The coefficient dictionary is proved from
power-series uniqueness, not supplied separately. -/
theorem real_complex_coeff_eq_of_germ_match
    (p : ℝ → (I → ℝ)) (g : ℂ → (I → ℂ))
    (a : FormalMultilinearSeries ℝ ℝ (I → ℝ))
    (b : FormalMultilinearSeries ℂ ℂ (I → ℂ))
    (ha : HasFPowerSeriesAt p a (0 : ℝ)) (hb : HasFPowerSeriesAt g b (0 : ℂ))
    (heq : (fun t => amplitudeEmbedding (p t))=ᶠ[𝓝 (0 : ℝ)](fun t => g (t : ℂ))) :
    ∀ n, b.coeff n=amplitudeEmbedding (a.coeff n) := by
  have hpa : HasFPowerSeriesAt (amplitudeEmbedding ∘ p)
      (amplitudeEmbedding.compFormalMultilinearSeries a) (0 : ℝ) := by
    obtain ⟨r,hr⟩ := ha
    exact ⟨r,amplitudeEmbedding.comp_hasFPowerSeriesOnBall hr⟩
  have hbr : HasFPowerSeriesAt g (b.restrictScalars ℝ) (0 : ℂ) := hb.restrictScalars
  have hba : HasFPowerSeriesAt (g ∘ Complex.ofRealCLM)
      ((b.restrictScalars ℝ).compContinuousLinearMap Complex.ofRealCLM) (0 : ℝ) := by
    exact hbr.compContinuousLinearMap
  have he := hpa.eq_formalMultilinearSeries_of_eventually hba heq
  intro n
  have hc := congrArg (fun c : FormalMultilinearSeries ℝ ℝ (I → ℂ) => c.coeff n) he
  change b n (fun _ => 1)=amplitudeEmbedding (a n (fun _ => 1))
  change amplitudeEmbedding (a n (fun _ => 1))=
    b n (fun _ => Complex.ofRealCLM (1 : ℝ)) at hc
  simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using hc.symm

/-- Exact embedded coefficients preserve the TRUE common Banach radius.
The field changes from real to complex; no separate radius identity is assumed. -/
theorem radius_eq_of_real_embedded_coefficients
    (a : FormalMultilinearSeries ℝ ℝ (I → ℝ))
    (b : FormalMultilinearSeries ℂ ℂ (I → ℂ))
    (hcoeff : ∀ n, b.coeff n=amplitudeEmbedding (a.coeff n)) : a.radius=b.radius := by
  unfold FormalMultilinearSeries.radius
  simp_rw [FormalMultilinearSeries.norm_apply_eq_norm_coef,hcoeff,amplitudeEmbedding_norm]

/-- Matching genuine analytic germs have EXACTLY the same common Taylor
radius, including zero/infinite radii and every finite coordinate dimension. -/
theorem real_complex_radius_eq_of_germ_match
    (p : ℝ → (I → ℝ)) (g : ℂ → (I → ℂ))
    (a : FormalMultilinearSeries ℝ ℝ (I → ℝ))
    (b : FormalMultilinearSeries ℂ ℂ (I → ℂ))
    (ha : HasFPowerSeriesAt p a (0 : ℝ)) (hb : HasFPowerSeriesAt g b (0 : ℂ))
    (heq : (fun t => amplitudeEmbedding (p t))=ᶠ[𝓝 (0 : ℝ)](fun t => g (t : ℂ))) :
    a.radius=b.radius :=
  radius_eq_of_real_embedded_coefficients a b (real_complex_coeff_eq_of_germ_match p g a b ha hb heq)

/-- A real regular polynomial root germ constructs a TRUE complex germ with
EXACTLY the same intrinsic common Banach radius. Neither a complex germ,
a coefficient identification nor a radius identity is supplied. -/
theorem exists_complex_germ_with_same_radius
    (F : I → MvPolynomial (Option I) ℝ) (p : ℝ → (I → ℝ))
    (a : FormalMultilinearSeries ℝ ℝ (I → ℝ)) (ha : HasFPowerSeriesAt p a (0 : ℝ))
    (hpr : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, MvPolynomial.eval (realPoint t (p t)) (F i)=0)
    (hdet : (realJacobian F 0 (p 0)).det≠0) :
    ∃ (g : ℂ → (I → ℂ)) (b : FormalMultilinearSeries ℂ ℂ (I → ℂ)),
      g 0=amplitudeEmbedding (p 0) ∧ HasFPowerSeriesAt g b 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), complexResidual F (z,g z)=0) ∧
      ((fun t => amplitudeEmbedding (p t))=ᶠ[𝓝 (0 : ℝ)](fun t => g (t : ℂ))) ∧
      a.radius=b.radius := by
  obtain ⟨g,hg0,hga,hgr,heq⟩ := exists_complex_analytic_root_matching_real_lift F 0 (p 0)
    hpr.self_of_nhds hdet p (𝓝 0) le_rfl ha.analyticAt.continuousAt.tendsto hpr
  obtain ⟨b,hb⟩ := hga
  exact ⟨g,b,hg0,hb,hgr,heq,real_complex_radius_eq_of_germ_match p g a b ha hb heq⟩

/-- Any continuous coordinate linear equivalence preserves a series' TRUE
common radius; no assertion that the equivalence is isometric is needed. -/
theorem radius_eq_of_continuousLinearEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (a : FormalMultilinearSeries ℝ ℝ E) :
    (e.toContinuousLinearMap.compFormalMultilinearSeries a).radius=a.radius := by
  have h1 := a.radius_le_radius_continuousLinearMap_comp e.toContinuousLinearMap
  have h2 := (e.toContinuousLinearMap.compFormalMultilinearSeries a).radius_le_radius_continuousLinearMap_comp
    e.symm.toContinuousLinearMap
  have hid : e.symm.toContinuousLinearMap.compFormalMultilinearSeries
      (e.toContinuousLinearMap.compFormalMultilinearSeries a)=a := by
    funext n
    exact DFunLike.ext _ _ (fun v => e.symm_apply_apply (a n v))
  rw [hid] at h2
  exact le_antisymm h2 h1

/-- Ordinary REAL vector convergence outside the intrinsic common radius
is impossible, including conditional convergence. No complex series is needed. -/
theorem real_not_summable_of_radius_lt_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : FormalMultilinearSeries ℝ ℝ E) (t : ℝ)
    (ht : a.radius<(‖t‖₊ : ENNReal)) : ¬Summable (fun n => t^n • a.coeff n) := by
  intro hs
  have hle : (‖t‖₊ : ENNReal)≤a.radius := by
    apply a.le_radius_of_tendsto (l := 0)
    have hd : Tendsto (fun n => ‖t^n • a.coeff n‖) atTop (𝓝 (0 : ℝ)) := by
      convert tendsto_norm.comp hs.tendsto_atTop_zero using 1 <;> simp [Function.comp_def]
    simpa only [norm_smul,norm_pow,FormalMultilinearSeries.norm_apply_eq_norm_coef,
      coe_nnnorm,mul_comm] using hd
  exact not_le_of_gt ht hle

/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.complex_eval_ofReal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.complex_eval_ofReal
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.complex_eval_analyticAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.complex_eval_analyticAt
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.complex_polynomial_line_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.complex_polynomial_line_hasDerivAt
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.pointMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.pointMap_apply
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.complexResidual_ofReal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.complexResidual_ofReal
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.complexResidual_analyticAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.complexResidual_analyticAt
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.complex_partial_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.complex_partial_coordinates
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.complex_partial_mulVec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.complex_partial_mulVec
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.complexJacobian_ofReal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.complexJacobian_ofReal
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.complexJacobian_det_ofReal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.complexJacobian_det_ofReal
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.complex_partial_isInvertible_iff_det_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.complex_partial_isInvertible_iff_det_ne_zero
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.complex_partial_isInvertible_of_real_det_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.complex_partial_isInvertible_of_real_det_ne_zero
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.exists_complex_analytic_root_of_real_regular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.exists_complex_analytic_root_of_real_regular
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.amplitudeEmbedding_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.amplitudeEmbedding_apply
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.amplitudeEmbedding_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.amplitudeEmbedding_norm
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.real_lift_matches_complex_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.real_lift_matches_complex_germ
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.exists_complex_analytic_root_matching_real_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.exists_complex_analytic_root_matching_real_lift
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.pderiv_specializeCoupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.pderiv_specializeCoupling
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.eval_specializeCoupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.eval_specializeCoupling
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.realJacobian_eq_specialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.realJacobian_eq_specialized
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.real_complex_coeff_eq_of_germ_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.real_complex_coeff_eq_of_germ_match
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.radius_eq_of_real_embedded_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.radius_eq_of_real_embedded_coefficients
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.real_complex_radius_eq_of_germ_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.real_complex_radius_eq_of_germ_match
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.exists_complex_germ_with_same_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.exists_complex_germ_with_same_radius
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.radius_eq_of_continuousLinearEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.radius_eq_of_continuousLinearEquiv
/-- info: 'FMSA.Convergence.ComplexPolynomialSystem.real_not_summable_of_radius_lt_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexPolynomialSystem.real_not_summable_of_radius_lt_norm
end FMSA.Convergence.ComplexPolynomialSystem
