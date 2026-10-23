import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearComplexReciprocity
import LeanCode.Analysis.FourierAEInjective

/-! Actual pointwise pair reciprocity, including contact, follows from the
finite coefficient certificate by damped Fourier inversion. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators FourierTransform RealInnerProductSpace
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def causalDampedComplex (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  (causalFull (fun t => exp (-t)*f t) t : ℂ)

theorem causalDampedComplex_fourier (f : ℝ → ℝ) (k : ℝ) :
    𝓕 (causalDampedComplex f) k=
      FMSA.causalComplexLaplace f (1+Complex.I*(2*π*k)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun t : ℝ => Complex.exp (↑(-2*π*t*k)*Complex.I) • causalDampedComplex f t)=
      fun t : ℝ => (causalFull f t : ℂ)*Complex.exp (-(1+Complex.I*(2*π*k))*t) := by
    funext t
    by_cases ht : t ∈ Ici (0 : ℝ)
    · simp only [causalDampedComplex, causalFull, indicator_of_mem ht,
        smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_exp]
      have hx : Complex.exp (↑(-2*π*t*k)*Complex.I)*Complex.exp ((-t : ℝ) : ℂ)=
          Complex.exp (-(1+Complex.I*(2*π*k))*(t : ℂ)) := by
        rw [← Complex.exp_add]; push_cast; congr 1; ring
      push_cast at hx
      push_cast
      linear_combination (f t : ℂ)*hx
    · simp only [causalDampedComplex, causalFull, indicator_of_notMem ht,
        Complex.ofReal_zero, smul_zero, zero_mul]
  rw [he, causalFull_complex_laplace]

/-- Uniqueness on the closed causal half-line. The affine RDF background
needs only positive damping, so no undamped integrability premise is used. -/
theorem causalComplexLaplace_injective_continuous (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hif : IntegrableOn (fun t => exp (-t)*f t) (Ioi 0))
    (hig : IntegrableOn (fun t => exp (-t)*g t) (Ioi 0))
    (hL : ∀ k : ℝ, FMSA.causalComplexLaplace f (1+Complex.I*(2*π*k))=
      FMSA.causalComplexLaplace g (1+Complex.I*(2*π*k))) :
    ∀ t, 0 ≤ t → f t=g t := by
  let U := causalDampedComplex f
  let V := causalDampedComplex g
  have hU : Integrable U := (causalFull_integrable _ hif).ofReal
  have hV : Integrable V := (causalFull_integrable _ hig).ofReal
  have hF : 𝓕 (U-V)=0 := by
    funext k
    have hIU := (Real.fourierIntegral_convergent_iff (V := ℝ) (E := ℂ) k).2 hU
    have hIV := (Real.fourierIntegral_convergent_iff (V := ℝ) (E := ℂ) k).2 hV
    rw [Real.fourier_eq]
    have he : ∀ t, 𝐞 (-⟪t, k⟫) • (U-V) t=
        𝐞 (-⟪t, k⟫) • U t-𝐞 (-⟪t, k⟫) • V t := by
      intro t; rw [Pi.sub_apply, smul_sub]
    rw [integral_congr_ae (Eventually.of_forall he), integral_sub hIU hIV,
      ← Real.fourier_eq, ← Real.fourier_eq]
    change 𝓕 (causalDampedComplex f) k-𝓕 (causalDampedComplex g) k=0
    rw [causalDampedComplex_fourier, causalDampedComplex_fourier, hL, sub_self]
  have hpos : EqOn f g (Ioi 0) := by
    intro t ht
    have he : U-V =ᶠ[𝓝 t] fun x => ((exp (-x)*(f x-g x) : ℝ) : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      simp only [U, V, Pi.sub_apply, causalDampedComplex, causalFull,
        indicator_of_mem (show x ∈ Ici (0 : ℝ) from (show 0 < x from hx).le)]
      push_cast
      ring
    have hc : ContinuousAt (U-V) t :=
      (Complex.continuous_ofReal.comp
        ((Real.continuous_exp.comp continuous_id.neg).mul (hf.sub hg))).continuousAt.congr_of_eventuallyEq he
    have hFI : Integrable (𝓕 (U-V)) := by rw [hF]; exact integrable_zero _ _ _
    have hinv := (hU.sub hV).fourierInv_fourier_eq hFI hc
    rw [hF] at hinv
    have hz : (𝓕⁻ (0 : ℝ → ℂ)) t=0 := by simp [Real.fourierInv_eq]
    rw [hz] at hinv
    have hv := (he.self_of_nhds).symm.trans hinv.symm
    have hvreal := congrArg Complex.re hv
    simp only [Complex.ofReal_re, Complex.zero_re] at hvreal
    exact sub_eq_zero.mp ((mul_eq_zero.mp hvreal).resolve_left (exp_ne_zero _))
  have hall := hpos.closure hf hg
  rw [closure_Ioi] at hall
  exact fun t ht => hall ht

theorem nonlinear_finite_certificate_actual_causal_reciprocity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hcert : NonlinearFiniteReciprocityCertificate z ρ σ Dt G)
    (i j : Fin N) (t : ℝ) (ht : 0 ≤ t) :
    nonlinearCausalG z ρ σ Dt G t i j=nonlinearCausalG z ρ σ Dt G t j i := by
  apply causalComplexLaplace_injective_continuous
    (fun t => nonlinearCausalG z ρ σ Dt G t i j)
    (fun t => nonlinearCausalG z ρ σ Dt G t j i)
    ((nonlinearCausalG_continuous z ρ σ Dt G).matrix_elem i j)
    ((nonlinearCausalG_continuous z ρ σ Dt G).matrix_elem j i)
    (by
      simpa only [neg_one_mul] using
        (nonlinearCausalG_laplace_integrable z ρ σ Dt G hz hσ hv δ hδ hδz hb 1 zero_lt_one i j))
    (by
      simpa only [neg_one_mul] using
        (nonlinearCausalG_laplace_integrable z ρ σ Dt G hz hσ hv δ hδ hδz hb 1 zero_lt_one j i)) _ t ht
  intro k
  have hs : 0 < (1+Complex.I*(2*(π : ℂ)*(k : ℂ))).re := by simp
  have he := congrFun (congrFun (nonlinear_finite_certificate_actual_complex_laplace_reciprocity
    z ρ σ Dt G hz hσ hv δ hδ hδz hb hcert (1+Complex.I*(2*π*k)) hs) j) i
  exact he

/-- The finite coefficient test implies actual pair reciprocity at every
positive radius, including contact. It does not by itself certify OZ. -/
theorem nonlinear_finite_certificate_actual_pair_reciprocity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hcert : NonlinearFiniteReciprocityCertificate z ρ σ Dt G)
    (i j : Fin N) (r : ℝ) (_hr : 0 < r) :
    nonlinearG z ρ σ Dt G i j r=nonlinearG z ρ σ Dt G j i r := by
  have hR : edgeHi σ j i=edgeHi σ i j := by unfold edgeHi; ring
  unfold nonlinearG
  rw [hR]
  split_ifs with h
  · rfl
  · rw [nonlinear_finite_certificate_actual_causal_reciprocity
      z ρ σ Dt G hz hσ hv δ hδ hδz hb hcert i j _ (sub_nonneg.mpr (not_lt.mp h))]

theorem nonlinear_finite_certificate_iff_actual_pair_reciprocity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i) (hv : vacMix ρ σ ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) :
    NonlinearFiniteReciprocityCertificate z ρ σ Dt G ↔
      ∀ i j r, 0 < r → nonlinearG z ρ σ Dt G i j r=nonlinearG z ρ σ Dt G j i r := by
  constructor
  · exact fun hc => nonlinear_finite_certificate_actual_pair_reciprocity
      z ρ σ Dt G hz (fun i => (hσ i).le) hv δ hδ hδz hb hc
  · intro hs
    by_contra hc
    exact nonlinear_failed_finite_certificate_excludes_pair_reciprocity
      z ρ σ Dt G hz hσ hv δ hδ hδz hb hc hs

end FMSA.ExactMSA.MultiTailMixture
