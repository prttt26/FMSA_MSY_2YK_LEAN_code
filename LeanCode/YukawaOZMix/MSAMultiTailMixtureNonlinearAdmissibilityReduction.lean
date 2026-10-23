import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearSymplectic
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearRadialOZ

/-! The finite Wronskian certificate implies the separate finite RDF
reciprocity certificate, including zero and signed species densities. This
does not derive Wronskian admissibility from arbitrary BH roots. -/
noncomputable section
open MeasureTheory Set Real Filter Topology Polynomial
open FMSA.MatrixQ0 MSAMixture FMSA.HardSphere
open scoped BigOperators ComplexOrder
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nonlinear_finite_wronskian_complex_reciprocity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u)
    (hw : NonlinearFiniteWronskianCertificate z ρ σ Dt G)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re=0) :
    nonlinearComplexReciprocityResidual z ρ σ Dt G s=0 := by
  have h := nonlinear_finite_wronskian_residuals_zero z ρ σ Dt G hz hw s hs hsre
  have hm := nonlinear_finite_wronskian_residuals_zero z ρ σ Dt G hz hw (-s)
    (neg_ne_zero.mpr hs) (by simp [hsre])
  simp only [neg_neg] at hm
  exact nonlinearWronskian_implies_reciprocity
    (nonlinearComplexJ z ρ σ Dt G s) (nonlinearComplexL z ρ σ Dt G s)
    (nonlinearComplexJ z ρ σ Dt G (-s)) (nonlinearComplexL z ρ σ Dt G (-s))
    (fun i => (ρ i : ℂ)) s hs h.1 h.2 hm.2

theorem nonlinear_finite_wronskian_implies_finite_reciprocity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u)
    (hw : NonlinearFiniteWronskianCertificate z ρ σ Dt G) :
    NonlinearFiniteReciprocityCertificate z ρ σ Dt G := by
  intro i j n _
  let p := nonlinearReciprocityPolynomial z ρ σ Dt G i j
  have hInjective : Function.Injective (fun t : ℝ => Complex.I*(t : ℂ)) := by
    intro t v he
    have hh := mul_left_cancel₀ Complex.I_ne_zero he
    exact Complex.ofReal_injective hh
  have hp : p.map (algebraMap ℝ ℂ)=0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((Set.Ioi_infinite (0 : ℝ)).image hInjective.injOn).mono
    rintro w ⟨t, ht, rfl⟩
    change (p.map (algebraMap ℝ ℂ)).eval (Complex.I*t)=0
    rw [Polynomial.eval_map]
    have hs : Complex.I*(t : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ne_of_gt ht)
    have hR := nonlinear_finite_wronskian_complex_reciprocity
      z ρ σ Dt G hz hw (Complex.I*t) hs (by simp)
    rw [show p=nonlinearReciprocityPolynomial z ρ σ Dt G i j from rfl,
      nonlinearReciprocityPolynomial_complex_eval z ρ σ Dt G hz (Complex.I*t) hs (by simp),
      hR, Matrix.zero_apply, mul_zero]
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff n) hp
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, Complex.coe_algebraMap,
    Complex.ofReal_eq_zero] using hc

theorem nonlinearH_actual_radial_OZ_of_finite_wronskian
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i) (hv : vacMix ρ σ ≠ 0)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j=K u j i)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hw : NonlinearFiniteWronskianCertificate z ρ σ Dt G) (i j : Fin N) :
    nonlinearH z ρ σ Dt G i j =ᵐ[volume.restrict (Ioi 0)] fun r =>
      orderedRadialCorrelation z ρ σ K Dt G i j r+
        radialMixtureConv (orderedRadialCorrelation z ρ σ K Dt G) (nonlinearH z ρ σ Dt G) ρ i j r :=
  nonlinearH_actual_radial_OZ_of_finite_certificates z ρ σ K Dt G hz hσ hv hroot hK
    δ hδ hδz hb (nonlinear_finite_wronskian_implies_finite_reciprocity z ρ σ Dt G hz hw) hw i j

theorem nonlinearMixtureRDF_single_finite_admissibility_certificate
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hv : vacMix ρ σ ≠ 0) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j=K u j i)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hw : NonlinearFiniteWronskianCertificate z ρ σ Dt G) :
    ((∀ i j r, r < edgeHi σ i j → nonlinearG z ρ σ Dt G i j r=0) ∧
    (∀ i j, Integrable (fun r => r*nonlinearH z ρ σ Dt G i j r)) ∧
    (∀ u i j, (∫ r in Ioi (0 : ℝ), exp (-z u*r)*(r*nonlinearG z ρ σ Dt G i j r))=
      exp (-z u*edgeHi σ i j)*G u i j) ∧
    (∀ i j r, 0 < r → nonlinearG z ρ σ Dt G i j r=nonlinearG z ρ σ Dt G j i r) ∧
    (∀ i j, nonlinearH z ρ σ Dt G i j =ᵐ[volume.restrict (Ioi 0)] fun r =>
      orderedRadialCorrelation z ρ σ K Dt G i j r+
        radialMixtureConv (orderedRadialCorrelation z ρ σ K Dt G) (nonlinearH z ρ σ Dt G) ρ i j r)) ∧
    (∀ k : ℝ, k ≠ 0 → Matrix.PosDef (1-Matrix.of (fun i j =>
      (sqrt (ρ i) : ℂ)*(sqrt (ρ j) : ℂ)*
        (radial_fourier (orderedRadialCorrelation z ρ σ K Dt G i j) k : ℂ)))) := by
  have hr := nonlinear_finite_wronskian_implies_finite_reciprocity z ρ σ Dt G hz hw
  exact ⟨nonlinearMixtureRDF_finite_admissibility_certificate z ρ σ K Dt G hz hσ hv
    hroot hK δ hδ hδz hb hr hw,
    nonlinear_actualRadial_posDef_of_finite_certificate_and_budget z ρ σ K Dt G hz hσ
      hρ hroot hK hw δ hδ.le hδz hb⟩

end FMSA.ExactMSA.MultiTailMixture
