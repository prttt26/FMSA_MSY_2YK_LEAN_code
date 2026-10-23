import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearAutomaticWronskian
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearAdmissibilityReduction

/-! Actual-root RDF/OZ and finite-k stability with automatic algebraic admissibility. -/
noncomputable section
open MeasureTheory Set Real Filter Topology Polynomial
open FMSA.MatrixQ0 MSAMixture FMSA.HardSphere
open scoped BigOperators ComplexOrder
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nonlinearMixtureRDF_automatic_admissibility_certificate
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hv : vacMix ρ σ ≠ 0) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j = K u j i)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    :
    ((∀ i j r, r < edgeHi σ i j → nonlinearG z ρ σ Dt G i j r = 0) ∧
    (∀ i j, Integrable (fun r => r*nonlinearH z ρ σ Dt G i j r)) ∧
    (∀ u i j, (∫ r in Ioi (0 : ℝ), exp (-z u*r)*(r*nonlinearG z ρ σ Dt G i j r)) =
      exp (-z u*edgeHi σ i j)*G u i j) ∧
    (∀ i j r, 0 < r → nonlinearG z ρ σ Dt G i j r = nonlinearG z ρ σ Dt G j i r) ∧
    (∀ i j, nonlinearH z ρ σ Dt G i j =ᵐ[volume.restrict (Ioi 0)] fun r =>
      orderedRadialCorrelation z ρ σ K Dt G i j r+
        radialMixtureConv (orderedRadialCorrelation z ρ σ K Dt G) (nonlinearH z ρ σ Dt G) ρ i j r)) ∧
    (∀ k : ℝ, k ≠ 0 → Matrix.PosDef (1-Matrix.of (fun i j =>
      (sqrt (ρ i) : ℂ)*(sqrt (ρ j) : ℂ)*
        (radial_fourier (orderedRadialCorrelation z ρ σ K Dt G i j) k : ℂ)))) := by
  exact nonlinearMixtureRDF_single_finite_admissibility_certificate
    z ρ σ K Dt G hz hσ hρ hv hroot hK δ hδ hδz hb
    (nonlinearRoot_automatic_finite_wronskian z ρ σ K Dt G hz hv hroot hK)

end FMSA.ExactMSA.MultiTailMixture
