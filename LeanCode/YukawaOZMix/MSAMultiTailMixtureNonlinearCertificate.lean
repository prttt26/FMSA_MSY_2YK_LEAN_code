import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearBoundary
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearFiniteTest

/-! Joint actual nonlinear reconstruction checkpoint. The capstone certifies
hard core, radius L1 and actual BH moments. It deliberately does not contain a
positive-density radial OZ field, which has not yet been derived from the root. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem nonlinearMixtureRDF_core_moments_decay_certificate (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i)
    (hv : vacMix ρ σ ≠ 0) (hroot : IsRoot z ρ σ K Dt G)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) :
    (∀ i j r, r < edgeHi σ i j → nonlinearG z ρ σ Dt G i j r=0) ∧
      (∀ i j r, 0 < r → r < edgeHi σ i j → nonlinearH z ρ σ Dt G i j r= -1) ∧
      (∀ i j, Integrable (fun r => r*nonlinearH z ρ σ Dt G i j r)) ∧
      (∀ u i j, (∫ r in Ioi (0 : ℝ), exp (-z u*r)*(r*nonlinearG z ρ σ Dt G i j r))=
        exp (-z u*edgeHi σ i j)*G u i j) :=
  ⟨nonlinearG_hardcore z ρ σ Dt G,
    nonlinearH_hardcore z ρ σ Dt G,
    nonlinearH_radius_integrable_of_weighted_budget z ρ σ Dt G hz (fun i => (hσ i).le) hv δ hδ hδz hb,
    nonlinearG_amplitude_eq_actual_radial_laplace z ρ σ K Dt G hz hσ hv hroot δ hδ hδz hb⟩

end FMSA.ExactMSA.MultiTailMixture
