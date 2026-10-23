import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearAutomaticWronskian
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearCoreCertificate

/-! The ordered radial DCF is the actual spectral Baxter coefficient at a
symmetric-strength BH root. Core reciprocity is derived from the automatic
finite Wronskian certificate, with no independent reciprocity assumption. -/
noncomputable section
open MeasureTheory Filter Topology

namespace FMSA.Paper.ActualRadialIdentification

open ExactMSA.MultiTailMixture MatrixQ0
variable {N : ℕ} {T : Type*} [Fintype T]

theorem root_primitive_reciprocity (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K Dt G : TailMatrix T N) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 <= sigma i) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (i j : Fin N) :
    baxterPrimitive z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) i j =ᵐ[volume]
    baxterPrimitive z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) j i := by
  classical
  exact nonlinear_finite_wronskian_actual_primitive_reciprocity z rho sigma Dt G hz hsigma
    (nonlinearRoot_automatic_finite_wronskian z rho sigma K Dt G hz hv hroot hK) i j

theorem root_core_reciprocity (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K Dt G : TailMatrix T N) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 <= sigma i) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) (hK : ∀ u i j, K u i j = K u j i) :
    AECorePrimitiveReciprocity z rho sigma Dt G := by
  intro i j
  filter_upwards [root_primitive_reciprocity z rho sigma K Dt G hz hsigma hv hroot hK i j]
    with r hr
  exact fun _ => hr

theorem root_radial_fourier (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K Dt G : TailMatrix T N) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    spectralBaxterC z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) k i j =
    (HardSphere.radial_fourier (orderedRadialCorrelation z rho sigma K Dt G i j) k : ℂ) := by
  exact spectralBaxterC_eq_ordered_radial_of_ae_core_reciprocity z hz rho sigma K Dt G hsigma
    hroot hK (root_core_reciprocity z rho sigma K Dt G hz (fun i => (hsigma i).le)
      hv hroot hK) k hk i j

/-- The Fourier identification holds throughout any local actual coupling
branch, with the strength rescaling and its symmetry discharged internally.
No convergence or interchange of Fourier integration and coupling derivatives
is assumed by this local equality. -/
theorem local_root_radial_fourier (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    (fun t => spectralBaxterC z rho sigma (amplitudeA z rho sigma (p t).1 (p t).2)
      (amplitudeQp z rho sigma (p t).1 (p t).2) (W z rho (p t).1 (p t).2)
      (C z rho sigma (p t).1 (p t).2) k i j) =ᶠ[𝓝 (0 : ℝ)]
    (fun t => (HardSphere.radial_fourier
      (orderedRadialCorrelation z rho sigma (t • K) (p t).1 (p t).2 i j) k : ℂ)) := by
  filter_upwards [hroot] with t ht
  apply root_radial_fourier z rho sigma (t • K) (p t).1 (p t).2 hz hsigma hv ht _ k hk i j
  intro u a b
  simp only [Pi.smul_apply, smul_eq_mul, hK u a b]

end FMSA.Paper.ActualRadialIdentification

/-- info: 'FMSA.Paper.ActualRadialIdentification.root_primitive_reciprocity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRadialIdentification.root_primitive_reciprocity

/-- info: 'FMSA.Paper.ActualRadialIdentification.root_core_reciprocity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRadialIdentification.root_core_reciprocity

/-- info: 'FMSA.Paper.ActualRadialIdentification.root_radial_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRadialIdentification.root_radial_fourier

/-- info: 'FMSA.Paper.ActualRadialIdentification.local_root_radial_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRadialIdentification.local_root_radial_fourier
