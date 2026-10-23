import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearFourier

/-! Completed actual nonlinear renewal at the Fourier boundary. Only the
integrable excess is taken to the boundary; the affine background stays explicit. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def nonlinearCompletedZ (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  rdfMatrixLaplace (nonlinearRDFExcess z ρ σ Dt G) s+nonlinearComplexBackground σ s

theorem nonlinear_boundary_eq_of_positive_eq {E : Type*} [TopologicalSpace E] [T2Space E]
    (f g : ℝ → E) (hf : ContinuousWithinAt f (Ici 0) 0)
    (hg : ContinuousWithinAt g (Ici 0) 0) (he : ∀ a, 0 < a → f a=g a) : f 0=g 0 := by
  have hae : f =ᶠ[𝓝[>] (0 : ℝ)] g := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact he a ha
  exact tendsto_nhds_unique ((hf.mono Ioi_subset_Ici_self).congr' hae)
    (hg.mono Ioi_subset_Ici_self)

theorem nonlinearComplexJ_continuousAt_axis (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re=0) :
    ContinuousAt (fun a : ℝ => nonlinearComplexJ z ρ σ Dt G ((a : ℂ)+s)) 0 := by
  classical
  have hzs : ∀ u, s+(z u : ℂ) ≠ 0 :=
    nonlinear_complex_rate_nonzero z hz s (by rw [hsre])
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  simp only [nonlinearComplexJ, Matrix.of_apply]
  fun_prop (disch := simp [hs, hzs])

theorem nonlinearComplexBackground_continuousAt_axis (σ : Fin N → ℝ)
    (s : ℂ) (hs : s ≠ 0) :
    ContinuousAt (fun a : ℝ => nonlinearComplexBackground σ ((a : ℂ)+s)) 0 := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  simp only [nonlinearComplexBackground, Matrix.of_apply]
  fun_prop (disch := simp [hs])

theorem nonlinearCompletedZ_boundary (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re=0) :
    ContinuousWithinAt (fun a : ℝ => nonlinearCompletedZ z ρ σ Dt G ((a : ℂ)+s)) (Ici 0) 0 := by
  apply ContinuousWithinAt.add _ (nonlinearComplexBackground_continuousAt_axis σ s hs).continuousWithinAt
  apply continuousWithinAt_pi.mpr
  intro i
  apply continuousWithinAt_pi.mpr
  intro j
  exact FMSA.causalComplexLaplace_boundary _
    ((nonlinearRDFExcess_continuous z ρ σ Dt G).matrix_elem i j).continuousOn
    (nonlinearRDFExcess_integrable_of_weighted_budget z ρ σ Dt G hz hσ hv δ hδ hδz hb i j) s hsre

theorem nonlinearCausalKernel_complex_boundary (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (s : ℂ) (hsre : s.re=0) :
    ContinuousWithinAt (fun a : ℝ => rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G)
      ((a : ℂ)+s)) (Ici 0) 0 := by
  apply continuousWithinAt_pi.mpr
  intro i
  apply continuousWithinAt_pi.mpr
  intro j
  have hi : IntegrableOn (fun t => nonlinearCausalKernel z ρ σ Dt G t i j) (Ioi 0) := by
    change Integrable (fun t => ρ i*nonlinearRecenteredQ z ρ σ Dt G i j t) (volume.restrict (Ioi 0))
    simpa only [zero_mul, exp_zero, one_mul] using
      (nonlinearRecenteredQ_weighted_integrable z ρ σ Dt G hσ 0 hz i j).const_mul (ρ i)
  exact FMSA.causalComplexLaplace_boundary _
    ((nonlinearCausalKernel_continuous z ρ σ Dt G).matrix_elem i j).continuousOn hi s hsre

theorem nonlinearCompletedZ_actual_axis_renewal (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re=0) :
    nonlinearCompletedZ z ρ σ Dt G s*
      (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s)=
      (2*(π : ℂ))⁻¹ • nonlinearComplexJ z ρ σ Dt G s := by
  have he := nonlinear_boundary_eq_of_positive_eq
    (fun a : ℝ => nonlinearCompletedZ z ρ σ Dt G ((a : ℂ)+s)*
      (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) ((a : ℂ)+s)))
    (fun a : ℝ => (2*(π : ℂ))⁻¹ • nonlinearComplexJ z ρ σ Dt G ((a : ℂ)+s))
    ((nonlinearCompletedZ_boundary z ρ σ Dt G hz hσ hv δ hδ hδz hb s hs hsre).mul
      (continuousWithinAt_const.sub (nonlinearCausalKernel_complex_boundary z ρ σ Dt G hz hσ s hsre)))
    ((nonlinearComplexJ_continuousAt_axis z ρ σ Dt G hz s hs hsre).continuousWithinAt.const_smul _)
    (by
      intro a ha
      have hre : 0 < ((a : ℂ)+s).re := by simpa [hsre] using ha
      rw [nonlinearCompletedZ, ← nonlinearCausalG_complex_background z ρ σ Dt G hz hσ hv δ hδ hδz hb _ hre,
        nonlinearCausalG_actual_complex_laplace_renewal z ρ σ Dt G hz hσ hv δ hδ hδz hb _ hre]
      ext i j
      rw [nonlinearGSource_actual_complex_laplace z ρ σ Dt G hz _ hre i j,
        Matrix.smul_apply, smul_eq_mul, inv_mul_eq_div])
  simpa only [Complex.ofReal_zero, zero_add] using he

end FMSA.ExactMSA.MultiTailMixture
