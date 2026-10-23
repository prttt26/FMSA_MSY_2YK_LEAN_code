import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearWronskian

/-! The finite Wronskian coefficient conditions imply actual primitive core
reciprocity by Fourier uniqueness. The core premise is discharged here. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators FourierTransform RealInnerProductSpace ComplexOrder
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primitiveBasisReal_continuousAt_off_lower_edge (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (Dt G : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : r ≠ edgeLo σ i j) :
    ContinuousAt (primitiveBasisReal z ρ σ (Dt,G) i j) r := by
  have hlin (a b : Fin N) (w : ℝ) (hw : w ≠ edgeLo σ a b) :
      ContinuousAt (fun r => ∑ c : BasisIndex ι, bhCoefficient z ρ σ (Dt,G) a b c*basisQ z σ c a b r) w :=
    tendsto_finsetSum _ (fun c _ => continuousAt_const.mul
      (basisQ_continuousAt_off_lower_edge z hz σ hσ c a b w hw))
  have hn : -r ≠ edgeLo σ j i := by
    intro he; apply hr; unfold edgeLo at he ⊢; linarith
  have href := (hlin j i (-r) hn).comp continuousAt_id.neg
  have hquad : Continuous (fun r => ∑ l, ρ l*∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
      (bhCoefficient z ρ σ (Dt,G) i l b*bhCoefficient z ρ σ (Dt,G) j l c)*basisQQ z σ b c i j l r) :=
    continuous_finsetSum _ (fun l _ => continuous_const.mul (continuous_finsetSum _ (fun b _ =>
      continuous_finsetSum _ (fun c _ => continuous_const.mul (basisQQ_continuous z hz σ hσ b c i j l)))))
  exact (hlin i j r hr).add href |>.sub hquad.continuousAt

theorem nonlinearActualPrimitive_ae_continuous (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (Dt G : TailMatrix ι N) (i j : Fin N) :
    ∀ᵐ r, ContinuousAt (baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G)
      (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j) r := by
  have he : baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j=
      fun r => (primitiveBasisReal z ρ σ (Dt,G) i j r : ℂ) := by
    funext r; exact baxterPrimitive_eq_basis z hz ρ σ hσ (Dt,G) i j r
  rw [he]
  filter_upwards [volume.ae_ne (edgeLo σ i j)] with r hr
  exact Complex.continuous_ofReal.continuousAt.comp
    (primitiveBasisReal_continuousAt_off_lower_edge z hz ρ σ hσ Dt G i j r hr)

theorem nonlinear_finite_wronskian_actual_primitive_reciprocity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hc : NonlinearFiniteWronskianCertificate z ρ σ Dt G) (i j : Fin N) :
    baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j =ᵐ[volume]
    baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) j i := by
  let P := fun a b => baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G)
    (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) a b
  have hi (a b : Fin N) : Integrable (P a b) := by
    simpa only [Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one] using
      baxterPrimitive_axis_weighted_integrable z hz ρ σ _ _ _ _ hσ 0 a b
  have hF (a b : Fin N) (w : ℝ) : 𝓕 (P a b) w=nonlinearActualFourierC z ρ σ Dt G (2*π*w) a b := by
    have he : FMSA.MixtureBaxter.zOfW w=Complex.I*(2*π*w : ℝ) := by
      unfold FMSA.MixtureBaxter.zOfW; push_cast; ring
    rw [FMSA.MixtureBaxter.fourier_eq_zOfW, he]
    simpa only [P, nonlinearActualFourierC, Matrix.of_apply, neg_mul] using
      baxterPrimitive_fourier z hz ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
        (W z ρ Dt G) (C z ρ σ Dt G) hσ (2*π*w) a b
  have hneq (w : ℝ) (hw : w ≠ 0) : 𝓕 (P i j) w=𝓕 (P j i) w := by
    rw [hF, hF]
    have he := congrFun (congrFun (nonlinear_finite_wronskian_actual_spectral_reciprocity
      z ρ σ Dt G hz hσ hc (2*π*w) (mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hw)) i) j
    exact he
  have hcont (a b : Fin N) : Continuous (𝓕 (P a b)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ (hi a b)
  have hzero : 𝓕 (P i j) 0=𝓕 (P j i) 0 :=
    nonlinear_boundary_eq_of_positive_eq _ _ (hcont i j).continuousAt.continuousWithinAt
      (hcont j i).continuousAt.continuousWithinAt (fun a ha => hneq a ha.ne')
  apply ae_eq_of_fourier_eq (hi i j) (hi j i) _
    (nonlinearActualPrimitive_ae_continuous z hz ρ σ hσ Dt G i j)
    (nonlinearActualPrimitive_ae_continuous z hz ρ σ hσ Dt G j i)
  funext w
  by_cases hw : w=0
  · rw [hw]; exact hzero
  · exact hneq w hw

theorem nonlinear_finite_wronskian_actual_core_reciprocity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hc : NonlinearFiniteWronskianCertificate z ρ σ Dt G) :
    AECorePrimitiveReciprocity z ρ σ Dt G := by
  intro i j
  filter_upwards [nonlinear_finite_wronskian_actual_primitive_reciprocity z ρ σ Dt G hz hσ hc i j] with r hr
  exact fun _ => hr

theorem nonlinear_actualRadial_posDef_of_finite_certificate_and_budget
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j=K u j i)
    (hc : NonlinearFiniteWronskianCertificate z ρ σ Dt G)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (k : ℝ) (hk : k ≠ 0) :
    Matrix.PosDef (1-Matrix.of (fun i j => (sqrt (ρ i) : ℂ)*(sqrt (ρ j) : ℂ)*
      (FMSA.HardSphere.radial_fourier (orderedRadialCorrelation z ρ σ K Dt G i j) k : ℂ))) :=
  nonlinear_actualRadial_posDef_of_core_and_budget z ρ σ K Dt G hz hσ hρ hroot hK
    (nonlinear_finite_wronskian_actual_core_reciprocity z ρ σ Dt G hz (fun i => (hσ i).le) hc)
    δ hδ hδz hb k hk

end FMSA.ExactMSA.MultiTailMixture
