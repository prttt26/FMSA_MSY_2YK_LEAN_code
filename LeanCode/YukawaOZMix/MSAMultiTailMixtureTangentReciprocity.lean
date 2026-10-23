import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPFactorTangent
import LeanCode.YukawaOZMix.MixtureDCFAEInjective

/-! Reciprocity of the actual first-order primitive: transfer the internally
proved spectral tangent symmetry by L1 Fourier injectivity. Endpoint values
of closed support representatives are allowed to differ on null sets. -/
noncomputable section
open MeasureTheory Real Set Filter Topology MSAMixture FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem q_continuousAt_off_lower_edge (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (r : ℝ) (hr : r ≠ edgeLo σ i j) :
    ContinuousAt (q z σ A qp W C i j) r := by
  rcases lt_or_gt_of_ne hr with h | h
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) r).congr
    filter_upwards [eventually_lt_nhds h] with t ht
    simp [q, ht]
  · obtain ⟨L, hL⟩ := qRight_lipschitz z hz σ A qp W C hσ i j
    apply hL.continuous.continuousAt.congr
    filter_upwards [eventually_gt_nhds h] with t ht
    exact qRight_eq_q z σ A qp W C i j t ht.le

theorem basisQ_continuousAt_off_lower_edge (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (b : BasisIndex ι) (i j : Fin N)
    (r : ℝ) (hr : r ≠ edgeLo σ i j) : ContinuousAt (basisQ z σ b i j) r := by
  have he : basisQ z σ b i j = q (fun _ : Fin 1 => basisRate z b) σ
      (fun _ => basisA b) (fun _ _ => basisQp b) (fun _ _ _ => basisW b)
      (fun _ _ _ => basisC b) i j := by funext r; exact basisQ_eq_single_q z σ b i j r
  rw [he]
  exact q_continuousAt_off_lower_edge (fun _ : Fin 1 => basisRate z b)
    (fun _ => basisRate_pos z hz b) σ _ _ _ _ hσ i j r hr

theorem basisQQ_continuous (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (b c : BasisIndex ι) (i j l : Fin N) :
    Continuous (basisQQ z σ b c i j l) := by
  obtain ⟨M, hM⟩ := basisQ_bounded z hz σ hσ c j l
  apply continuous_iff_continuousAt.mpr
  intro r
  unfold basisQQ
  apply continuousAt_of_dominated (bound := fun t => M*‖basisQ z σ b i l t‖)
  · exact Eventually.of_forall (fun w => (basisQQ_integrable z hz σ hσ b c i j l w).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro w
    filter_upwards with t
    rw [norm_mul]
    calc
      _ ≤ ‖basisQ z σ b i l t‖*M := mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using hM (t-w)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  · exact (basisQ_integrable z hz σ hσ b i l).norm.const_mul M
  · filter_upwards [volume.ae_ne (r+edgeLo σ j l)] with t ht
    have hneq : t-r ≠ edgeLo σ j l := by intro he; apply ht; linarith
    exact continuousAt_const.mul ((basisQ_continuousAt_off_lower_edge z hz σ hσ c j l (t-r) hneq).comp
      (continuousAt_const.sub continuousAt_id))

theorem linearizedPrimitiveReal_continuousAt_off_edges (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G0 : TailMatrix ι N) (i j : Fin N)
    (r : ℝ) (hr : r ≠ edgeLo σ i j) :
    ContinuousAt (linearizedPrimitiveReal z ρ σ D G0 i j) r := by
  have hlin (a b : Fin N) (w : ℝ) (hw : w ≠ edgeLo σ a b) :
      ContinuousAt (fun r => ∑ c : BasisIndex ι, coefficientSlope z ρ σ D G0 a b c*basisQ z σ c a b r) w :=
    tendsto_finsetSum _ (fun c _ => continuousAt_const.mul
      (basisQ_continuousAt_off_lower_edge z hz σ hσ c a b w hw))
  have hn : -r ≠ edgeLo σ j i := by
    intro he
    apply hr
    unfold edgeLo at he ⊢
    linarith
  have href := (hlin j i (-r) hn).comp continuousAt_id.neg
  have hquad : Continuous (fun r => ∑ l, ρ l*∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
      (coefficientSlope z ρ σ D G0 i l b*bhCoefficient z ρ σ (0, G0) j l c+
        bhCoefficient z ρ σ (0, G0) i l b*coefficientSlope z ρ σ D G0 j l c)*basisQQ z σ b c i j l r) :=
    continuous_finsetSum _ (fun l _ => continuous_const.mul (continuous_finsetSum _ (fun b _ =>
      continuous_finsetSum _ (fun c _ => continuous_const.mul (basisQQ_continuous z hz σ hσ b c i j l)))))
  exact (hlin i j r hr).add href |>.sub hquad.continuousAt

theorem linearizedPrimitiveReal_ae_continuous (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G0 : TailMatrix ι N) (i j : Fin N) :
    ∀ᵐ r, ContinuousAt (fun r => (linearizedPrimitiveReal z ρ σ D G0 i j r : ℂ)) r := by
  filter_upwards [volume.ae_ne (edgeLo σ i j)] with r hr
  exact Complex.continuous_ofReal.continuousAt.comp
    (linearizedPrimitiveReal_continuousAt_off_edges z hz ρ σ hσ D G0 i j r hr)

theorem linearizedPrimitiveReal_complex_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G0 : TailMatrix ι N) (i j : Fin N) :
    Integrable (fun r => (linearizedPrimitiveReal z ρ σ D G0 i j r : ℂ)) := by
  simpa only [Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one] using
    linearizedPrimitiveReal_axis_weighted_integrable z hz ρ σ hσ D G0 0 i j

/-- Actual first-order same-radius reciprocity, throughout the full core and
exterior up to a null set. Positive species densities are not required. -/
theorem linearizedPrimitiveReal_ae_reciprocity (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) :
    linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j =ᵐ[volume]
      linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) j i := by
  have hc := FMSA.MixtureBaxter.ae_eq_of_zOfW_transform_offdiag
    (linearizedPrimitiveReal_complex_integrable z hz ρ σ (fun i => (hσ i).le)
      (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j)
    (linearizedPrimitiveReal_complex_integrable z hz ρ σ (fun i => (hσ i).le)
      (firstOrderDt z ρ σ K) (baseSeed z ρ σ) j i)
    (linearizedPrimitiveReal_ae_continuous z hz ρ σ (fun i => (hσ i).le)
      (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j)
    (linearizedPrimitiveReal_ae_continuous z hz ρ σ (fun i => (hσ i).le)
      (firstOrderDt z ρ σ K) (baseSeed z ρ σ) j i)
    (fun w hw => ?_)
  · filter_upwards [hc] with r hr
    exact Complex.ofReal_injective hr
  · have hk : 2*π*w ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hw
    have he : FMSA.MixtureBaxter.zOfW w = Complex.I*(2*π*w : ℝ) := by
      unfold FMSA.MixtureBaxter.zOfW
      push_cast
      ring
    simp only [he, neg_mul]
    have hf (a b : Fin N) := linearizedPrimitiveReal_fourier z hz ρ σ (fun i => (hσ i).le)
      (firstOrderDt z ρ σ K) (baseSeed z ρ σ) (2*π*w) a b
    simp only [neg_mul] at hf
    rw [hf, hf, linearizedSpectralPrimitive_eq_spectralC z hz ρ σ (fun i => (hσ i).le),
      linearizedSpectralPrimitive_eq_spectralC z hz ρ σ (fun i => (hσ i).le)]
    exact linearizedSpectralC_symmetric z ρ σ K hz hv hρ hσ hK (2*π*w) hk i j

theorem linearizedPrimitiveReal_ae_even (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) :
    ∀ᵐ r, linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j (-r) =
      linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j r := by
  filter_upwards [linearizedPrimitiveReal_ae_reciprocity z ρ σ K hz hv hρ hσ hK i j] with r hr
  rw [linearizedPrimitiveReal_reflection z hz ρ σ (fun i => (hσ i).le)
    (firstOrderDt z ρ σ K) (baseSeed z ρ σ) j i r]
  exact hr.symm

end FMSA.ExactMSA.MultiTailMixture
