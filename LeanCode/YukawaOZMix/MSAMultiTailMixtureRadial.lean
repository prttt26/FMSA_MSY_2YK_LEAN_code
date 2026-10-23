import LeanCode.YukawaOZMix.MSAMultiTailMixtureShell
import LeanCode.YukawaOZMix.MSAMultiTailMixturePrimitiveExterior
import LeanCode.Analysis.OneContactCosine
import LeanCode.Analysis.EvenCosine
import LeanCode.YukawaOZMix.MixtureRowSum

/-! Actual ordered radial sine transform from the spatial primitive.
Full matrix Fourier identification additionally requires core reciprocity. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators FourierTransform ComplexOrder
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem shiftedRealExp_integrable (z R a : ℝ) (hz : 0 < z) :
    IntegrableOn (fun r => exp (-z*(r-R))) (Ioi a) := by
  have he : (fun r : ℝ => exp (-z*(r-R))) = (fun r => exp (z*R)*exp (-z*r)) := by
    funext r
    rw [← exp_add]
    congr 1
    ring
  rw [he]
  exact (integrableOn_exp_mul_Ioi (by linarith : -z<0) a).const_mul _

theorem shiftedRealExp_tendsto (z R : ℝ) (hz : 0 < z) :
    Tendsto (fun r => exp (-z*(r-R))) atTop (𝓝 0) := by
  have he : (fun r : ℝ => exp (-z*(r-R))) = (fun r => exp (z*R)*exp (-z*r)) := by
    funext r
    rw [← exp_add]
    congr 1
    ring
  rw [he]
  simpa using (Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hz))).const_mul (exp (z*R))

theorem rightPrimitiveReal_exterior_of_root (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i j : Fin N) (horder : σ j ≤ σ i)
    (r : ℝ) (hr : edgeHi σ i j < r) :
    rightPrimitiveReal z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j r =
        ∑ u, 2*π*K u i j/z u*exp (-z u*(r-edgeHi σ i j)) := by
  have hr0 : 0 < r := by unfold edgeHi at hr; linarith [hσ i, hσ j]
  have h := baxterPrimitive_exterior_of_root z hz ρ σ K Dt G hσ hroot i j r hr
  rw [baxterPrimitive_positive_eq_ofReal z ρ σ _ _ _ _ i j horder r hr0] at h
  have he := congrArg Complex.re h
  simpa only [Complex.ofReal_re, ← rightPrimitiveReal_eq_ordered_positive z ρ σ _ _ _ _ i j horder r hr0] using he

theorem rightPrimitiveReal_tendsto_zero_of_root (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i j : Fin N) (horder : σ j ≤ σ i) :
    Tendsto (rightPrimitiveReal z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j) atTop (𝓝 0) := by
  have h : Tendsto (fun r => ∑ u, 2*π*K u i j/z u*exp (-z u*(r-edgeHi σ i j))) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun u _ =>
      (shiftedRealExp_tendsto (z u) (edgeHi σ i j) (hz u)).const_mul (2*π*K u i j/z u))
  apply h.congr'
  filter_upwards [Ioi_mem_atTop (edgeHi σ i j)] with r hr
  exact (rightPrimitiveReal_exterior_of_root z hz ρ σ K Dt G hσ hroot i j horder r hr).symm

/-- Actual r*c has global positive-axis L1 at a supplied root. The core
regularity is internal and the exterior is the finite Yukawa sum. -/
theorem correlation_radius_integrable_of_root (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i j : Fin N) (horder : σ j ≤ σ i) :
    IntegrableOn (fun r => r*correlation z ρ σ (amplitudeA z ρ σ Dt G)
      (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j r) (Ioi 0) := by
  let R := edgeHi σ i j
  have hR : 0 ≤ R := by unfold R edgeHi; linarith [hσ i, hσ j]
  have hc := (orderedCorrelation_radius_intervalIntegrable z hz ρ σ
    (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) hσ i j horder
    0 R (le_refl _) hR).def'
  rw [uIoc_of_le hR] at hc
  have ht : IntegrableOn (fun r => r*correlation z ρ σ (amplitudeA z ρ σ Dt G)
      (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j r) (Ioi R) := by
    have hi : IntegrableOn (fun r => ∑ u, K u i j*exp (-z u*(r-R))) (Ioi R) :=
      integrable_finsetSum _ (fun u _ => (shiftedRealExp_integrable (z u) R R (hz u)).const_mul _)
    apply hi.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only
    rw [correlation_exterior_of_root z hz ρ σ K Dt G hσ hroot i j r hr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    field_simp [(hR.trans_lt hr).ne']
    rfl
  have he : Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi R := by
    ext x
    simp only [mem_Ioi, mem_Ioc, mem_union]
    constructor
    · intro hx
      by_cases h : x ≤ R
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (not_le.mp h)
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · exact hR.trans_lt hx
  rw [he, integrableOn_union]
  exact ⟨hc, ht⟩

theorem rightPrimitiveReal_integrable_positive (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (horder : σ j ≤ σ i) :
    IntegrableOn (rightPrimitiveReal z ρ σ A qp W C i j) (Ioi 0) := by
  have hi : Integrable (baxterPrimitive z ρ σ A qp W C i j) := by
    simpa using baxterPrimitive_axis_weighted_integrable z hz ρ σ A qp W C hσ 0 i j
  apply hi.re.integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  change (baxterPrimitive z ρ σ A qp W C i j r).re = _
  rw [baxterPrimitive_positive_eq_ofReal z ρ σ A qp W C i j horder r hr,
    rightPrimitiveReal_eq_ordered_positive z ρ σ A qp W C i j horder r hr]
  rfl

/-- Actual ordered cosine/sine transform identity, internally supplying
contact, origin, improper-integral and decay controls. -/
theorem rightPrimitiveReal_cosine_eq_radial_sine (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i j : Fin N) (horder : σ j ≤ σ i)
    (k : ℝ) (hk : k ≠ 0) :
    (∫ r in Ioi (0 : ℝ), rightPrimitiveReal z ρ σ (amplitudeA z ρ σ Dt G)
      (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j r * cos (k*r)) =
      (2*π/k) * ∫ r in Ioi (0 : ℝ), r*correlation z ρ σ (amplitudeA z ρ σ Dt G)
        (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j r * sin (k*r) := by
  have hσ0 : ∀ i, 0 ≤ σ i := fun i => (hσ i).le
  let P := rightPrimitiveReal z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
    (W z ρ Dt G) (C z ρ σ Dt G) i j
  let c := correlation z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
    (W z ρ Dt G) (C z ρ σ Dt G) i j
  obtain ⟨L, hL⟩ := rightPrimitiveReal_lipschitz z hz ρ σ
    (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) hσ0 i j
  have hpcos : IntegrableOn (fun r => P r*cos (k*r)) (Ioi 0) :=
    (rightPrimitiveReal_integrable_positive z hz ρ σ _ _ _ _ hσ0 i j horder).mul_bdd
      (by fun_prop) (Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using abs_cos_le_one (k*r)))
  have hcsin : IntegrableOn (fun r => r*c r*sin (k*r)) (Ioi 0) :=
    (correlation_radius_integrable_of_root z hz ρ σ K Dt G hσ0 hroot i j horder).mul_bdd
      (by fun_prop) (Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using abs_sin_le_one (k*r)))
  have hR : 0 < edgeHi σ i j := by unfold edgeHi; linarith [hσ i, hσ j]
  have h := FMSA.Analysis.cosine_of_one_contact P (fun r => 2*π*r*c r) (edgeHi σ i j) k hR hk
    hL.continuous (fun r hr hrR => by
      simpa only [neg_mul] using rightPrimitiveReal_hasDerivAt_positive z hz ρ σ
        (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) hσ0 i j horder r hr hrR)
    (rightPrimitiveReal_tendsto_zero_of_root z hz ρ σ K Dt G hσ0 hroot i j horder) hpcos
    (show IntegrableOn (fun r => (2*π*r*c r)*sin (k*r)) (Ioi 0) by
      have he : (fun r => (2*π*r*c r)*sin (k*r)) =
          (fun r => (2*π)*(r*c r*sin (k*r))) := by funext r; ring
      rw [he]
      exact hcsin.const_mul (2*π))
  convert! h using 1
  have he : (fun r => (2*π*r*c r)*sin (k*r)) =
      (fun r => (2*π)*(r*c r*sin (k*r))) := by funext r; ring
  rw [he, integral_const_mul]
  ring

/-- The actual radial transform equals the Q-side coefficient when the
actual full-line primitive is even. All analytic controls are internal. -/
theorem spectralBaxterC_eq_radial_of_ae_even (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i j : Fin N) (horder : σ j ≤ σ i)
    (heven : (fun r => baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G)
      (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j (-r)) =ᵐ[volume]
      baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G)
      (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j)
    (k : ℝ) (hk : k ≠ 0) :
    spectralBaxterC z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) k i j =
      (FMSA.HardSphere.radial_fourier
        (correlation z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
          (W z ρ Dt G) (C z ρ σ Dt G) i j) k : ℂ) := by
  have hσ0 : ∀ i, 0 ≤ σ i := fun i => (hσ i).le
  let P := baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
    (W z ρ Dt G) (C z ρ σ Dt G) i j
  let Pr := rightPrimitiveReal z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
    (W z ρ Dt G) (C z ρ σ Dt G) i j
  have hi : Integrable P := by
    simpa using baxterPrimitive_axis_weighted_integrable z hz ρ σ
      (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) hσ0 0 i j
  have hzW : FMSA.MixtureBaxter.zOfW (k/(2*π)) = Complex.I*k := by
    unfold FMSA.MixtureBaxter.zOfW
    push_cast
    field_simp
  have hf := fourier_of_ae_even P heven hi (k/(2*π))
  rw [FMSA.MixtureBaxter.fourier_eq_zOfW, hzW] at hf
  have hfP := baxterPrimitive_fourier z hz ρ σ
    (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) hσ0 k i j
  change (∫ r, P r * Complex.exp (-(Complex.I*k)*r)) = _ at hfP
  have hcos : (∫ r in Ioi (0 : ℝ), (cos (2*π*r*(k/(2*π))) : ℂ)*P r) =
      Complex.ofReal (∫ r in Ioi (0 : ℝ), Pr r*cos (k*r)) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    have he : 2*π*r*(k/(2*π)) = k*r := by field_simp
    rw [he]
    dsimp only [P, Pr]
    rw [baxterPrimitive_positive_eq_ofReal z ρ σ _ _ _ _ i j horder r hr,
      ← rightPrimitiveReal_eq_ordered_positive z ρ σ _ _ _ _ i j horder r hr]
    push_cast
    ring
  rw [← hfP]
  have hneg : (fun r : ℝ => P r * Complex.exp (-(Complex.I*k)*r)) =
      (fun r => P r * Complex.exp (-(Complex.I*k*r))) := by
    funext r
    congr 2
    ring
  rw [hneg, hf, hcos]
  have hs := rightPrimitiveReal_cosine_eq_radial_sine z hz ρ σ K Dt G hσ hroot i j horder k hk
  change (∫ r in Ioi (0 : ℝ), Pr r*cos (k*r)) = _ at hs
  rw [hs, FMSA.HardSphere.radial_fourier]
  push_cast
  ring

/-- Pointwise evenness remains a sufficient special case. -/
theorem spectralBaxterC_eq_radial_of_even (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i j : Fin N) (horder : σ j ≤ σ i)
    (heven : ∀ r, baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G)
      (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j (-r) =
      baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G)
      (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j r)
    (k : ℝ) (hk : k ≠ 0) :
    spectralBaxterC z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) k i j =
      (FMSA.HardSphere.radial_fourier
        (correlation z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
          (W z ρ Dt G) (C z ρ σ Dt G) i j) k : ℂ) :=
  spectralBaxterC_eq_radial_of_ae_even z hz ρ σ K Dt G hσ hroot i j horder
    (Eventually.of_forall heven) k hk

/-- Exterior reciprocity is supplied by the root and symmetric tail strengths;
only the finite-core reciprocity premise remains. -/
theorem spectralBaxterC_eq_radial_of_core_reciprocity
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (i j : Fin N) (horder : σ j ≤ σ i)
    (hcore : ∀ r ∈ Icc (-edgeHi σ i j) (edgeHi σ i j),
      baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
        (W z ρ Dt G) (C z ρ σ Dt G) i j r =
      baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
        (W z ρ Dt G) (C z ρ σ Dt G) j i r)
    (k : ℝ) (hk : k ≠ 0) :
    spectralBaxterC z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) k i j =
      (FMSA.HardSphere.radial_fourier
        (correlation z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
          (W z ρ Dt G) (C z ρ σ Dt G) i j) k : ℂ) := by
  apply spectralBaxterC_eq_radial_of_even z hz ρ σ K Dt G hσ hroot i j horder _ k hk
  intro r
  by_cases hr : edgeHi σ i j < |r|
  · exact baxterPrimitive_even_exterior z hz ρ σ K Dt G (fun i => (hσ i).le) hroot hK i j r hr
  · rw [baxterPrimitive_reflection]
    exact (hcore r (abs_le.mp (le_of_not_gt hr))).symm

/-- Every diagonal species entry has the actual radial factorization without
an evenness or core reciprocity premise, even in an unequal-size mixture. -/
theorem spectralBaxterC_diagonal_eq_radial
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i : Fin N) (k : ℝ) (hk : k ≠ 0) :
    spectralBaxterC z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) k i i =
      (FMSA.HardSphere.radial_fourier
        (correlation z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
          (W z ρ Dt G) (C z ρ σ Dt G) i i) k : ℂ) := by
  exact spectralBaxterC_eq_radial_of_even z hz ρ σ K Dt G hσ hroot i i (le_refl _)
    (fun r => baxterPrimitive_reflection z ρ σ _ _ _ _ i i r) k hk

/-- Use the larger diameter as the row for the actual positive-radius DCF. -/
def orderedRadialCorrelation (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (i j : Fin N) : ℝ → ℝ :=
  if σ j ≤ σ i then
    correlation z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j
  else
    correlation z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) j i

/-- Explicit remaining physical premise, limited to the finite core. -/
def CorePrimitiveReciprocity (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) : Prop :=
  ∀ i j r, r ∈ Icc (-edgeHi σ i j) (edgeHi σ i j) →
    baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j r =
    baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) j i r

theorem spectralBaxterC_eq_ordered_radial_of_core_reciprocity
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (hcore : CorePrimitiveReciprocity z ρ σ Dt G)
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    spectralBaxterC z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) k i j =
      (FMSA.HardSphere.radial_fourier (orderedRadialCorrelation z ρ σ K Dt G i j) k : ℂ) := by
  unfold orderedRadialCorrelation
  split_ifs with horder
  · exact spectralBaxterC_eq_radial_of_core_reciprocity z hz ρ σ K Dt G hσ hroot hK
      i j horder (hcore i j) k hk
  · have h := spectralBaxterC_eq_radial_of_core_reciprocity z hz ρ σ K Dt G hσ hroot hK
      j i (le_of_not_ge horder) (hcore j i) k hk
    rw [← spectralBaxterC_star_swap z ρ σ _ _ _ _ k i j, h]
    simp [Complex.star_def]

/-- Conditional actual radial matrix factorization. No global root existence,
strict stability, or proof of the finite-core reciprocity premise is implied. -/
theorem actualRadial_matrix_gram_of_core_reciprocity
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (hcore : CorePrimitiveReciprocity z ρ σ Dt G) (k : ℝ) (hk : k ≠ 0) :
    fourierFactor z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) k *
      (fourierFactor z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
        (W z ρ Dt G) (C z ρ σ Dt G) k).conjTranspose =
      1 - Matrix.of (fun i j => (Real.sqrt (ρ i) : ℂ)*(Real.sqrt (ρ j) : ℂ)*
        (FMSA.HardSphere.radial_fourier (orderedRadialCorrelation z ρ σ K Dt G i j) k : ℂ)) := by
  rw [fourierFactor_gram_eq z ρ σ _ _ _ _ k hρ]
  congr 1
  ext i j
  rw [Matrix.of_apply, Matrix.of_apply,
    spectralBaxterC_eq_ordered_radial_of_core_reciprocity z hz ρ σ K Dt G hσ hroot hK hcore k hk i j]

theorem actualRadial_matrix_posSemidef_of_core_reciprocity
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (hcore : CorePrimitiveReciprocity z ρ σ Dt G) (k : ℝ) (hk : k ≠ 0) :
    Matrix.PosSemidef (1 - Matrix.of (fun i j =>
      (Real.sqrt (ρ i) : ℂ)*(Real.sqrt (ρ j) : ℂ)*
        (FMSA.HardSphere.radial_fourier (orderedRadialCorrelation z ρ σ K Dt G i j) k : ℂ))) := by
  rw [← actualRadial_matrix_gram_of_core_reciprocity z hz ρ σ K Dt G hσ hρ hroot hK hcore k hk]
  exact fourierFactor_gram_posSemidef z ρ σ _ _ _ _ k

end FMSA.ExactMSA.MultiTailMixture
