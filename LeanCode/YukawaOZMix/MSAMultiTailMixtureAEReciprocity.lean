import LeanCode.YukawaOZMix.MSAMultiTailMixtureRadial
import LeanCode.YukawaOZMix.MixtureDCFAEInjective
import LeanCode.YukawaOZMix.MSAMultiTailMixtureFamily

/-! Reciprocity relevant to the radial transform is an a.e. statement.
Closed support windows may assign a removable spike at a size-asymmetry knot.
The actual hard-sphere seed is bridged to the independent general-N HS kernel.
This does not assert reciprocity of arbitrary real BH roots or of the full
first-order tangent. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture
open FMSA.MatrixQ0
open scoped BigOperators FourierTransform ComplexOrder
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def AECorePrimitiveReciprocity (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) : Prop :=
  ∀ i j, ∀ᵐ r ∂volume, r ∈ Icc (-edgeHi σ i j) (edgeHi σ i j) →
    baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j r =
    baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) j i r

theorem corePrimitiveReciprocity_ae (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (h : CorePrimitiveReciprocity z ρ σ Dt G) :
    AECorePrimitiveReciprocity z ρ σ Dt G :=
  fun i j => Eventually.of_forall (fun r => h i j r)

theorem spectralBaxterC_eq_ordered_radial_of_ae_core_reciprocity
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (hcore : AECorePrimitiveReciprocity z ρ σ Dt G)
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    spectralBaxterC z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) k i j =
      (FMSA.HardSphere.radial_fourier (orderedRadialCorrelation z ρ σ K Dt G i j) k : ℂ) := by
  have heven : ∀ a b, (fun r => baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G)
      (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) a b (-r)) =ᵐ[volume]
      baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
        (W z ρ Dt G) (C z ρ σ Dt G) a b := by
    intro a b
    filter_upwards [hcore a b] with r hr
    by_cases he : edgeHi σ a b < |r|
    · exact baxterPrimitive_even_exterior z hz ρ σ K Dt G (fun i => (hσ i).le)
        hroot hK a b r he
    · rw [baxterPrimitive_reflection]
      exact (hr (abs_le.mp (le_of_not_gt he))).symm
  unfold orderedRadialCorrelation
  split_ifs with horder
  · exact spectralBaxterC_eq_radial_of_ae_even z hz ρ σ K Dt G hσ hroot i j horder
      (heven i j) k hk
  · have h := spectralBaxterC_eq_radial_of_ae_even z hz ρ σ K Dt G hσ hroot j i
      (le_of_not_ge horder) (heven j i) k hk
    rw [← spectralBaxterC_star_swap z ρ σ _ _ _ _ k i j, h]
    simp [Complex.star_def]

theorem actualRadial_matrix_gram_of_ae_core_reciprocity
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (hcore : AECorePrimitiveReciprocity z ρ σ Dt G) (k : ℝ) (hk : k ≠ 0) :
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
    spectralBaxterC_eq_ordered_radial_of_ae_core_reciprocity z hz ρ σ K Dt G hσ hroot hK hcore k hk i j]

theorem actualRadial_matrix_posSemidef_of_ae_core_reciprocity
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (hcore : AECorePrimitiveReciprocity z ρ σ Dt G) (k : ℝ) (hk : k ≠ 0) :
    Matrix.PosSemidef (1 - Matrix.of (fun i j =>
      (Real.sqrt (ρ i) : ℂ)*(Real.sqrt (ρ j) : ℂ)*
        (FMSA.HardSphere.radial_fourier (orderedRadialCorrelation z ρ σ K Dt G i j) k : ℂ))) := by
  rw [← actualRadial_matrix_gram_of_ae_core_reciprocity z hz ρ σ K Dt G hσ hρ hroot hK hcore k hk]
  exact fourierFactor_gram_posSemidef z ρ σ _ _ _ _ k

theorem q_zero_eq_physMixN (z : ι → ℝ) (ρ σ : Fin N → ℝ) (G : TailMatrix ι N)
    (hσ : ∀ i, 0 < σ i) (i j : Fin N) (r : ℝ) :
    q z σ (amplitudeA z ρ σ 0 G) (amplitudeQp z ρ σ 0 G)
      (W z ρ 0 G) (C z ρ σ 0 G) i j r =
      (FMSA.MixtureBaxter.physMixN ρ σ hσ).q0MixEntry i j r := by
  simp only [q, amplitudeA_zero, amplitudeQp_zero, W, C, Wt, Ct, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, sub_zero, zero_mul, add_zero]
  unfold FMSA.HSMix.q0MixEntry FMSA.HSMix.lam FMSA.HSMix.R
    FMSA.MixtureBaxter.physMixN
  change (if r < edgeLo σ i j then 0 else if r ≤ edgeHi σ i j then _ else 0) =
    (Icc (edgeLo σ i j) (edgeHi σ i j)).indicator
      (fun t => Q0phys ρ σ i j * (t-edgeHi σ i j) +
        Qppphys ρ σ j j * (t-edgeHi σ i j)^2 / 2) r
  split_ifs with hlo hhi
  · rw [indicator_of_notMem (by intro h; exact (not_le_of_gt hlo) h.1)]
  · rw [indicator_of_mem (show r ∈ Icc (edgeLo σ i j) (edgeHi σ i j) from
      ⟨le_of_not_gt hlo, hhi⟩)]
    ring
  · rw [indicator_of_notMem (by intro h; exact hhi h.2)]

theorem baxterPrimitive_zero_weighted_eq_physMixN (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (i j : Fin N) (r : ℝ) :
    (rhoGeoPhys ρ i j : ℂ) *
      baxterPrimitive z ρ σ (amplitudeA z ρ σ 0 G) (amplitudeQp z ρ σ 0 G)
        (W z ρ 0 G) (C z ρ σ 0 G) i j r =
      FMSA.MixtureBaxter.matDCFfullN ρ σ hσ i j r := by
  have hs : rhoGeoPhys ρ j i = rhoGeoPhys ρ i j := by
    simp only [rhoGeoPhys, mul_comm]
  have hc : FMSA.MixtureBaxter.matCorrWN (FMSA.MixtureBaxter.physMixN ρ σ hσ)
      (rhoGeoPhys ρ) i j r = (rhoGeoPhys ρ i j : ℂ) *
        ∑ l, (ρ l : ℂ) * qCrossCorr z σ (amplitudeA z ρ σ 0 G)
          (amplitudeQp z ρ σ 0 G) (W z ρ 0 G) (C z ρ σ 0 G) i j l r := by
    simp only [FMSA.MixtureBaxter.matCorrWN, Finset.mul_sum, qCrossCorr,
      ← q_zero_eq_physMixN z ρ σ G hσ]
    apply Finset.sum_congr rfl
    intro l hl
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae (Eventually.of_forall _)
    intro t
    have hp := congrArg Complex.ofReal (rhoGeoPhys_mul_eq ρ hρ i j l)
    push_cast at hp
    calc
      _ = ((rhoGeoPhys ρ i l : ℂ)*(rhoGeoPhys ρ j l : ℂ)) *
        ((q z σ _ _ _ _ i l t : ℂ)*(q z σ _ _ _ _ j l (t-r) : ℂ)) := by ring
      _ = _ := by rw [hp]; ring
  simp only [FMSA.MixtureBaxter.matDCFfullN, baxterPrimitive,
    q_zero_eq_physMixN z ρ σ G hσ, hs, hc]
  ring

/-- At positive species densities the density weights cancel, so the actual
unweighted full-space PY primitive is reciprocal a.e. No reciprocity premise
is supplied. Zero-density species are outside this cancellation theorem. -/
theorem baxterPrimitive_zero_ae_reciprocity (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 < ρ i)
    (hvac : vacMix ρ σ ≠ 0) (i j : Fin N) :
    baxterPrimitive z ρ σ (amplitudeA z ρ σ 0 G) (amplitudeQp z ρ σ 0 G)
      (W z ρ 0 G) (C z ρ σ 0 G) i j =ᵐ[volume]
    baxterPrimitive z ρ σ (amplitudeA z ρ σ 0 G) (amplitudeQp z ρ σ 0 G)
      (W z ρ 0 G) (C z ρ σ 0 G) j i := by
  have hs : rhoGeoPhys ρ j i = rhoGeoPhys ρ i j := by simp only [rhoGeoPhys, mul_comm]
  have hn : (rhoGeoPhys ρ i j : ℂ) ≠ 0 := by
    exact_mod_cast (sqrt_pos.2 (mul_pos (hρ i) (hρ j))).ne'
  filter_upwards [FMSA.MixtureBaxter.matDCF_ae_symmN ρ σ hσ (fun i => (hρ i).le) hvac i j]
    with r hr
  apply mul_left_cancel₀ hn
  rw [baxterPrimitive_zero_weighted_eq_physMixN z ρ σ G hσ (fun i => (hρ i).le),
    ← hs, baxterPrimitive_zero_weighted_eq_physMixN z ρ σ G hσ (fun i => (hρ i).le)]
  exact hr

theorem aeCorePrimitiveReciprocity_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (G : TailMatrix ι N) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 < ρ i)
    (hvac : vacMix ρ σ ≠ 0) : AECorePrimitiveReciprocity z ρ σ 0 G := by
  intro i j
  filter_upwards [baxterPrimitive_zero_ae_reciprocity z ρ σ G hσ hρ hvac i j] with r hr
  exact fun _ => hr

/-- The actual zero-coupling seed satisfies the BH equations internally. -/
theorem baseSeed_isRoot (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    IsRoot z ρ σ 0 0 (baseSeed z ρ σ) := by
  have h := (residual_eq_zero_iff z ρ σ (0 : TailMatrix ι N) 0
    (baseSeed z ρ σ) 0).mp
    (residual_base z ρ σ 0 (baseSecond_isUnit_det z ρ σ hz hvac hρ hσ))
  simpa only [zero_smul] using h

/-- All species pairs of the actual PY seed have radial Q-factorization.
No finite-core reciprocity premise remains. Densities are strictly positive
here because the independent weighted HS certificate is canceled entrywise. -/
theorem spectralBaxterC_zero_eq_ordered_radial (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    spectralBaxterC z ρ σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ))
      (amplitudeQp z ρ σ 0 (baseSeed z ρ σ)) (W z ρ 0 (baseSeed z ρ σ))
      (C z ρ σ 0 (baseSeed z ρ σ)) k i j =
      (FMSA.HardSphere.radial_fourier
        (orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j) k : ℂ) := by
  exact spectralBaxterC_eq_ordered_radial_of_ae_core_reciprocity z hz ρ σ 0 0
    (baseSeed z ρ σ) hσ (baseSeed_isRoot z ρ σ hz hvac (fun i => (hρ i).le) hσ)
    (by intros; rfl) (aeCorePrimitiveReciprocity_zero z ρ σ _ hσ hρ hvac.ne') k hk i j

theorem actualRadial_zero_matrix_posSemidef (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (k : ℝ) (hk : k ≠ 0) :
    Matrix.PosSemidef (1 - Matrix.of (fun i j =>
      (Real.sqrt (ρ i) : ℂ)*(Real.sqrt (ρ j) : ℂ)*
        (FMSA.HardSphere.radial_fourier
          (orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j) k : ℂ))) := by
  exact actualRadial_matrix_posSemidef_of_ae_core_reciprocity z hz ρ σ 0 0
    (baseSeed z ρ σ) hσ (fun i => (hρ i).le)
    (baseSeed_isRoot z ρ σ hz hvac (fun i => (hρ i).le) hσ) (by intros; rfl)
    (aeCorePrimitiveReciprocity_zero z ρ σ _ hσ hρ hvac.ne') k hk

/-- A zero-density, unequal-size HS example, with no Yukawa labels. Its
single-point discrepancy is an endpoint convention, not a physical anomaly. -/
def vacuumUnequalPrimitive (i j : Fin 2) (r : ℝ) : ℂ :=
  baxterPrimitive (fun u : Fin 0 => u.elim0) 0 ![1, 2]
    (amplitudeA (fun u : Fin 0 => u.elim0) 0 ![1, 2] 0 0)
    (amplitudeQp (fun u : Fin 0 => u.elim0) 0 ![1, 2] 0 0)
    (W (fun u : Fin 0 => u.elim0) 0 0 0)
    (C (fun u : Fin 0 => u.elim0) 0 ![1, 2] 0 0) i j r

theorem vacuumUnequalPrimitive_point_values :
    vacuumUnequalPrimitive 0 1 (1/2) = (-4*π : ℂ) ∧
    vacuumUnequalPrimitive 1 0 (1/2) = (-2*π : ℂ) := by
  constructor <;>
    simp [vacuumUnequalPrimitive, baxterPrimitive, q, amplitudeA, amplitudeQp,
      W, C, Q0phys, Qppphys, vacMix, etaMix, xi2, edgeLo, edgeHi] <;>
    norm_num <;> push_cast <;> ring

theorem vacuumUnequalPrimitive_not_pointwise_reciprocal :
    vacuumUnequalPrimitive 0 1 (1/2) ≠ vacuumUnequalPrimitive 1 0 (1/2) := by
  rw [vacuumUnequalPrimitive_point_values.1, vacuumUnequalPrimitive_point_values.2]
  intro h
  have hreal := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hreal
  norm_num at hreal

end FMSA.ExactMSA.MultiTailMixture
