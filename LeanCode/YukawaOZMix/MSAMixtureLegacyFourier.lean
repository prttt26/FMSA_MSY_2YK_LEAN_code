import LeanCode.YukawaOZMix.MSAMixtureLegacySingleTail
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearAutomaticWronskian
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearCoreCertificate

/-! Kernel proofs connecting the original single-tail Fourier factors to
the actual radial DCF. No computation-backed closure axiom is assumed. -/
noncomputable section
open Real MeasureTheory Set Filter MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

theorem legacyRadial_matrix_gram (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hv : vacMix ρ σ ≠ 0) (hroot : MixBHRootUneq z ρ σ Gt Dt K)
    (hK : ∀ i j, K i j = K j i) (k : ℝ) (hk : k ≠ 0) :
    FtMSAuneq z ρ σ Gt Dt (Complex.I * k) *
      (FtMSAuneq z ρ σ Gt Dt (-(Complex.I * k))).transpose =
      1 - Matrix.of (fun i j => (sqrt (ρ i * ρ j) : ℂ) *
        (FMSA.HardSphere.radial_fourier (legacyRadial z ρ σ Gt Dt K i j) k : ℂ)) := by
  have hr := (isRoot_single_iff z hz.ne' ρ σ Gt Dt K).mpr hroot
  have hc := nonlinearRoot_automatic_finite_wronskian (fun _ : Unit => z) ρ σ
    (fun _ => K) (fun _ => Dt) (fun _ => Gt) (fun _ => hz) hv hr (fun _ => hK)
  have hp := nonlinear_finite_wronskian_actual_core_reciprocity (fun _ : Unit => z)
    ρ σ (fun _ => Dt) (fun _ => Gt) (fun _ => hz) (fun i => (hσ i).le) hc
  have h := actualRadial_matrix_gram_of_ae_core_reciprocity (fun _ : Unit => z)
    (fun _ => hz) ρ σ (fun _ => K) (fun _ => Dt) (fun _ => Gt) hσ hρ hr (fun _ => hK) hp k hk
  rw [fourierFactor_single z hz ρ σ Gt Dt (fun i => (hσ i).le) hρ k hk,
    FtMSAuneq_conjTranspose] at h
  simpa only [legacyRadial, Real.sqrt_mul (hρ _), Complex.ofReal_mul,
    mul_assoc] using h

/-- The HS specialization requires a regular supplied seed; this is available
throughout the positive-vacancy physical domain. -/
theorem legacyHS_root (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i) (hv : 0 < vacMix ρ σ) :
    MixBHRootUneq z ρ σ (baseSeed (fun _ : Unit => z) ρ σ ()) 0 0 := by
  apply (isRoot_single_iff z hz.ne' ρ σ _ 0 0).mp
  have h := baseSeed_isRoot (fun _ : Unit => z) ρ σ (fun _ => hz) hv hρ hσ
  convert h using 1 <;> (try rfl)


theorem legacyRadial_radius_integrable (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : MixBHRootUneq z ρ σ Gt Dt K) (i j : Fin N) :
    IntegrableOn (fun r => r * legacyRadial z ρ σ Gt Dt K i j r) (Ioi 0) := by
  have hr := (isRoot_single_iff z hz.ne' ρ σ Gt Dt K).mpr hroot
  unfold legacyRadial orderedRadialCorrelation
  split_ifs with ho
  · exact correlation_radius_integrable_of_root _ (fun _ => hz) ρ σ _ _ _ hσ hr i j ho
  · exact correlation_radius_integrable_of_root _ (fun _ => hz) ρ σ _ _ _ hσ hr j i
      (le_of_not_ge ho)

theorem legacyHS_radial_eq_closed_ae (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i) (hv : 0 < vacMix ρ σ) (i j : Fin N) :
    legacyRadial z ρ σ (baseSeed (fun _ : Unit => z) ρ σ ()) 0 0 i j =ᵐ[volume.restrict (Ioi 0)]
      matCoreHSuneq z ρ σ i j := by
  have h := legacyRadial_eq_closed_ae z hz ρ σ _ 0 0 hσ
    (legacyHS_root z hz ρ σ hσ hρ hv) (by intros; rfl) i j
  simpa only [matCoreCorrUneq, MSAMixture.AVec_zero_Dt, MSAMixture.qpMat_zero_Dt, MSAMixture.Wt_zero_Dt,
    MSAMixture.Ct_zero_Dt, sub_self, ite_self, matMSAtail, FMSA.ExactMSA.cMSAtail,
    Matrix.zero_apply, Pi.zero_apply, zero_mul, zero_div, ite_self, add_zero] using h

theorem legacyTail_radius_integrable (z : ℝ) (hz : 0 < z) (σ : Fin N → ℝ)
    (K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) :
    IntegrableOn (fun r => r * matMSAtail K z σ i j r) (Ioi 0) := by
  have ht : IntegrableOn (fun r => K i j * exp (-z * (r - edgeHi σ i j))) (Ioi (edgeHi σ i j)) :=
    (shiftedRealExp_integrable z (edgeHi σ i j) (edgeHi σ i j) hz).const_mul (K i j)
  have hi := ht.integrable_indicator measurableSet_Ioi
  have hi0 : IntegrableOn ((Ioi (edgeHi σ i j)).indicator
      (fun r => K i j * exp (-z * (r - edgeHi σ i j)))) (Ioi 0) :=
    hi.mono_measure Measure.restrict_le_self
  apply hi0.congr_fun _ measurableSet_Ioi
  intro r hr
  unfold matMSAtail FMSA.ExactMSA.cMSAtail sigMix
  simp only [edgeHi] at *
  by_cases h : (σ i + σ j) / 2 < r
  · rw [indicator_of_mem (show r ∈ Ioi ((σ i + σ j) / 2) from h), if_pos h]
    field_simp [(show r ≠ 0 from hr.ne')]
  · rw [indicator_of_notMem (show r ∉ Ioi ((σ i + σ j) / 2) from h), if_neg h, mul_zero]

private theorem radial_integrand_integrable (f : ℝ → ℝ)
    (hf : IntegrableOn (fun r => r * f r) (Ioi 0)) (k : ℝ) :
    IntegrableOn (fun r => r * f r * sin (k * r)) (Ioi 0) := by
  exact hf.mul_bdd (by fun_prop) (Eventually.of_forall (fun r => by
    rw [Real.norm_eq_abs]; exact abs_sin_le_one _))

theorem legacyRadial_fourier_split (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hv : 0 < vacMix ρ σ) (hroot : MixBHRootUneq z ρ σ Gt Dt K)
    (hK : ∀ i j, K i j = K j i) (k : ℝ) (i j : Fin N) :
    FMSA.HardSphere.radial_fourier (legacyRadial z ρ σ Gt Dt K i j) k =
      FMSA.HardSphere.radial_fourier (matCoreHSuneq z ρ σ i j) k +
      FMSA.HardSphere.radial_fourier (matCoreCorrUneq z ρ σ Gt Dt i j) k +
      FMSA.HardSphere.radial_fourier (matMSAtail K z σ i j) k := by
  have hm := legacyRadial_eq_closed_ae z hz ρ σ Gt Dt K hσ hroot hK i j
  have hh := legacyHS_radial_eq_closed_ae z hz ρ σ hσ hρ hv i j
  have im := legacyRadial_radius_integrable z hz ρ σ Gt Dt K (fun i => (hσ i).le) hroot i j
  have ih : IntegrableOn (fun r => r * matCoreHSuneq z ρ σ i j r) (Ioi 0) := by
    apply (legacyRadial_radius_integrable z hz ρ σ _ 0 0 (fun i => (hσ i).le)
      (legacyHS_root z hz ρ σ hσ hρ hv) i j).congr
    filter_upwards [hh] with r hr
    rw [hr]
  have it := legacyTail_radius_integrable z hz σ K (fun i => (hσ i).le) i j
  have ic : IntegrableOn (fun r => r * matCoreCorrUneq z ρ σ Gt Dt i j r) (Ioi 0) := by
    apply ((im.sub ih).sub it).congr
    filter_upwards [hm] with r hr
    change r * legacyRadial z ρ σ Gt Dt K i j r - r * matCoreHSuneq z ρ σ i j r -
      r * matMSAtail K z σ i j r = _
    rw [hr]
    ring
  unfold FMSA.HardSphere.radial_fourier
  have he : (fun r => r * legacyRadial z ρ σ Gt Dt K i j r * sin (k*r)) =ᵐ[volume.restrict (Ioi 0)]
      (fun r => r * matCoreHSuneq z ρ σ i j r * sin (k*r) +
        r * matCoreCorrUneq z ρ σ Gt Dt i j r * sin (k*r) +
        r * matMSAtail K z σ i j r * sin (k*r)) := by
    filter_upwards [hm] with r hr; rw [hr]; ring
  rw [integral_congr_ae he]
  change (4*π/k) * ∫ r in Ioi 0,
    ((fun r => r * matCoreHSuneq z ρ σ i j r * sin (k*r)) +
      (fun r => r * matCoreCorrUneq z ρ σ Gt Dt i j r * sin (k*r)) +
      (fun r => r * matMSAtail K z σ i j r * sin (k*r))) r = _
  rw [integral_add' ((radial_integrand_integrable _ ih k).add
      (radial_integrand_integrable _ ic k)) (radial_integrand_integrable _ it k),
    integral_add' (radial_integrand_integrable _ ih k) (radial_integrand_integrable _ ic k)]
  ring


theorem radial_fourier_congr_positive_ae (f g : ℝ → ℝ)
    (h : f =ᵐ[volume.restrict (Ioi 0)] g) (k : ℝ) :
    FMSA.HardSphere.radial_fourier f k = FMSA.HardSphere.radial_fourier g k := by
  unfold FMSA.HardSphere.radial_fourier
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with r hr
  rw [hr]

theorem FtMSAuneq_zero (z : ℝ) (ρ σ : Fin N → ℝ) (Gt : Matrix (Fin N) (Fin N) ℝ) (s : ℂ) :
    FtMSAuneq z ρ σ Gt 0 s = FtHSuneq z ρ σ s := by
  simp only [FtMSAuneq, FtHSuneq, MSAMixture.qpMat_zero_Dt, MSAMixture.AVec_zero_Dt,
    MSAMixture.Wt_zero_Dt, MSAMixture.Ct_zero_Dt]
  rfl

theorem legacyHS_matrix_gram (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i) (hv : 0 < vacMix ρ σ)
    (k : ℝ) (hk : k ≠ 0) :
    FtHSuneq z ρ σ (Complex.I * k) * (FtHSuneq z ρ σ (-(Complex.I * k))).transpose =
      1 - Matrix.of (fun i j => (sqrt (ρ i * ρ j) : ℂ) *
        (FMSA.HardSphere.radial_fourier (matCoreHSuneq z ρ σ i j) k : ℂ)) := by
  have h := legacyRadial_matrix_gram z hz ρ σ (baseSeed (fun _ : Unit => z) ρ σ ()) 0 0
    hσ hρ hv.ne' (legacyHS_root z hz ρ σ hσ hρ hv) (by intros; rfl) k hk
  rw [FtMSAuneq_zero, FtMSAuneq_zero] at h
  rw [h]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  exact congrArg (fun t : ℝ => (sqrt (ρ i * ρ j) : ℂ) * (t : ℂ))
    (radial_fourier_congr_positive_ae _ _ (legacyHS_radial_eq_closed_ae z hz ρ σ hσ hρ hv i j) k)

theorem legacyUnequal_hcore (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hv : 0 < vacMix ρ σ) (hroot : MixBHRootUneq z ρ σ Gt Dt K)
    (hK : ∀ i j, K i j = K j i) (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    (FtHSuneq z ρ σ (Complex.I * k) * (Ft1uneq z ρ σ Gt Dt (-(Complex.I * k))).transpose) i j +
      (Ft1uneq z ρ σ Gt Dt (Complex.I * k) * (FtHSuneq z ρ σ (-(Complex.I * k))).transpose) i j +
      (Ft1uneq z ρ σ Gt Dt (Complex.I * k) * (Ft1uneq z ρ σ Gt Dt (-(Complex.I * k))).transpose) i j =
      -(sqrt (ρ i * ρ j) : ℂ) *
        ((FMSA.HardSphere.radial_fourier (matCoreCorrUneq z ρ σ Gt Dt i j) k : ℂ) +
          (FMSA.HardSphere.radial_fourier (matMSAtail K z σ i j) k : ℂ)) := by
  have he : FtHSuneq z ρ σ (Complex.I * k) * (Ft1uneq z ρ σ Gt Dt (-(Complex.I * k))).transpose +
      Ft1uneq z ρ σ Gt Dt (Complex.I * k) * (FtHSuneq z ρ σ (-(Complex.I * k))).transpose +
      Ft1uneq z ρ σ Gt Dt (Complex.I * k) * (Ft1uneq z ρ σ Gt Dt (-(Complex.I * k))).transpose =
      FtMSAuneq z ρ σ Gt Dt (Complex.I * k) * (FtMSAuneq z ρ σ Gt Dt (-(Complex.I * k))).transpose -
        FtHSuneq z ρ σ (Complex.I * k) * (FtHSuneq z ρ σ (-(Complex.I * k))).transpose := by
    unfold Ft1uneq
    rw [Matrix.transpose_sub]
    noncomm_ring
  rw [legacyRadial_matrix_gram z hz ρ σ Gt Dt K hσ hρ hv.ne' hroot hK k hk,
    legacyHS_matrix_gram z hz ρ σ hσ hρ hv k hk] at he
  have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) he
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply] at h
  rw [legacyRadial_fourier_split z hz ρ σ Gt Dt K hσ hρ hv hroot hK k i j] at h
  push_cast at h
  linear_combination h

end FMSA.ExactMSA.MultiTailMixture
