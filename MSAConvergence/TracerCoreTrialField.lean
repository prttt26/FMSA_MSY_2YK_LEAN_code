import MSAConvergence.TracerBaseCField
import MSAConvergence.RadialCovarianceBounds

/-! A fixed hard-core trial field and exact physical-to-spectral split of the
actual MSA c h pairing. Integrability and contact-null reduction are internal. -/
noncomputable section
open MeasureTheory Set Real FMSA.HardSphere
open FMSA.Convergence.TracerTailSpectralBound FMSA.Convergence.TracerBaseCField
open FMSA.Convergence.RadialCovarianceBounds FMSA.ExactMSA.MultiTailMixture MSAMixture
namespace FMSA.Convergence.TracerCoreTrialField

/-- The fixed hard-core comparison has an integrable positive radial moment. -/
theorem core_radius_integrable (R : ℝ) :
    IntegrableOn (fun r : ℝ => r*coreValue R r) (Ioi 0) := by
  have hi : IntegrableOn (fun r : ℝ => -r) (Ioo 0 R) :=
    (continuous_id.neg.integrableOn_Icc).mono_set (fun r hr => ⟨hr.1.le,hr.2.le⟩)
  have he : (Ioi (0:ℝ)).indicator (fun r => r*coreValue R r) =
      (Ioo 0 R).indicator (fun r => -r) := by
    funext r
    by_cases hr : 0 < r
    · rw [indicator_of_mem (mem_Ioi.mpr hr)]
      by_cases hsmall : r < R
      · rw [indicator_of_mem (show r ∈ Ioo 0 R from ⟨hr,hsmall⟩)]
        simp only [coreValue,if_pos hsmall,mul_neg_one]
      · rw [indicator_of_notMem (show r ∉ Ioo 0 R from fun h => hsmall h.2)]
        simp only [coreValue,if_neg hsmall,mul_zero]
    · rw [indicator_of_notMem (show r ∉ Ioi 0 from hr),
          indicator_of_notMem (show r ∉ Ioo 0 R from fun h => hr h.1)]
  apply (integrable_indicator_iff measurableSet_Ioi).mp
  rw [he]
  exact hi.integrable_indicator measurableSet_Ioo

/-- The fixed hard-core comparison has an honest odd radial L1/L2 field. -/
theorem core_odd_L1_L2 (R : ℝ) (hR : 0 < R) :
    Integrable (oddRadialMoment (coreValue R)) ∧
      MemLp (oddRadialMoment (coreValue R)) 2 volume := by
  have hi := oddRadialMoment_integrable (core_radius_integrable R)
  refine ⟨hi,?_⟩
  apply FMSA.Convergence.ActualHRadialL2.integrable_bounded_memLp_two _ hi R
  apply ae_of_all
  intro r
  by_cases hsmall : |r| < R
  · have hh : |r| ≤ R := hsmall.le
    simpa only [oddRadialMoment,coreValue,if_pos hsmall,Complex.norm_real,Real.norm_eq_abs,
      mul_neg_one,abs_neg] using hh
  · have hh : 0 ≤ R := hR.le
    simpa only [oddRadialMoment,coreValue,if_neg hsmall,mul_zero,Complex.ofReal_zero,norm_zero] using hh

/-- The hard-core trial field has a finite exact spectral square norm. -/
theorem core_trial_parseval (R : ℝ) (hR : 0 < R) :
    Integrable (fun w : ℝ => w^2*(radial_fourier (coreValue R) (2*Real.pi*w))^2) ∧
    (∫ w : ℝ, w^2*(radial_fourier (coreValue R) (2*Real.pi*w))^2) =
      ∫ r : ℝ, r^2*(coreValue R |r|)^2 := by
  obtain ⟨hi,h₂⟩ := core_odd_L1_L2 R hR
  obtain ⟨hfi,hfe⟩ := FMSA.Convergence.RadialCovarianceBounds.radial_spectral_pairing
    (coreValue R) (coreValue R) hi hi h₂ h₂
  have hleft : (fun w : ℝ => w^2*radial_fourier (coreValue R) (2*Real.pi*w)*
      radial_fourier (coreValue R) (2*Real.pi*w)) =
      (fun w => w^2*(radial_fourier (coreValue R) (2*Real.pi*w))^2) := by
    funext w; ring
  have hright : (fun r : ℝ => r^2*coreValue R |r| *coreValue R |r|) =
      (fun r => r^2*(coreValue R |r|)^2) := by
    funext r; ring
  rw [hleft] at hfi hfe
  rw [hright] at hfe
  exact ⟨hfi,hfe⟩

/-- Any two odd radial L2 fields have an integrable real radial pairing. -/
theorem radial_pair_integrable (f g : ℝ → ℝ)
    (hf : MemLp (oddRadialMoment f) 2 volume)
    (hg : MemLp (oddRadialMoment g) 2 volume) :
    Integrable (fun r : ℝ => r^2*f |r| *g |r|) := by
  have hi : Integrable (fun r => oddRadialMoment f r*oddRadialMoment g r) := hf.integrable_mul hg
  have he : (fun r : ℝ => r^2*f |r| *g |r|) =
      (fun r => (oddRadialMoment f r*oddRadialMoment g r).re) := by
    funext r
    simp only [oddRadialMoment,← Complex.ofReal_mul,Complex.ofReal_re]
    ring
  rw [he]
  exact hi.re

variable {N : ℕ} {T : Type*} [Fintype T]
/-- The true c h spatial integral splits into hard core and exterior forcing. -/
theorem actual_spatial_pair_integral_split (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 < sigma i)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma D G) s))
    (i j : Fin N) :
    (∫ r : ℝ, r^2*orderedRadialCorrelation z rho sigma K D G i j |r| *
      nonlinearH z rho sigma D G i j |r|) =
    (∫ r : ℝ, r^2*orderedRadialCorrelation z rho sigma K D G i j |r| *
      coreValue (edgeHi sigma i j) |r|)+
    (∫ r : ℝ, r^2*tailField z (edgeHi sigma i j) (fun u => K u i j) |r| *
      nonlinearH z rho sigma D G i j |r|) := by
  let R := edgeHi sigma i j
  have hR : 0 < R := by dsimp [R,edgeHi]; linarith [hs i,hs j]
  obtain ⟨hci,hc₂⟩ := actual_odd_c_L1_L2 z hz rho sigma hs K D G hroot i j
  obtain ⟨h0i,h0₂⟩ := core_odd_L1_L2 R hR
  obtain ⟨hti,ht₂⟩ := tail_field_odd_L1_L2 z hz R hR (fun u => K u i j)
  have hh₂ := actual_odd_h_memLp_two z hz rho sigma hs hv D G hcanon i j
  have hleft := radial_pair_integrable _ _ hc₂ hh₂
  have hcore := radial_pair_integrable _ _ hc₂ h0₂
  have htail := radial_pair_integrable _ _ ht₂ hh₂
  have he : (fun r : ℝ => r^2*orderedRadialCorrelation z rho sigma K D G i j |r| *
      nonlinearH z rho sigma D G i j |r|) =ᵐ[volume]
      (fun r => r^2*orderedRadialCorrelation z rho sigma K D G i j |r| *coreValue R |r|+
        r^2*tailField z R (fun u => K u i j) |r| *nonlinearH z rho sigma D G i j |r|) := by
    filter_upwards [volume.ae_ne (0 : ℝ),volume.ae_ne R,volume.ae_ne (-R)] with r hr0 hrp hrm
    have habs : |r| ≠ R := by
      intro hx
      rcases le_or_gt 0 r with hp | hn
      · rw [abs_of_nonneg hp] at hx
        exact hrp hx
      · rw [abs_of_neg hn] at hx
        exact hrm (by linarith)
    have hp := actual_pair_product_split_field z hz rho sigma hs K D G hK hroot i j |r|
      (abs_pos.mpr hr0) habs
    change orderedRadialCorrelation z rho sigma K D G i j |r| *
      nonlinearH z rho sigma D G i j |r| =
      orderedRadialCorrelation z rho sigma K D G i j |r| *coreValue R |r|+
        tailField z R (fun u => K u i j) |r| *nonlinearH z rho sigma D G i j |r| at hp
    calc
      _ = r^2*(orderedRadialCorrelation z rho sigma K D G i j |r| *
          nonlinearH z rho sigma D G i j |r|) := by ring
      _ = r^2*(orderedRadialCorrelation z rho sigma K D G i j |r| *coreValue R |r|+
          tailField z R (fun u => K u i j) |r| *nonlinearH z rho sigma D G i j |r|) :=
        congrArg (fun x : ℝ => r^2*x) hp
      _ = _ := by ring
  rw [integral_congr_ae he]
  exact integral_add hcore htail

/-- Three genuine Parseval identities transfer that split to Fourier space. -/
theorem actual_spectral_pair_integral_split (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 < sigma i)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma D G) s))
    (i j : Fin N) :
    let c := orderedRadialCorrelation z rho sigma K D G i j
    let h := nonlinearH z rho sigma D G i j
    let h0 := coreValue (edgeHi sigma i j)
    let tail := tailField z (edgeHi sigma i j) (fun u => K u i j)
    (∫ w : ℝ, w^2*radial_fourier c (2*Real.pi*w)*radial_fourier h (2*Real.pi*w)) =
      (∫ w : ℝ, w^2*radial_fourier c (2*Real.pi*w)*radial_fourier h0 (2*Real.pi*w))+
      (∫ w : ℝ, w^2*radial_fourier tail (2*Real.pi*w)*radial_fourier h (2*Real.pi*w)) := by
  dsimp only
  let c := orderedRadialCorrelation z rho sigma K D G i j
  let h := nonlinearH z rho sigma D G i j
  let h0 := coreValue (edgeHi sigma i j)
  let tail := tailField z (edgeHi sigma i j) (fun u => K u i j)
  have hR : 0 < edgeHi sigma i j := by dsimp [edgeHi]; linarith [hs i,hs j]
  obtain ⟨hci,hc₂⟩ := actual_odd_c_L1_L2 z hz rho sigma hs K D G hroot i j
  obtain ⟨h0i,h0₂⟩ := core_odd_L1_L2 (edgeHi sigma i j) hR
  obtain ⟨hti,ht₂⟩ := tail_field_odd_L1_L2 z hz (edgeHi sigma i j) hR (fun u => K u i j)
  have hhi := actual_odd_h_integrable z hz rho sigma (fun i => (hs i).le) hv D G hcanon i j
  have hh₂ := actual_odd_h_memLp_two z hz rho sigma hs hv D G hcanon i j
  have hch := (radial_spectral_pairing c h hci hhi hc₂ hh₂).2
  have hch0 := (radial_spectral_pairing c h0 hci h0i hc₂ h0₂).2
  have hth := (radial_spectral_pairing tail h hti hhi ht₂ hh₂).2
  change (∫ w : ℝ, w^2*radial_fourier c (2*Real.pi*w)*radial_fourier h (2*Real.pi*w)) =
    (∫ w : ℝ, w^2*radial_fourier c (2*Real.pi*w)*radial_fourier h0 (2*Real.pi*w))+
    (∫ w : ℝ, w^2*radial_fourier tail (2*Real.pi*w)*radial_fourier h (2*Real.pi*w))
  calc
    _ = ∫ r : ℝ, r^2*c |r| *h |r| := hch
    _ = (∫ r : ℝ, r^2*c |r| *h0 |r|)+
        (∫ r : ℝ, r^2*tail |r| *h |r|) :=
      actual_spatial_pair_integral_split z hz rho sigma hs hv K D G hK hroot hcanon i j
    _ = _ := by rw [hch0,hth]

end FMSA.Convergence.TracerCoreTrialField
/-- info: 'FMSA.Convergence.TracerCoreTrialField.core_radius_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCoreTrialField.core_radius_integrable
/-- info: 'FMSA.Convergence.TracerCoreTrialField.core_odd_L1_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCoreTrialField.core_odd_L1_L2
/-- info: 'FMSA.Convergence.TracerCoreTrialField.core_trial_parseval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCoreTrialField.core_trial_parseval
/-- info: 'FMSA.Convergence.TracerCoreTrialField.radial_pair_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCoreTrialField.radial_pair_integrable
/-- info: 'FMSA.Convergence.TracerCoreTrialField.actual_spatial_pair_integral_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCoreTrialField.actual_spatial_pair_integral_split
/-- info: 'FMSA.Convergence.TracerCoreTrialField.actual_spectral_pair_integral_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCoreTrialField.actual_spectral_pair_integral_split
