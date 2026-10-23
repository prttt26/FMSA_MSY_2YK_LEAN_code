import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearFiniteK
import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairFourier

/-! Actual nonlinear radial Fourier integrals with additive pair contact. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem nonlinearRDFMoment_positive_laplace (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (i j : Fin N)
    (hR : 0 < edgeHi σ i j) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (k : ℝ) (hk : k ≠ 0) :
    FMSA.causalComplexLaplace (nonlinearRDFMoment z ρ σ Dt G i j) (Complex.I*k) =
      -1/(Complex.I*k)^2+Complex.exp (-(Complex.I*k)*(edgeHi σ i j : ℂ))*
        (rdfMatrixLaplace (nonlinearRDFExcess z ρ σ Dt G) (Complex.I*k) i j+
          hsPairBackground σ (Complex.I*k) i j) := by
  let R := edgeHi σ i j
  let C := (Ioo (-R) R).indicator (fun r : ℝ => -r)
  let E := causalShift (fun u => nonlinearRDFExcess z ρ σ Dt G u i j) R
  have hci : Integrable C :=
    (continuous_id.neg.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  have hei : Integrable E := causalShift_integrable _
    (nonlinearRDFExcess_integrable_of_weighted_budget z ρ σ Dt G hz hσ hv δ hδ hδz hb i j) R
  have hc := (real_axis_weighted_integrable C hci k).integrableOn (s := Ioi 0)
  have he := (real_axis_weighted_integrable E hei k).integrableOn (s := Ioi 0)
  have hsplit : FMSA.causalComplexLaplace (nonlinearRDFMoment z ρ σ Dt G i j) (Complex.I*k) =
      (∫ r in Ioi (0 : ℝ), (C r : ℂ)*Complex.exp (-(Complex.I*k)*r))+
        ∫ r in Ioi (0 : ℝ), (E r : ℂ)*Complex.exp (-(Complex.I*k)*r) := by
    unfold FMSA.causalComplexLaplace
    rw [← integral_add hc he]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := hr
    dsimp only [C, E, R]
    rw [nonlinearRDFMoment, causalShift_eq_zero_below _ _ _ (show -r < edgeHi σ i j from by linarith)]
    push_cast
    ring
  have hcore : (∫ r in Ioi (0 : ℝ), (C r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
      ∫ r in (0 : ℝ)..R, (-r : ℂ)*Complex.exp (-(Complex.I*k)*r) := by
    have heq : (fun r => (C r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
        (Ioo (-R) R).indicator (fun r => (-r : ℂ)*Complex.exp (-(Complex.I*k)*r)) := by
      funext r
      by_cases hr : r ∈ Ioo (-R) R <;> simp [C, hr]
    rw [heq, setIntegral_indicator measurableSet_Ioo]
    have hset : Ioi (0 : ℝ) ∩ Ioo (-R) R=Ioo 0 R := by
      ext r
      simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h, _, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by dsimp only [R]; linarith, h'⟩
    rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le]
  have hs : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
  have ha := hsPair_affine_exp_integral R R (Complex.I*k) hs
  simp only [sub_self, Complex.ofReal_zero, zero_div, zero_sub] at ha
  have ha' : (∫ r in (0 : ℝ)..R, (-r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
      -1/(Complex.I*k)^2+((R : ℂ)/(Complex.I*k)+1/(Complex.I*k)^2)*
        Complex.exp (-(Complex.I*k)*R) := by
    have harg : (fun u : ℝ => ((R-u-R : ℝ) : ℂ)*Complex.exp (-(Complex.I*k)*u)) =
        fun u : ℝ => (-u : ℂ)*Complex.exp (-(Complex.I*k)*u) := by
      funext u
      push_cast
      congr 1
      ring
    rw [harg] at ha
    simpa only [neg_div] using ha
  rw [hsplit, hcore, ha']
  dsimp only [E]
  rw [causalShift_positive_complex_laplace _ R hR]
  simp only [hsPairBackground, rdfMatrixLaplace, Matrix.of_apply]
  change _ = _
  dsimp only [R, E]
  field_simp [hs]
  ring

theorem nonlinearH_radial_fourier (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (i j : Fin N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u) (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (k : ℝ) (hk : k ≠ 0) :
    (radial_fourier (nonlinearH z ρ σ Dt G i j) k : ℂ) =
      (2*Real.pi/(Complex.I*k))*
        (FMSA.causalComplexLaplace (nonlinearRDFMoment z ρ σ Dt G i j) (-(Complex.I*k))-
          FMSA.causalComplexLaplace (nonlinearRDFMoment z ρ σ Dt G i j) (Complex.I*k)) := by
  let U := nonlinearRDFMoment z ρ σ Dt G i j
  have hi := nonlinearRDFMoment_integrable_of_weighted_budget z ρ σ Dt G hz hσ hv δ hδ hδz hb i j
  have hpos := (real_axis_weighted_integrable U hi (-k)).integrableOn (s := Ioi 0)
  have hneg := (real_axis_weighted_integrable U hi k).integrableOn (s := Ioi 0)
  simp only [Complex.ofReal_neg, mul_neg, neg_neg] at hpos
  have he : FMSA.causalComplexLaplace U (-(Complex.I*k))-
      FMSA.causalComplexLaplace U (Complex.I*k) =
      2*Complex.I*Complex.ofReal (∫ r in Ioi (0 : ℝ), U r*sin (k*r)) := by
    unfold FMSA.causalComplexLaplace
    simp only [neg_neg]
    rw [← integral_sub hpos hneg, ← integral_complex_ofReal, ← integral_const_mul]
    apply integral_congr_ae (Eventually.of_forall _)
    intro r
    rw [← mul_sub, complex_axis_exp_difference]
    push_cast
    ring
  have hradius : (∫ r in Ioi (0 : ℝ), r*nonlinearH z ρ σ Dt G i j r*sin (k*r)) =
      ∫ r in Ioi (0 : ℝ), U r*sin (k*r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only [nonlinearH, U]
    field_simp [show r ≠ 0 from (show 0 < r from hr).ne']
  unfold radial_fourier
  rw [hradius, he]
  push_cast
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  field_simp [hkC, Complex.I_ne_zero]
  ring

end FMSA.ExactMSA.MultiTailMixture
