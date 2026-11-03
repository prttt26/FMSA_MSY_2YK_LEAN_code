import MSAConvergence.CanonicalInverseCovariance

/-! Actual G/Laplace identification under full canonicity, without a small
weighted kernel budget. The original BH second equation fixes normalization. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.ActualGCanonicalIdentification
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.ActualExcessDecay FMSA.Convergence.ActualSourceBoundary
open FMSA.Convergence.ActualStructureCovariance FMSA.Convergence.ActualReciprocityTangent
open FMSA.Convergence.ActualBHAmplitudeRecovery FMSA.Convergence.ActualBHSecondAmplitudeRecovery
open FMSA.Convergence.CanonicalInverseCovariance FMSA.Convergence.ActualHLaplaceJets
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The honest actual causal G transform equals the finite completion on the
open right half-plane. Integrability is derived from actual canonical decay. -/
theorem actual_causal_G_laplace (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) (s : ℂ) (hs : 0 < s.re) :
    (∀ i j : Fin N, IntegrableOn (fun r : ℝ => (nonlinearCausalG z ρ σ D G r i j : ℂ)*
      Complex.exp (-s*r)) (Ioi 0)) ∧
    rdfMatrixLaplace (nonlinearCausalG z ρ σ D G) s =
      (2*(Real.pi : ℂ))⁻¹ • completedJSymbol z ρ σ (D,G) s := by
  obtain ⟨ε,hε,hEx⟩ := actual_excess_canonical_laplace z hz ρ σ hσ hv (D,G) hc
  have hiE := (hEx s (by linarith)).1
  have hiB (i j : Fin N) : IntegrableOn (fun r : ℝ => (affineBackground σ r i j : ℂ)*Complex.exp (-s*r)) (Ioi 0) :=
    FMSA.complex_laplace_integrable _ (by unfold affineBackground; fun_prop) s
      (background_real_damped_integrable σ s.re hs i j)
  have he (i j : Fin N) : (fun r : ℝ => (nonlinearCausalG z ρ σ D G r i j : ℂ)*Complex.exp (-s*r)) =
      fun r => (nonlinearRDFExcess z ρ σ D G r i j : ℂ)*Complex.exp (-s*r)+
        (affineBackground σ r i j : ℂ)*Complex.exp (-s*r) := by
    funext r
    simp only [nonlinearCausalG,affineBackground,Matrix.of_apply]
    push_cast
    ring
  refine ⟨(fun i j => by rw [he]; exact (hiE i j).add (hiB i j)),?_⟩
  rw [← actual_excess_completed_symbol z hz ρ σ hσ hv D G hc s (by intro h; simp [h] at hs) hs.le,
    ← background_laplace σ s hs]
  ext i j
  simp only [rdfMatrixLaplace,Matrix.of_apply,Matrix.add_apply,FMSA.causalComplexLaplace]
  rw [he,integral_add (hiE i j) (hiB i j)]

/-- The ORIGINAL second BH amplitude is the honest actual causal G Laplace
value at its positive tail rate, without a small-kernel-budget hypothesis. -/
theorem actual_G_amplitude_laplace (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0)
    (K D G : TailMatrix T N) (hroot : IsRoot z ρ σ K D G)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) (u : T) :
    rdfMatrixLaplace (nonlinearCausalG z ρ σ D G) (z u : ℂ) = gSymbol (D,G) u := by
  have hA : causalFactor z ρ σ D G (z u : ℂ) =
      1-Matrix.diagonal (fun i => (ρ i : ℂ))*rootTransformSymbol z ρ σ (D,G) u := by
    change 1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ D G) (z u : ℂ)=_
    rw [actual_kernel_root_dictionary z hz ρ σ hσ (D,G) u]
  have hsec : ((2*(Real.pi : ℂ)) • gSymbol (D,G) u)*causalFactor z ρ σ D G (z u : ℂ) =
      nonlinearComplexJ z ρ σ D G (z u : ℂ) := by
    have hr := second_residual_matrix_identity z hz ρ σ K 1 (D,G) u
    rw [← hA] at hr
    have hzero : Matrix.of (fun i j => ((FMSA.ExactMSA.MultiTailMixture.residual z ρ σ K (1,(D,G))).2 u i j : ℂ)) = 0 := by
      ext i j
      simp only [Matrix.of_apply,Matrix.zero_apply,FMSA.ExactMSA.MultiTailMixture.residual,hroot.2,sub_self,Complex.ofReal_zero]
    rw [hzero] at hr
    exact sub_eq_zero.mp hr
  have hu := (Matrix.isUnit_iff_isUnit_det (causalFactor z ρ σ D G (z u : ℂ))).mp
    (hc _ (by simpa using (hz u).le))
  rw [(actual_causal_G_laplace z hz ρ σ hσ hv D G hc (z u : ℂ) (by simpa using hz u)).2]
  change (2*(Real.pi : ℂ))⁻¹ • (nonlinearComplexJ z ρ σ D G (z u : ℂ)*
    (causalFactor z ρ σ D G (z u : ℂ))⁻¹) = _
  rw [← hsec,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hu,Matrix.mul_one,smul_smul,
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)),one_smul]

/-- Actual positive-radius h moment at a tail rate, with the fixed background
kept explicitly. The value is tied to the original second amplitude. -/
theorem actual_h_moment_at_rate (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 < σ i) (hv : vacMix ρ σ ≠ 0)
    (K D G : TailMatrix T N) (hroot : IsRoot z ρ σ K D G)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) (u : T) (i j : Fin N) :
    (∫ r in Ioi (0 : ℝ), r*nonlinearH z ρ σ D G i j r*exp (-z u*r)) =
      -(z u)⁻¹^2+exp (-z u*edgeHi σ i j)*G u i j := by
  have hσ₀ := fun i => (hσ i).le
  have hpos : 0 < (z u : ℂ).re := by simpa using hz u
  have hi := (actual_causal_G_laplace z hz ρ σ hσ₀ hv D G hc (z u : ℂ) hpos).1 i j
  have he := (hMomentLaplace_of_causal_integrable z ρ σ (D,G) i j
    (by unfold edgeHi; linarith [hσ i,hσ j]) (z u : ℂ) hpos hi).2
  rw [actual_G_amplitude_laplace z hz ρ σ hσ₀ hv K D G hroot hc u] at he
  have hcExp : Complex.exp (-(z u : ℂ)*(edgeHi σ i j : ℂ)) = (exp (-z u*edgeHi σ i j) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hcExp] at he
  have hleft : hMomentLaplace z ρ σ (D,G) (z u : ℂ) i j =
      ((∫ r in Ioi (0 : ℝ), r*nonlinearH z ρ σ D G i j r*exp (-z u*r) : ℝ) : ℂ) := by
    simp only [hMomentLaplace,FMSA.causalComplexLaplace,← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    simp only [Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,neg_mul]
  rw [hleft] at he
  have hconst : -1/(z u : ℂ)^2 = ((-(z u)⁻¹^2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hconst] at he
  have hre := congrArg Complex.re he
  simpa only [gSymbol,Matrix.of_apply,Complex.ofReal_re,Complex.add_re,
    Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero] using hre

end FMSA.Convergence.ActualGCanonicalIdentification
/-- info: 'FMSA.Convergence.ActualGCanonicalIdentification.actual_causal_G_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualGCanonicalIdentification.actual_causal_G_laplace
/-- info: 'FMSA.Convergence.ActualGCanonicalIdentification.actual_G_amplitude_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualGCanonicalIdentification.actual_G_amplitude_laplace
/-- info: 'FMSA.Convergence.ActualGCanonicalIdentification.actual_h_moment_at_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualGCanonicalIdentification.actual_h_moment_at_rate
