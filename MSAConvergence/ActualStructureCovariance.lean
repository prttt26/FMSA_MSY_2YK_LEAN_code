import MSAConvergence.ActualRadialTangentOZ

/-! Honest non-tangent RDF Fourier identities under full canonicity.
No small physical kernel budget or amplitude bound is assumed. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ComplexOrder
namespace FMSA.Convergence.ActualStructureCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.Paper.JacobianExterior
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open FMSA.Convergence.ActualExcessDecay FMSA.Convergence.ActualSourceBoundary
open FMSA.Convergence.ActualReciprocityTangent FMSA.Convergence.ActualRadialTangentOZ
open FMSA.Convergence.ActualHLaplaceJets
variable {N : ℕ} {ι : Type*} [Fintype ι]

private theorem excess_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0) (Dt G : TailMatrix ι N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s))
    (i j : Fin N) : IntegrableOn (fun r => nonlinearRDFExcess z ρ σ Dt G r i j) (Ioi 0) := by
  obtain ⟨epsilon,D,he,hD,h⟩ := actual_excess_canonical_integrable z hz ρ σ hσ hv (Dt,G) hc
  exact (h i j).2.1

/-- The whole actual odd h moment is L1 at every canonical amplitude point. -/
theorem actual_rdf_moment_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0) (Dt G : TailMatrix ι N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s))
    (i j : Fin N) : Integrable (nonlinearRDFMoment z ρ σ Dt G i j) := by
  have ho := causalShift_integrable _ (excess_integrable z hz ρ σ hσ hv Dt G hc i j) (edgeHi σ i j)
  have hn := (Measure.measurePreserving_neg volume).integrable_comp_of_integrable ho
  have hcore : Integrable ((Ioo (-edgeHi σ i j) (edgeHi σ i j)).indicator (fun r : ℝ => -r)) :=
    (continuous_id.neg.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  exact (hcore.add ho).sub hn

/-- The actual positive-radius h-moment transform at the Fourier axis. -/
theorem actual_rdf_moment_axis_laplace (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (i j : Fin N)
    (hR : 0 < edgeHi σ i j) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s)) (k : ℝ) (hk : k ≠ 0) :
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
    (excess_integrable z hz ρ σ hσ hv Dt G hc i j) R
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

/-- The honest radial Fourier transform in terms of actual half-line integrals. -/
theorem actual_h_radial_fourier (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (i j : Fin N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s))
    (k : ℝ) (hk : k ≠ 0) :
    (radial_fourier (nonlinearH z ρ σ Dt G i j) k : ℂ) =
      (2*Real.pi/(Complex.I*k))*
        (FMSA.causalComplexLaplace (nonlinearRDFMoment z ρ σ Dt G i j) (-(Complex.I*k))-
          FMSA.causalComplexLaplace (nonlinearRDFMoment z ρ σ Dt G i j) (Complex.I*k)) := by
  let U := nonlinearRDFMoment z ρ σ Dt G i j
  have hi := actual_rdf_moment_integrable z hz ρ σ hσ hv Dt G hc i j
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

/-- The actual excess plus its finite affine background equals the finite
completed J symbol on the closed right half-plane, excluding zero. -/
theorem actual_excess_completed_symbol (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0) (Dt G : TailMatrix ι N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s))
    (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) :
    rdfMatrixLaplace (nonlinearRDFExcess z ρ σ Dt G) s+nonlinearComplexBackground σ s =
      (2*(Real.pi : ℂ))⁻¹ • completedJSymbol z ρ σ (Dt,G) s := by
  obtain ⟨epsilon,he,h⟩ := actual_excess_canonical_laplace z hz ρ σ hσ hv (Dt,G) hc
  rw [(h s (by linarith)).2,actual_source_laplace_closed_right z hz ρ σ hσ hv (Dt,G) s hs hre]
  let A := 1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s
  have hu : IsUnit A := hc s hre
  have hh : (nonlinearComplexBackground σ s*A)*A⁻¹ = nonlinearComplexBackground σ s := by
    rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hu),Matrix.mul_one]
  change _ = (2*(Real.pi : ℂ))⁻¹ • (nonlinearComplexJ z ρ σ Dt G s*A⁻¹)
  rw [← Matrix.smul_mul]
  dsimp only [A] at hh ⊢
  linear_combination (norm := noncomm_ring) -hh

/-- The actual half-line h moment equals its phased finite completion,
with the fixed affine-core term retained explicitly at the Fourier axis. -/
theorem actual_h_moment_axis_completed (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (hv : vacMix ρ σ ≠ 0) (Dt G : TailMatrix ι N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s))
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    FMSA.causalComplexLaplace (nonlinearRDFMoment z ρ σ Dt G i j) (Complex.I*k) =
      -1/(Complex.I*k)^2+(2*(Real.pi : ℂ))⁻¹*completedPhase z ρ σ (Dt,G) (Complex.I*k) i j := by
  have hs : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  rw [actual_rdf_moment_axis_laplace z ρ σ Dt G i j
    (by unfold edgeHi; linarith [hσ i,hσ j]) hz (fun i => (hσ i).le) hv hc k hk]
  have he := congrFun (congrFun (actual_excess_completed_symbol z hz ρ σ (fun i => (hσ i).le)
    hv Dt G hc (Complex.I*k) hs (by simp)) i) j
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at he
  have hb : hsPairBackground σ (Complex.I*k) i j = nonlinearComplexBackground σ (Complex.I*k) i j := by
    simp only [hsPairBackground,nonlinearComplexBackground,Matrix.of_apply]
    field_simp [hs]
  rw [hb,he]
  have hp := congrFun (congrFun (additive_contact_phase_sandwich σ (Complex.I*k)
    (completedJSymbol z ρ σ (Dt,G) (Complex.I*k))) i) j
  change Complex.exp (-(Complex.I*(k : ℂ))*(edgeHi σ i j : ℂ))*
    completedJSymbol z ρ σ (Dt,G) (Complex.I*k) i j = completedPhase z ρ σ (Dt,G) (Complex.I*k) i j at hp
  rw [← hp]
  ring

/-- The HONEST base radial h Fourier integral equals its finite completion.
This is a value identity; it is not inferred from a tangent identity. -/
theorem actual_h_radial_eq_completed (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (hv : vacMix ρ σ ≠ 0) (Dt G : TailMatrix ι N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s))
    (k : ℝ) (hk : k ≠ 0) :
    Matrix.of (fun i j => (FMSA.HardSphere.radial_fourier (nonlinearH z ρ σ Dt G i j) k : ℂ)) =
      completedRadial z ρ σ (Dt,G) k := by
  ext i j
  rw [Matrix.of_apply,actual_h_radial_fourier z ρ σ Dt G i j hz (fun i => (hσ i).le) hv hc k hk]
  have hm := actual_h_moment_axis_completed z hz ρ σ hσ hv Dt G hc (-k) (neg_ne_zero.mpr hk) i j
  simp only [Complex.ofReal_neg,mul_neg] at hm
  rw [hm,actual_h_moment_axis_completed z hz ρ σ hσ hv Dt G hc k hk i j]
  change _ = (Complex.I*(k : ℂ))⁻¹*(completedPhase z ρ σ (Dt,G) (-(Complex.I*k)) i j-
    completedPhase z ρ σ (Dt,G) (Complex.I*k) i j)
  rw [neg_sq]
  field_simp [Complex.I_ne_zero,Complex.ofReal_ne_zero.mpr hk,
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

/-- The POSITIVE physical structure matrix is the covariance Fourier symbol
of the HONEST constructed h field, at every nonzero frequency. -/
theorem actual_structure_eq_covariance (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (hv : vacMix ρ σ ≠ 0)
    (K Dt G : TailMatrix ι N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z ρ σ K Dt G)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s))
    (k : ℝ) (hk : k ≠ 0) :
    1+Matrix.diagonal (fun i => (sqrt (ρ i) : ℂ))*
      Matrix.of (fun i j => (FMSA.HardSphere.radial_fourier (nonlinearH z ρ σ Dt G i j) k : ℂ))*
      Matrix.diagonal (fun i => (sqrt (ρ i) : ℂ)) =
        MatrixOZPairing.structureMatrix z ρ σ K Dt G k := by
  rw [actual_h_radial_eq_completed z hz ρ σ hσ hv Dt G hc k hk]
  let S := Matrix.diagonal (fun i => (sqrt (ρ i) : ℂ))
  let R := Matrix.diagonal (fun i => (ρ i : ℂ))
  let C := nonlinearActualFourierC z ρ σ Dt G k
  let H := completedRadial z ρ σ (Dt,G) k
  let A := 1-S*C*S
  have hsquare : S*S=R := by
    rw [show S=Matrix.diagonal (fun i => (sqrt (ρ i) : ℂ)) from rfl,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast Real.mul_self_sqrt (hρ i)
  have hoz : (1-C*R)*H=C := (actual_kernel_completed_OZ z hz ρ σ (fun i => (hσ i).le)
    K hK hv 1 (Dt,G) 0 (by simpa only [one_smul] using hroot) (by exact map_zero _) hc k hk).1
  have he := congrArg (fun X : Matrix (Fin N) (Fin N) ℂ => S*X*S) hoz
  rw [← hsquare] at he
  have hmul : A*(1+S*H*S)=1 := by
    dsimp only [A]
    linear_combination (norm := noncomm_ring) he
  have hden : A=MatrixOZPairing.radialDenominator z ρ σ K Dt G k :=
    actual_weighted_source_denominator z hz ρ σ hσ hv K hK (Dt,G) hroot k hk
  have hF := physical_fourier_factor_unit_of_kernel_unit z ρ σ hρ (Dt,G) k
    (hc _ (by simp))
  have hpos := MatrixOZPairing.actual_radial_denominator_posDef z hz ρ σ K Dt G hρ hσ hv hroot hK k hF
  have hu : IsUnit A := by rw [hden]; exact hpos.isUnit
  have hh := congrArg (fun X : Matrix (Fin N) (Fin N) ℂ => A⁻¹*X) hmul
  rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det A).mp hu),
    Matrix.one_mul,Matrix.mul_one] at hh
  change 1+S*H*S=(MatrixOZPairing.radialDenominator z ρ σ K Dt G k)⁻¹
  rw [← hden]
  exact hh

/-- No pointwise g positivity or covariance axiom is assumed: actual BH
roots and full canonicity imply positivity of the actual covariance symbol. -/
theorem actual_covariance_posDef (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (hv : vacMix ρ σ ≠ 0)
    (K Dt G : TailMatrix ι N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z ρ σ K Dt G)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s))
    (k : ℝ) (hk : k ≠ 0) :
    (1+Matrix.diagonal (fun i => (sqrt (ρ i) : ℂ))*
      Matrix.of (fun i j => (FMSA.HardSphere.radial_fourier (nonlinearH z ρ σ Dt G i j) k : ℂ))*
      Matrix.diagonal (fun i => (sqrt (ρ i) : ℂ))).PosDef := by
  rw [actual_structure_eq_covariance z hz ρ σ hρ hσ hv K Dt G hK hroot hc k hk]
  exact MatrixOZPairing.actual_structure_matrix_posDef z hz ρ σ K Dt G hρ hσ hv hroot hK k
    (physical_fourier_factor_unit_of_kernel_unit z ρ σ hρ (Dt,G) k (hc _ (by simp)))

end FMSA.Convergence.ActualStructureCovariance
/-- info: 'FMSA.Convergence.ActualStructureCovariance.actual_rdf_moment_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualStructureCovariance.actual_rdf_moment_integrable
/-- info: 'FMSA.Convergence.ActualStructureCovariance.actual_rdf_moment_axis_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualStructureCovariance.actual_rdf_moment_axis_laplace
/-- info: 'FMSA.Convergence.ActualStructureCovariance.actual_h_radial_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualStructureCovariance.actual_h_radial_fourier
/-- info: 'FMSA.Convergence.ActualStructureCovariance.actual_excess_completed_symbol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualStructureCovariance.actual_excess_completed_symbol
/-- info: 'FMSA.Convergence.ActualStructureCovariance.actual_h_moment_axis_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualStructureCovariance.actual_h_moment_axis_completed
/-- info: 'FMSA.Convergence.ActualStructureCovariance.actual_h_radial_eq_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualStructureCovariance.actual_h_radial_eq_completed
/-- info: 'FMSA.Convergence.ActualStructureCovariance.actual_structure_eq_covariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualStructureCovariance.actual_structure_eq_covariance
/-- info: 'FMSA.Convergence.ActualStructureCovariance.actual_covariance_posDef' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualStructureCovariance.actual_covariance_posDef
