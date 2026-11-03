import MSAConvergence.RadialCovarianceBounds

/-! Density-weighted control of the TRUE causal inverse by the physical
inverse Gram trace. The intertwiner is never inverted, so tracers are included. -/
noncomputable section
open Set Real MeasureTheory
open scoped BigOperators ComplexOrder
namespace FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.ActualRadialTangentOZ FMSA.Convergence.RadialCovarianceBounds
variable {N : ℕ}

/-- The inverse physical Gram trace is exactly the sum of squared inverse
entries. This finite algebraic identity also respects singular-inverse zero. -/
theorem inverse_gram_trace (A : Matrix (Fin N) (Fin N) ℂ) :
    ((A*A.conjTranspose)⁻¹).trace.re = ∑ i, ∑ j, ‖A⁻¹ i j‖^2 := by
  rw [Matrix.mul_inv_rev,← Matrix.conjTranspose_nonsing_inv]
  change Complex.reCLM (∑ i, ∑ j, star (A⁻¹ j i)*A⁻¹ j i) = _
  rw [map_sum]
  simp_rw [map_sum]
  change (∑ i, ∑ j, (star (A⁻¹ j i)*A⁻¹ j i).re) = _
  simp only [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,← Complex.sq_norm]
  exact Finset.sum_comm

/-- Each inverse entry is controlled by that same inverse Gram trace. -/
theorem inverse_entry_sq_le_gram_trace (A : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ‖A⁻¹ i j‖^2 ≤ ((A*A.conjTranspose)⁻¹).trace.re := by
  rw [inverse_gram_trace]
  exact (Finset.single_le_sum (fun k _ => sq_nonneg ‖A⁻¹ i k‖) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg ‖A⁻¹ k l‖)) (Finset.mem_univ i))

variable {T : Type*} [Fintype T]

def causalFactor (z : T → ℝ) (ρ σ : Fin N → ℝ) (D G : TailMatrix T N) (s : ℂ) :
    Matrix (Fin N) (Fin N) ℂ := 1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ D G) s

def physicalFactor (z : T → ℝ) (ρ σ : Fin N → ℝ) (D G : TailMatrix T N) (k : ℝ) :
    Matrix (Fin N) (Fin N) ℂ := fourierFactor z ρ σ (amplitudeA z ρ σ D G)
      (amplitudeQp z ρ σ D G) (W z ρ D G) (C z ρ σ D G) k

private theorem physical_factor_formula (z : T → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix T N) (k : ℝ) : physicalFactor z ρ σ D G k =
    1-Matrix.diagonal (fun i => (sqrt (ρ i) : ℂ))*nonlinearActualFourierQ z ρ σ D G k*
      Matrix.diagonal (fun i => (sqrt (ρ i) : ℂ)) := by
  unfold physicalFactor fourierFactor
  congr 1
  ext i j
  simp only [nonlinearActualFourierQ,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.of_apply]
  ring

/-- Exact density-weighted inverse-entry identification. It uses the CAUSAL
factor, not the growing unequal-diameter unrecentered symbol. No density is divided. -/
theorem actual_inverse_weighted_norm (z : T → ℝ) (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (D G : TailMatrix T N) (k : ℝ) (hu : IsUnit (causalFactor z ρ σ D G (Complex.I * k)))
    (i j : Fin N) :
    ρ j*‖(causalFactor z ρ σ D G (Complex.I*k))⁻¹ i j‖^2 =
      ρ i*‖(physicalFactor z ρ σ D G k)⁻¹ i j‖^2 := by
  classical
  let P := rdfPhase σ (Complex.I*k)
  let S := Matrix.diagonal (fun i => (sqrt (ρ i) : ℂ))
  let R := Matrix.diagonal (fun i => (ρ i : ℂ))
  let Q := nonlinearActualFourierQ z ρ σ D G k
  let A := causalFactor z ρ σ D G (Complex.I*k)
  let B := physicalFactor z ρ σ D G k
  let E := Matrix.diagonal (fun i => Complex.exp (-(Complex.I*(k : ℂ))*(σ i : ℂ)/2)*(sqrt (ρ i) : ℂ))
  have hE : E=P*S := by simp only [P,S,E,rdfPhase,Matrix.diagonal_mul_diagonal]
  have hS : S*S=R := by
    rw [show S=Matrix.diagonal (fun i => (sqrt (ρ i) : ℂ)) from rfl,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast Real.mul_self_sqrt (hρ i)
  have hphase : A*P=P*(1-R*Q) := by
    have h := congrArg Matrix.transpose (nonlinear_actual_recentered_factor_phase z ρ σ D G k)
    simpa only [A,P,R,Q,causalFactor,Matrix.transpose_mul,Matrix.transpose_sub,Matrix.transpose_one,Matrix.transpose_transpose,
      rdfPhase,Matrix.diagonal_transpose] using h.symm
  have hsim : A*E=E*B := by
    rw [hE,← Matrix.mul_assoc,hphase]
    rw [show B=1-S*Q*S from physical_factor_formula z ρ σ D G k,← hS]
    noncomm_ring
  have huB : IsUnit B := physical_fourier_factor_unit_of_kernel_unit z ρ σ hρ (D,G) k hu
  have hleft : A⁻¹*A=1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det A).mp hu)
  have hright : B*B⁻¹=1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det B).mp huB)
  have hinv : A⁻¹*E=E*B⁻¹ := by
    calc
      A⁻¹*E = (A⁻¹*E)*(B*B⁻¹) := by rw [hright,Matrix.mul_one]
      _ = (A⁻¹*(E*B))*B⁻¹ := by noncomm_ring
      _ = (A⁻¹*(A*E))*B⁻¹ := by rw [← hsim]
      _ = E*B⁻¹ := by rw [← Matrix.mul_assoc,hleft,Matrix.one_mul]
  let d : Fin N → ℂ := fun l => Complex.exp (-(Complex.I*(k : ℂ))*(σ l : ℂ)/2)*(sqrt (ρ l) : ℂ)
  have hn (l : Fin N) : ‖d l‖ = sqrt (ρ l) := by
    simp [d,Complex.norm_exp,Complex.mul_re,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg (ρ l))]
  have hij := congrFun (congrFun hinv i) j
  simp only [E,Matrix.mul_diagonal,Matrix.diagonal_mul] at hij
  change A⁻¹ i j*d j=d i*B⁻¹ i j at hij
  have hnorm : ‖A⁻¹ i j‖*sqrt (ρ j)=sqrt (ρ i)*‖B⁻¹ i j‖ := by
    calc
      _ = ‖A⁻¹ i j‖*‖d j‖ := congrArg (fun x : ℝ => ‖A⁻¹ i j‖*x) (hn j).symm
      _ = ‖A⁻¹ i j*d j‖ := (norm_mul _ _).symm
      _ = ‖d i*B⁻¹ i j‖ := congrArg norm hij
      _ = ‖d i‖*‖B⁻¹ i j‖ := norm_mul _ _
      _ = _ := congrArg (fun x : ℝ => x*‖B⁻¹ i j‖) (hn i)
  have hsquare := congrArg (fun x : ℝ => x^2) hnorm
  simp only [mul_pow,Real.sq_sqrt (hρ i),Real.sq_sqrt (hρ j)] at hsquare
  change ρ j*‖A⁻¹ i j‖^2=ρ i*‖B⁻¹ i j‖^2
  nlinarith [hsquare]

/-- The TRUE causal inverse is bounded by the actual physical structure
trace with density weights. Full positive-density division is deferred. -/
theorem actual_inverse_weighted_sq_le_trace (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (K D G : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hroot : IsRoot z ρ σ K D G)
    (k : ℝ) (hu : IsUnit (causalFactor z ρ σ D G (Complex.I * k))) (i j : Fin N) :
    ρ j*‖(causalFactor z ρ σ D G (Complex.I*k))⁻¹ i j‖^2 ≤
      ρ i*(FMSA.Paper.MatrixOZPairing.structureMatrix z ρ σ K D G k).trace.re := by
  rw [actual_inverse_weighted_norm z ρ σ hρ D G k hu i j]
  apply mul_le_mul_of_nonneg_left _ (hρ i)
  have hg : physicalFactor z ρ σ D G k*(physicalFactor z ρ σ D G k).conjTranspose =
      FMSA.Paper.MatrixOZPairing.radialDenominator z ρ σ K D G k :=
    FMSA.Paper.RadialZeroMode.root_factor_gram_radial z ρ σ K D G hz hρ hσ hv hroot hK k
  change _ ≤ ((FMSA.Paper.MatrixOZPairing.radialDenominator z ρ σ K D G k)⁻¹).trace.re
  rw [← hg]
  exact inverse_entry_sq_le_gram_trace _ i j

/-- The true causal inverse varies continuously on the whole Fourier axis
under full canonicity, including frequency zero. -/
theorem actual_inverse_axis_continuous (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) :
    Continuous (fun k : ℝ => (causalFactor z ρ σ D G (Complex.I*k))⁻¹) := by
  have hL : ContinuousOn (fun s : ℂ => rdfMatrixLaplace (nonlinearCausalKernel z ρ σ D G) s)
      {s : ℂ | 0 ≤ s.re} := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simpa only [neg_zero] using CanonicalKernelEstimates.kernel_laplace_entry_continuous_halfplane
      z ρ σ hσ (D,G) 0 hz i j
  have hA : ContinuousOn (causalFactor z ρ σ D G) {s : ℂ | 0 ≤ s.re} := continuousOn_const.sub hL
  have hi := CanonicalKernelEstimates.matrix_inverse_continuousOn (causalFactor z ρ σ D G)
    {s : ℂ | 0 ≤ s.re} hA (fun s hs => hc s hs)
  exact hi.comp_continuous (continuous_const.mul Complex.continuous_ofReal) (fun k => by simp)

private theorem testWeight_nonneg (R : ℝ) (hR : 0 < R) (w : ℝ) : 0 ≤ testWeight R w := by
  by_cases hw : w=0
  · simp [testWeight,hw]
  · rw [testWeight,CompactSpectralTest.radial_fourier_dilate CompactSpectralTest.profile R hR]
    exact mul_nonneg (sq_nonneg w) (mul_nonneg (pow_nonneg hR.le 3)
      (CompactSpectralTest.profile_radial_fourier_pos _
        (mul_ne_zero hR.ne' (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw))).le)

/-- UNIFORM weighted L2 control of every actual causal inverse entry, over
ALL canonical reciprocal roots. Neither an inverse bound nor a strength bound
is supplied; the right side is independent of K and amplitudes. -/
theorem actual_inverse_weighted_test_integral_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (R : ℝ) (hR : 0 < R) (hRσ : ∀ i, R < σ i)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z ρ σ K D G)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) (i j : Fin N) :
    Integrable (fun w : ℝ => testWeight R w*(ρ j*
      ‖(causalFactor z ρ σ D G (Complex.I*(2*Real.pi*w)))⁻¹ i j‖^2)) ∧
    (∫ w : ℝ, testWeight R w*(ρ j*‖(causalFactor z ρ σ D G (Complex.I*(2*Real.pi*w)))⁻¹ i j‖^2)) ≤
      ρ i*((N : ℝ)*(∫ w : ℝ, testWeight R w)) := by
  obtain ⟨htrace,htracebound⟩ := actual_structure_weighted_trace_bound z hz ρ σ hρ hσ hv R hR hRσ K D G hK hroot hc
  have hpoint (w : ℝ) : testWeight R w*(ρ j*‖(causalFactor z ρ σ D G (Complex.I*(2*Real.pi*w)))⁻¹ i j‖^2) ≤
      ρ i*(testWeight R w*(FMSA.Paper.MatrixOZPairing.structureMatrix z ρ σ K D G (2*Real.pi*w)).trace.re) := by
    have h := mul_le_mul_of_nonneg_left (actual_inverse_weighted_sq_le_trace z hz ρ σ hρ hσ hv K D G hK hroot
      (2*Real.pi*w) (hc _ (by simp)) i j) (testWeight_nonneg R hR w)
    simpa only [mul_comm,mul_left_comm,mul_assoc,Complex.ofReal_mul,Complex.ofReal_ofNat] using h
  have hinv0 := (actual_inverse_axis_continuous z hz ρ σ (fun i => (hσ i).le) D G hc).comp
    (show Continuous (fun w : ℝ => 2*Real.pi*w) by fun_prop)
  have hinv : Continuous (fun w : ℝ => (causalFactor z ρ σ D G (Complex.I*(2*Real.pi*w)))⁻¹) := by
    simpa only [Function.comp_def,Complex.ofReal_mul,Complex.ofReal_ofNat] using hinv0
  have hentry : Continuous (fun w : ℝ => (causalFactor z ρ σ D G (Complex.I*(2*Real.pi*w)))⁻¹ i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hinv)
  have hmeas : AEStronglyMeasurable (fun w : ℝ => testWeight R w*(ρ j*
      ‖(causalFactor z ρ σ D G (Complex.I*(2*Real.pi*w)))⁻¹ i j‖^2)) volume :=
    (scaled_test_weight_integrable R hR).aestronglyMeasurable.mul
      ((continuous_const.mul (hentry.norm.pow 2)).aestronglyMeasurable)
  have hint : Integrable (fun w : ℝ => testWeight R w*(ρ j*
      ‖(causalFactor z ρ σ D G (Complex.I*(2*Real.pi*w)))⁻¹ i j‖^2)) := by
    apply (htrace.const_mul (ρ i)).mono' hmeas
    apply ae_of_all
    intro w
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (testWeight_nonneg R hR w)
      (mul_nonneg (hρ j) (sq_nonneg _)))]
    exact hpoint w
  refine ⟨hint,?_⟩
  calc
    _ ≤ ∫ w : ℝ, ρ i*(testWeight R w*(FMSA.Paper.MatrixOZPairing.structureMatrix z ρ σ K D G (2*Real.pi*w)).trace.re) :=
      integral_mono hint (htrace.const_mul (ρ i)) hpoint
    _ = ρ i*(∫ w : ℝ, testWeight R w*(FMSA.Paper.MatrixOZPairing.structureMatrix z ρ σ K D G (2*Real.pi*w)).trace.re) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left htracebound (hρ i)

end FMSA.Convergence.CanonicalInverseCovariance
/-- info: 'FMSA.Convergence.CanonicalInverseCovariance.inverse_gram_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CanonicalInverseCovariance.inverse_gram_trace
/-- info: 'FMSA.Convergence.CanonicalInverseCovariance.inverse_entry_sq_le_gram_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CanonicalInverseCovariance.inverse_entry_sq_le_gram_trace
/-- info: 'FMSA.Convergence.CanonicalInverseCovariance.actual_inverse_weighted_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CanonicalInverseCovariance.actual_inverse_weighted_norm
/-- info: 'FMSA.Convergence.CanonicalInverseCovariance.actual_inverse_weighted_sq_le_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CanonicalInverseCovariance.actual_inverse_weighted_sq_le_trace
/-- info: 'FMSA.Convergence.CanonicalInverseCovariance.actual_inverse_axis_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CanonicalInverseCovariance.actual_inverse_axis_continuous
/-- info: 'FMSA.Convergence.CanonicalInverseCovariance.actual_inverse_weighted_test_integral_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CanonicalInverseCovariance.actual_inverse_weighted_test_integral_bound
