import MSAConvergence.TracerCoreTrialField
import MSAConvergence.ActiveBathKernelBounds
/-! Uniform bounds for the physical active-bath Fourier factor and the trace
of its Gram denominator, at reciprocal canonical roots with retained tracers. -/
noncomputable section
open MeasureTheory Set Real FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Paper FMSA.Paper.ActualRDFParameters
open FMSA.Convergence.CanonicalInverseCovariance FMSA.Convergence.ActiveBathKernelBounds
open scoped BigOperators ComplexOrder
namespace FMSA.Convergence.TracerBathFactorBound
variable {N : ℕ} {T : Type*} [Fintype T]

omit [Fintype T] in
theorem basis_fourier_q_mass_bound (z : T → ℝ)
    (sigma : Fin N → ℝ)
    (b : BasisIndex T) (i j : Fin N) (k : ℝ) :
    ‖basisFourierQ z sigma b k i j‖ ≤ ∫ r : ℝ, |basisQ z sigma b i j r| := by
  unfold basisFourierQ
  calc
    _ ≤ ∫ r : ℝ, ‖(basisQ z sigma b i j r : ℂ)*Complex.exp (-(Complex.I*k)*r)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ r : ℝ, |basisQ z sigma b i j r| := by
      apply integral_congr_ae
      apply ae_of_all
      intro r
      change ‖(basisQ z sigma b i j r : ℂ)*Complex.exp (-(Complex.I*k)*r)‖ = |basisQ z sigma b i j r|
      rw [norm_mul,Complex.norm_real]
      have he : ‖Complex.exp (-(Complex.I*(k : ℂ))*r)‖ = 1 := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re]
      rw [he,mul_one,Real.norm_eq_abs]

theorem actual_q_entry_norm_le_coeff (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i)
    (D G : TailMatrix T N) (k : ℝ) (i j : Fin N) :
    ‖nonlinearActualFourierQ z rho sigma D G k i j‖ ≤
      ‖bhCoefficient z rho sigma (D,G) i j‖ *
        ∑ b : BasisIndex T, ∫ r : ℝ, |basisQ z sigma b i j r| := by
  rw [nonlinearActualFourierQ,Matrix.of_apply]
  rw [fourierQ_eq_basis z hz sigma (amplitudeA z rho sigma D G)
    (amplitudeQp z rho sigma D G) (W z rho D G) (C z rho sigma D G) hs k i j]
  change ‖∑ b : BasisIndex T, (bhCoefficient z rho sigma (D,G) i j b : ℂ)*
    basisFourierQ z sigma b k i j‖ ≤ _
  calc
    _ ≤ ∑ b : BasisIndex T, ‖(bhCoefficient z rho sigma (D,G) i j b : ℂ)*
      basisFourierQ z sigma b k i j‖ := norm_sum_le _ _
    _ ≤ ∑ b : BasisIndex T, ‖bhCoefficient z rho sigma (D,G) i j‖ *
      (∫ r : ℝ, |basisQ z sigma b i j r|) := by
      apply Finset.sum_le_sum
      intro b _
      rw [norm_mul,Complex.norm_real]
      exact mul_le_mul (norm_le_pi_norm _ b)
        (basis_fourier_q_mass_bound z sigma b i j k) (norm_nonneg _)
        (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem active_q_entry_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i) (hs : ∀ i, 0 < sigma i)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u i j, K u i j = K u j i) → IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
      ∀ i j, 0 < rho i → 0 < rho j → ∀ k : ℝ,
        ‖nonlinearActualFourierQ z rho sigma D G k i j‖ ≤ M := by
  obtain ⟨C,hC,hcoeff⟩ := active_coefficients_uniformly_bounded z hz rho sigma hρ hs hv B
  let mass : Fin N → Fin N → ℝ := fun i j =>
    ∑ b : BasisIndex T, ∫ r : ℝ, |basisQ z sigma b i j r|
  let M := C*‖mass‖
  have hM : 0 ≤ M := mul_nonneg hC (norm_nonneg _)
  refine ⟨M,hM,?_⟩
  intro K D G hK hsym hroot hcanon i j hi hj k
  have hmass : mass i j ≤ ‖mass‖ := by
    have h1 := norm_le_pi_norm (mass i) j
    have h2 := norm_le_pi_norm mass i
    have h0 : mass i j ≤ ‖mass i j‖ := Real.le_norm_self _
    exact h0.trans (h1.trans h2)
  have hbase := actual_q_entry_norm_le_coeff z hz rho sigma (fun i => (hs i).le) D G k i j
  calc
    _ ≤ ‖bhCoefficient z rho sigma (D,G) i j‖*mass i j := hbase
    _ ≤ C*‖mass‖ := mul_le_mul (hcoeff K D G hK hsym hroot hcanon i j hi hj)
      hmass (by dsimp [mass]; exact Finset.sum_nonneg (fun b _ => integral_nonneg (fun r => abs_nonneg _))) hC

theorem physical_factor_entries_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i) (hs : ∀ i, 0 < sigma i)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) (B : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u i j, K u i j = K u j i) → IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
      ∀ i j k, ‖physicalFactor z rho sigma D G k i j‖ ≤ L := by
  obtain ⟨M,hM,hq⟩ := active_q_entry_uniformly_bounded z hz rho sigma hρ hs hv B
  let P := ‖fun i : Fin N => sqrt (rho i)‖
  let L := 1+P^2*M
  have hP : 0 ≤ P := norm_nonneg _
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨L,hL,?_⟩
  intro K D G hK hsym hroot hcanon i j k
  have hδ : ‖(1 : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 1 := by
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have hsi : sqrt (rho i) ≤ P := by
    exact (Real.le_norm_self _).trans (norm_le_pi_norm (fun l : Fin N => sqrt (rho l)) i)
  have hsj : sqrt (rho j) ≤ P := by
    exact (Real.le_norm_self _).trans (norm_le_pi_norm (fun l : Fin N => sqrt (rho l)) j)
  have hsi0 : 0 ≤ sqrt (rho i) := sqrt_nonneg _
  have hsj0 : 0 ≤ sqrt (rho j) := sqrt_nonneg _
  have hqij : sqrt (rho i)*sqrt (rho j)*
      ‖nonlinearActualFourierQ z rho sigma D G k i j‖ ≤ P^2*M := by
    by_cases hi : rho i = 0
    · simp only [hi,sqrt_zero,zero_mul]
      positivity
    by_cases hj : rho j = 0
    · simp only [hj,sqrt_zero,mul_zero,zero_mul]
      positivity
    have hip : 0 < rho i := lt_of_le_of_ne (hρ i) (Ne.symm hi)
    have hjp : 0 < rho j := lt_of_le_of_ne (hρ j) (Ne.symm hj)
    have hprod : sqrt (rho i)*sqrt (rho j) ≤ P^2 := by
      calc
        _ ≤ P*P := mul_le_mul hsi hsj hsj0 hP
        _ = P^2 := by ring
    exact mul_le_mul hprod (hq K D G hK hsym hroot hcanon i j hip hjp k)
      (norm_nonneg _) (sq_nonneg P)
  unfold physicalFactor fourierFactor
  simp only [Matrix.sub_apply,Matrix.of_apply]
  have he : fourierQ z sigma (amplitudeA z rho sigma D G) (amplitudeQp z rho sigma D G)
      (W z rho D G) (C z rho sigma D G) k i j =
      nonlinearActualFourierQ z rho sigma D G k i j := rfl
  rw [he]
  calc
    _ ≤ ‖(1 : Matrix (Fin N) (Fin N) ℂ) i j‖+
      ‖(sqrt (rho i) : ℂ)*(sqrt (rho j) : ℂ)*
          nonlinearActualFourierQ z rho sigma D G k i j‖ := norm_sub_le _ _
    _ ≤ L := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hsi0,abs_of_nonneg hsj0]
      dsimp only [L]
      linarith [hδ,hqij]

theorem gram_trace_eq_entry_squares (A : Matrix (Fin N) (Fin N) ℂ) :
    (A*A.conjTranspose).trace.re = ∑ i, ∑ j, ‖A i j‖^2 := by
  change Complex.reCLM (∑ i, ∑ j, A i j*star (A i j)) = _
  rw [map_sum]
  simp_rw [map_sum]
  change (∑ i, ∑ j, (A i j*star (A i j)).re) = _
  have hentry (x : ℂ) : (x*star x).re = ‖x‖^2 := by
    rw [mul_comm]
    simp only [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,← Complex.sq_norm]
  simp_rw [hentry]

theorem physical_denominator_trace_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i) (hs : ∀ i, 0 < sigma i)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u i j, K u i j = K u j i) → IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
      ∀ k : ℝ,
        (MatrixOZPairing.radialDenominator z rho sigma K D G k).trace.re ≤ M := by
  obtain ⟨L,hL,hf⟩ := physical_factor_entries_uniformly_bounded z hz rho sigma hρ hs hv B
  let M : ℝ := ∑ i : Fin N, ∑ j : Fin N, L^2
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg L))
  refine ⟨M,hM,?_⟩
  intro K D G hK hsym hroot hcanon k
  have hgram : physicalFactor z rho sigma D G k*(physicalFactor z rho sigma D G k).conjTranspose =
      MatrixOZPairing.radialDenominator z rho sigma K D G k :=
    FMSA.Paper.RadialZeroMode.root_factor_gram_radial z rho sigma K D G hz hρ hs hv hroot hsym k
  rw [← hgram,gram_trace_eq_entry_squares]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hi := hf K D G hK hsym hroot hcanon i j k
  nlinarith [mul_nonneg (sub_nonneg.mpr hi) (add_nonneg (norm_nonneg (physicalFactor z rho sigma D G k i j)) hL)]

/-- The inverse of the actual physical structure matrix is precisely the
Gram denominator. Canonicality supplies invertibility even with tracer rows. -/
theorem actual_structure_inverse_eq_denominator (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i) (hs : ∀ i, 0 < sigma i)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hsym : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s))
    (k : ℝ) :
    (MatrixOZPairing.structureMatrix z rho sigma K D G k)⁻¹ =
      MatrixOZPairing.radialDenominator z rho sigma K D G k := by
  have hF : IsUnit (physicalFactor z rho sigma D G k) :=
    FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit
      z rho sigma hρ (D,G) k (hcanon _ (by simp))
  have hpos : (MatrixOZPairing.radialDenominator z rho sigma K D G k).PosDef :=
    MatrixOZPairing.actual_radial_denominator_posDef z hz rho sigma K D G
      hρ hs hv hroot hsym k hF
  change ((MatrixOZPairing.radialDenominator z rho sigma K D G k)⁻¹)⁻¹ = _
  exact Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit)

/-- The actual inverse covariance has a uniform trace bound at every real
frequency; zero-density tracer rows require no division. -/
theorem actual_structure_inverse_trace_uniformly_bounded (z : T → ℝ)
    (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hρ : ∀ i, 0 ≤ rho i) (hs : ∀ i, 0 < sigma i)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u i j, K u i j = K u j i) → IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
      ∀ k : ℝ,
        ((MatrixOZPairing.structureMatrix z rho sigma K D G k)⁻¹).trace.re ≤ M := by
  obtain ⟨M,hM,hden⟩ := physical_denominator_trace_uniformly_bounded
    z hz rho sigma hρ hs hv B
  refine ⟨M,hM,?_⟩
  intro K D G hK hsym hroot hcanon k
  rw [actual_structure_inverse_eq_denominator z hz rho sigma hρ hs hv K D G
    hsym hroot hcanon k]
  exact hden K D G hK hsym hroot hcanon k

/-- Each physical Gram denominator entry has a uniform all-frequency
bound, including the inactive tracer rows. -/
theorem actual_denominator_entries_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i) (hs : ∀ i, 0 < sigma i)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u i j, K u i j = K u j i) → IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
      ∀ k : ℝ, ∀ i j : Fin N,
        ‖MatrixOZPairing.radialDenominator z rho sigma K D G k i j‖ ≤ M := by
  obtain ⟨L,hL,hf⟩ := physical_factor_entries_uniformly_bounded z hz rho sigma hρ hs hv B
  let M : ℝ := ∑ l : Fin N, L^2
  have hM : 0 ≤ M := Finset.sum_nonneg (fun l _ => sq_nonneg L)
  refine ⟨M,hM,?_⟩
  intro K D G hK hsym hroot hcanon k i j
  have hgram : physicalFactor z rho sigma D G k * (physicalFactor z rho sigma D G k).conjTranspose =
      MatrixOZPairing.radialDenominator z rho sigma K D G k :=
    FMSA.Paper.RadialZeroMode.root_factor_gram_radial z rho sigma K D G hz hρ hs hv hroot hsym k
  rw [← hgram, Matrix.mul_apply]
  calc
    ‖∑ l : Fin N, physicalFactor z rho sigma D G k i l *
        (physicalFactor z rho sigma D G k).conjTranspose l j‖ ≤
      ∑ l : Fin N, ‖physicalFactor z rho sigma D G k i l *
        (physicalFactor z rho sigma D G k).conjTranspose l j‖ :=
      norm_sum_le _ _
    _ ≤ M := by
      dsimp only [M]
      apply Finset.sum_le_sum
      intro l _
      rw [Matrix.conjTranspose_apply,norm_mul,norm_star]
      have hi := hf K D G hK hsym hroot hcanon i l k
      have hj := hf K D G hK hsym hroot hcanon j l k
      simpa only [pow_two] using mul_le_mul hi hj
        (norm_nonneg (physicalFactor z rho sigma D G k j l)) hL
/-- The actual physical Gram denominator is entrywise continuous on the
real frequency axis, including its physical zero mode. -/
theorem actual_denominator_entry_continuous (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 < sigma i)
    (K D G : TailMatrix T N) (hroot : IsRoot z rho sigma K D G)
    (i j : Fin N) :
    Continuous (fun k : ℝ => (MatrixOZPairing.radialDenominator z rho sigma K D G k) i j) := by
  have hc : Continuous (fun k : ℝ =>
      (RadialZeroMode.radialSymbol (orderedRadialCorrelation z rho sigma K D G i j) k : ℂ)) :=
    Complex.continuous_ofReal.comp
      (RadialZeroMode.actual_radialSymbol_continuous z hz rho sigma K D G
        (fun a => (hs a).le) hroot i j)
  simp only [MatrixOZPairing.radialDenominator, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply]
  fun_prop

end FMSA.Convergence.TracerBathFactorBound
/-- info: 'FMSA.Convergence.TracerBathFactorBound.basis_fourier_q_mass_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBathFactorBound.basis_fourier_q_mass_bound
/-- info: 'FMSA.Convergence.TracerBathFactorBound.actual_q_entry_norm_le_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBathFactorBound.actual_q_entry_norm_le_coeff
/-- info: 'FMSA.Convergence.TracerBathFactorBound.active_q_entry_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBathFactorBound.active_q_entry_uniformly_bounded
/-- info: 'FMSA.Convergence.TracerBathFactorBound.physical_factor_entries_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBathFactorBound.physical_factor_entries_uniformly_bounded
/-- info: 'FMSA.Convergence.TracerBathFactorBound.gram_trace_eq_entry_squares' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBathFactorBound.gram_trace_eq_entry_squares
/-- info: 'FMSA.Convergence.TracerBathFactorBound.physical_denominator_trace_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBathFactorBound.physical_denominator_trace_uniformly_bounded
/-- info: 'FMSA.Convergence.TracerBathFactorBound.actual_structure_inverse_eq_denominator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBathFactorBound.actual_structure_inverse_eq_denominator
/-- info: 'FMSA.Convergence.TracerBathFactorBound.actual_structure_inverse_trace_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBathFactorBound.actual_structure_inverse_trace_uniformly_bounded
/-- info: 'FMSA.Convergence.TracerBathFactorBound.actual_denominator_entries_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBathFactorBound.actual_denominator_entries_uniformly_bounded
/-- info: 'FMSA.Convergence.TracerBathFactorBound.actual_denominator_entry_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBathFactorBound.actual_denominator_entry_continuous
