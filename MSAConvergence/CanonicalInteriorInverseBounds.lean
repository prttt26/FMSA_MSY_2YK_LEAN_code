import MSAConvergence.RegularizedInverseField

/-! Uniform positive-real inverse bounds from actual covariance, actual
causal time fields, Plancherel and Cauchy–Schwarz. No Hardy axiom. -/
noncomputable section
open MeasureTheory Set Real Filter Topology FourierTransform
open scoped BigOperators
namespace FMSA.Convergence.CanonicalInteriorInverseBounds
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.CausalLaplaceL2 FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Convergence.RegularizedInverseField FMSA.Convergence.RadialCovarianceBounds
variable {N : ℕ} {T : Type*} [Fintype T]

private theorem regularizer_norm_sq (k : ℝ) :
    ‖(Complex.I*(k : ℂ))/(Complex.I*(k : ℂ)+1)^2‖^2 = k^2/(1+k^2)^2 := by
  have hn : ‖Complex.I*(k : ℂ)‖^2 = k^2 := by simp [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hd : ‖Complex.I*(k : ℂ)+1‖^2 = 1+k^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,pow_two]
  rw [norm_div,norm_pow,div_pow,hn,hd]

private theorem weight_nonneg (R : ℝ) (hR : 0 < R) (w : ℝ) : 0 ≤ testWeight R w := by
  by_cases hw : w=0
  · simp [testWeight,hw]
  · rw [testWeight,CompactSpectralTest.radial_fourier_dilate CompactSpectralTest.profile R hR]
    exact mul_nonneg (sq_nonneg w) (mul_nonneg (pow_nonneg hR.le 3)
      (CompactSpectralTest.profile_radial_fourier_pos _
        (mul_ne_zero hR.ne' (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw))).le)

/-- The actual regularized inverse field has its exact spectral squared norm. -/
theorem actual_regularized_fourier_sq (z : T → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) (i j : Fin N) (w : ℝ) :
    ‖𝓕 (field z ρ σ D G i j) w‖^2 =
      (2*Real.pi*w)^2/(1+(2*Real.pi*w)^2)^2 *
        ‖(causalFactor z ρ σ D G (Complex.I*((2*Real.pi*w : ℝ) : ℂ)))⁻¹ i j‖^2 := by
  rw [actual_field_fourier z hz ρ σ hσ D G hc i j w]
  rw [norm_mul,mul_pow,regularizer_norm_sq]

/-- Uniform spectral L2 bound for the ACTUAL constructed regularized field.
The constant contains no strengths or amplitudes, and density weights may vanish. -/
theorem actual_regularized_fourier_uniform_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (R : ℝ) (hR : 0 < R) (hRσ : ∀ i, R < σ i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      (∀ u i j, K u i j = K u j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) → ∀ i j : Fin N,
      ρ j*(∫ w : ℝ, ‖𝓕 (field z ρ σ D G i j) w‖^2) ≤ ρ i*C := by
  obtain ⟨c,hc,hphi⟩ := CompactSpectralTest.scaled_profile_radial_fourier_lower R hR
  let C₀ := (2*Real.pi)^2/c
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  let C := C₀*((N : ℝ)*(∫ w : ℝ, testWeight R w))
  have hC : 0 ≤ C := mul_nonneg hC₀.le (mul_nonneg (Nat.cast_nonneg _)
    (integral_nonneg (fun w => weight_nonneg R hR w)))
  refine ⟨C,hC,?_⟩
  intro K D G hK hroot hcanon i j
  let invNorm : ℝ → ℝ := fun w => ‖(causalFactor z ρ σ D G (Complex.I*((2*Real.pi*w : ℝ) : ℂ)))⁻¹ i j‖^2
  have hcoeff (w : ℝ) : (2*Real.pi*w)^2/(1+(2*Real.pi*w)^2)^2 ≤ C₀*testWeight R w := by
    by_cases hw : w=0
    · simp [hw,testWeight]
    · have hk : 2*Real.pi*w ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw
      have h := mul_le_mul_of_nonneg_left (hphi (2*Real.pi*w) hk) (sq_nonneg w)
      calc
        _ = C₀*(w^2*(c/(1+(2*Real.pi*w)^2)^2)) := by dsimp [C₀]; field_simp [hc.ne']
        _ ≤ C₀*(w^2*FMSA.HardSphere.radial_fourier (fun r => CompactSpectralTest.profile (r/R)) (2*Real.pi*w)) :=
          mul_le_mul_of_nonneg_left h hC₀.le
        _ = _ := rfl
  have hpoint (w : ℝ) : ρ j*‖𝓕 (field z ρ σ D G i j) w‖^2 ≤ C₀*(testWeight R w*(ρ j*invNorm w)) := by
    rw [actual_regularized_fourier_sq z hz ρ σ (fun i => (hσ i).le) D G hcanon i j w]
    have h := mul_le_mul_of_nonneg_right (hcoeff w)
      (mul_nonneg (hρ j) (show 0 ≤ invNorm w by dsimp [invNorm]; positivity))
    dsimp only [invNorm] at *
    nlinarith [h]
  have hInv := actual_inverse_weighted_test_integral_bound z hz ρ σ hρ hσ hv R hR hRσ K D G hK hroot hcanon i j
  have hiInv : Integrable (fun w : ℝ => testWeight R w*(ρ j*invNorm w)) := by
    simpa only [invNorm,Complex.ofReal_mul,Complex.ofReal_ofNat] using hInv.1
  have hbInv : (∫ w : ℝ, testWeight R w*(ρ j*invNorm w)) ≤ ρ i*((N : ℝ)*(∫ w : ℝ, testWeight R w)) := by
    simpa only [invNorm,Complex.ofReal_mul,Complex.ofReal_ofNat] using hInv.2
  obtain ⟨hfi,hf₂⟩ := actual_field_L1_L2 z hz ρ σ (fun i => (hσ i).le) D G hcanon i j
  have hiFT := (integral_fourier_norm_sq_eq _ hfi hf₂).1
  calc
    _ = ∫ w : ℝ, ρ j*‖𝓕 (field z ρ σ D G i j) w‖^2 := (integral_const_mul _ _).symm
    _ ≤ ∫ w : ℝ, C₀*(testWeight R w*(ρ j*invNorm w)) := integral_mono (hiFT.const_mul (ρ j)) (hiInv.const_mul C₀) hpoint
    _ = C₀*(∫ w : ℝ, testWeight R w*(ρ j*invNorm w)) := integral_const_mul _ _
    _ ≤ C₀*(ρ i*((N : ℝ)*(∫ w : ℝ, testWeight R w))) := mul_le_mul_of_nonneg_left hbInv hC₀.le
    _ = _ := by dsimp [C]; ring

/-- Uniform POSITIVE-REAL point control of the true actual inverse, with
retained density weights. It is derived from actual causal L2 fields, not
from a supplied inverse bound or a Hardy-space axiom. -/
theorem actual_inverse_positive_point_weighted_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (R : ℝ) (hR : 0 < R) (hRσ : ∀ i, R < σ i)
    (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      (∀ u i j, K u i j = K u j i) → IsRoot z ρ σ K D G →
      (∀ w : ℂ, 0 ≤ w.re → IsUnit (causalFactor z ρ σ D G w)) → ∀ i j : Fin N,
      ρ j*‖(causalFactor z ρ σ D G (s : ℂ))⁻¹ i j‖^2 ≤ ρ i*C := by
  obtain ⟨B,hB,hbound⟩ := actual_regularized_fourier_uniform_bound z hz ρ σ hρ hσ hv R hR hRσ
  let a := s/(s+1)^2
  have ha : 0 < a := by dsimp [a]; positivity
  let C := (2*s)⁻¹*B/a^2
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro K D G hK hroot hcanon i j
  obtain ⟨hfi,hf₂⟩ := actual_field_L1_L2 z hz ρ σ (fun i => (hσ i).le) D G hcanon i j
  have hpl := (integral_fourier_norm_sq_eq _ hfi hf₂).2
  have hp := laplace_point_sq_le_L2 (field z ρ σ D G i j) hf₂ s hs
  have hn : ‖∫ t in Ioi (0 : ℝ), field z ρ σ D G i j t*Complex.exp (-(s : ℂ)*t)‖^2 =
      a^2*‖(causalFactor z ρ σ D G (s : ℂ))⁻¹ i j‖^2 := by
    rw [actual_field_positive_laplace z hz ρ σ (fun i => (hσ i).le) D G hcanon i j s hs]
    change ‖(a : ℂ)*(causalFactor z ρ σ D G (s : ℂ))⁻¹ i j‖^2 = _
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
  rw [hn,← hpl] at hp
  have hmul := mul_le_mul_of_nonneg_left hp (hρ j)
  have hstrong : (ρ j*‖(causalFactor z ρ σ D G (s : ℂ))⁻¹ i j‖^2)*a^2 ≤ ρ i*((2*s)⁻¹*B) := by
    calc
      _ = ρ j*(a^2*‖(causalFactor z ρ σ D G (s : ℂ))⁻¹ i j‖^2) := by ring
      _ ≤ ρ j*((2*s)⁻¹*(∫ w : ℝ, ‖𝓕 (field z ρ σ D G i j) w‖^2)) := hmul
      _ = (2*s)⁻¹*(ρ j*(∫ w : ℝ, ‖𝓕 (field z ρ σ D G i j) w‖^2)) := by ring
      _ ≤ (2*s)⁻¹*(ρ i*B) := mul_le_mul_of_nonneg_left (hbound K D G hK hroot hcanon i j) (by positivity)
      _ = _ := by ring
  have hdiv := (le_div_iff₀ (sq_pos_of_pos ha)).mpr hstrong
  simpa only [C,mul_div_assoc] using hdiv

/-- For POSITIVE species densities, every actual canonical reciprocal root
has a uniform inverse-entry bound at every fixed positive real frequency.
The common test radius is constructed internally from the physical diameters. -/
theorem actual_inverse_positive_point_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      (∀ u i j, K u i j = K u j i) → IsRoot z ρ σ K D G →
      (∀ w : ℂ, 0 ≤ w.re → IsUnit (causalFactor z ρ σ D G w)) → ∀ i j : Fin N,
      ‖(causalFactor z ρ σ D G (s : ℂ))⁻¹ i j‖ ≤ C := by
  classical
  have hsmall : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i : Fin N, r < σ i :=
    Filter.eventually_all.mpr (fun i => Iio_mem_nhds (hσ i))
  have hpositive : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨R,hR,hRσ⟩ := (hpositive.and (hsmall.filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨B,hB,hbound⟩ := actual_inverse_positive_point_weighted_bound z hz ρ σ (fun i => (hρ i).le)
    hσ hv R hR hRσ s hs
  let M := (∑ i, ρ i)*(∑ j, (ρ j)⁻¹)*B
  have hsum : 0 ≤ ∑ i, ρ i := Finset.sum_nonneg (fun i _ => (hρ i).le)
  have hinvsum : 0 ≤ ∑ j, (ρ j)⁻¹ := Finset.sum_nonneg (fun j _ => (inv_pos.mpr (hρ j)).le)
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hsum hinvsum) hB
  refine ⟨sqrt M,sqrt_nonneg M,?_⟩
  intro K D G hK hroot hcanon i j
  have hw := hbound K D G hK hroot hcanon i j
  have hi : ρ i ≤ ∑ k, ρ k := Finset.single_le_sum (fun k _ => (hρ k).le) (Finset.mem_univ i)
  have hj : (ρ j)⁻¹ ≤ ∑ k, (ρ k)⁻¹ :=
    Finset.single_le_sum (fun k _ => (inv_pos.mpr (hρ k)).le) (Finset.mem_univ j)
  have hprod : ρ i*(ρ j)⁻¹ ≤ (∑ k, ρ k)*(∑ k, (ρ k)⁻¹) :=
    mul_le_mul hi hj (inv_pos.mpr (hρ j)).le hsum
  have hn : ‖(causalFactor z ρ σ D G (s : ℂ))⁻¹ i j‖^2 ≤ M := by
    calc
      _ ≤ (ρ i*B)/ρ j := (le_div_iff₀ (hρ j)).mpr (by simpa only [mul_comm] using hw)
      _ = (ρ i*(ρ j)⁻¹)*B := by ring
      _ ≤ ((∑ k, ρ k)*(∑ k, (ρ k)⁻¹))*B := mul_le_mul_of_nonneg_right hprod hB
      _ = _ := rfl
  have hsq := Real.sq_sqrt hM
  have hpos := sqrt_nonneg M
  have hnorm := norm_nonneg ((causalFactor z ρ σ D G (s : ℂ))⁻¹ i j)
  nlinarith

end FMSA.Convergence.CanonicalInteriorInverseBounds
/-- info: 'FMSA.Convergence.CanonicalInteriorInverseBounds.actual_regularized_fourier_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CanonicalInteriorInverseBounds.actual_regularized_fourier_sq
/-- info: 'FMSA.Convergence.CanonicalInteriorInverseBounds.actual_regularized_fourier_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CanonicalInteriorInverseBounds.actual_regularized_fourier_uniform_bound
/-- info: 'FMSA.Convergence.CanonicalInteriorInverseBounds.actual_inverse_positive_point_weighted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CanonicalInteriorInverseBounds.actual_inverse_positive_point_weighted_bound
/-- info: 'FMSA.Convergence.CanonicalInteriorInverseBounds.actual_inverse_positive_point_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CanonicalInteriorInverseBounds.actual_inverse_positive_point_uniformly_bounded
