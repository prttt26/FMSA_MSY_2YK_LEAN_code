import MSAConvergence.CanonicalInverseCovariance

/-! Uniform actual covariance pairings against dominated radial tests. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.CovariancePairingBounds
open FMSA.HardSphere FMSA.Paper FMSA.Paper.ActualRDFParameters
open FMSA.ExactMSA.MultiTailMixture FMSA.Convergence.ActualStructureCovariance
open FMSA.Convergence.CanonicalInverseCovariance FMSA.Convergence.RadialCovarianceBounds
variable {N : ℕ}

/-- Every inverse Gram entry is bounded by its nonnegative real trace. -/
theorem inverse_gram_entry_le_trace (A : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ‖(A*A.conjTranspose)⁻¹ i j‖ ≤ ((A*A.conjTranspose)⁻¹).trace.re := by
  have hcolumn (i : Fin N) : (∑ l, ‖A⁻¹ l i‖^2) ≤ ∑ l, ∑ m, ‖A⁻¹ l m‖^2 := by
    apply Finset.sum_le_sum
    intro l _
    exact Finset.single_le_sum (fun m _ => sq_nonneg ‖A⁻¹ l m‖) (Finset.mem_univ i)
  have htrace := inverse_gram_trace A
  rw [Matrix.mul_inv_rev,← Matrix.conjTranspose_nonsing_inv,Matrix.mul_apply]
  change ‖∑ l, star (A⁻¹ l i)*A⁻¹ l j‖ ≤ (A⁻¹.conjTranspose*A⁻¹).trace.re
  have htr : (A⁻¹.conjTranspose*A⁻¹).trace.re = ∑ l, ∑ m, ‖A⁻¹ l m‖^2 := by
    simpa only [Matrix.mul_inv_rev,← Matrix.conjTranspose_nonsing_inv] using htrace
  calc
    _ ≤ ∑ l, ‖star (A⁻¹ l i)*A⁻¹ l j‖ := norm_sum_le _ _
    _ = ∑ l, ‖A⁻¹ l i‖*‖A⁻¹ l j‖ := by simp only [norm_mul,norm_star]
    _ ≤ ∑ l, (‖A⁻¹ l i‖^2+‖A⁻¹ l j‖^2)/2 := by
      apply Finset.sum_le_sum
      intro l _
      nlinarith [sq_nonneg (‖A⁻¹ l i‖-‖A⁻¹ l j‖)]
    _ ≤ _ := by
      rw [← Finset.sum_div,Finset.sum_add_distrib,htr]
      linarith [hcolumn i,hcolumn j]

variable {T : Type*} [Fintype T]

/-- Actual density-weighted h Fourier entries are controlled by the actual
structure trace plus the fixed identity contribution, including tracers. -/
theorem actual_weighted_h_fourier_le_trace (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (K D G : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hroot : IsRoot z ρ σ K D G)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s))
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    sqrt (ρ i)*sqrt (ρ j)*|radial_fourier (nonlinearH z ρ σ D G i j) k| ≤
      (MatrixOZPairing.structureMatrix z ρ σ K D G k).trace.re+1 := by
  classical
  have hm := actual_structure_eq_covariance z hz ρ σ hρ hσ hv K D G hK hroot hc k hk
  have he := congrFun (congrFun hm i) j
  simp only [Matrix.add_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.of_apply] at he
  let S := MatrixOZPairing.structureMatrix z ρ σ K D G k
  have hg : physicalFactor z ρ σ D G k*(physicalFactor z ρ σ D G k).conjTranspose =
      MatrixOZPairing.radialDenominator z ρ σ K D G k :=
    RadialZeroMode.root_factor_gram_radial z ρ σ K D G hz hρ hσ hv hroot hK k
  have hS : ‖S i j‖ ≤ S.trace.re := by
    dsimp only [S,MatrixOZPairing.structureMatrix]
    rw [← hg]
    exact inverse_gram_entry_le_trace _ i j
  have hI : ‖(1 : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 1 := by
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have hd : (sqrt (ρ i) : ℂ)*(radial_fourier (nonlinearH z ρ σ D G i j) k : ℂ)*(sqrt (ρ j) : ℂ) =
      S i j-(1 : Matrix (Fin N) (Fin N) ℂ) i j := by
    change _ = MatrixOZPairing.structureMatrix z ρ σ K D G k i j-_
    linear_combination he
  have hb := (norm_sub_le (S i j) ((1 : Matrix (Fin N) (Fin N) ℂ) i j)).trans
    (add_le_add hS hI)
  rw [← hd] at hb
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg (ρ i)),
    abs_of_nonneg (sqrt_nonneg (ρ j)),mul_assoc,mul_comm,mul_left_comm] using hb


/-- Honest radial test pairings have a uniform, density-weighted bound
whenever the test Fourier transform is dominated by the fixed compact test.
The test's own L1/L2 premises are analytic memberships, not amplitude bounds. -/
theorem actual_dominated_radial_pairing_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (R : ℝ) (hR : 0 < R) (hRσ : ∀ i, R < σ i)
    (ψ : ℝ → ℝ) (hψi : Integrable (oddRadialMoment ψ))
    (hψ₂ : MemLp (oddRadialMoment ψ) 2 volume) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ k : ℝ, k ≠ 0 → |radial_fourier ψ k| ≤
      C*radial_fourier (fun r => CompactSpectralTest.profile (r/R)) k)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z ρ σ K D G)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) (i j : Fin N) :
    sqrt (ρ i)*sqrt (ρ j)*|(∫ r : ℝ, r^2*nonlinearH z ρ σ D G i j |r| *ψ |r|)| ≤
      C*((N : ℝ)+1)*(∫ w : ℝ, testWeight R w) := by
  let H := nonlinearH z ρ σ D G i j
  let S : ℝ → ℝ := fun w => (MatrixOZPairing.structureMatrix z ρ σ K D G (2*Real.pi*w)).trace.re
  let d := sqrt (ρ i)*sqrt (ρ j)
  have hd : 0 ≤ d := mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  obtain ⟨hfi,hfe⟩ := radial_spectral_pairing H ψ
    (actual_odd_h_integrable z hz ρ σ (fun i => (hσ i).le) hv D G hc i j) hψi
    (actual_odd_h_memLp_two z hz ρ σ hσ hv D G hc i j) hψ₂
  let F : ℝ → ℝ := fun w => w^2*radial_fourier H (2*Real.pi*w)*radial_fourier ψ (2*Real.pi*w)
  have hF : Integrable F := hfi
  obtain ⟨hSi,hSb⟩ := actual_structure_weighted_trace_bound z hz ρ σ hρ hσ hv R hR hRσ K D G hK hroot hc
  have hβ := scaled_test_weight_integrable R hR
  have hpoint : ∀ᵐ w : ℝ, d*|F w| ≤ C*(testWeight R w*S w+testWeight R w) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with w hw
    have hk : 2*Real.pi*w ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw
    have hphi : 0 ≤ radial_fourier (fun r => CompactSpectralTest.profile (r/R)) (2*Real.pi*w) := by
      rw [CompactSpectralTest.radial_fourier_dilate CompactSpectralTest.profile R hR]
      exact mul_nonneg (pow_nonneg hR.le 3)
        (CompactSpectralTest.profile_radial_fourier_pos _ (mul_ne_zero hR.ne' hk)).le
    have hH := actual_weighted_h_fourier_le_trace z hz ρ σ hρ hσ hv K D G hK hroot hc _ hk i j
    change d*|radial_fourier H (2*Real.pi*w)| ≤ S w+1 at hH
    have hS : 0 ≤ S w+1 := (mul_nonneg hd (abs_nonneg _)).trans hH
    calc
      _ = (w^2*|radial_fourier ψ (2*Real.pi*w)|)*(d*|radial_fourier H (2*Real.pi*w)|) := by
        dsimp only [F]
        rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg w)]
        ring
      _ ≤ (w^2*(C*radial_fourier (fun r => CompactSpectralTest.profile (r/R)) (2*Real.pi*w)))*(S w+1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hψ _ hk) (sq_nonneg w)) hH
          (mul_nonneg hd (abs_nonneg _)) (mul_nonneg (sq_nonneg w) (mul_nonneg hC hphi))
      _ = _ := by dsimp only [testWeight]; ring
  have hRi : Integrable (fun w => C*(testWeight R w*S w+testWeight R w)) := (hSi.add hβ).const_mul C
  change d*|(∫ r : ℝ, r^2*H |r| *ψ |r|)| ≤ _
  rw [← hfe]
  calc
    _ ≤ d*(∫ w : ℝ, |F w|) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm F) hd
    _ = ∫ w : ℝ, d*|F w| := (integral_const_mul _ _).symm
    _ ≤ ∫ w : ℝ, C*(testWeight R w*S w+testWeight R w) :=
      integral_mono_ae (hF.norm.const_mul d) hRi hpoint
    _ = C*((∫ w : ℝ, testWeight R w*S w)+(∫ w : ℝ, testWeight R w)) := by
      rw [integral_const_mul,integral_add hSi hβ]
    _ ≤ C*((N : ℝ)*(∫ w : ℝ, testWeight R w)+(∫ w : ℝ, testWeight R w)) :=
      mul_le_mul_of_nonneg_left (by dsimp only [S]; linarith [hSb]) hC
    _ = _ := by ring

end FMSA.Convergence.CovariancePairingBounds
/-- info: 'FMSA.Convergence.CovariancePairingBounds.inverse_gram_entry_le_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CovariancePairingBounds.inverse_gram_entry_le_trace
/-- info: 'FMSA.Convergence.CovariancePairingBounds.actual_weighted_h_fourier_le_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CovariancePairingBounds.actual_weighted_h_fourier_le_trace
/-- info: 'FMSA.Convergence.CovariancePairingBounds.actual_dominated_radial_pairing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CovariancePairingBounds.actual_dominated_radial_pairing_bound
