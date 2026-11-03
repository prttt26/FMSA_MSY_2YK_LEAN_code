import MSAConvergence.MixtureHSKernel

/-! Actual HS density perturbation and joint determinant continuity. Full
canonicity is open off zero vacancy; no density-path inverse is assumed. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.MixtureHSContinuity
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.MatrixQ0
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.MixtureHSKernel FMSA.Convergence.LowDensityCanonicalSeed
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.CanonicalResolventAnalysis
variable {N : ℕ}

def densityDistance (rho base sigma : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, (|rho i*Q0phys rho sigma i j-base i*Q0phys base sigma i j| *(sigma i^2/2)+
    |rho i*Qppphys rho sigma j j-base i*Qppphys base sigma j j| *(sigma i^3/6))

/-- Fixed-diameter weighted physical Qp coefficients are continuous off vacancy zero. -/
theorem weighted_qp_continuousAt (rho sigma : Fin N → ℝ) (hv : vacMix rho sigma ≠ 0) (i j : Fin N) :
    ContinuousAt (fun r : Fin N → ℝ => r i*Q0phys r sigma i j) rho := by
  have hvac : Continuous (fun r : Fin N → ℝ => vacMix r sigma) := by unfold vacMix etaMix; fun_prop
  have hxi : Continuous (fun r : Fin N → ℝ => xi2 r sigma) := by unfold xi2; fun_prop
  have hc := hvac.continuousAt (x := rho)
  have hx := hxi.continuousAt (x := rho)
  have h4 : 4*vacMix rho sigma ≠ 0 := mul_ne_zero (by norm_num) hv
  have hQ : ContinuousAt (fun r : Fin N → ℝ => Q0phys r sigma i j) rho := by
    unfold Q0phys
    fun_prop
  exact (continuousAt_apply i rho).mul hQ

/-- Weighted physical quadratic coefficients have the same honest continuity. -/
theorem weighted_A_continuousAt (rho sigma : Fin N → ℝ) (hv : vacMix rho sigma ≠ 0) (i j : Fin N) :
    ContinuousAt (fun r : Fin N → ℝ => r i*Qppphys r sigma j j) rho := by
  have hvac : Continuous (fun r : Fin N → ℝ => vacMix r sigma) := by unfold vacMix etaMix; fun_prop
  have hxi : Continuous (fun r : Fin N → ℝ => xi2 r sigma) := by unfold xi2; fun_prop
  have hc := hvac.continuousAt (x := rho)
  have hx := hxi.continuousAt (x := rho)
  have h2 : 2*vacMix rho sigma ≠ 0 := mul_ne_zero (by norm_num) hv
  have hA : ContinuousAt (fun r : Fin N → ℝ => Qppphys r sigma j j) rho := by
    unfold Qppphys
    fun_prop
  exact (continuousAt_apply i rho).mul hA

/-- The actual physical coefficient-distance budget is continuous at its base. -/
theorem density_distance_continuousAt (rho sigma : Fin N → ℝ) (hv : vacMix rho sigma ≠ 0) :
    ContinuousAt (fun r => densityDistance r rho sigma) rho := by
  unfold densityDistance
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact (((weighted_qp_continuousAt rho sigma hv i j).sub continuousAt_const).abs.mul_const _).add
    (((weighted_A_continuousAt rho sigma hv i j).sub continuousAt_const).abs.mul_const _)

theorem density_distance_self (rho sigma : Fin N → ℝ) : densityDistance rho rho sigma = 0 := by
  simp [densityDistance]

theorem density_distance_nonneg (rho base sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) :
    0 ≤ densityDistance rho base sigma := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact add_nonneg (mul_nonneg (abs_nonneg _) (div_nonneg (sq_nonneg _) (by norm_num)))
    (mul_nonneg (abs_nonneg _) (div_nonneg (pow_nonneg (hsigma i) 3) (by norm_num)))

/-- HS density changes have a TRUE coefficient/basis integral bound,
uniform over the entire closed right half-plane, including zero. -/
theorem seed_symbol_entry_difference_bound (rho base sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (s : ℂ) (hs : 0 ≤ s.re) (i j : Fin N) :
    ‖seedSymbol rho sigma s i j-seedSymbol base sigma s i j‖ ≤
      |rho i*Q0phys rho sigma i j-base i*Q0phys base sigma i j| *(sigma i^2/2)+
      |rho i*Qppphys rho sigma j j-base i*Qppphys base sigma j j| *(sigma i^3/6) := by
  change ‖rdfMatrixLaplace (nonlinearCausalKernel emptyRates rho sigma 0 0) s i j-
    rdfMatrixLaplace (nonlinearCausalKernel emptyRates base sigma 0 0) s i j‖ ≤ _
  rw [hs_kernel_symbol emptyRates empty_rates_pos rho sigma 0 s hs i j,
    hs_kernel_symbol emptyRates empty_rates_pos base sigma 0 s hs i j]
  let L := FMSA.causalComplexLaplace (recenteredBasis emptyRates sigma (.inl 0) i) s
  let A := FMSA.causalComplexLaplace (recenteredBasis emptyRates sigma (.inl 1) i) s
  have he : ((rho i*Q0phys rho sigma i j : ℝ) : ℂ)*L+((rho i*Qppphys rho sigma j j : ℝ) : ℂ)*A-
      (((base i*Q0phys base sigma i j : ℝ) : ℂ)*L+((base i*Qppphys base sigma j j : ℝ) : ℂ)*A) =
      ((rho i*Q0phys rho sigma i j-base i*Q0phys base sigma i j : ℝ) : ℂ)*L+
        ((rho i*Qppphys rho sigma j j-base i*Qppphys base sigma j j : ℝ) : ℂ)*A := by push_cast; ring
  rw [he]
  have hL : ‖L‖ ≤ sigma i^2/2 := by
    have h := kernel_basis_laplace_uniform_bound emptyRates empty_rates_pos (fun _ => 1) sigma (.inl 0) i s hs
    simpa only [one_mul,hs_linear_basis_mass emptyRates empty_rates_pos sigma i (hsigma i)] using h
  have hA : ‖A‖ ≤ sigma i^3/6 := by
    have h := kernel_basis_laplace_uniform_bound emptyRates empty_rates_pos (fun _ => 1) sigma (.inl 1) i s hs
    simpa only [one_mul,hs_quadratic_basis_mass emptyRates empty_rates_pos sigma i (hsigma i)] using h
  apply (norm_add_le _ _).trans
  apply add_le_add
  all_goals rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  · exact mul_le_mul_of_nonneg_left hL (abs_nonneg _)
  · exact mul_le_mul_of_nonneg_left hA (abs_nonneg _)

/-- A single actual density budget controls every matrix entry/frequency. -/
theorem seed_symbol_difference_bound (rho base sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (s : ℂ) (hs : 0 ≤ s.re) :
    complexNormSum (seedSymbol rho sigma s-seedSymbol base sigma s) ≤ densityDistance rho base sigma := by
  unfold complexNormSum densityDistance
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
    seed_symbol_entry_difference_bound rho base sigma hsigma s hs i j))

/-- FULL HS canonicity is open with respect to DENSITY, derived from the
actual canonical inverse control and genuine uniform coefficient distance. -/
theorem seed_canonicity_eventually (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (hv : vacMix rho sigma ≠ 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (seedFactor rho sigma s)) :
    ∀ᶠ r : Fin N → ℝ in 𝓝 rho, ∀ s : ℂ, 0 ≤ s.re → IsUnit (seedFactor r sigma s) := by
  obtain ⟨delta,R,B,C,hd,_hdz,_hR,_hB,hC,_hcont,hbound⟩ :=
    actual_canonical_resolvent_control emptyRates empty_rates_pos rho sigma hsigma (0,0) hcanon
  have hc : ContinuousAt (fun r => (C+1)*densityDistance r rho sigma) rho :=
    continuousAt_const.mul (density_distance_continuousAt rho sigma hv)
  have he : ∀ᶠ r in 𝓝 rho, (C+1)*densityDistance r rho sigma < 1 :=
    hc.eventually_lt continuousAt_const (by rw [density_distance_self,mul_zero]; norm_num)
  filter_upwards [he] with r hr
  intro s hs
  apply unit_of_inverse_perturbation (seedSymbol rho sigma s) (seedSymbol r sigma s) (hcanon s hs)
  have hinv : complexNormSum ((1-seedSymbol rho sigma s)⁻¹) ≤ C :=
    (hbound s (by linarith : -delta ≤ s.re)).2.1
  calc
    _ ≤ complexNormSum ((1-seedSymbol rho sigma s)⁻¹)*
        complexNormSum (seedSymbol r sigma s-seedSymbol rho sigma s) := complexNormSum_mul_le _ _
    _ ≤ C*densityDistance r rho sigma := mul_le_mul hinv
      (seed_symbol_difference_bound r rho sigma hsigma s hs) (complexNormSum_nonneg _) hC
    _ ≤ (C+1)*densityDistance r rho sigma :=
      mul_le_mul_of_nonneg_right (by linarith) (density_distance_nonneg r rho sigma hsigma)
    _ < 1 := hr

/-- Joint density/frequency continuity of actual HS kernel integrals at every
strictly-right point, with no uniform density path premise. -/
theorem seed_symbol_entry_joint_continuousAt (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (hv : vacMix rho sigma ≠ 0) (s : ℂ) (hs : 0 < s.re) (i j : Fin N) :
    ContinuousAt (fun x : (Fin N → ℝ) × ℂ => seedSymbol x.1 sigma x.2 i j) (rho,s) := by
  have hRe : ∀ᶠ x : (Fin N → ℝ) × ℂ in 𝓝 (rho,s), 0 < x.2.re :=
    continuousAt_const.eventually_lt (Complex.continuous_re.comp continuous_snd).continuousAt hs
  have hdist : Tendsto (fun x : (Fin N → ℝ) × ℂ => densityDistance x.1 rho sigma)
      (𝓝 (rho,s)) (𝓝 0) := by
    have hc := ContinuousAt.comp (f := fun x : (Fin N → ℝ) × ℂ => x.1) (x := (rho,s))
      (density_distance_continuousAt rho sigma hv) continuous_fst.continuousAt
    simpa only [Function.comp_def, density_distance_self] using hc.tendsto
  have hdiff : Tendsto (fun x : (Fin N → ℝ) × ℂ =>
      seedSymbol x.1 sigma x.2 i j-seedSymbol rho sigma x.2 i j) (𝓝 (rho,s)) (𝓝 0) := by
    apply squeeze_zero_norm' _ hdist
    filter_upwards [hRe] with x hx
    exact (complexNormSum_entry_le _ i j).trans (seed_symbol_difference_bound x.1 rho sigma hsigma x.2 hx.le)
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs
  have hfixed : ContinuousAt (fun w : ℂ => seedSymbol rho sigma w i j) s :=
    (actual_kernel_frequency_differentiableAt_off_zero emptyRates rho sigma hsigma (0,0) 0
      (fun u => Fin.elim0 u) s (by simpa only [neg_zero] using hs) hs0 i j).continuousAt
  have hsum := hdiff.add (hfixed.tendsto.comp (continuous_snd.tendsto (rho,s)))
  change Tendsto (fun x : (Fin N → ℝ) × ℂ => seedSymbol x.1 sigma x.2 i j)
    (𝓝 (rho,s)) (𝓝 (seedSymbol rho sigma s i j))
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hsum

/-- The honest HS determinant is jointly continuous in density and right
frequency off zero vacancy, BEFORE applying a zero-free closure theorem. -/
theorem seed_det_joint_continuousAt (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (hv : vacMix rho sigma ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    ContinuousAt (fun x : (Fin N → ℝ) × ℂ => seedDet x.1 sigma x.2) (rho,s) := by
  have hM : ContinuousAt (fun x : (Fin N → ℝ) × ℂ => seedFactor x.1 sigma x.2) (rho,s) := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact continuousAt_const.sub (seed_symbol_entry_joint_continuousAt rho sigma hsigma hv s hs i j)
  have hD : Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => A.det) := continuous_id.matrix_det
  exact ContinuousAt.comp (f := fun x : (Fin N → ℝ) × ℂ => seedFactor x.1 sigma x.2) (x := (rho,s)) hD.continuousAt hM

end FMSA.Convergence.MixtureHSContinuity

/-- info: 'FMSA.Convergence.MixtureHSContinuity.weighted_qp_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSContinuity.weighted_qp_continuousAt

/-- info: 'FMSA.Convergence.MixtureHSContinuity.weighted_A_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSContinuity.weighted_A_continuousAt

/-- info: 'FMSA.Convergence.MixtureHSContinuity.density_distance_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSContinuity.density_distance_continuousAt

/-- info: 'FMSA.Convergence.MixtureHSContinuity.density_distance_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSContinuity.density_distance_self

/-- info: 'FMSA.Convergence.MixtureHSContinuity.density_distance_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSContinuity.density_distance_nonneg

/-- info: 'FMSA.Convergence.MixtureHSContinuity.seed_symbol_entry_difference_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSContinuity.seed_symbol_entry_difference_bound

/-- info: 'FMSA.Convergence.MixtureHSContinuity.seed_symbol_difference_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSContinuity.seed_symbol_difference_bound

/-- info: 'FMSA.Convergence.MixtureHSContinuity.seed_canonicity_eventually' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSContinuity.seed_canonicity_eventually

/-- info: 'FMSA.Convergence.MixtureHSContinuity.seed_symbol_entry_joint_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSContinuity.seed_symbol_entry_joint_continuousAt

/-- info: 'FMSA.Convergence.MixtureHSContinuity.seed_det_joint_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSContinuity.seed_det_joint_continuousAt

