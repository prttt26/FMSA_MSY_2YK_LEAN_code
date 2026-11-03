import MSAConvergence.MixtureCouplingSlabCertificate

/-! A uniform finite-frequency inverse certificate cannot persist up to a
continuously reached singular endpoint. This identifies the scope of the
finite-center numerical route without making a Taylor-radius claim. -/
noncomputable section
open Filter Topology Set
open scoped BigOperators ContDiff
namespace FMSA.Convergence.MixtureUniformInverseObstruction
open FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.CanonicalResolventAnalysis
open FMSA.Convergence.MixtureAxisFrequencyGrid
open FMSA.Convergence.MixtureFrequencyGridCoverage
open FMSA.Convergence.MixtureEndpointNoEscape
open FMSA.Convergence.ActualAlgebraicEndpoint
open FMSA.Convergence.MaximalCanonicalBranch
open FMSA.ExactMSA.MultiTailMixture FMSA.Paper FMSA.MatrixQ0
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual full-line Fourier Q entry is smooth in original amplitudes
at every fixed real wave number, including zero. -/
theorem actual_fourierQ_all_frequency_contDiff
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hσ : ∀ i, 0 ≤ sigma i)
    (k : ℝ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      fourierQ z sigma
        (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2)
        (W z rho a.1 a.2)
        (C z rho sigma a.1 a.2) k i j) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      fourierQ z sigma
        (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2)
        (W z rho a.1 a.2)
        (C z rho sigma a.1 a.2) k i j) =
      fun a => ∑ c : BasisIndex T,
        (bhCoefficient z rho sigma a i j c : ℂ) *
          basisFourierQ z sigma c k i j := by
    funext a
    rw [fourierQ_eq_basis z hz sigma
      (amplitudeA z rho sigma a.1 a.2)
      (amplitudeQp z rho sigma a.1 a.2)
      (W z rho a.1 a.2)
      (C z rho sigma a.1 a.2) hσ k i j]
    rfl
  rw [he]
  exact ContDiff.sum fun c _ =>
    (Complex.ofRealCLM.contDiff.comp
      (bhCoefficient_contDiff z rho sigma i j c)).mul contDiff_const

def actualFactorAt (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (k : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    Matrix (Fin N) (Fin N) ℂ :=
  fourierFactor z rho sigma
    (amplitudeA z rho sigma a.1 a.2)
    (amplitudeQp z rho sigma a.1 a.2)
    (W z rho a.1 a.2)
    (C z rho sigma a.1 a.2) k

/-- The genuine density-weighted Fourier factor varies continuously with
the original MSA amplitudes at each real wave number, including zero. -/
theorem actual_factor_amplitude_continuous
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hσ : ∀ i, 0 ≤ sigma i)
    (k : ℝ) : Continuous (actualFactorAt z rho sigma k) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun a : TailMatrix T N × TailMatrix T N =>
    (1 : Matrix (Fin N) (Fin N) ℂ) i j -
      (Real.sqrt (rho i) : ℂ) * (Real.sqrt (rho j) : ℂ) *
        fourierQ z sigma
          (amplitudeA z rho sigma a.1 a.2)
          (amplitudeQp z rho sigma a.1 a.2)
          (W z rho a.1 a.2)
          (C z rho sigma a.1 a.2) k i j)
  exact continuous_const.sub
    ((continuous_const.mul continuous_const).mul
      (actual_fourierQ_all_frequency_contDiff z hz rho sigma hσ k i j).continuous)

def actualPathFactor (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (k t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  actualFactorAt z rho sigma k (p t)

def actualPathWeightedQ (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (k t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  weightedFourierQ z rho sigma
    (amplitudeA z rho sigma (p t).1 (p t).2)
    (amplitudeQp z rho sigma (p t).1 (p t).2)
    (W z rho (p t).1 (p t).2)
    (C z rho sigma (p t).1 (p t).2) k

theorem actualPathFactor_eq_one_sub_weightedQ
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (k t : ℝ) :
    actualPathFactor z rho sigma p k t =
      1 - actualPathWeightedQ z rho sigma p k t := rfl

theorem actual_path_factor_continuousWithinAt
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (b k : ℝ) (hp : ContinuousWithinAt p (Icc 0 b) b) :
    ContinuousWithinAt (actualPathFactor z rho sigma p k) (Icc 0 b) b :=
  (actual_factor_amplitude_continuous z hz rho sigma hσ k).continuousAt.comp_continuousWithinAt hp

/-- A continuous finite-matrix path approaching a singular endpoint has no
uniform entry-norm bound on its inverses over the whole open prefix. -/
theorem no_uniform_inverse_bound_at_singular_endpoint
    (F : ℝ → Matrix (Fin N) (Fin N) ℂ) (b : ℝ) (hb : 0 < b)
    (hcont : ContinuousWithinAt F (Icc 0 b) b) (hzero : (F b).det = 0)
    (hdet : ∀ t ∈ Ico 0 b, (F t).det ≠ 0) :
    ¬∃ R : ℝ, ∀ t ∈ Ico 0 b, complexNormSum ((F t)⁻¹) ≤ R := by
  classical
  rintro ⟨R,hR⟩
  have hR0 : 0 ≤ R :=
    (complexNormSum_nonneg ((F 0)⁻¹)).trans (hR 0 ⟨le_rfl,hb⟩)
  have hclose : b ∈ closure (Ico (0 : ℝ) b) := by
    rw [closure_Ico hb.ne]
    exact ⟨hb.le,le_rfl⟩
  obtain ⟨u,hu,ht⟩ := mem_closure_iff_seq_limit.mp hclose
  have htWithin : Tendsto u atTop (𝓝[Icc 0 b] b) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨ht,Eventually.of_forall (fun n => Ico_subset_Icc_self (hu n))⟩
  have hball (n : ℕ) : (fun i j => (F (u n))⁻¹ i j) ∈
      Metric.closedBall (0 : Fin N → Fin N → ℂ) R := by
    rw [Metric.mem_closedBall,dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hR0).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hR0).mpr
    intro j
    exact (complexNormSum_entry_le ((F (u n))⁻¹) i j).trans
      (hR (u n) (hu n))
  obtain ⟨B,_,v,hv,hInv⟩ :=
    (isCompact_closedBall (0 : Fin N → Fin N → ℂ) R).tendsto_subseq hball
  have hInvM : Tendsto (fun n => (F (u (v n)))⁻¹) atTop
      (𝓝 (Matrix.of B)) := hInv
  have hF : Tendsto (fun n => F (u (v n))) atTop (𝓝 (F b)) :=
    hcont.tendsto.comp (htWithin.comp hv.tendsto_atTop)
  have hprod : Tendsto (fun n => F (u (v n)) * (F (u (v n)))⁻¹)
      atTop (𝓝 (F b * Matrix.of B)) := hF.mul hInvM
  have heq (n : ℕ) : F (u (v n)) * (F (u (v n)))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet _ (hu _)))
  have hlimit : F b * Matrix.of B = 1 := by
    apply tendsto_nhds_unique hprod
    simpa only [heq] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : Matrix (Fin N) (Fin N) ℂ)) atTop (𝓝 1))
  exact (isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_right_inverse hlimit)) hzero

/-- An actual left limit suffices for inverse blowup. The value assigned to
the path at the excluded endpoint is irrelevant. -/
theorem no_uniform_inverse_bound_at_singular_left_limit
    (F : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (A : Matrix (Fin N) (Fin N) ℂ) (b : ℝ) (hb : 0 < b)
    (hleft : Tendsto F (𝓝[<] b) (𝓝 A)) (hzero : A.det = 0)
    (hdet : ∀ t ∈ Ico 0 b, (F t).det ≠ 0) :
    ¬∃ R : ℝ, ∀ t ∈ Ico 0 b, complexNormSum ((F t)⁻¹) ≤ R := by
  classical
  rintro ⟨R,hR⟩
  have hR0 : 0 ≤ R :=
    (complexNormSum_nonneg ((F 0)⁻¹)).trans (hR 0 ⟨le_rfl,hb⟩)
  have hclose : b ∈ closure (Ico (0 : ℝ) b) := by
    rw [closure_Ico hb.ne]
    exact ⟨hb.le,le_rfl⟩
  obtain ⟨u,hu,ht⟩ := mem_closure_iff_seq_limit.mp hclose
  have htLeft : Tendsto u atTop (𝓝[<] b) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨ht,Eventually.of_forall (fun n => (hu n).2)⟩
  have hball (n : ℕ) : (fun i j => (F (u n))⁻¹ i j) ∈
      Metric.closedBall (0 : Fin N → Fin N → ℂ) R := by
    rw [Metric.mem_closedBall,dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hR0).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hR0).mpr
    intro j
    exact (complexNormSum_entry_le ((F (u n))⁻¹) i j).trans
      (hR (u n) (hu n))
  obtain ⟨B,_,v,hv,hInv⟩ :=
    (isCompact_closedBall (0 : Fin N → Fin N → ℂ) R).tendsto_subseq hball
  have hInvM : Tendsto (fun n => (F (u (v n)))⁻¹) atTop
      (𝓝 (Matrix.of B)) := hInv
  have hF : Tendsto (fun n => F (u (v n))) atTop (𝓝 A) :=
    hleft.comp (htLeft.comp hv.tendsto_atTop)
  have hprod : Tendsto (fun n => F (u (v n)) * (F (u (v n)))⁻¹)
      atTop (𝓝 (A * Matrix.of B)) := hF.mul hInvM
  have heq (n : ℕ) : F (u (v n)) * (F (u (v n)))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet _ (hu _)))
  have hlimit : A * Matrix.of B = 1 := by
    apply tendsto_nhds_unique hprod
    simpa only [heq] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : Matrix (Fin N) (Fin N) ℂ)) atTop (𝓝 1))
  exact (isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_right_inverse hlimit)) hzero

/-- The inverse entry norm admits a quantitative bound for every strict
perturbation budget below one. -/
theorem one_sub_inverse_normSum_bound_of_lt_one
    (Q : Matrix (Fin N) (Fin N) ℂ) (q : ℝ)
    (hQ : complexNormSum Q ≤ q) (hq : q < 1) :
    IsUnit (1-Q) ∧
      complexNormSum ((1-Q)⁻¹) ≤ (N : ℝ)/(1-q) := by
  have hu : IsUnit (1-Q) :=
    complex_matrix_one_sub_isUnit_of_normSum Q (hQ.trans_lt hq)
  have hmul := Matrix.nonsing_inv_mul (1-Q)
    ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have he : (1-Q)⁻¹ = 1 + (1-Q)⁻¹*Q := by
    rw [mul_sub, mul_one] at hmul
    exact sub_eq_iff_eq_add.mp hmul
  have hb : complexNormSum ((1-Q)⁻¹) ≤ (N : ℝ) +
      complexNormSum ((1-Q)⁻¹)*complexNormSum Q := by
    calc
      _ = complexNormSum (1+(1-Q)⁻¹*Q) := congrArg complexNormSum he
      _ ≤ complexNormSum 1 + complexNormSum ((1-Q)⁻¹*Q) :=
        complexNormSum_add_le _ _
      _ ≤ _ := by
        rw [complexNormSum_one]
        exact add_le_add le_rfl (complexNormSum_mul_le _ _)
  have hM : 0 ≤ complexNormSum ((1-Q)⁻¹) := complexNormSum_nonneg _
  have hqpos : 0 < 1-q := by linarith
  have hbound : complexNormSum ((1-Q)⁻¹)*(1-q) ≤ (N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hQ hM]
  exact ⟨hu,(le_div_iff₀ hqpos).mpr hbound⟩

/-- A center inverse and any strict product perturbation budget give a
uniform inverse bound at the perturbed matrix. -/
theorem inverse_bound_of_strict_perturbation
    (Q P : Matrix (Fin N) (Fin N) ℂ) (C D : ℝ)
    (hbase : IsUnit (1-Q))
    (hC : complexNormSum ((1-Q)⁻¹) ≤ C)
    (hD : complexNormSum (P-Q) ≤ D)
    (hstep : C*D < 1) :
    IsUnit (1-P) ∧
      complexNormSum ((1-P)⁻¹) ≤ ((N : ℝ)/(1-C*D))*C := by
  let E := (1-Q)⁻¹*(P-Q)
  have hE : complexNormSum E ≤ C*D := by
    calc
      complexNormSum E ≤ complexNormSum ((1-Q)⁻¹)*complexNormSum (P-Q) :=
        complexNormSum_mul_le _ _
      _ ≤ C*D := mul_le_mul hC hD (complexNormSum_nonneg _) (by
        exact (complexNormSum_nonneg _).trans hC)
  obtain ⟨huE,hInvE⟩ := one_sub_inverse_normSum_bound_of_lt_one E
    (C*D) hE hstep
  have hprod : (1-Q)*(1-E) = 1-P := by
    dsimp [E]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hbase),
      Matrix.one_mul]
    noncomm_ring
  have hunit : IsUnit (1-P) := by
    rw [← hprod]
    exact hbase.mul huE
  have hinv : (1-P)⁻¹ = (1-E)⁻¹*(1-Q)⁻¹ := by
    rw [← hprod,Matrix.mul_inv_rev]
  refine ⟨hunit,?_⟩
  rw [hinv]
  exact (complexNormSum_mul_le _ _).trans
    (mul_le_mul hInvE hC (complexNormSum_nonneg _) (by positivity))

/-- At a continuously reached actual mixture Fourier zero, the fixed-wave-
number inverse sample budget diverges along the open root prefix. The path
needs only left continuity on the closed interval at its endpoint. -/
theorem no_uniform_actual_inverse_at_axis_loss
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (b k : ℝ) (hb : 0 < b)
    (hp : ContinuousWithinAt p (Icc 0 b) b)
    (hzero : (actualPathFactor z rho sigma p k b).det = 0)
    (hdet : ∀ t ∈ Ico 0 b, (actualPathFactor z rho sigma p k t).det ≠ 0) :
    ¬∃ R : ℝ, ∀ t ∈ Ico 0 b,
      complexNormSum ((actualPathFactor z rho sigma p k t)⁻¹) ≤ R :=
  no_uniform_inverse_bound_at_singular_endpoint
    (actualPathFactor z rho sigma p k) b hb
    (actual_path_factor_continuousWithinAt z hz rho sigma hσ p b k hp)
    hzero hdet

/-- Uniform sample inverse bounds plus one strict matrix-change budget
cannot reach a continuously attained actual Fourier axis zero. Samples
may vary with the coupling value; no fixed sample is assumed. -/
theorem no_uniform_sample_perturbation_at_axis_loss
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (b k : ℝ) (hb : 0 < b)
    (hp : ContinuousWithinAt p (Icc 0 b) b)
    (hzero : (actualPathFactor z rho sigma p k b).det = 0)
    (hdet : ∀ t ∈ Ico 0 b, (actualPathFactor z rho sigma p k t).det ≠ 0)
    (R D : ℝ) (hstep : R*D < 1)
    (hsample : ∀ t ∈ Ico 0 b, ∃ a : ℝ,
      (actualPathFactor z rho sigma p a t).det ≠ 0 ∧
      complexNormSum ((actualPathFactor z rho sigma p a t)⁻¹) ≤ R ∧
      complexNormSum (actualPathWeightedQ z rho sigma p k t -
        actualPathWeightedQ z rho sigma p a t) ≤ D) : False := by
  apply no_uniform_actual_inverse_at_axis_loss z hz rho sigma hσ p b k
    hb hp hzero hdet
  refine ⟨((N : ℝ)/(1-R*D))*R,?_⟩
  intro t ht
  obtain ⟨a,hbase,hR,hD⟩ := hsample t ht
  have hbaseUnit : IsUnit (1-actualPathWeightedQ z rho sigma p a t) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (by
      simpa only [← actualPathFactor_eq_one_sub_weightedQ] using hbase))
  obtain ⟨_,hinv⟩ := inverse_bound_of_strict_perturbation
    (actualPathWeightedQ z rho sigma p a t)
    (actualPathWeightedQ z rho sigma p k t) R D
    hbaseUnit (by simpa only [← actualPathFactor_eq_one_sub_weightedQ] using hR)
    hD hstep
  simpa only [← actualPathFactor_eq_one_sub_weightedQ] using hinv

/-- The arithmetic frequency mesh with a single strict step budget cannot
remain uniformly certified over an entire left-continuous prefix ending
at an actual Fourier zero inside its frequency window. -/
theorem no_uniform_mesh_certificate_at_axis_loss
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (b k : ℝ) (hb : 0 < b)
    (hp : ContinuousWithinAt p (Icc 0 b) b)
    (hzero : (actualPathFactor z rho sigma p k b).det = 0)
    (hdet : ∀ t ∈ Ico 0 b, (actualPathFactor z rho sigma p k t).det ≠ 0)
    (L h : ℝ) (n : ℕ) (hh : 0 < h)
    (hspan : 2*L ≤ (n : ℝ)*h) (hk : |k| ≤ L)
    (R Bmom : ℝ) (hB0 : 0 ≤ Bmom)
    (hstep : R*(h*Bmom) < 1)
    (M : Fin N → Fin N → ℝ)
    (hM : ∀ t ∈ Ico 0 b, ∀ i j,
      (∫ r : ℝ, |r| * |q z sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (C z rho sigma (p t).1 (p t).2) i j r|) ≤ M i j)
    (hBudget : momentBudget rho M ≤ Bmom)
    (hbase : ∀ t ∈ Ico 0 b, ∀ a ∈ uniformSamples L h n,
      (actualPathFactor z rho sigma p a t).det ≠ 0)
    (hR : ∀ t ∈ Ico 0 b, ∀ a ∈ uniformSamples L h n,
      complexNormSum ((actualPathFactor z rho sigma p a t)⁻¹) ≤ R) : False := by
  apply no_uniform_sample_perturbation_at_axis_loss z hz rho sigma hσ p b k
    hb hp hzero hdet R (h*Bmom) hstep
  intro t ht
  obtain ⟨a,ha,hnear⟩ := uniformSamples_cover L h n hh hspan k hk
  refine ⟨a,hbase t ht a ha,hR t ht a ha,?_⟩
  have hfreq := weightedFourierQ_sub_normSum_le_moment z hz rho sigma
    (amplitudeA z rho sigma (p t).1 (p t).2)
    (amplitudeQp z rho sigma (p t).1 (p t).2)
    (W z rho (p t).1 (p t).2)
    (C z rho sigma (p t).1 (p t).2)
    hσ a k M (hM t ht)
  change complexNormSum
    (weightedFourierQ z rho sigma
      (amplitudeA z rho sigma (p t).1 (p t).2)
      (amplitudeQp z rho sigma (p t).1 (p t).2)
      (W z rho (p t).1 (p t).2)
      (C z rho sigma (p t).1 (p t).2) k -
      weightedFourierQ z rho sigma
      (amplitudeA z rho sigma (p t).1 (p t).2)
      (amplitudeQp z rho sigma (p t).1 (p t).2)
      (W z rho (p t).1 (p t).2)
      (C z rho sigma (p t).1 (p t).2) a) ≤ _
  calc
    _ ≤ |k-a| * momentBudget rho M := hfreq
    _ ≤ |k-a| * Bmom := mul_le_mul_of_nonneg_left hBudget (abs_nonneg _)
    _ ≤ h*Bmom := mul_le_mul_of_nonneg_right hnear.le hB0

/-- The finite endpoint of the actual maximal canonical mixture branch has
bounded original amplitudes and a selected physical root limit, while the
fixed-frequency inverse at one endpoint zero has no uniform prefix bound. -/
theorem maximal_finite_mixture_endpoint_amplitude_bounded_inverse_unbounded
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (seed : TailMatrix T N × TailMatrix T N)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ t ∈ Ico 0 M.bound.toReal, ‖M.path t‖ ≤ B) ∧
      ∃ a : TailMatrix T N × TailMatrix T N, ∃ k : ℝ,
        PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a ∧
        ¬∃ R : ℝ, ∀ t ∈ Ico 0 M.bound.toReal,
          complexNormSum ((actualPathFactor z rho sigma M.path k t)⁻¹) ≤ R := by
  obtain ⟨B,hB,hbound⟩ := maximal_finite_mixture_prefix_bounded
    z hz rho sigma hρ hσ hv K hK seed M hfinite
  obtain ⟨haxis,a,ha,_⟩ :=
    maximal_finite_mixture_endpoint_first_physical_axis_loss
      z hz rho sigma hρ hσ hv K hK seed M hfinite
  have hleft := ha.2.2.2.1
  obtain ⟨k,hzero⟩ := ha.2.2.2.2
  refine ⟨B,hB,hbound,a,k,ha,?_⟩
  have hb : 0 < M.bound.toReal :=
    ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hleftF : Tendsto (actualPathFactor z rho sigma M.path k)
      (𝓝[<] M.bound.toReal) (𝓝 (actualFactorAt z rho sigma k a)) :=
    ((actual_factor_amplitude_continuous z hz rho sigma
      (fun i => (hσ i).le) k).tendsto a).comp hleft
  have hzeroF : (actualFactorAt z rho sigma k a).det = 0 := hzero
  have hdetF : ∀ t ∈ Ico 0 M.bound.toReal,
      (actualPathFactor z rho sigma M.path k t).det ≠ 0 := by
    intro t ht
    exact haxis t ht k
  exact no_uniform_inverse_bound_at_singular_left_limit
    (actualPathFactor z rho sigma M.path k)
    (actualFactorAt z rho sigma k a) M.bound.toReal hb
    hleftF hzeroF hdetF

/-- Physical mixture data construct the HS-seeded maximal initial branch.
At any finite endpoint, its original amplitudes are uniformly bounded,
its selected limit is an actual root, and its Fourier inverse is unbounded
at at least one endpoint zero frequency. -/
theorem exists_hs_branch_with_bounded_amplitudes_and_unbounded_endpoint_inverse
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) ∧
      (M.bound ≠ ⊤ →
        ∃ B : ℝ, 0 ≤ B ∧
          (∀ t ∈ Ico 0 M.bound.toReal, ‖M.path t‖ ≤ B) ∧
          ∃ a : TailMatrix T N × TailMatrix T N, ∃ k : ℝ,
            PhysicalEndpointLimit z rho sigma K M.path M.bound.toReal a ∧
            ¬∃ R : ℝ, ∀ t ∈ Ico 0 M.bound.toReal,
              complexNormSum ((actualPathFactor z rho sigma M.path k t)⁻¹) ≤ R) := by
  obtain ⟨M,hM,_⟩ :=
    exists_mixture_hs_maximal_branch_with_finite_endpoint_limit_at_eta_lt_one
      z hz rho sigma hρ hσ hη K hK
  refine ⟨M,hM,?_⟩
  intro hfinite
  have hv : vacMix rho sigma ≠ 0 := by
    unfold vacMix
    linarith
  exact maximal_finite_mixture_endpoint_amplitude_bounded_inverse_unbounded
    z hz rho sigma hρ hσ hv K hK (0,baseSeed z rho sigma) M hfinite

end FMSA.Convergence.MixtureUniformInverseObstruction

/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.actual_fourierQ_all_frequency_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.actual_fourierQ_all_frequency_contDiff
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.actual_factor_amplitude_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.actual_factor_amplitude_continuous
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.actualPathFactor_eq_one_sub_weightedQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.actualPathFactor_eq_one_sub_weightedQ
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.actual_path_factor_continuousWithinAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.actual_path_factor_continuousWithinAt
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.no_uniform_inverse_bound_at_singular_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.no_uniform_inverse_bound_at_singular_endpoint
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.no_uniform_inverse_bound_at_singular_left_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.no_uniform_inverse_bound_at_singular_left_limit
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.one_sub_inverse_normSum_bound_of_lt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.one_sub_inverse_normSum_bound_of_lt_one
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.inverse_bound_of_strict_perturbation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.inverse_bound_of_strict_perturbation
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.no_uniform_actual_inverse_at_axis_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.no_uniform_actual_inverse_at_axis_loss
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.no_uniform_sample_perturbation_at_axis_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.no_uniform_sample_perturbation_at_axis_loss
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.no_uniform_mesh_certificate_at_axis_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.no_uniform_mesh_certificate_at_axis_loss
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.maximal_finite_mixture_endpoint_amplitude_bounded_inverse_unbounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.maximal_finite_mixture_endpoint_amplitude_bounded_inverse_unbounded
/-- info: 'FMSA.Convergence.MixtureUniformInverseObstruction.exists_hs_branch_with_bounded_amplitudes_and_unbounded_endpoint_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureUniformInverseObstruction.exists_hs_branch_with_bounded_amplitudes_and_unbounded_endpoint_inverse
