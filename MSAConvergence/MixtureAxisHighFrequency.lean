import MSAConvergence.ActualRadialTangentOZ
import MSAConvergence.CanonicalKernelEstimates

/-! An explicit high-frequency cutoff for the actual physical Fourier
factor. It applies off-root and does not assume canonicity or an amplitude
properness bound; any pathwise budget must be supplied independently. -/
noncomputable section
open Real MeasureTheory
open scoped BigOperators
namespace FMSA.Convergence.MixtureAxisHighFrequency
open FMSA.Paper FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.ActualRadialTangentOZ
variable {N : ℕ} {T : Type*} [Fintype T]

def rateCutoff (z : T → ℝ) : ℝ := 1 + 2 * ∑ u, |z u|

def decayBudget (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) : ℝ :=
  FMSA.matrixAbsSum (nonlinearCausalKernel z rho sigma p.1 p.2 0) +
    ∑ i, ∑ j, leadingErrorBound z rho sigma p 0 i j

def safeCutoff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) : ℝ :=
  rateCutoff z + decayBudget z rho sigma p + 1

/-- The cutoff budget is a continuous finite expression in the original
BH amplitudes, including all retained tracer entries. -/
theorem decayBudget_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ) :
    Continuous (decayBudget z rho sigma :
      (TailMatrix T N × TailMatrix T N) → ℝ) := by
  unfold decayBudget FMSA.matrixAbsSum leadingErrorBound lDecayBound jDecayBound
    nonlinearCausalKernel nonlinearRecenteredQ amplitudeA amplitudeQp W C
    mixDqp mixDA mixM mixN Wt Ct gam
  fun_prop

/-- The two finite ingredients of the explicit cutoff are nonnegative. -/
theorem cutoff_nonneg (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) :
    1 ≤ rateCutoff z ∧ 0 ≤ decayBudget z rho sigma p := by
  constructor
  · unfold rateCutoff
    have hsum : 0 ≤ ∑ u, |z u| := Finset.sum_nonneg (fun u _ => abs_nonneg _)
    linarith
  · unfold decayBudget
    exact add_nonneg (FMSA.matrixAbsSum_nonneg _)
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
        (fun j _ => (decayBounds_nonneg z rho sigma p 0 i j).2.2)))

/-- The actual physical Fourier determinant is continuous on the entire
real frequency axis, including zero frequency. The proof uses the genuine
full-line integrable Baxter kernel, rather than a meromorphic formula. -/
theorem physical_fourier_determinant_continuous
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hσ : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) :
    Continuous (fun k : ℝ =>
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2)
        (C z rho sigma p.1 p.2) k).det) := by
  have hfourier (i j : Fin N) : Continuous (fun k : ℝ =>
      fourierQ z sigma (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2) (C z rho sigma p.1 p.2) k i j) := by
    let q0 : ℝ → ℂ := fun r =>
      (q z sigma (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j r : ℂ)
    have hq : Integrable q0 := by
      have h := q_complex_weighted_integrable z hz sigma
        (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2) (C z rho sigma p.1 p.2)
        hσ 0 (by simp) i j
      simpa only [q0, zero_mul, neg_zero, Complex.exp_zero, mul_one] using h
    unfold fourierQ
    apply continuous_of_dominated (bound := fun r : ℝ => ‖q0 r‖)
    · intro k
      have he : Continuous (fun r : ℝ => Complex.exp (-(Complex.I * (k : ℂ)) * (r : ℂ))) := by
        fun_prop
      exact hq.aestronglyMeasurable.mul he.aestronglyMeasurable
    · intro k
      exact Filter.Eventually.of_forall (fun r => by
        change ‖q0 r * Complex.exp (-(Complex.I * (k : ℂ)) * (r : ℂ))‖ ≤ ‖q0 r‖
        rw [norm_mul]
        have he : ‖Complex.exp (-(Complex.I * (k : ℂ)) * (r : ℂ))‖ = 1 := by
          simp [Complex.norm_exp, Complex.mul_re]
        rw [he,mul_one])
    · exact hq.norm
    · exact Filter.Eventually.of_forall (fun r => by fun_prop)
  have hfactor : Continuous (fun k : ℝ =>
      fourierFactor z rho sigma
        (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2)
        (C z rho sigma p.1 p.2) k) := by
    unfold fourierFactor
    apply Continuous.sub continuous_const
    apply continuous_matrix
    intro i j
    simpa only [Matrix.of_apply, mul_assoc] using
      (hfourier i j).const_mul
        ((Real.sqrt (rho i) : ℂ) * (Real.sqrt (rho j) : ℂ))
  exact hfactor.matrix_det

/-- An independent bound on the original finite-dimensional amplitude norm
automatically bounds the explicit decay budget on that ball. -/
theorem exists_budget_bound_on_amplitude_ball
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (M : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : TailMatrix T N × TailMatrix T N,
      ‖p‖ ≤ M → decayBudget z rho sigma p ≤ B := by
  obtain ⟨C,hC⟩ :=
    (isCompact_closedBall (0 : TailMatrix T N × TailMatrix T N) M).exists_bound_of_continuousOn
      (decayBudget_continuous z rho sigma).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro p hp
  have hmem : p ∈ Metric.closedBall (0 : TailMatrix T N × TailMatrix T N) M := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hp
  calc
    decayBudget z rho sigma p ≤ ‖decayBudget z rho sigma p‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (decayBudget z rho sigma p)
    _ ≤ C := hC p hmem
    _ ≤ max C 0 := le_max_left _ _

/-- At every frequency past the explicit finite cutoff, the true physical
Fourier factor is a unit. No MSA root or canonical hypothesis is used. -/
theorem physical_factor_unit_at_high_frequency
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ)
    (hk : safeCutoff z rho sigma p ≤ |k|) :
    IsUnit (fourierFactor z rho sigma
      (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2)
      (W z rho p.1 p.2)
      (C z rho sigma p.1 p.2) k) := by
  let s : ℂ := Complex.I * (k : ℂ)
  let Q := rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s
  have hsNorm : ‖s‖ = |k| := by simp [s]
  have hR : 1 ≤ rateCutoff z := (cutoff_nonneg z rho sigma p).1
  have hB : 0 ≤ decayBudget z rho sigma p := (cutoff_nonneg z rho sigma p).2
  have hs : 1 ≤ ‖s‖ := by
    rw [hsNorm]
    unfold safeCutoff at hk
    linarith
  have hzrate (u : T) : 2 * |z u| ≤ ‖s‖ := by
    have hu := Finset.single_le_sum (f := fun v : T => |z v|)
      (fun v _ => abs_nonneg (z v)) (Finset.mem_univ u)
    rw [hsNorm]
    unfold safeCutoff rateCutoff at hk
    linarith
  have hscaled : ‖s‖ * complexNormSum Q ≤ decayBudget z rho sigma p := by
    dsimp only [Q,complexNormSum,decayBudget,FMSA.matrixAbsSum]
    simpa only [Finset.mul_sum,Finset.sum_add_distrib] using
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        kernel_scaled_bound z rho sigma hσ p 0 hz s (by simp [s]) hs hzrate i j))
  have hcut : decayBudget z rho sigma p < ‖s‖ := by
    rw [hsNorm]
    unfold safeCutoff at hk
    linarith
  have hsmall : complexNormSum Q < 1 := by
    by_contra hn
    have hlarge : 1 ≤ complexNormSum Q := le_of_not_gt hn
    have hmul := mul_le_mul_of_nonneg_left hlarge (norm_nonneg s)
    have hbad : ‖s‖ ≤ decayBudget z rho sigma p := by
      simpa only [mul_one] using hmul.trans hscaled
    exact (not_lt_of_ge hbad) hcut
  have hu : IsUnit (1-Q) := complex_matrix_one_sub_isUnit_of_normSum Q hsmall
  exact physical_fourier_factor_unit_of_kernel_unit z rho sigma hρ p k hu

/-- Every physical real-axis Fourier zero of an arbitrary original amplitude
pair lies in a compact set. This includes possible zeros at `k = 0`. -/
theorem physical_fourier_zero_set_isCompact
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) :
    IsCompact {k : ℝ |
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2)
        (C z rho sigma p.1 p.2) k).det = 0} := by
  let S : Set ℝ := {k : ℝ |
    (fourierFactor z rho sigma
      (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2)
      (W z rho p.1 p.2)
      (C z rho sigma p.1 p.2) k).det = 0}
  have hclosed : IsClosed S :=
    isClosed_eq (physical_fourier_determinant_continuous z hz rho sigma hσ p)
      continuous_const
  have hsubset : S ⊆ Metric.closedBall 0 (safeCutoff z rho sigma p) := by
    intro k hk
    have hlt : |k| < safeCutoff z rho sigma p := by
      by_contra hn
      have hu := physical_factor_unit_at_high_frequency
        z hz rho sigma hρ hσ p k (le_of_not_gt hn)
      exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)) hk
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      using hlt.le
  exact (isCompact_closedBall (0 : ℝ) (safeCutoff z rho sigma p)).of_isClosed_subset
    hclosed hsubset

/-- Whenever a physical Fourier zero exists, its absolute wave number has
a minimum. Several signed frequencies may attain the same minimum. -/
theorem physical_fourier_zero_abs_minimum
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N)
    (hzero : ∃ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2)
        (C z rho sigma p.1 p.2) k).det = 0) :
    ∃ k₀ : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2)
        (C z rho sigma p.1 p.2) k₀).det = 0 ∧
      ∀ k : ℝ,
        (fourierFactor z rho sigma
          (amplitudeA z rho sigma p.1 p.2)
          (amplitudeQp z rho sigma p.1 p.2)
          (W z rho p.1 p.2)
          (C z rho sigma p.1 p.2) k).det = 0 → |k₀| ≤ |k| := by
  let S : Set ℝ := {k : ℝ |
    (fourierFactor z rho sigma
      (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2)
      (W z rho p.1 p.2)
      (C z rho sigma p.1 p.2) k).det = 0}
  have hc : IsCompact S := physical_fourier_zero_set_isCompact
    z hz rho sigma hρ hσ p
  obtain ⟨k₀,hk₀,hmin⟩ := hc.exists_isMinOn (by rcases hzero with ⟨k,hk⟩; exact ⟨k,hk⟩)
    continuous_abs.continuousOn
  exact ⟨k₀,hk₀,fun k hk => hmin hk⟩

/-- Reality of the actual Baxter kernel pairs Fourier determinant zeros
at opposite real frequencies, including the zero mode. -/
theorem physical_fourier_zero_neg
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ)
    (hzero : (fourierFactor z rho sigma
      (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2)
      (W z rho p.1 p.2)
      (C z rho sigma p.1 p.2) k).det = 0) :
    (fourierFactor z rho sigma
      (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2)
      (W z rho p.1 p.2)
      (C z rho sigma p.1 p.2) (-k)).det = 0 := by
  have hfac : fourierFactor z rho sigma
      (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2)
      (W z rho p.1 p.2)
      (C z rho sigma p.1 p.2) (-k) =
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2)
        (C z rho sigma p.1 p.2) k).map (starRingEnd ℂ) := by
    ext i j
    simp only [fourierFactor, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply]
    rw [← fourierQ_conj]
    simp [Matrix.one_apply, map_sub, map_mul, Complex.conj_ofReal]
  rw [hfac]
  change ((starRingEnd ℂ).mapMatrix
    (fourierFactor z rho sigma
      (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2)
      (W z rho p.1 p.2)
      (C z rho sigma p.1 p.2) k)).det = 0
  rw [← RingHom.map_det, hzero, map_zero]

/-- A nonempty physical Fourier zero set has a nonnegative smallest
wave number. The theorem does not assert uniqueness of its signed zeros. -/
theorem physical_fourier_nonnegative_zero_minimum
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N)
    (hzero : ∃ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2)
        (C z rho sigma p.1 p.2) k).det = 0) :
    ∃ k₀ : ℝ, 0 ≤ k₀ ∧
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2)
        (C z rho sigma p.1 p.2) k₀).det = 0 ∧
      ∀ k : ℝ,
        (fourierFactor z rho sigma
          (amplitudeA z rho sigma p.1 p.2)
          (amplitudeQp z rho sigma p.1 p.2)
          (W z rho p.1 p.2)
          (C z rho sigma p.1 p.2) k).det = 0 → k₀ ≤ |k| := by
  obtain ⟨k,hk,hmin⟩ := physical_fourier_zero_abs_minimum
    z hz rho sigma hρ hσ p hzero
  by_cases hnonneg : 0 ≤ k
  · exact ⟨k,hnonneg,hk,fun v hv => by simpa only [abs_of_nonneg hnonneg] using hmin v hv⟩
  · have hkneg : k < 0 := lt_of_not_ge hnonneg
    have hkn : 0 ≤ -k := by linarith
    refine ⟨-k,hkn,physical_fourier_zero_neg z rho sigma p k hk,?_⟩
    intro v hv
    simpa only [abs_of_neg hkneg] using hmin v hv

/-- A single independently certified decay budget on a path provides one
uniform physical Fourier cutoff for every state on that path. -/
theorem path_physical_factor_unit_above_cutoff
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (S : Set ℝ) (B : ℝ)
    (hbudget : ∀ t ∈ S, decayBudget z rho sigma (p t) ≤ B) :
    ∀ t ∈ S, ∀ k : ℝ, rateCutoff z + B + 1 ≤ |k| →
      IsUnit (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (C z rho sigma (p t).1 (p t).2) k) := by
  intro t ht k hk
  apply physical_factor_unit_at_high_frequency z hz rho sigma hρ hσ (p t) k
  unfold safeCutoff
  linarith [hbudget t ht]

/-- A norm bound on any family of original amplitudes gives a uniform
high-frequency physical Fourier cutoff, without root or canonical premises. -/
theorem exists_uniform_path_axis_cutoff_of_amplitude_bound
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (S : Set ℝ) (M : ℝ)
    (hamp : ∀ t ∈ S, ‖p t‖ ≤ M) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ S, ∀ k : ℝ, R ≤ |k| →
      IsUnit (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (C z rho sigma (p t).1 (p t).2) k) := by
  obtain ⟨B,hB,hbudget⟩ := exists_budget_bound_on_amplitude_ball z rho sigma M
  refine ⟨rateCutoff z + B + 1,by linarith [(cutoff_nonneg z rho sigma (p 0)).1],?_⟩
  exact path_physical_factor_unit_above_cutoff z hz rho sigma hρ hσ p S B
    (fun t ht => hbudget (p t) (hamp t ht))

/-- A continuous finite original-amplitude path on a closed coupling
interval has one physical Fourier cutoff for its entire image. This uses
compactness, not root canonicity or amplitude-escape exclusion. -/
theorem exists_uniform_axis_cutoff_of_continuous_closed_path
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (hp : ContinuousOn p (Set.Icc 0 b)) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Set.Icc 0 b, ∀ k : ℝ, R ≤ |k| →
      IsUnit (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (C z rho sigma (p t).1 (p t).2) k) := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  exact exists_uniform_path_axis_cutoff_of_amplitude_bound
    z hz rho sigma hρ hσ p (Set.Icc 0 b) M hM

/-- Along any continuous closed finite path, there exists a finite real
frequency interval whose zero-free verification implies zero-freeness on
the entire physical Fourier axis. -/
theorem exists_compact_axis_test_for_continuous_closed_path
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (hp : ContinuousOn p (Set.Icc 0 b)) :
    ∃ R : ℝ, 0 < R ∧
      ((∀ t ∈ Set.Icc 0 b, ∀ k : ℝ, |k| ≤ R →
        (fourierFactor z rho sigma
          (amplitudeA z rho sigma (p t).1 (p t).2)
          (amplitudeQp z rho sigma (p t).1 (p t).2)
          (W z rho (p t).1 (p t).2)
          (C z rho sigma (p t).1 (p t).2) k).det ≠ 0) →
        ∀ t ∈ Set.Icc 0 b, ∀ k : ℝ,
          (fourierFactor z rho sigma
            (amplitudeA z rho sigma (p t).1 (p t).2)
            (amplitudeQp z rho sigma (p t).1 (p t).2)
            (W z rho (p t).1 (p t).2)
            (C z rho sigma (p t).1 (p t).2) k).det ≠ 0) := by
  obtain ⟨R,hR,hhigh⟩ := exists_uniform_axis_cutoff_of_continuous_closed_path
    z hz rho sigma hρ hσ p b hp
  refine ⟨R,hR,?_⟩
  intro hcompact t ht k
  by_cases hk : |k| ≤ R
  · exact hcompact t ht k hk
  · have hu := hhigh t ht k (le_of_lt (lt_of_not_ge hk))
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

/-- The endpoint may itself have a physical Fourier zero: closed-interval
continuity still gives one high-frequency cutoff, while the compact test
is required only on the initial half-open prefix. -/
theorem exists_compact_prefix_axis_test_of_continuous_closed_path
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ)
    (hp : ContinuousOn p (Set.Icc 0 b)) :
    ∃ R : ℝ, 0 < R ∧
      ((∀ t ∈ Set.Ico 0 b, ∀ k : ℝ, |k| ≤ R →
        (fourierFactor z rho sigma
          (amplitudeA z rho sigma (p t).1 (p t).2)
          (amplitudeQp z rho sigma (p t).1 (p t).2)
          (W z rho (p t).1 (p t).2)
          (C z rho sigma (p t).1 (p t).2) k).det ≠ 0) →
        ∀ t ∈ Set.Ico 0 b, ∀ k : ℝ,
          (fourierFactor z rho sigma
            (amplitudeA z rho sigma (p t).1 (p t).2)
            (amplitudeQp z rho sigma (p t).1 (p t).2)
            (W z rho (p t).1 (p t).2)
            (C z rho sigma (p t).1 (p t).2) k).det ≠ 0) := by
  obtain ⟨R,hR,hhigh⟩ := exists_uniform_axis_cutoff_of_continuous_closed_path
    z hz rho sigma hρ hσ p b hp
  refine ⟨R,hR,?_⟩
  intro hcompact t ht k
  by_cases hk : |k| ≤ R
  · exact hcompact t ht k hk
  · have ht' : t ∈ Set.Icc (0 : ℝ) b := ⟨ht.1,ht.2.le⟩
    have hu := hhigh t ht' k (le_of_lt (lt_of_not_ge hk))
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

/-- A verified finite frequency interval plus the explicit high-frequency
budget certifies nonvanishing on the entire real Fourier axis. -/
theorem path_axis_zero_free_of_compact_test
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (S : Set ℝ) (B : ℝ)
    (hbudget : ∀ t ∈ S, decayBudget z rho sigma (p t) ≤ B)
    (hcompact : ∀ t ∈ S, ∀ k : ℝ,
      |k| ≤ rateCutoff z + B + 1 →
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (C z rho sigma (p t).1 (p t).2) k).det ≠ 0) :
    ∀ t ∈ S, ∀ k : ℝ,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (C z rho sigma (p t).1 (p t).2) k).det ≠ 0 := by
  intro t ht k
  by_cases hk : |k| ≤ rateCutoff z + B + 1
  · exact hcompact t ht k hk
  · have hu := path_physical_factor_unit_above_cutoff
      z hz rho sigma hρ hσ p S B hbudget t ht k (le_of_lt (lt_of_not_ge hk))
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

end FMSA.Convergence.MixtureAxisHighFrequency
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.decayBudget_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.decayBudget_continuous
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.cutoff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.cutoff_nonneg
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.physical_fourier_determinant_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.physical_fourier_determinant_continuous
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.exists_budget_bound_on_amplitude_ball' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.exists_budget_bound_on_amplitude_ball
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.physical_factor_unit_at_high_frequency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.physical_factor_unit_at_high_frequency
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.physical_fourier_zero_set_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.physical_fourier_zero_set_isCompact
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.physical_fourier_zero_abs_minimum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.physical_fourier_zero_abs_minimum
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.physical_fourier_zero_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.physical_fourier_zero_neg
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.physical_fourier_nonnegative_zero_minimum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.physical_fourier_nonnegative_zero_minimum
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.path_physical_factor_unit_above_cutoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.path_physical_factor_unit_above_cutoff
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.exists_uniform_path_axis_cutoff_of_amplitude_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.exists_uniform_path_axis_cutoff_of_amplitude_bound
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.exists_uniform_axis_cutoff_of_continuous_closed_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.exists_uniform_axis_cutoff_of_continuous_closed_path
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.exists_compact_axis_test_for_continuous_closed_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.exists_compact_axis_test_for_continuous_closed_path
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.exists_compact_prefix_axis_test_of_continuous_closed_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.exists_compact_prefix_axis_test_of_continuous_closed_path
/-- info: 'FMSA.Convergence.MixtureAxisHighFrequency.path_axis_zero_free_of_compact_test' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisHighFrequency.path_axis_zero_free_of_compact_test
