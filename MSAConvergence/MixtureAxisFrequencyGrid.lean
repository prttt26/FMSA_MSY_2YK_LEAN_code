import MSAConvergence.MixtureCoefficientBudget
import MSAConvergence.CanonicalNeighborhood
import MSAConvergence.MixtureEndpointNoEscape
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Frequency slab certificates for the actual finite-mixture Fourier factor.
The moment bound is a real integral of the original full-line Baxter kernel. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace FMSA.Convergence.MixtureAxisFrequencyGrid
open FMSA.ExactMSA.MultiTailMixture
open MSAMixture
open FMSA.Paper
open FMSA.MatrixQ0
open FMSA.Paper.StableIntervalRadius
open FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.CanonicalNeighborhood
open FMSA.Convergence.MixtureAxisHighFrequency
open FMSA.Convergence.MixtureCoefficientBudget
open FMSA.Convergence.MixtureEndpointNoEscape
variable {N : ℕ} {T : Type*} [Fintype T]

def weightedFourierQ (z : T → ℝ) (rho sigma A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N) (k : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (Real.sqrt (rho i) : ℂ) *
    (Real.sqrt (rho j) : ℂ) * fourierQ z sigma A qp W C k i j)

def momentBudget (rho : Fin N → ℝ) (M : Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, |Real.sqrt (rho i)| * |Real.sqrt (rho j)| * M i j

/-- Finite positive Yukawa rates admit a common positive decay rate, also
when the tail index type is empty. -/
theorem exists_common_rate (z : T → ℝ) (hz : ∀ u, 0 < z u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u, δ < z u := by
  classical
  by_cases hT : Nonempty T
  · obtain ⟨u,_,hu⟩ := Finset.exists_min_image Finset.univ z
      ⟨Classical.choice hT,Finset.mem_univ _⟩
    refine ⟨z u/2,by linarith [hz u],?_⟩
    intro v
    have hv := hu v (Finset.mem_univ v)
    linarith [hz u]
  · refine ⟨1,by norm_num,?_⟩
    intro u
    exact False.elim (hT ⟨u⟩)

/-- The full-line actual Baxter kernel has an exponential moment anywhere
strictly above all negative Yukawa tail rates. -/
theorem actual_q_rate_integrable
    (z : T → ℝ) (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (s : ℂ) (hrate : ∀ u, 0 < s.re + z u) (i j : Fin N) :
    Integrable (fun r : ℝ => (q z sigma A qp W C i j r : ℂ) *
      Complex.exp (-s*r)) := by
  rw [q_complex_decomposition z sigma A qp W C hσ s i j]
  exact (qComplexPoly_integrable sigma A qp s i j).add
    (integrable_finsetSum _ (fun u _ =>
      qComplexRow_integrable z sigma W C s i j u (hrate u)))

/-- The actual unequal-diameter finite-mixture Baxter kernel has an honest
first absolute moment. No numerical or pathwise moment premise is needed. -/
theorem actual_q_first_absolute_moment_integrable
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (i j : Fin N) :
    Integrable (fun r : ℝ => |r| * |q z sigma A qp W C i j r|) := by
  obtain ⟨δ,hδ,hδz⟩ := exists_common_rate z hz
  let q0 : ℝ → ℂ := fun r => (q z sigma A qp W C i j r : ℂ)
  have hq0 : Integrable q0 := by
    simpa only [q0, zero_mul, neg_zero, Complex.exp_zero, mul_one] using
      actual_q_rate_integrable z sigma A qp W C hσ 0
        (fun u => by simpa using hz u) i j
  have hqδ : Integrable (fun r : ℝ => q0 r * Complex.exp ((δ : ℂ)*r)) := by
    simpa only [q0, neg_neg] using
      actual_q_rate_integrable z sigma A qp W C hσ (-δ : ℂ)
        (fun u => by simp only [Complex.neg_re, Complex.ofReal_re]; linarith [hδz u]) i j
  have hdom : Integrable (fun r : ℝ =>
      |edgeLo sigma i j| * ‖q0 r‖ + (1/δ) * ‖q0 r * Complex.exp ((δ : ℂ)*r)‖) :=
    (hq0.norm.const_mul _).add (hqδ.norm.const_mul _)
  have hmeas : AEStronglyMeasurable (fun r : ℝ =>
      |r| * |q z sigma A qp W C i j r|) := by
    have hnorm : AEStronglyMeasurable (fun r : ℝ => ‖q0 r‖) := hq0.aestronglyMeasurable.norm
    have hh := continuous_abs.aestronglyMeasurable.mul hnorm
    change AEStronglyMeasurable (fun r : ℝ => |r| * ‖q0 r‖) at hh
    simpa only [q0, Complex.norm_real, Real.norm_eq_abs] using hh
  apply Integrable.mono' hdom hmeas
  filter_upwards [] with r
  have hqzero (hr : r < edgeLo sigma i j) : q z sigma A qp W C i j r = 0 := by
    simp [q,hr]
  by_cases hrlo : r < edgeLo sigma i j
  · simp [hqzero hrlo, q0]
  · have hrlo' : edgeLo sigma i j ≤ r := le_of_not_gt hrlo
    by_cases hr : r < 0
    · have hrabs : |r| ≤ |edgeLo sigma i j| := by
        rw [abs_of_neg hr,abs_of_nonpos (by linarith : edgeLo sigma i j ≤ 0)]
        linarith
      have hnonneg : 0 ≤ (1/δ) * ‖q0 r * Complex.exp ((δ : ℂ)*r)‖ := by positivity
      simp only [Real.norm_eq_abs, abs_mul, abs_abs]
      calc
        |r| * |q z sigma A qp W C i j r| ≤
            |edgeLo sigma i j| * |q z sigma A qp W C i j r| :=
          mul_le_mul_of_nonneg_right hrabs (abs_nonneg _)
        _ ≤ |edgeLo sigma i j| * ‖q0 r‖ +
            (1/δ) * ‖q0 r * Complex.exp ((δ : ℂ)*r)‖ := by
          simpa only [q0, Complex.norm_real, Real.norm_eq_abs] using
            le_add_of_nonneg_right hnonneg
    · have hr0 : 0 ≤ r := le_of_not_gt hr
      have hδr : δ*r ≤ exp (δ*r) := by
        have hh := Real.add_one_le_exp (δ*r)
        linarith
      have hbound : r ≤ (1/δ)*exp (δ*r) := by
        calc
          r ≤ exp (δ*r)/δ := (le_div_iff₀ hδ).mpr (by nlinarith)
          _ = (1/δ)*exp (δ*r) := by ring
      have hnonneg : 0 ≤ |edgeLo sigma i j| * ‖q0 r‖ := by positivity
      simp only [Real.norm_eq_abs, abs_mul, abs_abs]
      calc
        |r| * |q z sigma A qp W C i j r| ≤
            (1/δ)*exp (δ*r) * |q z sigma A qp W C i j r| := by
          rw [abs_of_nonneg hr0]
          exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
        _ ≤ |edgeLo sigma i j| * ‖q0 r‖ +
            (1/δ) * ‖q0 r * Complex.exp ((δ : ℂ)*r)‖ := by
          have he : ‖q0 r * Complex.exp ((δ : ℂ)*r)‖ =
              |q z sigma A qp W C i j r| * exp (δ*r) := by
            simp [q0,Complex.norm_exp,Complex.mul_re]
          rw [he]
          have hnonneg' : 0 ≤ |edgeLo sigma i j| *
              |q z sigma A qp W C i j r| := by
            simpa only [q0,Complex.norm_real,Real.norm_eq_abs] using hnonneg
          calc
            (1/δ)*exp (δ*r) * |q z sigma A qp W C i j r| =
                (1/δ) * (|q z sigma A qp W C i j r| * exp (δ*r)) := by ring
            _ ≤ |edgeLo sigma i j| * |q z sigma A qp W C i j r| +
                (1/δ) * (|q z sigma A qp W C i j r| * exp (δ*r)) :=
              le_add_of_nonneg_left hnonneg'
            _ = |edgeLo sigma i j| * ‖q0 r‖ +
                (1/δ) * (|q z sigma A qp W C i j r| * exp (δ*r)) := by
              simp [q0]

/-- A first absolute moment bounds variation of the genuine Fourier integral. -/
theorem fourierQ_sub_norm_le_moment
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (i j : Fin N) (a k M : ℝ)
    (hM : (∫ r : ℝ, |r| * |q z sigma A qp W C i j r|) ≤ M) :
    ‖fourierQ z sigma A qp W C k i j -
      fourierQ z sigma A qp W C a i j‖ ≤ |k-a| * M := by
  let q0 : ℝ → ℂ := fun r => (q z sigma A qp W C i j r : ℂ)
  let fk : ℝ → ℂ := fun r => q0 r * Complex.exp (-(Complex.I * (k : ℂ)) * (r : ℂ))
  let fa : ℝ → ℂ := fun r => q0 r * Complex.exp (-(Complex.I * (a : ℂ)) * (r : ℂ))
  have hmoment := actual_q_first_absolute_moment_integrable
    z hz sigma A qp W C hσ i j
  have hik : Integrable fk := by
    simpa only [fk, q0] using q_complex_weighted_integrable z hz sigma A qp W C hσ
      (Complex.I * (k : ℂ)) (by simp) i j
  have hia : Integrable fa := by
    simpa only [fa, q0] using q_complex_weighted_integrable z hz sigma A qp W C hσ
      (Complex.I * (a : ℂ)) (by simp) i j
  have hpoint (r : ℝ) : ‖fk r - fa r‖ ≤ |k-a| * (|r| * |q z sigma A qp W C i j r|) := by
    have he : Complex.exp (-(Complex.I * (k : ℂ)) * (r : ℂ)) -
        Complex.exp (-(Complex.I * (a : ℂ)) * (r : ℂ)) =
        Complex.exp (-(Complex.I * (a : ℂ)) * (r : ℂ)) *
          (Complex.exp (Complex.I * ((-(k-a)*r : ℝ) : ℂ)) - 1) := by
      have harg : -(Complex.I * (k : ℂ)) * (r : ℂ) =
          -(Complex.I * (a : ℂ)) * (r : ℂ) +
            Complex.I * ((-(k-a)*r : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, Complex.exp_add]
      ring
    have hphase : ‖Complex.exp (Complex.I * ((-(k-a)*r : ℝ) : ℂ)) - 1‖ ≤
        |k-a| * |r| := by
      simpa only [Real.norm_eq_abs, abs_neg, abs_mul] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(k-a)*r))
    change ‖q0 r * Complex.exp (-(Complex.I * (k : ℂ)) * (r : ℂ)) -
      q0 r * Complex.exp (-(Complex.I * (a : ℂ)) * (r : ℂ))‖ ≤ _
    rw [← mul_sub, he, norm_mul, norm_mul]
    have hunit : ‖Complex.exp (-(Complex.I * (a : ℂ)) * (r : ℂ))‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re]
    rw [hunit, one_mul]
    calc
      ‖q0 r‖ * ‖Complex.exp (Complex.I * ↑(-(k - a) * r)) - 1‖
          ≤ ‖q0 r‖ * (|k-a| * |r|) :=
            mul_le_mul_of_nonneg_left hphase (norm_nonneg (q0 r))
      _ = |k-a| * (|r| * |q z sigma A qp W C i j r|) := by
        simp only [q0, Complex.norm_real, Real.norm_eq_abs]
        ring
  have hdom : Integrable (fun r : ℝ => |k-a| * (|r| * |q z sigma A qp W C i j r|)) :=
    hmoment.const_mul _
  have hnorm : Integrable (fun r : ℝ => ‖fk r - fa r‖) := (hik.sub hia).norm
  have hint : (∫ r : ℝ, ‖fk r-fa r‖) ≤
      ∫ r : ℝ, |k-a| * (|r| * |q z sigma A qp W C i j r|) :=
    integral_mono hnorm hdom hpoint
  unfold fourierQ
  change ‖(∫ r, fk r) - (∫ r, fa r)‖ ≤ _
  rw [← integral_sub hik hia]
  calc
    ‖∫ r, fk r-fa r‖ ≤ ∫ r, ‖fk r-fa r‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r, |k-a| * (|r| * |q z sigma A qp W C i j r|) := hint
    _ = |k-a| * (∫ r, |r| * |q z sigma A qp W C i j r|) := integral_const_mul ..
    _ ≤ |k-a| * M := mul_le_mul_of_nonneg_left hM (abs_nonneg _)

/-- The entry moments supply one matrix-norm Lipschitz budget. -/
theorem weightedFourierQ_sub_normSum_le_moment
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (a k : ℝ) (M : Fin N → Fin N → ℝ)
    (hM : ∀ i j, (∫ r : ℝ,
      |r| * |q z sigma A qp W C i j r|) ≤ M i j) :
    complexNormSum (weightedFourierQ z rho sigma A qp W C k -
      weightedFourierQ z rho sigma A qp W C a) ≤
      |k-a| * momentBudget rho M := by
  unfold complexNormSum momentBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.sub_apply, weightedFourierQ, Matrix.of_apply]
  rw [← mul_sub, norm_mul, norm_mul]
  have hq := fourierQ_sub_norm_le_moment z hz sigma A qp W C hσ i j a k
    (M i j) (hM i j)
  calc
    ‖(Real.sqrt (rho i) : ℂ)‖ * ‖(Real.sqrt (rho j) : ℂ)‖ *
        ‖fourierQ z sigma A qp W C k i j - fourierQ z sigma A qp W C a i j‖
      ≤ ‖(Real.sqrt (rho i) : ℂ)‖ * ‖(Real.sqrt (rho j) : ℂ)‖ *
          (|k-a| * M i j) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = |k-a| * (|Real.sqrt (rho i)| * |Real.sqrt (rho j)| * M i j) := by
      simp only [Complex.norm_real, Real.norm_eq_abs]
      ring

/-- A certified inverse at one sample excludes every zero in its frequency
slab. The only analytic input is the first absolute moment of the actual Q. -/
theorem factor_det_ne_zero_on_sample_slab
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (a k R : ℝ) (M : Fin N → Fin N → ℝ)
    (hM : ∀ i j, (∫ r : ℝ,
      |r| * |q z sigma A qp W C i j r|) ≤ M i j)
    (hbase : (fourierFactor z rho sigma A qp W C a).det ≠ 0)
    (hR : complexNormSum ((fourierFactor z rho sigma A qp W C a)⁻¹) ≤ R)
    (hstep : R * (|k-a| * momentBudget rho M) < 1) :
    (fourierFactor z rho sigma A qp W C k).det ≠ 0 := by
  let Q := weightedFourierQ z rho sigma A qp W C a
  let P := weightedFourierQ z rho sigma A qp W C k
  have hfactor (v : ℝ) : fourierFactor z rho sigma A qp W C v =
      1 - weightedFourierQ z rho sigma A qp W C v := rfl
  have hu : IsUnit (1-Q) := by
    rw [← hfactor a]
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hbase)
  have hRnonneg : 0 ≤ R := (complexNormSum_nonneg _).trans hR
  have hdiff : complexNormSum (P-Q) ≤ |k-a| * momentBudget rho M :=
    weightedFourierQ_sub_normSum_le_moment z hz rho sigma A qp W C hσ a k M
      hM
  have hsmall : complexNormSum ((1-Q)⁻¹ * (P-Q)) < 1 := by
    calc
      complexNormSum ((1-Q)⁻¹ * (P-Q))
          ≤ complexNormSum ((1-Q)⁻¹) * complexNormSum (P-Q) :=
            complexNormSum_mul_le _ _
      _ ≤ R * (|k-a| * momentBudget rho M) :=
        mul_le_mul hR hdiff (complexNormSum_nonneg _) hRnonneg
      _ < 1 := hstep
  have hunit := unit_of_inverse_perturbation Q P hu hsmall
  rw [hfactor k]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-- Finitely many certified frequency samples, with inverse and first-moment
bounds uniform on a same-HS-seed root prefix, exclude original amplitude
escape. The coverage inequality is a finite real-arithmetic obligation. -/
theorem hs_grid_certificate_uniform_amplitude_bound
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = (0,baseSeed z rho sigma))
    (hp : ContinuousOn p (Set.Ico 0 b))
    (hroot : ∀ t ∈ Set.Ico 0 b,
      IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA : ∀ t ∈ Set.Ico 0 b, ∀ j,
      |amplitudeA z rho sigma (p t).1 (p t).2 j| ≤ Abar j)
    (hQ : ∀ t ∈ Set.Ico 0 b, ∀ i j,
      |amplitudeQp z rho sigma (p t).1 (p t).2 i j| ≤ Qbar i j)
    (hW : ∀ t ∈ Set.Ico 0 b, ∀ u i j,
      |W z rho (p t).1 (p t).2 u i j| ≤ Wbar u i j)
    (hC : ∀ t ∈ Set.Ico 0 b, ∀ u i j,
      |FMSA.ExactMSA.MultiTailMixture.C z rho sigma
        (p t).1 (p t).2 u i j| ≤ Cbar u i j)
    (samples : Finset ℝ) (R : ℝ → ℝ)
    (M : Fin N → Fin N → ℝ)
    (hM : ∀ t ∈ Set.Ico 0 b, ∀ i j,
      (∫ r : ℝ, |r| *
        |q z sigma
          (amplitudeA z rho sigma (p t).1 (p t).2)
          (amplitudeQp z rho sigma (p t).1 (p t).2)
          (W z rho (p t).1 (p t).2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
            (p t).1 (p t).2) i j r|) ≤ M i j)
    (hbase : ∀ t ∈ Set.Ico 0 b, ∀ a ∈ samples,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) a).det ≠ 0)
    (hR : ∀ t ∈ Set.Ico 0 b, ∀ a ∈ samples,
      complexNormSum ((fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) a)⁻¹) ≤ R a)
    (hcover : ∀ k : ℝ,
      |k| ≤ rateCutoff z + explicitBudget z rho sigma Abar Qbar Wbar Cbar + 1 →
      ∃ a ∈ samples, R a * (|k-a| * momentBudget rho M) < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ico 0 b, ‖p t‖ ≤ B := by
  apply hs_coefficient_certificate_uniform_amplitude_bound z hz rho sigma
    hρ hσ hη K hK p b hb hp0 hp hroot Abar Qbar Wbar Cbar
    hA hQ hW hC
  intro t ht k hk
  obtain ⟨a,ha,hstep⟩ := hcover k hk
  exact factor_det_ne_zero_on_sample_slab z hz rho sigma
    (amplitudeA z rho sigma (p t).1 (p t).2)
    (amplitudeQp z rho sigma (p t).1 (p t).2)
    (W z rho (p t).1 (p t).2)
    (FMSA.ExactMSA.MultiTailMixture.C z rho sigma (p t).1 (p t).2)
    (fun i => (hσ i).le) a k (R a) M
    (hM t ht) (hbase t ht a ha) (hR t ht a ha) hstep

end FMSA.Convergence.MixtureAxisFrequencyGrid

/-- info: 'FMSA.Convergence.MixtureAxisFrequencyGrid.exists_common_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisFrequencyGrid.exists_common_rate
/-- info: 'FMSA.Convergence.MixtureAxisFrequencyGrid.actual_q_rate_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisFrequencyGrid.actual_q_rate_integrable
/-- info: 'FMSA.Convergence.MixtureAxisFrequencyGrid.actual_q_first_absolute_moment_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisFrequencyGrid.actual_q_first_absolute_moment_integrable
/-- info: 'FMSA.Convergence.MixtureAxisFrequencyGrid.fourierQ_sub_norm_le_moment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisFrequencyGrid.fourierQ_sub_norm_le_moment
/-- info: 'FMSA.Convergence.MixtureAxisFrequencyGrid.weightedFourierQ_sub_normSum_le_moment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisFrequencyGrid.weightedFourierQ_sub_normSum_le_moment
/-- info: 'FMSA.Convergence.MixtureAxisFrequencyGrid.factor_det_ne_zero_on_sample_slab' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisFrequencyGrid.factor_det_ne_zero_on_sample_slab
/-- info: 'FMSA.Convergence.MixtureAxisFrequencyGrid.hs_grid_certificate_uniform_amplitude_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureAxisFrequencyGrid.hs_grid_certificate_uniform_amplitude_bound
