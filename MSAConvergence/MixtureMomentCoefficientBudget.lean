import MSAConvergence.MixtureAxisFrequencyGrid

/-! A fixed positive reference Baxter kernel dominates every coefficient
box, giving an actual first-moment budget without a separate path integral. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace FMSA.Convergence.MixtureMomentCoefficientBudget
open FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Paper FMSA.MatrixQ0 FMSA.Paper.StableIntervalRadius
open FMSA.Convergence.MixtureAxisFrequencyGrid
open FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.MixtureAxisHighFrequency
open FMSA.Convergence.MixtureCoefficientBudget
variable {N : ℕ} {T : Type*} [Fintype T]

def referenceQ (z : T → ℝ) (sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (i j : Fin N) (r : ℝ) : ℝ :=
  q z sigma Abar (fun i j => -Qbar i j) Wbar Cbar i j r

def referenceMoment (z : T → ℝ) (sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (i j : Fin N) : ℝ :=
  ∫ r : ℝ, |r| * |referenceQ z sigma Abar Qbar Wbar Cbar i j r|

/-- Any actual Baxter kernel inside four coefficient caps is pointwise
dominated by one fixed reference kernel on the whole real line. -/
theorem actual_q_abs_le_reference_q
    (z : T → ℝ) (sigma A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA : ∀ j, |A j| ≤ Abar j)
    (hQ : ∀ i j, |qp i j| ≤ Qbar i j)
    (hW : ∀ u i j, |W u i j| ≤ Wbar u i j)
    (hC : ∀ u i j, |C u i j| ≤ Cbar u i j)
    (i j : Fin N) (r : ℝ) :
    |q z sigma A qp W C i j r| ≤
      referenceQ z sigma Abar Qbar Wbar Cbar i j r := by
  unfold referenceQ q
  by_cases hlo : r < edgeLo sigma i j
  · simp [hlo]
  · simp only [if_neg hlo]
    by_cases hhi : r ≤ edgeHi sigma i j
    · simp only [if_pos hhi]
      have hd : r-edgeHi sigma i j ≤ 0 := by linarith
      have hqp : |qp i j * (r-edgeHi sigma i j)| ≤
          -Qbar i j * (r-edgeHi sigma i j) := by
        rw [abs_mul,abs_of_nonpos hd]
        have h := mul_le_mul_of_nonneg_right (hQ i j) (by linarith : 0 ≤ edgeHi sigma i j-r)
        nlinarith
      have hA' : |A j / 2 * (r-edgeHi sigma i j)^2| ≤
          Abar j / 2 * (r-edgeHi sigma i j)^2 := by
        have h := mul_le_mul_of_nonneg_right (hA j) (by positivity : 0 ≤ (r-edgeHi sigma i j)^2/2)
        calc
          |A j / 2 * (r-edgeHi sigma i j)^2| =
              |A j| * ((r-edgeHi sigma i j)^2/2) := by
                rw [abs_mul,abs_div]
                simp only [abs_of_nonneg (sq_nonneg (r-edgeHi sigma i j)), Nat.abs_ofNat]
                ring
          _ ≤ Abar j * ((r-edgeHi sigma i j)^2/2) := h
          _ = Abar j / 2 * (r-edgeHi sigma i j)^2 := by ring
      have hsum : |∑ u, (W u i j * exp (-z u*(r-edgeLo sigma i j)) + C u i j)| ≤
          ∑ u, (Wbar u i j * exp (-z u*(r-edgeLo sigma i j)) + Cbar u i j) := by
        calc
          _ ≤ ∑ u, |W u i j * exp (-z u*(r-edgeLo sigma i j)) + C u i j| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ u, (Wbar u i j * exp (-z u*(r-edgeLo sigma i j)) + Cbar u i j) := by
            apply Finset.sum_le_sum
            intro u _
            have hWu : |W u i j * exp (-z u*(r-edgeLo sigma i j))| ≤
                Wbar u i j * exp (-z u*(r-edgeLo sigma i j)) := by
              rw [abs_mul,abs_of_pos (exp_pos _)]
              exact mul_le_mul_of_nonneg_right (hW u i j) (exp_pos _).le
            exact (abs_add_le _ _).trans (add_le_add hWu (hC u i j))
      calc
        |qp i j * (r-edgeHi sigma i j) + A j / 2 * (r-edgeHi sigma i j)^2 +
            ∑ u, (W u i j * exp (-z u*(r-edgeLo sigma i j)) + C u i j)|
          ≤ |qp i j * (r-edgeHi sigma i j)| +
            |A j / 2 * (r-edgeHi sigma i j)^2| +
            |∑ u, (W u i j * exp (-z u*(r-edgeLo sigma i j)) + C u i j)| := by
              linarith [abs_add_le (qp i j * (r-edgeHi sigma i j))
                (A j / 2 * (r-edgeHi sigma i j)^2),
                abs_add_le (qp i j * (r-edgeHi sigma i j) +
                  A j / 2 * (r-edgeHi sigma i j)^2)
                  (∑ u, (W u i j * exp (-z u*(r-edgeLo sigma i j)) + C u i j))]
        _ ≤ -Qbar i j * (r-edgeHi sigma i j) +
            Abar j / 2 * (r-edgeHi sigma i j)^2 +
            ∑ u, (Wbar u i j * exp (-z u*(r-edgeLo sigma i j)) + Cbar u i j) := by
              linarith [hqp,hA',hsum]
    · simp only [if_neg hhi]
      have hsum : |∑ u, (W u i j * exp (-z u*(r-edgeLo sigma i j)) +
          C u i j * exp (-z u*(r-edgeHi sigma i j)))| ≤
          ∑ u, (Wbar u i j * exp (-z u*(r-edgeLo sigma i j)) +
            Cbar u i j * exp (-z u*(r-edgeHi sigma i j))) := by
        calc
          _ ≤ ∑ u, |W u i j * exp (-z u*(r-edgeLo sigma i j)) +
              C u i j * exp (-z u*(r-edgeHi sigma i j))| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ u, (Wbar u i j * exp (-z u*(r-edgeLo sigma i j)) +
              Cbar u i j * exp (-z u*(r-edgeHi sigma i j))) := by
            apply Finset.sum_le_sum
            intro u _
            have hWu : |W u i j * exp (-z u*(r-edgeLo sigma i j))| ≤
                Wbar u i j * exp (-z u*(r-edgeLo sigma i j)) := by
              rw [abs_mul,abs_of_pos (exp_pos _)]
              exact mul_le_mul_of_nonneg_right (hW u i j) (exp_pos _).le
            have hCu : |C u i j * exp (-z u*(r-edgeHi sigma i j))| ≤
                Cbar u i j * exp (-z u*(r-edgeHi sigma i j)) := by
              rw [abs_mul,abs_of_pos (exp_pos _)]
              exact mul_le_mul_of_nonneg_right (hC u i j) (exp_pos _).le
            exact (abs_add_le _ _).trans (add_le_add hWu hCu)
      exact hsum

/-- The positive reference kernel's first absolute moment is a finite,
fixed function of rates, diameters and four coefficient caps. -/
theorem referenceMoment_integrable
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (i j : Fin N) :
    Integrable (fun r : ℝ => |r| *
      |referenceQ z sigma Abar Qbar Wbar Cbar i j r|) := by
  exact actual_q_first_absolute_moment_integrable z hz sigma Abar
    (fun i j => -Qbar i j) Wbar Cbar hσ i j

/-- Four coefficient caps alone bound the actual first absolute moments.
The bound is the fixed reference integral, independent of the MSA amplitudes. -/
theorem actual_first_moment_le_referenceMoment
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix T N) (hσ : ∀ i, 0 ≤ sigma i)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA : ∀ j, |A j| ≤ Abar j)
    (hQ : ∀ i j, |qp i j| ≤ Qbar i j)
    (hW : ∀ u i j, |W u i j| ≤ Wbar u i j)
    (hC : ∀ u i j, |C u i j| ≤ Cbar u i j)
    (i j : Fin N) :
    (∫ r : ℝ, |r| * |q z sigma A qp W C i j r|) ≤
      referenceMoment z sigma Abar Qbar Wbar Cbar i j := by
  unfold referenceMoment
  apply integral_mono
    (actual_q_first_absolute_moment_integrable z hz sigma A qp W C hσ i j)
    (referenceMoment_integrable z hz sigma Abar Qbar Wbar Cbar hσ i j)
  intro r
  exact mul_le_mul_of_nonneg_left
    ((actual_q_abs_le_reference_q z sigma A qp W C Abar Qbar Wbar Cbar
      hA hQ hW hC i j r).trans (le_abs_self _)) (abs_nonneg r)

/-- Valid nonnegative coefficient caps make the reference Baxter kernel
itself pointwise nonnegative. -/
theorem referenceQ_nonneg
    (z : T → ℝ) (sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (hA : ∀ j, 0 ≤ Abar j) (hQ : ∀ i j, 0 ≤ Qbar i j)
    (hW : ∀ u i j, 0 ≤ Wbar u i j)
    (hC : ∀ u i j, 0 ≤ Cbar u i j)
    (i j : Fin N) (r : ℝ) :
    0 ≤ referenceQ z sigma Abar Qbar Wbar Cbar i j r := by
  have hh := actual_q_abs_le_reference_q z sigma Abar
    (fun i j => -Qbar i j) Wbar Cbar Abar Qbar Wbar Cbar
    (fun j => by rw [abs_of_nonneg (hA j)])
    (fun i j => by rw [abs_neg,abs_of_nonneg (hQ i j)])
    (fun u i j => by rw [abs_of_nonneg (hW u i j)])
    (fun u i j => by rw [abs_of_nonneg (hC u i j)]) i j r
  exact (abs_nonneg _).trans hh

def transformMomentUpper (z : T → ℝ) (sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (δ : ℝ) (i j : Fin N) : ℝ :=
  (|edgeLo sigma i j| + 1/δ) * exp (-δ*edgeLo sigma i j) *
    Qhat z sigma Abar (fun i j => -Qbar i j) Wbar Cbar (-δ) i j

/-- The positive-rate reference moment is bounded by one explicit
real Laplace transform evaluation strictly inside its convergence domain. -/
theorem referenceMoment_le_transformMomentUpper
    (z : T → ℝ) (sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (hσ : ∀ i, 0 ≤ sigma i)
    (hA : ∀ j, 0 ≤ Abar j) (hQ : ∀ i j, 0 ≤ Qbar i j)
    (hW : ∀ u i j, 0 ≤ Wbar u i j)
    (hC : ∀ u i j, 0 ≤ Cbar u i j)
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u)
    (i j : Fin N) :
    referenceMoment z sigma Abar Qbar Wbar Cbar i j ≤
      transformMomentUpper z sigma Abar Qbar Wbar Cbar δ i j := by
  let qref : ℝ → ℝ := referenceQ z sigma Abar Qbar Wbar Cbar i j
  have hqpos (r : ℝ) : 0 ≤ qref r :=
    referenceQ_nonneg z sigma Abar Qbar Wbar Cbar hA hQ hW hC i j r
  have hqzero (r : ℝ) (hr : r < edgeLo sigma i j) : qref r = 0 := by
    simp [qref,referenceQ,q,hr]
  have hraw : Integrable (fun r : ℝ => |r| * |qref r|) :=
    referenceMoment_integrable z (fun u => lt_trans hδ (hrate u))
      sigma Abar Qbar Wbar Cbar hσ i j
  have hweightComplex : Integrable (fun r : ℝ => (qref r : ℂ) *
      Complex.exp (((δ : ℝ) : ℂ) * r)) := by
    simpa only [qref,referenceQ,neg_neg] using
      actual_q_rate_integrable z sigma Abar (fun i j => -Qbar i j)
        Wbar Cbar hσ (-δ : ℂ)
        (fun u => by simp only [Complex.neg_re,Complex.ofReal_re]; linarith [hrate u]) i j
  have hweightReal : Integrable (fun r : ℝ => qref r * exp (δ*r)) := by
    have hcast : Integrable (fun r : ℝ => ((qref r * exp (δ*r) : ℝ) : ℂ)) := by
      convert hweightComplex using 1
      funext r
      simp [Complex.ofReal_exp]
    simpa [Complex.exp_re,Complex.mul_re] using hcast.re
  have hdom : Integrable (fun r : ℝ =>
      (|edgeLo sigma i j|+1/δ)*exp (-δ*edgeLo sigma i j) *
        (qref r*exp (δ*r))) :=
    hweightReal.const_mul _
  have hpoint (r : ℝ) : |r| * |qref r| ≤
      (|edgeLo sigma i j|+1/δ)*exp (-δ*edgeLo sigma i j) *
        (qref r*exp (δ*r)) := by
    by_cases hr : r < edgeLo sigma i j
    · simp [hqzero r hr]
    · have ht : 0 ≤ r-edgeLo sigma i j := by linarith
      have hδt : δ*(r-edgeLo sigma i j) ≤ exp (δ*(r-edgeLo sigma i j)) := by
        linarith [Real.add_one_le_exp (δ*(r-edgeLo sigma i j))]
      have htbound : r-edgeLo sigma i j ≤
          (1/δ)*exp (δ*(r-edgeLo sigma i j)) := by
        calc
          r-edgeLo sigma i j ≤ exp (δ*(r-edgeLo sigma i j))/δ :=
            (le_div_iff₀ hδ).mpr (by nlinarith)
          _ = (1/δ)*exp (δ*(r-edgeLo sigma i j)) := by ring
      have hbase : 1 ≤ exp (δ*(r-edgeLo sigma i j)) := by
        linarith [Real.add_one_le_exp (δ*(r-edgeLo sigma i j)),mul_nonneg hδ.le ht]
      have hrabs : |r| ≤ |edgeLo sigma i j| + (r-edgeLo sigma i j) := by
        have hh := abs_add_le (edgeLo sigma i j) (r-edgeLo sigma i j)
        simpa only [show edgeLo sigma i j + (r-edgeLo sigma i j) = r by ring,
          abs_of_nonneg ht] using hh
      have hcap : |r| ≤ (|edgeLo sigma i j|+1/δ) *
          exp (δ*(r-edgeLo sigma i j)) := by
        have hfirst := mul_le_mul_of_nonneg_left hbase (abs_nonneg (edgeLo sigma i j))
        nlinarith [hrabs,htbound,hfirst]
      have he : exp (δ*(r-edgeLo sigma i j)) =
          exp (-δ*edgeLo sigma i j)*exp (δ*r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [abs_of_nonneg (hqpos r)]
      calc
        |r| * qref r ≤ ((|edgeLo sigma i j|+1/δ) *
            exp (δ*(r-edgeLo sigma i j))) * qref r :=
          mul_le_mul_of_nonneg_right hcap (hqpos r)
        _ = (|edgeLo sigma i j|+1/δ)*exp (-δ*edgeLo sigma i j) *
            (qref r*exp (δ*r)) := by rw [he]; ring
  have hraw' : Integrable (fun r : ℝ => |r| * qref r) := by
    simpa only [abs_of_nonneg (hqpos _)] using hraw
  have hint : (∫ r : ℝ, |r| * qref r) ≤
      ∫ r : ℝ, (|edgeLo sigma i j|+1/δ)*exp (-δ*edgeLo sigma i j)*
        (qref r*exp (δ*r)) := by
    apply integral_mono hraw' hdom
    intro r
    simpa only [abs_of_nonneg (hqpos r)] using hpoint r
  have htransform : (∫ r : ℝ, qref r*exp (δ*r)) =
      Qhat z sigma Abar (fun i j => -Qbar i j) Wbar Cbar (-δ) i j := by
    have hcomplex := FMSA.Convergence.CanonicalKernelEstimates.full_q_integral_rate_domain
      z sigma Abar (fun i j => -Qbar i j) Wbar Cbar hσ (-δ : ℂ)
      (by simp [ne_of_gt hδ])
      (fun u => by simp only [Complex.neg_re,Complex.ofReal_re]; linarith [hrate u]) i j
    have hqeq : QhatComplex z sigma Abar (fun i j => -Qbar i j)
        Wbar Cbar (-δ : ℂ) i j =
        (Qhat z sigma Abar (fun i j => -Qbar i j) Wbar Cbar (-δ) i j : ℂ) := by
      simpa only [Complex.ofReal_neg] using
        (QhatComplex_ofReal z sigma Abar (fun i j => -Qbar i j)
          Wbar Cbar (-δ) i j)
    rw [hqeq] at hcomplex
    have hcast : ((∫ r : ℝ, qref r*exp (δ*r) : ℝ) : ℂ) =
        (Qhat z sigma Abar (fun i j => -Qbar i j) Wbar Cbar (-δ) i j : ℂ) := by
      rw [← integral_complex_ofReal]
      calc
        (∫ r : ℝ, ((qref r*exp (δ*r) : ℝ) : ℂ)) =
            ∫ r : ℝ, (q z sigma Abar (fun i j => -Qbar i j) Wbar Cbar i j r : ℂ) *
              Complex.exp (-(-δ : ℂ)*r) := by
          apply integral_congr_ae
          filter_upwards [] with r
          simp [qref,referenceQ,Complex.ofReal_exp]
        _ = _ := hcomplex
    exact Complex.ofReal_injective hcast
  unfold referenceMoment transformMomentUpper
  change (∫ r : ℝ, |r| * |qref r|) ≤ _
  simpa only [abs_of_nonneg (hqpos _),integral_const_mul,htransform] using hint

/-- The rational-exponential upper expression is nonnegative whenever its
four caps are nonnegative and the rate-domain conditions hold. -/
theorem transformMomentUpper_nonneg
    (z : T → ℝ) (sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (hσ : ∀ i, 0 ≤ sigma i)
    (hA : ∀ j, 0 ≤ Abar j) (hQ : ∀ i j, 0 ≤ Qbar i j)
    (hW : ∀ u i j, 0 ≤ Wbar u i j)
    (hC : ∀ u i j, 0 ≤ Cbar u i j)
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u)
    (i j : Fin N) :
    0 ≤ transformMomentUpper z sigma Abar Qbar Wbar Cbar δ i j := by
  have hM : 0 ≤ referenceMoment z sigma Abar Qbar Wbar Cbar i j := by
    unfold referenceMoment
    exact integral_nonneg (fun r => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  exact hM.trans (referenceMoment_le_transformMomentUpper z sigma Abar Qbar Wbar Cbar
    hσ hA hQ hW hC δ hδ hrate i j)

/-- Uniform BH coefficient boxes give the grid theorem's pathwise moment
certificate from one fixed reference integral per species pair. -/
theorem path_actual_moment_le_referenceMoment
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hσ : ∀ i, 0 ≤ sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (S : Set ℝ)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA : ∀ t ∈ S, ∀ j,
      |amplitudeA z rho sigma (p t).1 (p t).2 j| ≤ Abar j)
    (hQ : ∀ t ∈ S, ∀ i j,
      |amplitudeQp z rho sigma (p t).1 (p t).2 i j| ≤ Qbar i j)
    (hW : ∀ t ∈ S, ∀ u i j,
      |W z rho (p t).1 (p t).2 u i j| ≤ Wbar u i j)
    (hC : ∀ t ∈ S, ∀ u i j,
      |FMSA.ExactMSA.MultiTailMixture.C z rho sigma
        (p t).1 (p t).2 u i j| ≤ Cbar u i j) :
    ∀ t ∈ S, ∀ i j,
      (∫ r : ℝ, |r| *
        |q z sigma
          (amplitudeA z rho sigma (p t).1 (p t).2)
          (amplitudeQp z rho sigma (p t).1 (p t).2)
          (W z rho (p t).1 (p t).2)
          (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
            (p t).1 (p t).2) i j r|) ≤
        referenceMoment z sigma Abar Qbar Wbar Cbar i j := by
  intro t ht i j
  exact actual_first_moment_le_referenceMoment z hz sigma
    (amplitudeA z rho sigma (p t).1 (p t).2)
    (amplitudeQp z rho sigma (p t).1 (p t).2)
    (W z rho (p t).1 (p t).2)
    (FMSA.ExactMSA.MultiTailMixture.C z rho sigma (p t).1 (p t).2)
    hσ Abar Qbar Wbar Cbar (hA t ht) (hQ t ht) (hW t ht)
    (hC t ht) i j

/-- A finite frequency grid and four BH coefficient caps suffice for
original mixture amplitude noescape; no separate path integral bound is
supplied. All first moments use the fixed positive reference kernel. -/
theorem hs_coefficient_grid_uniform_amplitude_bound
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
      ∃ a ∈ samples,
        R a * (|k-a| *
          momentBudget rho (referenceMoment z sigma Abar Qbar Wbar Cbar)) < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ico 0 b, ‖p t‖ ≤ B := by
  apply hs_grid_certificate_uniform_amplitude_bound z hz rho sigma hρ hσ hη
    K hK p b hb hp0 hp hroot Abar Qbar Wbar Cbar hA hQ hW hC
    samples R (referenceMoment z sigma Abar Qbar Wbar Cbar)
  · exact path_actual_moment_le_referenceMoment z hz rho sigma
      (fun i => (hσ i).le) p (Set.Ico 0 b) Abar Qbar Wbar Cbar hA hQ hW hC
  · exact hbase
  · exact hR
  · exact hcover

/-- The entire frequency-grid noescape certificate uses a real rational-
exponential transform expression for the first moment, with no integral
left in its frequency-coverage premise. -/
theorem hs_transform_grid_uniform_amplitude_bound
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
    (hA0 : ∀ j, 0 ≤ Abar j) (hQ0 : ∀ i j, 0 ≤ Qbar i j)
    (hW0 : ∀ u i j, 0 ≤ Wbar u i j)
    (hC0 : ∀ u i j, 0 ≤ Cbar u i j)
    (hA : ∀ t ∈ Set.Ico 0 b, ∀ j,
      |amplitudeA z rho sigma (p t).1 (p t).2 j| ≤ Abar j)
    (hQ : ∀ t ∈ Set.Ico 0 b, ∀ i j,
      |amplitudeQp z rho sigma (p t).1 (p t).2 i j| ≤ Qbar i j)
    (hW : ∀ t ∈ Set.Ico 0 b, ∀ u i j,
      |W z rho (p t).1 (p t).2 u i j| ≤ Wbar u i j)
    (hC : ∀ t ∈ Set.Ico 0 b, ∀ u i j,
      |FMSA.ExactMSA.MultiTailMixture.C z rho sigma
        (p t).1 (p t).2 u i j| ≤ Cbar u i j)
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u)
    (samples : Finset ℝ) (R : ℝ → ℝ)
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
      ∃ a ∈ samples,
        R a * (|k-a| *
          momentBudget rho
            (transformMomentUpper z sigma Abar Qbar Wbar Cbar δ)) < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ico 0 b, ‖p t‖ ≤ B := by
  apply hs_grid_certificate_uniform_amplitude_bound z hz rho sigma hρ hσ hη
    K hK p b hb hp0 hp hroot Abar Qbar Wbar Cbar hA hQ hW hC
    samples R (transformMomentUpper z sigma Abar Qbar Wbar Cbar δ)
  · intro t ht i j
    exact (path_actual_moment_le_referenceMoment z hz rho sigma
      (fun i => (hσ i).le) p (Set.Ico 0 b) Abar Qbar Wbar Cbar
      hA hQ hW hC t ht i j).trans
      (referenceMoment_le_transformMomentUpper z sigma Abar Qbar Wbar Cbar
        (fun i => (hσ i).le) hA0 hQ0 hW0 hC0 δ hδ hrate i j)
  · exact hbase
  · exact hR
  · exact hcover

end FMSA.Convergence.MixtureMomentCoefficientBudget

/-- info: 'FMSA.Convergence.MixtureMomentCoefficientBudget.actual_q_abs_le_reference_q' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureMomentCoefficientBudget.actual_q_abs_le_reference_q
/-- info: 'FMSA.Convergence.MixtureMomentCoefficientBudget.referenceMoment_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureMomentCoefficientBudget.referenceMoment_integrable
/-- info: 'FMSA.Convergence.MixtureMomentCoefficientBudget.actual_first_moment_le_referenceMoment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureMomentCoefficientBudget.actual_first_moment_le_referenceMoment
/-- info: 'FMSA.Convergence.MixtureMomentCoefficientBudget.referenceQ_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureMomentCoefficientBudget.referenceQ_nonneg
/-- info: 'FMSA.Convergence.MixtureMomentCoefficientBudget.referenceMoment_le_transformMomentUpper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureMomentCoefficientBudget.referenceMoment_le_transformMomentUpper
/-- info: 'FMSA.Convergence.MixtureMomentCoefficientBudget.transformMomentUpper_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureMomentCoefficientBudget.transformMomentUpper_nonneg
/-- info: 'FMSA.Convergence.MixtureMomentCoefficientBudget.path_actual_moment_le_referenceMoment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureMomentCoefficientBudget.path_actual_moment_le_referenceMoment
/-- info: 'FMSA.Convergence.MixtureMomentCoefficientBudget.hs_coefficient_grid_uniform_amplitude_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureMomentCoefficientBudget.hs_coefficient_grid_uniform_amplitude_bound
/-- info: 'FMSA.Convergence.MixtureMomentCoefficientBudget.hs_transform_grid_uniform_amplitude_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureMomentCoefficientBudget.hs_transform_grid_uniform_amplitude_bound
