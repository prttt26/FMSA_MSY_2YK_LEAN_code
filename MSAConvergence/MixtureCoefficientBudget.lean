import MSAConvergence.MixtureAxisHighFrequency

/-! A finite coefficientwise certificate for the actual mixture Fourier
high-frequency decay budget. The cap values can be produced by interval
arithmetic; no compactness or root equation is used in this module. -/
noncomputable section
open Real
open scoped BigOperators
namespace FMSA.Convergence.MixtureCoefficientBudget
open FMSA.Paper FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.MixtureAxisHighFrequency
variable {N : ℕ} {T : Type*} [Fintype T]

def lowerCap (z : T → ℝ) (sigma : Fin N → ℝ)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar : TailMatrix T N) (i j : Fin N) : ℝ :=
  Abar j + (Qbar i j + |sigma i| * Abar j) +
    ∑ u, 2 * |z u| * Wbar u i j

def upperCap (z : T → ℝ) (Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Cbar : TailMatrix T N)
    (i j : Fin N) : ℝ :=
  Abar j + Qbar i j + ∑ u, 2 * |z u| * Cbar u i j

def coefficientBudget (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (Kbar : Fin N → Fin N → ℝ)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N) : ℝ :=
  ∑ i, ∑ j, (Kbar i j + |rho i| *
    (lowerCap z sigma Abar Qbar Wbar i j +
      upperCap z Abar Qbar Cbar i j))

def originCap (rho sigma : Fin N → ℝ)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N) (i j : Fin N) : ℝ :=
  |rho i| * (|sigma i| * Qbar i j +
    sigma i ^ 2 / 2 * Abar j + ∑ u, (Wbar u i j + Cbar u i j))

/-- The zero-distance causal-kernel entry is bounded by the same four
finite coefficient caps. The identity at `t = 0` is the original recentered
Blum–Høye kernel, including the compact and Yukawa terms. -/
theorem origin_kernel_le_originCap
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA : ∀ j, |amplitudeA z rho sigma p.1 p.2 j| ≤ Abar j)
    (hQ : ∀ i j, |amplitudeQp z rho sigma p.1 p.2 i j| ≤ Qbar i j)
    (hW : ∀ u i j, |W z rho p.1 p.2 u i j| ≤ Wbar u i j)
    (hC : ∀ u i j, |C z rho sigma p.1 p.2 u i j| ≤ Cbar u i j)
    (i j : Fin N) :
    |nonlinearCausalKernel z rho sigma p.1 p.2 0 i j| ≤
      originCap rho sigma Abar Qbar Wbar Cbar i j := by
  have hq0 : nonlinearRecenteredQ z rho sigma p.1 p.2 i j 0 =
      -sigma i * amplitudeQp z rho sigma p.1 p.2 i j +
        amplitudeA z rho sigma p.1 p.2 j * sigma i ^ 2 / 2 +
        ∑ u, (W z rho p.1 p.2 u i j + C z rho sigma p.1 p.2 u i j) := by
    unfold nonlinearRecenteredQ
    simp only [min_eq_left (hσ i), max_eq_right (hσ i), zero_sub,
      sub_self, mul_zero, Real.exp_zero, mul_one]
    ring
  have hsum : |∑ u, (W z rho p.1 p.2 u i j +
      C z rho sigma p.1 p.2 u i j)| ≤ ∑ u, (Wbar u i j + Cbar u i j) := by
    calc
      |∑ u, (W z rho p.1 p.2 u i j + C z rho sigma p.1 p.2 u i j)|
          ≤ ∑ u, |W z rho p.1 p.2 u i j + C z rho sigma p.1 p.2 u i j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u, (Wbar u i j + Cbar u i j) := by
        apply Finset.sum_le_sum
        intro u _
        exact (abs_add_le _ _).trans (add_le_add (hW u i j) (hC u i j))
  have hfirst : |-sigma i * amplitudeQp z rho sigma p.1 p.2 i j| ≤
      |sigma i| * Qbar i j := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hQ i j) (abs_nonneg _)
  have hsecond : |amplitudeA z rho sigma p.1 p.2 j * sigma i ^ 2 / 2| ≤
      sigma i ^ 2 / 2 * Abar j := by
    have hcoeff : 0 ≤ sigma i ^ 2 / 2 := by positivity
    have hh := mul_le_mul_of_nonneg_left (hA j) hcoeff
    calc
      |amplitudeA z rho sigma p.1 p.2 j * sigma i ^ 2 / 2| =
          (sigma i ^ 2 / 2) * |amplitudeA z rho sigma p.1 p.2 j| := by
            rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (sigma i)),
              abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            ring
      _ ≤ sigma i ^ 2 / 2 * Abar j := hh
  unfold nonlinearCausalKernel originCap
  simp only [Matrix.of_apply, abs_mul, hq0]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    |(-sigma i * amplitudeQp z rho sigma p.1 p.2 i j +
        amplitudeA z rho sigma p.1 p.2 j * sigma i ^ 2 / 2) +
        ∑ u, (W z rho p.1 p.2 u i j + C z rho sigma p.1 p.2 u i j)|
        ≤ |-sigma i * amplitudeQp z rho sigma p.1 p.2 i j +
            amplitudeA z rho sigma p.1 p.2 j * sigma i ^ 2 / 2| +
          |∑ u, (W z rho p.1 p.2 u i j + C z rho sigma p.1 p.2 u i j)| :=
            abs_add_le _ _
    _ ≤ |-sigma i * amplitudeQp z rho sigma p.1 p.2 i j| +
          |amplitudeA z rho sigma p.1 p.2 j * sigma i ^ 2 / 2| +
          |∑ u, (W z rho p.1 p.2 u i j + C z rho sigma p.1 p.2 u i j)| := by
            linarith [abs_add_le (-sigma i * amplitudeQp z rho sigma p.1 p.2 i j)
              (amplitudeA z rho sigma p.1 p.2 j * sigma i ^ 2 / 2)]
    _ ≤ |sigma i| * Qbar i j + sigma i ^ 2 / 2 * Abar j +
          ∑ u, (Wbar u i j + Cbar u i j) := by
            linarith [hfirst,hsecond,hsum]

/-- Bounds on the five actual finite coefficient families imply a fully
evaluated bound for the high-frequency decay budget. -/
theorem decayBudget_le_coefficientBudget
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N)
    (Kbar : Fin N → Fin N → ℝ)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hK : ∀ i j, |nonlinearCausalKernel z rho sigma p.1 p.2 0 i j| ≤ Kbar i j)
    (hA : ∀ j, |amplitudeA z rho sigma p.1 p.2 j| ≤ Abar j)
    (hQ : ∀ i j, |amplitudeQp z rho sigma p.1 p.2 i j| ≤ Qbar i j)
    (hW : ∀ u i j, |W z rho p.1 p.2 u i j| ≤ Wbar u i j)
    (hC : ∀ u i j, |C z rho sigma p.1 p.2 u i j| ≤ Cbar u i j) :
    decayBudget z rho sigma p ≤
      coefficientBudget z rho sigma Kbar Abar Qbar Wbar Cbar := by
  have hL (i j : Fin N) :
      lDecayBound z rho sigma p i j ≤ lowerCap z sigma Abar Qbar Wbar i j := by
    unfold lDecayBound lowerCap
    apply add_le_add
    · apply add_le_add (hA j)
      calc
        |amplitudeQp z rho sigma p.1 p.2 i j -
            sigma i * amplitudeA z rho sigma p.1 p.2 j|
            ≤ |amplitudeQp z rho sigma p.1 p.2 i j| +
              |sigma i * amplitudeA z rho sigma p.1 p.2 j| := by
                simpa only [sub_zero, zero_sub, abs_neg] using
                  abs_sub_le (amplitudeQp z rho sigma p.1 p.2 i j) 0
                    (sigma i * amplitudeA z rho sigma p.1 p.2 j)
        _ ≤ Qbar i j + |sigma i| * Abar j := by
          rw [abs_mul]
          exact add_le_add (hQ i j)
            (mul_le_mul_of_nonneg_left (hA j) (abs_nonneg _))
    · apply Finset.sum_le_sum
      intro u _
      rw [abs_mul]
      have hfac : 0 ≤ 2 * |z u| := by positivity
      have hu := mul_le_mul_of_nonneg_left (hW u i j) hfac
      nlinarith
  have hJ (i j : Fin N) :
      jDecayBound z rho sigma p i j ≤ upperCap z Abar Qbar Cbar i j := by
    unfold jDecayBound upperCap
    apply add_le_add (add_le_add (hA j) (hQ i j))
    apply Finset.sum_le_sum
    intro u _
    rw [abs_mul]
    have hfac : 0 ≤ 2 * |z u| := by positivity
    have hu := mul_le_mul_of_nonneg_left (hC u i j) hfac
    nlinarith
  have hE (i j : Fin N) : leadingErrorBound z rho sigma p 0 i j ≤
      |rho i| * (lowerCap z sigma Abar Qbar Wbar i j +
        upperCap z Abar Qbar Cbar i j) := by
    unfold leadingErrorBound
    simp only [zero_mul, Real.exp_zero, one_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add (hL i j) (hJ i j)) (abs_nonneg _)
  unfold decayBudget coefficientBudget FMSA.matrixAbsSum
  simp only [Finset.sum_add_distrib]
  apply add_le_add
  · exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hK i j))
  · exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hE i j))

def explicitBudget (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N) : ℝ :=
  coefficientBudget z rho sigma
    (originCap rho sigma Abar Qbar Wbar Cbar) Abar Qbar Wbar Cbar

/-- Four coefficientwise interval caps suffice to bound the actual
high-frequency budget. The origin causal-kernel cap is derived internally. -/
theorem decayBudget_le_explicitBudget
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA : ∀ j, |amplitudeA z rho sigma p.1 p.2 j| ≤ Abar j)
    (hQ : ∀ i j, |amplitudeQp z rho sigma p.1 p.2 i j| ≤ Qbar i j)
    (hW : ∀ u i j, |W z rho p.1 p.2 u i j| ≤ Wbar u i j)
    (hC : ∀ u i j, |C z rho sigma p.1 p.2 u i j| ≤ Cbar u i j) :
    decayBudget z rho sigma p ≤
      explicitBudget z rho sigma Abar Qbar Wbar Cbar := by
  exact decayBudget_le_coefficientBudget z rho sigma p
    (originCap rho sigma Abar Qbar Wbar Cbar) Abar Qbar Wbar Cbar
    (origin_kernel_le_originCap z rho sigma hσ p Abar Qbar Wbar Cbar
      hA hQ hW hC) hA hQ hW hC

/-- A bounded real-frequency determinant certificate plus four uniform
coefficient caps proves nonvanishing on the entire real axis, at every
state in the chosen path set. The cutoff is the finite, explicit
`rateCutoff + explicitBudget + 1`; no compactness argument is used. -/
theorem path_axis_zero_free_of_coefficient_caps
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 ≤ sigma i)
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
      |C z rho sigma (p t).1 (p t).2 u i j| ≤ Cbar u i j)
    (hcompact : ∀ t ∈ S, ∀ k : ℝ,
      |k| ≤ rateCutoff z + explicitBudget z rho sigma Abar Qbar Wbar Cbar + 1 →
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
  apply path_axis_zero_free_of_compact_test z hz rho sigma hρ hσ p S
    (explicitBudget z rho sigma Abar Qbar Wbar Cbar)
  · intro t ht
    exact decayBudget_le_explicitBudget z rho sigma hσ (p t)
      Abar Qbar Wbar Cbar (hA t ht) (hQ t ht) (hW t ht) (hC t ht)
  · exact hcompact

end FMSA.Convergence.MixtureCoefficientBudget
/-- info: 'FMSA.Convergence.MixtureCoefficientBudget.origin_kernel_le_originCap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCoefficientBudget.origin_kernel_le_originCap
/-- info: 'FMSA.Convergence.MixtureCoefficientBudget.decayBudget_le_coefficientBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCoefficientBudget.decayBudget_le_coefficientBudget
/-- info: 'FMSA.Convergence.MixtureCoefficientBudget.decayBudget_le_explicitBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCoefficientBudget.decayBudget_le_explicitBudget
/-- info: 'FMSA.Convergence.MixtureCoefficientBudget.path_axis_zero_free_of_coefficient_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureCoefficientBudget.path_axis_zero_free_of_coefficient_caps
