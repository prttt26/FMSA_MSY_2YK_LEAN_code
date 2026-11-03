import MSAConvergence.TracerCovarianceQuadraticTrace

/-! Uniform compact-spectrum domination for the actual finite Yukawa tail
trial vector, preparatory to the covariance-weighted forcing budget. -/
noncomputable section
open MeasureTheory Real FMSA.HardSphere FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.TracerTailSpectralBound FMSA.Convergence.RadialCovarianceBounds
open FMSA.Convergence.TracerCovarianceQuadraticTrace FMSA.Convergence.TracerCovarianceEntryTrace
open FMSA.Paper FMSA.Paper.ActualRDFParameters
open scoped BigOperators ComplexOrder
namespace FMSA.Convergence.TracerTailForcingBound
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Every physical tail strength is bounded by the full coupling norm. -/
theorem tail_strength_component_le_norm (K : TailMatrix T N)
    (u : T) (i j : Fin N) : |K u i j| ≤ ‖K‖ := by
  calc
    |K u i j| = ‖K u i j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖K u i‖ := norm_le_pi_norm (K u i) j
    _ ≤ ‖K u‖ := norm_le_pi_norm (K u) i
    _ ≤ ‖K‖ := norm_le_pi_norm K u

/-- The actual density-weighted exterior Yukawa spectral trial vector. -/
def tailTrialVector (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (i a : Fin N) (w : ℝ) : ℂ :=
  (Real.sqrt (rho a) : ℂ) *
    ((w*radial_fourier (tailField z (edgeHi sigma i a) (fun u => K u i a))
      (2*Real.pi*w) : ℝ) : ℂ)

/-- The squared norm of the actual finite tail trial vector is dominated by
one compact-spectrum test weight uniformly over bounded couplings. -/
theorem tail_trial_square_sum_uniformly_dominated (z : T → ℝ)
    (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hρ : ∀ a, 0 ≤ rho a) (hs : ∀ a, 0 < sigma a)
    (R : ℝ) (hR : 0 < R) (B : ℝ) (i : Fin N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : TailMatrix T N, ‖K‖ ≤ B →
      ∀ w : ℝ, (∑ a : Fin N, ‖tailTrialVector z rho sigma K i a w‖^2) ≤
        C*testWeight R w := by
  classical
  have hCa (a : Fin N) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ F : T → ℝ, (∀ u, |F u| ≤ B) → ∀ k : ℝ, k ≠ 0 →
        |radial_fourier (tailField z (edgeHi sigma i a) F) k|^2 ≤
          C*radial_fourier (fun r => CompactSpectralTest.profile (r/R)) k := by
    have hσ : 0 < edgeHi sigma i a := by dsimp [edgeHi]; linarith [hs i,hs a]
    exact tail_field_square_dominated z hz (edgeHi sigma i a) R hσ hR B
  choose C hC htail using hCa
  let M : ℝ := ∑ a : Fin N, rho a*C a
  have hM : 0 ≤ M := Finset.sum_nonneg (fun a _ => mul_nonneg (hρ a) (hC a))
  refine ⟨M,hM,?_⟩
  intro K hK w
  by_cases hw : w = 0
  · subst w
    simp [tailTrialVector,testWeight]
  have hk : 2*Real.pi*w ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw
  have hterm (a : Fin N) : ‖tailTrialVector z rho sigma K i a w‖^2 ≤
      rho a*C a*testWeight R w := by
    have hcoeff (u : T) : |K u i a| ≤ B :=
      (tail_strength_component_le_norm K u i a).trans hK
    have htaila := htail a (fun u => K u i a) hcoeff
      (2*Real.pi*w) hk
    have hnorm : ‖tailTrialVector z rho sigma K i a w‖^2 =
        rho a*w^2*|radial_fourier
          (tailField z (edgeHi sigma i a) (fun u => K u i a)) (2*Real.pi*w)|^2 := by
      simp only [tailTrialVector,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,sq_abs,
        Real.sq_sqrt (hρ a)]
      ring
    calc
      _ = rho a*w^2*|radial_fourier
          (tailField z (edgeHi sigma i a) (fun u => K u i a)) (2*Real.pi*w)|^2 := hnorm
      _ ≤ (rho a*w^2)*(C a*radial_fourier
          (fun r => CompactSpectralTest.profile (r/R)) (2*Real.pi*w)) :=
        mul_le_mul_of_nonneg_left htaila (mul_nonneg (hρ a) (sq_nonneg w))
      _ = rho a*C a*testWeight R w := by dsimp [testWeight]; ring
  calc
    _ ≤ ∑ a : Fin N, rho a*C a*testWeight R w :=
      Finset.sum_le_sum (fun a _ => hterm a)
    _ = M*testWeight R w := by
      rw [Finset.sum_mul]

end FMSA.Convergence.TracerTailForcingBound
/-- info: 'FMSA.Convergence.TracerTailForcingBound.tail_strength_component_le_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailForcingBound.tail_strength_component_le_norm
/-- info: 'FMSA.Convergence.TracerTailForcingBound.tail_trial_square_sum_uniformly_dominated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailForcingBound.tail_trial_square_sum_uniformly_dominated
