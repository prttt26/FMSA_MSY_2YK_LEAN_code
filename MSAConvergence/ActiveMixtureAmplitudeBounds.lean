import MSAConvergence.MixtureFirstAmplitudeBounds
import MSAConvergence.WeightedMixtureAmplitudeBounds

/-! Uniform active-column and active-block amplitudes in the presence of
retained zero-density tracers. No unweighted tracer escape conclusion follows. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.ActiveMixtureAmplitudeBounds
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.CanonicalInverseCovariance FMSA.Convergence.CanonicalInteriorInverseBounds
open FMSA.Convergence.ActualBHAmplitudeRecovery FMSA.Convergence.MixtureFirstAmplitudeBounds
open FMSA.Convergence.WeightedMixtureAmplitudeBounds
variable {N : ℕ} {T : Type*} [Fintype T]

private theorem strength_entry_bound (K : TailMatrix T N) (B : ℝ) (hB : ‖K‖ ≤ B)
    (u : T) (i j : Fin N) : |K u i j| ≤ max B 0 := by
  exact (((norm_le_pi_norm (K u i) j).trans
    ((norm_le_pi_norm (K u) i).trans (norm_le_pi_norm K u))).trans hB).trans (le_max_left _ _)

/-- Every ORIGINAL D column of positive density stays bounded, including its
tracer rows. No positivity of the other retained species densities is assumed. -/
theorem first_active_column_uniform_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (B : ℝ) (u : T) (j : Fin N) (hj : 0 < ρ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) → ∀ i : Fin N, |D u i j| ≤ C := by
  classical
  have hsmall : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i : Fin N, r < σ i :=
    Filter.eventually_all.mpr (fun i => Iio_mem_nhds (hσ i))
  have hpositive : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨R,hR,hRσ⟩ := (hpositive.and (hsmall.filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨C₀,hC₀,hbound⟩ := actual_inverse_positive_point_weighted_bound z hz ρ σ hρ hσ hv R hR hRσ (z u) (hz u)
  let Q := (|2*Real.pi/z u| *max B 0)*(∑ l, sqrt (ρ l*ρ j*C₀))
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg (abs_nonneg _) (le_max_right B 0))
    (Finset.sum_nonneg (fun l _ => sqrt_nonneg _))
  refine ⟨Q/ρ j,div_nonneg hQ hj.le,?_⟩
  intro K D G hKnorm hK hroot hcanon i
  have hmatrix := first_weighted_inverse_identity z hz ρ σ (fun i => (hσ i).le) K D G hroot hcanon u
  have he := congrFun (congrFun hmatrix i) j
  simp only [Matrix.mul_diagonal,Matrix.of_apply,dtSymbol] at he
  rw [Matrix.mul_apply] at he
  simp only [Matrix.transpose_apply,Matrix.mul_diagonal,Matrix.smul_apply,Matrix.of_apply,smul_eq_mul] at he
  have hweighted (l : Fin N) : ρ l*‖(causalFactor z ρ σ D G (z u : ℂ))⁻¹ j l‖ ≤ sqrt (ρ l*ρ j*C₀) := by
    have h := hbound K D G hK hroot hcanon j l
    have hmul := mul_le_mul_of_nonneg_left h (hρ l)
    have hnonneg : 0 ≤ ρ l*ρ j*C₀ := mul_nonneg (mul_nonneg (hρ l) hj.le) hC₀
    have hsq := Real.sq_sqrt hnonneg
    have hs := sqrt_nonneg (ρ l*ρ j*C₀)
    have hn := mul_nonneg (hρ l) (norm_nonneg ((causalFactor z ρ σ D G (z u : ℂ))⁻¹ j l))
    nlinarith
  have hsum : ‖∑ l, (((2*Real.pi/z u : ℝ) : ℂ)*(K u i l : ℂ)*(ρ l : ℂ))*
      (causalFactor z ρ σ D G (z u : ℂ))⁻¹ j l‖ ≤ Q := by
    calc
      _ ≤ ∑ l, ‖(((2*Real.pi/z u : ℝ) : ℂ)*(K u i l : ℂ)*(ρ l : ℂ))*
          (causalFactor z ρ σ D G (z u : ℂ))⁻¹ j l‖ := norm_sum_le _ _
      _ ≤ ∑ l, (|2*Real.pi/z u| *max B 0)*sqrt (ρ l*ρ j*C₀) := by
        apply Finset.sum_le_sum
        intro l _
        rw [norm_mul,norm_mul,norm_mul]
        simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hρ l)]
        rw [mul_assoc]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (strength_entry_bound K B hKnorm u i l) (abs_nonneg _))
          (hweighted l) (mul_nonneg (hρ l) (norm_nonneg _))
          (mul_nonneg (abs_nonneg _) (le_max_right B 0))
      _ = Q := by rw [← Finset.mul_sum]
  have hn : |D u i j| *ρ j ≤ Q := by
    have h := (congrArg norm he).le.trans hsum
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hj] using h
  exact (le_div_iff₀ hj).mpr hn

/-- Uniform bound for ALL original first-amplitude columns with positive
density, including active/tracer row pairs. Zero-density columns are not claimed. -/
theorem first_active_columns_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) →
      ∀ u i j, 0 < ρ j → |D u i j| ≤ C := by
  classical
  have hlocal (u : T) (j : Fin N) : ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) →
      ∀ i : Fin N, 0 < ρ j → |D u i j| ≤ C := by
    by_cases hj : 0 < ρ j
    · obtain ⟨C,hC,hb⟩ := first_active_column_uniform_bound z hz ρ σ hρ hσ hv B u j hj
      exact ⟨C,hC,fun K D G hn hK hr hc i _ => hb K D G hn hK hr hc i⟩
    · exact ⟨0,le_rfl,fun _ _ _ _ _ _ _ _ hp => False.elim (hj hp)⟩
  choose C hC hb using hlocal
  refine ⟨∑ u, ∑ j, C u j,Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun j _ => hC u j)),?_⟩
  intro K D G hn hK hr hc u i j hj
  exact (hb u j K D G hn hK hr hc i hj).trans
    ((Finset.single_le_sum (fun j _ => hC u j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun u _ => Finset.sum_nonneg (fun j _ => hC u j)) (Finset.mem_univ u)))

/-- The ORIGINAL active-active G block remains uniformly bounded even in the
presence of arbitrary retained zero-density tracers. No K bound is supplied. -/
theorem second_active_block_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) →
      ∀ u i j, 0 < ρ i → 0 < ρ j → |G u i j| ≤ C := by
  classical
  have hsmall : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i : Fin N, r < σ i :=
    Filter.eventually_all.mpr (fun i => Iio_mem_nhds (hσ i))
  have hpositive : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨R,hR,hRσ⟩ := (hpositive.and (hsmall.filter_mono nhdsWithin_le_nhds)).exists
  have hlocal (u : T) (i j : Fin N) : ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) →
      0 < ρ i → 0 < ρ j → |G u i j| ≤ C := by
    by_cases hi : 0 < ρ i
    · by_cases hj : 0 < ρ j
      · obtain ⟨C,hC,hb⟩ := second_entry_weighted_uniform_bound z hz ρ σ hρ hσ hv R hR hRσ u i j
        have hd : 0 < sqrt (ρ i)*sqrt (ρ j) := mul_pos (sqrt_pos.mpr hi) (sqrt_pos.mpr hj)
        refine ⟨C/(sqrt (ρ i)*sqrt (ρ j)),div_nonneg hC hd.le,?_⟩
        intro K D G hK hr hc _ _
        exact (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hb K D G hK hr hc)
      · exact ⟨0,le_rfl,fun _ _ _ _ _ _ _ hp => False.elim (hj hp)⟩
    · exact ⟨0,le_rfl,fun _ _ _ _ _ _ hp _ => False.elim (hi hp)⟩
  choose C hC hb using hlocal
  refine ⟨∑ u, ∑ i, ∑ j, C u i j,Finset.sum_nonneg (fun u _ =>
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC u i j))),?_⟩
  intro K D G hK hr hc u i j hi hj
  exact (hb u i j K D G hK hr hc hi hj).trans
    ((Finset.single_le_sum (fun j _ => hC u i j) (Finset.mem_univ j)).trans
      ((Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hC u i j)) (Finset.mem_univ i)).trans
        (Finset.single_le_sum (fun u _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC u i j)))
          (Finset.mem_univ u))))

end FMSA.Convergence.ActiveMixtureAmplitudeBounds
/-- info: 'FMSA.Convergence.ActiveMixtureAmplitudeBounds.first_active_column_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActiveMixtureAmplitudeBounds.first_active_column_uniform_bound
/-- info: 'FMSA.Convergence.ActiveMixtureAmplitudeBounds.first_active_columns_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActiveMixtureAmplitudeBounds.first_active_columns_uniformly_bounded
/-- info: 'FMSA.Convergence.ActiveMixtureAmplitudeBounds.second_active_block_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActiveMixtureAmplitudeBounds.second_active_block_uniformly_bounded
