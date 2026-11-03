import MSAConvergence.TracerUnitYukawaMoment
import MSAConvergence.TracerAlgebraicProperness

/-! Uniform ORIGINAL second BH amplitudes in every positive-density column,
including rows belonging to retained zero-density tracers. -/
noncomputable section
open MeasureTheory Real FMSA.HardSphere FMSA.ExactMSA FMSA.ExactMSA.MultiTailMixture MSAMixture
open Set
open FMSA.Convergence.TracerUnitYukawaPairing
open FMSA.Convergence.TracerUnitYukawaMoment
open FMSA.Convergence.TracerAlgebraicProperness
open FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters
namespace FMSA.Convergence.TracerActiveGUniform
variable {N : ℕ} {T : Type*} [Fintype T]

/-- A fixed original G entry in an active column is uniformly bounded over
all canonical reciprocal MSA roots with bounded K, regardless of row density. -/
theorem actual_active_column_G_entry_uniform
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hσ : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (R : ℝ) (hR : 0 < R) (hRσ : ∀ a, R < sigma a)
    (B : ℝ) (u : T) (i j : Fin N) (hj : 0 < rho j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ v a b, K v a b = K v b a) →
      IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
      |G u i j| ≤ C := by
  obtain ⟨MP,hMP,hpair⟩ := actual_unit_yukawa_spectral_pair_uniform
    z hz rho sigma hρ hσ hv R hR hRσ B (z u) (hz u) i j
  let fixed : ℝ := exp ((z u)*edgeHi sigma i j)*
    ((∫ r in (0 : ℝ)..edgeHi sigma i j, r*exp (-(z u)*r))-(z u)⁻¹^2)
  let C : ℝ := (MP/2+rho j*|fixed|)/rho j
  have hC : 0 ≤ C := div_nonneg
    (add_nonneg (div_nonneg hMP (by norm_num)) (mul_nonneg (hρ j) (abs_nonneg _))) hj.le
  refine ⟨C,hC,?_⟩
  intro K D G hB hK hroot hcanon
  let P : ℝ := ∫ w : ℝ, w^2*
    radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w)*
    radial_fourier (cMSAtail 1 (z u) (edgeHi sigma i j)) (2*Real.pi*w)
  have hp : rho j*|P| ≤ MP := hpair K D G hB hK hroot hcanon
  have hident : P = 2*G u i j+2*fixed := by
    simpa only [P,fixed,mul_assoc] using
      (actual_unit_yukawa_spectral_pair_eq_G_plus_fixed z hz rho sigma hσ hv
        K D G hroot hcanon u i j)
  have hG : G u i j = P/2-fixed := by linarith [hident]
  have htri : |G u i j| ≤ |P|/2+|fixed| := by
    rw [hG]
    calc
      |P/2-fixed| ≤ |P/2|+|fixed| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (P/2) 0 fixed
      _ = |P|/2+|fixed| := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hm : rho j*|G u i j| ≤ MP/2+rho j*|fixed| := by
    have h := mul_le_mul_of_nonneg_left htri (hρ j)
    nlinarith [hp]
  exact (le_div_iff₀ hj).mpr (by simpa only [C,mul_comm] using hm)


/-- One uniform constant controls every ORIGINAL second-amplitude entry in
positive-density columns, for all rows and all finite Yukawa rates. -/
theorem actual_all_active_column_G_uniform
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hσ : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (R : ℝ) (hR : 0 < R) (hRσ : ∀ a, R < sigma a)
    (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ v a b, K v a b = K v b a) →
      IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
      ∀ u i j, 0 < rho j → |G u i j| ≤ C := by
  classical
  have hentry : ∀ u : T, ∀ i j : Fin N,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
        ‖K‖ ≤ B → (∀ v a b, K v a b = K v b a) →
        IsRoot z rho sigma K D G →
        (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
        0 < rho j → |G u i j| ≤ C := by
    intro u i j
    by_cases hj : 0 < rho j
    · obtain ⟨C,hC,hbound⟩ := actual_active_column_G_entry_uniform
        z hz rho sigma hρ hσ hv R hR hRσ B u i j hj
      exact ⟨C,hC,fun K D G hB hK hroot hcanon _ =>
        hbound K D G hB hK hroot hcanon⟩
    · exact ⟨0,le_refl 0,fun K D G hB hK hroot hcanon hj' => False.elim (hj hj')⟩
  choose C hC hbound using hentry
  let M : ℝ := ∑ u : T, ∑ i : Fin N, ∑ j : Fin N, C u i j
  have hM : 0 ≤ M := by
    dsimp only [M]
    apply Finset.sum_nonneg
    intro u _
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg (fun j _ => hC u i j)
  refine ⟨M,hM,?_⟩
  intro K D G hB hK hroot hcanon u i j hj
  have hb := hbound u i j K D G hB hK hroot hcanon hj
  have hjb : C u i j ≤ ∑ l : Fin N, C u i l :=
    Finset.single_le_sum (fun l _ => hC u i l) (Finset.mem_univ j)
  have hib : (∑ l : Fin N, C u i l) ≤ ∑ k : Fin N, ∑ l : Fin N, C u k l :=
    Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hC u k l))
      (Finset.mem_univ i)
  have hub : (∑ k : Fin N, ∑ l : Fin N, C u k l) ≤ M :=
    Finset.single_le_sum
      (fun v _ => Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => hC v k l)))
      (Finset.mem_univ u)
  exact hb.trans (hjb.trans (hib.trans hub))

/-- Full original-pair amplitude properness for any finite mixture with
nonzero hard-sphere packing denominator, including all-vacuum and
arbitrarily many retained zero-density tracer species.
No density in a tracer column is inverted. -/
theorem actual_full_mixture_amplitude_properness
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hσ : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (R : ℝ) (hR : 0 < R) (hRσ : ∀ a, R < sigma a)
    (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ v a b, K v a b = K v b a) →
      IsRoot z rho sigma K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s)) →
      ‖(D,G)‖ ≤ M := by
  obtain ⟨C,hC,hactive⟩ := actual_all_active_column_G_uniform
    z hz rho sigma hρ hσ hv R hR hRσ B
  obtain ⟨M,hM,hfull⟩ := full_bound_of_active_second_columns
    z hz rho sigma hρ hσ hv B C
  exact ⟨M,hM,fun K D G hB hK hroot hcanon =>
    hfull K D G hB hK hroot hcanon
      (hactive K D G hB hK hroot hcanon)⟩

/-- A canonical reciprocal physical root prefix cannot undergo finite-time
escape of its ORIGINAL first and second amplitudes, including retained
zero-density tracer rows and columns. -/
theorem no_finite_mixture_amplitude_escape
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hσ : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (R : ℝ) (hR : 0 < R) (hRσ : ∀ a, R < sigma a)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (b : ℝ) (hb : 0 < b)
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, ∀ s : ℂ, 0 ≤ s.re →
      IsUnit (causalFactor z rho sigma (p t).1 (p t).2 s)) :
    ¬∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖p t‖ := by
  obtain ⟨M,_hM,hbound⟩ := actual_full_mixture_amplitude_properness
    z hz rho sigma hρ hσ hv R hR hRσ (b*‖K‖)
  intro hescape
  obtain ⟨t,ht,_hc,hlarge⟩ := hescape M 0 hb
  have hKt : ‖t • K‖ ≤ b*‖K‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
  have hKtSym : ∀ u i j, (t • K) u i j = (t • K) u j i := by
    intro u i j
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hK u i j]
  have hp := hbound (t • K) (p t).1 (p t).2 hKt hKtSym
    (hroot t ht) (hcanon t ht)
  exact (not_lt_of_ge hp) hlarge

end FMSA.Convergence.TracerActiveGUniform
/-- info: 'FMSA.Convergence.TracerActiveGUniform.actual_active_column_G_entry_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerActiveGUniform.actual_active_column_G_entry_uniform
/-- info: 'FMSA.Convergence.TracerActiveGUniform.actual_all_active_column_G_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerActiveGUniform.actual_all_active_column_G_uniform
/-- info: 'FMSA.Convergence.TracerActiveGUniform.actual_full_mixture_amplitude_properness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerActiveGUniform.actual_full_mixture_amplitude_properness
/-- info: 'FMSA.Convergence.TracerActiveGUniform.no_finite_mixture_amplitude_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerActiveGUniform.no_finite_mixture_amplitude_escape
