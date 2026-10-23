import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFDCFRegularity

/-! The actual HS DCF radius moment is internal: its numerator is bounded
by the compact polynomial Q0 derivative and actual Q0 L1, and it vanishes
outside contact. No actual HS RDF/OZ premise is needed for this DCF fact. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def hsPrimeBound (ρ σ : Fin N → ℝ) (i j : Fin N) : ℝ :=
  |Q0phys ρ σ i j|+|Qppphys ρ σ j j| *σ i

theorem qPrime_zero_abs_le (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (r : ℝ) :
    |qPrime z σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ))
      (amplitudeQp z ρ σ 0 (baseSeed z ρ σ)) (W z ρ 0 (baseSeed z ρ σ))
      (C z ρ σ 0 (baseSeed z ρ σ)) i j r| ≤ hsPrimeBound ρ σ i j := by
  have hm : 0 ≤ hsPrimeBound ρ σ i j := by
    unfold hsPrimeBound
    exact add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (hσ i))
  simp only [qPrime, amplitudeA_zero, amplitudeQp_zero, W, C, Wt, Ct, Pi.zero_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, sub_zero]
  split_ifs with hl hh
  · simpa using hm
  · have harg : |r-edgeHi σ i j| ≤ σ i := by
      rw [abs_le]
      simp only [edgeLo, edgeHi] at hl hh ⊢
      constructor <;> linarith
    unfold hsPrimeBound
    exact (abs_add_le _ _).trans (add_le_add (le_refl _)
      ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left harg (abs_nonneg _))))
  · simpa using hm

theorem correlation_radius_bounded_of_qPrime_bound (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (M : Fin N → Fin N → ℝ)
    (hb : ∀ i j r, |qPrime z σ A qp W C i j r| ≤ M i j) (i j : Fin N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r > 0, |r*correlation z ρ σ A qp W C i j r| ≤ B := by
  let B := M i j+∑ l, |ρ l| *(M i l*∫ t : ℝ, |q z σ A qp W C j l t|)
  have hM : ∀ a b, 0 ≤ M a b := fun a b => (abs_nonneg _).trans (hb a b 0)
  have hB : 0 ≤ B := by
    dsimp only [B]
    apply add_nonneg (hM i j)
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (hM i l) (integral_nonneg (fun _ => abs_nonneg _)))
  refine ⟨B/(2*π), by positivity, ?_⟩
  intro r hr
  have hconv (l : Fin N) :
      |∫ t : ℝ, qPrime z σ A qp W C i l (t+r)*q z σ A qp W C j l t| ≤
        M i l*∫ t : ℝ, |q z σ A qp W C j l t| := by
    have hi : Integrable (fun t => M i l*|q z σ A qp W C j l t|) :=
      (q_integrable z hz σ A qp W C hσ j l).abs.const_mul _
    have he := norm_integral_le_of_norm_le hi (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hb i l (t+r)) (abs_nonneg _)))
    simpa only [Real.norm_eq_abs, integral_const_mul] using he
  have hn : |(-qPrime z σ A qp W C i j r)+∑ l, ρ l*
      ∫ t : ℝ, qPrime z σ A qp W C i l (t+r)*q z σ A qp W C j l t| ≤ B := by
    apply (abs_add_le _ _).trans
    apply add_le_add
    · simpa only [abs_neg] using hb i j r
    · apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hconv l) (abs_nonneg _)
  have he : r*correlation z ρ σ A qp W C i j r =
      ((-qPrime z σ A qp W C i j r)+∑ l, ρ l*
        ∫ t : ℝ, qPrime z σ A qp W C i l (t+r)*q z σ A qp W C j l t)/(2*π) := by
    unfold correlation
    field_simp [hr.ne']
  rw [he, abs_div, abs_of_pos (by positivity : 0 < 2*π)]
  exact div_le_div_of_nonneg_right hn (by positivity)

theorem orderedRadialCorrelation_zero_radius_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 ≤ ρ i)
    (hσ : ∀ i, 0 < σ i) (i j : Fin N) :
    IntegrableOn (fun r => r*orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j r) (Ioi 0) := by
  have hb (a b : Fin N) := correlation_radius_bounded_of_qPrime_bound z hz ρ σ
    (amplitudeA z ρ σ 0 (baseSeed z ρ σ)) (amplitudeQp z ρ σ 0 (baseSeed z ρ σ))
    (W z ρ 0 (baseSeed z ρ σ)) (C z ρ σ 0 (baseSeed z ρ σ)) (fun i => (hσ i).le)
    (hsPrimeBound ρ σ) (qPrime_zero_abs_le z ρ σ (fun i => (hσ i).le)) a b
  obtain ⟨B, hB, hbound⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ r > 0,
      |r*orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j r| ≤ B := by
    unfold orderedRadialCorrelation
    split_ifs <;> exact hb _ _
  let R := edgeHi σ i j
  let c := orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j
  have hdom : Integrable ((Icc (0 : ℝ) R).indicator (fun _ => B)) :=
    ((continuous_const (y := B)).integrableOn_Icc).integrable_indicator measurableSet_Icc
  apply hdom.integrableOn.mono' (measurable_id.mul
    (orderedRadialCorrelation_measurable z hz ρ σ (fun i => (hσ i).le) 0 0 _ i j)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  by_cases hh : r ≤ R
  · rw [indicator_of_mem (show r ∈ Icc (0 : ℝ) R from ⟨hr.le, hh⟩), Real.norm_eq_abs]
    exact hbound r hr
  · rw [indicator_of_notMem (show r ∉ Icc (0 : ℝ) R from fun h => hh h.2)]
    rw [orderedRadialCorrelation_zero_exterior z hz ρ σ hv hρ hσ i j r (not_le.mp hh)]
    simp

end FMSA.ExactMSA.MultiTailMixture
