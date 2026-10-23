import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFBudget

/-! Pair-contact HS Volterra candidate, retaining each actual R_ij and the
left-density recentered HS kernel. Its reference OZ/WT identity is deliberately
not inferred from the construction or the weighted decay criterion. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def rdfHSCoreSource (ρ σ : Fin N → ℝ) (u : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => ∑ m, ρ m*((∫ v in (0 : ℝ)..σ m,
    rdfRecenteredHSQ ρ σ m i v*(v-u-edgeHi σ m j))-
      ∫ v in (0 : ℝ)..min u (σ m), rdfRecenteredHSQ ρ σ m i v*(v-u-edgeHi σ m j)))

theorem rdfHSCoreSource_continuous (ρ σ : Fin N → ℝ) : Continuous (rdfHSCoreSource ρ σ) := by
  apply continuous_matrix
  intro i j
  simp only [rdfHSCoreSource, Matrix.of_apply]
  apply continuous_finsetSum
  intro m _
  have hc : Continuous (Function.uncurry (fun u v : ℝ =>
      rdfRecenteredHSQ ρ σ m i v*(v-u-edgeHi σ m j))) := by
    exact ((rdfRecenteredHSQ_continuous ρ σ m i).comp continuous_snd).mul
      (continuous_snd.sub continuous_fst |>.sub continuous_const)
  exact ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 (σ m)).sub
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hc
      (continuous_id.min continuous_const))).const_mul (ρ m)

theorem rdfHSCoreSource_eq_tail_windows (ρ σ : Fin N → ℝ) (u : ℝ) (i j : Fin N) :
    rdfHSCoreSource ρ σ u i j=∑ m, ρ m*∫ v in min u (σ m)..σ m,
      rdfRecenteredHSQ ρ σ m i v*(v-u-edgeHi σ m j) := by
  simp only [rdfHSCoreSource, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  have hc : Continuous (fun v => rdfRecenteredHSQ ρ σ m i v*(v-u-edgeHi σ m j)) := by
    exact (rdfRecenteredHSQ_continuous ρ σ m i).mul (by fun_prop)
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 (min u (σ m)))
    (hc.intervalIntegrable (μ := volume) (min u (σ m)) (σ m))
  linear_combination -h

def rdfHSSupportCeiling (σ : Fin N → ℝ) : ℝ := ∑ i, |σ i|

theorem rdfHSSupportCeiling_nonneg (σ : Fin N → ℝ) : 0 ≤ rdfHSSupportCeiling σ := by
  unfold rdfHSSupportCeiling; positivity

theorem rdfHSCoreSource_zero_above (ρ σ : Fin N → ℝ) (u : ℝ)
    (hu : rdfHSSupportCeiling σ ≤ u) : rdfHSCoreSource ρ σ u=0 := by
  ext i j
  have hs (m : Fin N) : σ m ≤ u := (le_abs_self _).trans
    ((Finset.single_le_sum (f := fun i : Fin N => |σ i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ m)).trans hu)
  simp [rdfHSCoreSource, min_eq_right (hs _)]

theorem rdfHSCoreSource_weighted_bounded (ρ σ : Fin N → ℝ) (δ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u, 0 ≤ u → exp (δ*u)*FMSA.matrixAbsSum (rdfHSCoreSource ρ σ u) ≤ B := by
  let f := fun u => exp (δ*u)*FMSA.matrixAbsSum (rdfHSCoreSource ρ σ u)
  have hc : Continuous f := (by fun_prop : Continuous (fun u : ℝ => exp (δ*u))).mul
    (FMSA.matrixAbsSum_continuous _ (rdfHSCoreSource_continuous ρ σ))
  obtain ⟨x, _, hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) (rdfHSSupportCeiling σ)).Nonempty from
      ⟨0, ⟨le_rfl, rdfHSSupportCeiling_nonneg σ⟩⟩) hc.continuousOn
  refine ⟨f x, mul_nonneg (exp_pos _).le (FMSA.matrixAbsSum_nonneg _), ?_⟩
  intro u hu
  by_cases hh : u ≤ rdfHSSupportCeiling σ
  · exact hm ⟨hu, hh⟩
  · rw [rdfHSCoreSource_zero_above ρ σ u (not_le.mp hh).le]
    simpa [f, FMSA.matrixAbsSum] using (mul_nonneg (exp_pos (δ*x)).le
      (FMSA.matrixAbsSum_nonneg (rdfHSCoreSource ρ σ x)))

def rdfHSPairExterior (ρ σ : Fin N → ℝ) : ℝ → Matrix (Fin N) (Fin N) ℝ :=
  FMSA.MixtureOzStar.matBaxterPsiOuterFun 0 (fun t => (rdfCausalKernel ρ σ t).transpose)
    (rdfHSCoreSource ρ σ) (rdfCausalKernelTranspose_continuous ρ σ) (rdfHSCoreSource_continuous ρ σ)

theorem rdfHSPairExterior_continuous (ρ σ : Fin N → ℝ) : Continuous (rdfHSPairExterior ρ σ) :=
  FMSA.MixtureOzStar.matBaxterPsiOuterFun_continuous 0 _ _ _ _

theorem rdfHSPairExterior_renewal (ρ σ : Fin N → ℝ) (i j : Fin N) (u : ℝ) (hu : 0 ≤ u) :
    rdfHSPairExterior ρ σ u i j=rdfHSCoreSource ρ σ u i j+
      ∑ m, ∫ t in (0 : ℝ)..u, rdfCausalKernel ρ σ (u-t) m i*rdfHSPairExterior ρ σ t m j :=
  FMSA.MixtureOzStar.matBaxterPsiOuter_matRenewalEq 0 _ _ _ _ i j u hu

theorem rdfHSPairExterior_integrable_of_weighted_budget (ρ σ : Fin N → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1) (i j : Fin N) :
    IntegrableOn (fun u => rdfHSPairExterior ρ σ u i j) (Ioi 0) := by
  obtain ⟨B, hB, hf⟩ := rdfHSCoreSource_weighted_bounded ρ σ δ
  apply FMSA.matrixRenewal_entry_integrable_of_weighted_budget
    (fun t => (rdfCausalKernel ρ σ t).transpose) (rdfHSCoreSource ρ σ) (rdfHSPairExterior ρ σ)
    (rdfCausalKernelTranspose_continuous ρ σ) (rdfHSPairExterior_continuous ρ σ)
    δ (rdfWeightedKernelBudget ρ σ δ) B hδ
    (by simpa only [FMSA.matrixAbsSum_transpose] using rdfCausalKernel_weighted_absSum_integrable ρ σ δ)
    (by simp only [FMSA.matrixAbsSum_transpose, rdfWeightedKernelBudget]; exact le_refl _)
    hb hB hf (rdfHSPairExterior_renewal ρ σ) i j

def rdfHSPairMoment (ρ σ : Fin N → ℝ) (i j : Fin N) (r : ℝ) : ℝ :=
  (Ioo (-edgeHi σ i j) (edgeHi σ i j)).indicator (fun r => -r) r+
    causalShift (fun u => rdfHSPairExterior ρ σ u i j) (edgeHi σ i j) r-
      causalShift (fun u => rdfHSPairExterior ρ σ u i j) (edgeHi σ i j) (-r)

def rdfHSPairCandidate (ρ σ : Fin N → ℝ) (i j : Fin N) (r : ℝ) : ℝ :=
  rdfHSPairMoment ρ σ i j r/r

theorem rdfHSPairMoment_measurable (ρ σ : Fin N → ℝ) (i j : Fin N) :
    Measurable (rdfHSPairMoment ρ σ i j) := by
  have hc : Measurable (causalShift (fun u => rdfHSPairExterior ρ σ u i j) (edgeHi σ i j)) :=
    (((rdfHSPairExterior_continuous ρ σ).matrix_elem i j).measurable.indicator measurableSet_Ici).comp
      (by fun_prop)
  exact ((measurable_id.neg.indicator measurableSet_Ioo).add hc).sub (hc.comp measurable_neg)

theorem rdfHSPairMoment_core (ρ σ : Fin N → ℝ) (i j : Fin N) (r : ℝ)
    (hr : r ∈ Ioo (-edgeHi σ i j) (edgeHi σ i j)) : rdfHSPairMoment ρ σ i j r= -r := by
  rw [rdfHSPairMoment, indicator_of_mem hr, causalShift_eq_zero_below _ _ _ hr.2,
    causalShift_eq_zero_below _ _ _ (show -r < edgeHi σ i j from by linarith [hr.1])]
  ring

theorem rdfHSPairMoment_outer (ρ σ : Fin N → ℝ) (i j : Fin N)
    (hR : 0 < edgeHi σ i j) (r : ℝ) (hr : edgeHi σ i j ≤ r) :
    rdfHSPairMoment ρ σ i j r=rdfHSPairExterior ρ σ (r-edgeHi σ i j) i j := by
  rw [rdfHSPairMoment, indicator_of_notMem
    (show r ∉ Ioo (-edgeHi σ i j) (edgeHi σ i j) from fun h => not_lt_of_ge hr h.2),
    causalShift_eq_zero_below _ _ _ (show -r < edgeHi σ i j from by linarith)]
  unfold causalShift causalFull
  rw [indicator_of_mem (show r-edgeHi σ i j ∈ Ici (0 : ℝ) from sub_nonneg.mpr hr)]
  ring

theorem rdfHSPairMoment_integrable_of_weighted_budget (ρ σ : Fin N → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1) (i j : Fin N) :
    Integrable (rdfHSPairMoment ρ σ i j) := by
  have ho := causalShift_integrable _ (rdfHSPairExterior_integrable_of_weighted_budget ρ σ δ hδ hb i j)
    (edgeHi σ i j)
  have hn := (Measure.measurePreserving_neg volume).integrable_comp_of_integrable ho
  have hc : Integrable ((Ioo (-edgeHi σ i j) (edgeHi σ i j)).indicator (fun r : ℝ => -r)) :=
    (continuous_id.neg.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  exact (hc.add ho).sub hn

theorem rdfHSPairCandidate_radius_measurable (ρ σ : Fin N → ℝ) (i j : Fin N) :
    Measurable (fun r => r*rdfHSPairCandidate ρ σ i j r) :=
  measurable_id.mul ((rdfHSPairMoment_measurable ρ σ i j).div measurable_id)

theorem rdfHSPairCandidate_radius_integrable_of_weighted_budget (ρ σ : Fin N → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1) (i j : Fin N) :
    Integrable (fun r => r*rdfHSPairCandidate ρ σ i j r) := by
  apply (rdfHSPairMoment_integrable_of_weighted_budget ρ σ δ hδ hb i j).congr
  filter_upwards [volume.ae_ne (0 : ℝ)] with r hr
  unfold rdfHSPairCandidate
  field_simp [hr]

theorem rdfHSPairCandidate_hardcore (ρ σ : Fin N → ℝ) (i j : Fin N)
    (r : ℝ) (hr : 0 < r) (hR : r < edgeHi σ i j) : rdfHSPairCandidate ρ σ i j r= -1 := by
  unfold rdfHSPairCandidate
  rw [rdfHSPairMoment_core ρ σ i j r ⟨by linarith, hR⟩]
  field_simp

theorem hsPair_contact_argument_shift (σ : Fin N → ℝ) (i j m : Fin N) (u v : ℝ) :
    edgeHi σ i j+u-(edgeLo σ m i+v)=edgeHi σ m j+u-v := by
  unfold edgeHi edgeLo; ring

theorem rdfHSPairMoment_window_integrable (ρ σ : Fin N → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1)
    (m i j : Fin N) (u a b : ℝ) :
    IntervalIntegrable (fun v => rdfRecenteredHSQ ρ σ m i v*
      rdfHSPairMoment ρ σ m j (edgeHi σ m j+u-v)) volume a b := by
  have hi := (Measure.measurePreserving_sub_left volume (edgeHi σ m j+u)).integrable_comp_of_integrable
    (rdfHSPairMoment_integrable_of_weighted_budget ρ σ δ hδ hb m j)
  have hi' : Integrable (fun v => rdfHSPairMoment ρ σ m j (edgeHi σ m j+u-v)) := hi
  rw [intervalIntegrable_iff]
  exact (MeasureTheory.IntegrableOn.continuousOn_mul
    (rdfRecenteredHSQ_continuous ρ σ m i).continuousOn
    hi'.integrableOn isCompact_uIcc).mono_set uIoc_subset_uIcc

theorem rdfHSPairMoment_recentered_window (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (δ : ℝ) (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1)
    (m i j : Fin N) (u : ℝ) (hu : 0 ≤ u) :
    (∫ v in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m i v*
      rdfHSPairMoment ρ σ m j (edgeHi σ m j+u-v)) =
    (∫ v in min u (σ m)..σ m, rdfRecenteredHSQ ρ σ m i v*(v-u-edgeHi σ m j))+
      ∫ v in (0 : ℝ)..u, rdfRecenteredHSQ ρ σ m i v*rdfHSPairExterior ρ σ (u-v) m j := by
  have hR : 0 < edgeHi σ m j := by unfold edgeHi; linarith [hσ m, hσ j]
  have hmin0 : 0 ≤ min u (σ m) := le_min hu (hσ m).le
  have hminu : min u (σ m) ≤ u := min_le_left _ _
  have hA : (∫ v in (0 : ℝ)..min u (σ m), rdfRecenteredHSQ ρ σ m i v*
      rdfHSPairMoment ρ σ m j (edgeHi σ m j+u-v)) =
      ∫ v in (0 : ℝ)..min u (σ m), rdfRecenteredHSQ ρ σ m i v*rdfHSPairExterior ρ σ (u-v) m j := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hmin0]
    intro v hv
    dsimp only
    rw [rdfHSPairMoment_outer ρ σ m j hR _ (by linarith [hv.2])]
    congr 2
    ring
  have hB : (∫ v in min u (σ m)..σ m, rdfRecenteredHSQ ρ σ m i v*
      rdfHSPairMoment ρ σ m j (edgeHi σ m j+u-v)) =
      ∫ v in min u (σ m)..σ m, rdfRecenteredHSQ ρ σ m i v*(v-u-edgeHi σ m j) := by
    by_cases hs : σ m ≤ u
    · simp [min_eq_right hs]
    · rw [min_eq_left (not_le.mp hs).le]
      apply intervalIntegral.integral_congr_Ioo_of_le (not_le.mp hs).le
      intro v hv
      dsimp only
      rw [rdfHSPairMoment_core ρ σ m j _
        (show edgeHi σ m j+u-v ∈ Ioo (-edgeHi σ m j) (edgeHi σ m j) from
          ⟨by unfold edgeHi; linarith [hv.2, hσ j], by linarith [hv.1]⟩)]
      ring
  have hc : Continuous (fun v => rdfRecenteredHSQ ρ σ m i v*rdfHSPairExterior ρ σ (u-v) m j) :=
    (rdfRecenteredHSQ_continuous ρ σ m i).mul
      (((rdfHSPairExterior_continuous ρ σ).matrix_elem m j).comp (by fun_prop))
  have hC : (∫ v in (0 : ℝ)..min u (σ m), rdfRecenteredHSQ ρ σ m i v*rdfHSPairExterior ρ σ (u-v) m j) =
      ∫ v in (0 : ℝ)..u, rdfRecenteredHSQ ρ σ m i v*rdfHSPairExterior ρ σ (u-v) m j := by
    by_cases hs : u ≤ σ m
    · simp [min_eq_left hs]
    · rw [min_eq_right (not_le.mp hs).le]
      have hz : (∫ v in σ m..u, rdfRecenteredHSQ ρ σ m i v*rdfHSPairExterior ρ σ (u-v) m j)=0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
        rw [uIcc_of_le (not_le.mp hs).le]
        intro v hv
        simp [rdfRecenteredHSQ, min_eq_right hv.1]
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable (μ := volume) 0 (σ m))
        (hc.intervalIntegrable (μ := volume) (σ m) u), hz, add_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (rdfHSPairMoment_window_integrable ρ σ δ hδ hb m i j u 0 (min u (σ m)))
    (rdfHSPairMoment_window_integrable ρ σ δ hδ hb m i j u (min u (σ m)) (σ m)), hA, hB, hC]
  ring

/-- The actual pairwise exterior satisfies the physical support-recentered
renewal, with actual row lengths and pair contact. Contact samples are treated
by a.e. interval identities in the source/core truncation. No HS OZ is inferred. -/
theorem rdfHSPairMoment_recentered_outer_renewal (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (δ : ℝ) (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1)
    (i j : Fin N) (u : ℝ) (hu : 0 ≤ u) :
    rdfHSPairMoment ρ σ i j (edgeHi σ i j+u)=∑ m, ρ m*
      ∫ v in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m i v*
        rdfHSPairMoment ρ σ m j (edgeHi σ m j+u-v) := by
  have hR : 0 < edgeHi σ i j := by unfold edgeHi; linarith [hσ i, hσ j]
  rw [rdfHSPairMoment_outer ρ σ i j hR _ (by linarith), add_sub_cancel_left,
    rdfHSPairExterior_renewal ρ σ i j u hu, rdfHSCoreSource_eq_tail_windows]
  have he (m : Fin N) : (∫ t in (0 : ℝ)..u, rdfCausalKernel ρ σ (u-t) m i*rdfHSPairExterior ρ σ t m j)=
      ρ m*∫ v in (0 : ℝ)..u, rdfRecenteredHSQ ρ σ m i v*rdfHSPairExterior ρ σ (u-v) m j := by
    simp only [rdfCausalKernel, Matrix.of_apply, mul_assoc, intervalIntegral.integral_const_mul]
    apply congrArg (fun x => ρ m*x)
    have h := intervalIntegral.integral_comp_sub_left
      (fun v => rdfRecenteredHSQ ρ σ m i v*rdfHSPairExterior ρ σ (u-v) m j)
      (a := (0 : ℝ)) (b := u) u
    simpa only [sub_sub_cancel, sub_self, sub_zero] using h
  simp_rw [he]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← mul_add]
  exact congrArg (fun x => ρ m*x)
    (rdfHSPairMoment_recentered_window ρ σ hσ δ hδ hb m i j u hu).symm

theorem dpSeedQ_recentered_indicator {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (m i : Fin N) (v : ℝ) :
    dpSeedQ z ρ σ m i (v+edgeLo σ m i)=
      (Icc (0 : ℝ) (σ m)).indicator (rdfRecenteredHSQ ρ σ m i) v := by
  by_cases hv : 0 ≤ v
  · rw [← rdfRecenteredHSQ_eq_actual z ρ σ m i v hv]
    by_cases hs : v ≤ σ m
    · exact (indicator_of_mem (show v ∈ Icc (0 : ℝ) (σ m) from ⟨hv, hs⟩) _).symm
    · rw [indicator_of_notMem (show v ∉ Icc (0 : ℝ) (σ m) from fun h => hs h.2)]
      simp [rdfRecenteredHSQ, min_eq_right (not_le.mp hs).le]
  · have hl : v+edgeLo σ m i < edgeLo σ m i := by linarith
    rw [indicator_of_notMem (show v ∉ Icc (0 : ℝ) (σ m) from fun h => hv h.1)]
    simp [dpSeedQ, q, hl]

theorem dpSeedQ_contact_window {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (m i j : Fin N) (u : ℝ) (f : ℝ → ℝ) :
    (∫ t : ℝ, dpSeedQ z ρ σ m i t*f (edgeHi σ i j+u-t)) =
      ∫ v in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m i v*f (edgeHi σ m j+u-v) := by
  have he := integral_add_right_eq_self (μ := volume)
    (fun t : ℝ => dpSeedQ z ρ σ m i t*f (edgeHi σ i j+u-t)) (edgeLo σ m i)
  rw [← he]
  have hp : (fun v : ℝ => dpSeedQ z ρ σ m i (v+edgeLo σ m i)*
      f (edgeHi σ i j+u-(v+edgeLo σ m i))) =
      (Icc (0 : ℝ) (σ m)).indicator
        (fun v => rdfRecenteredHSQ ρ σ m i v*f (edgeHi σ m j+u-v)) := by
    funext v
    rw [dpSeedQ_recentered_indicator]
    have ha : edgeHi σ i j+u-(v+edgeLo σ m i)=edgeHi σ m j+u-v := by
      unfold edgeHi edgeLo; ring
    rw [ha]
    by_cases hv : v ∈ Icc (0 : ℝ) (σ m)
    · rw [indicator_of_mem hv, indicator_of_mem hv]
    · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_mul]
  rw [hp, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (hσ m)).symm

theorem rdfHSPairMoment_actual_outer_renewal {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 < σ i) (δ : ℝ)
    (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1)
    (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j ≤ r) :
    rdfHSPairMoment ρ σ i j r=∑ m, ρ m*∫ t : ℝ, dpSeedQ z ρ σ m i t*
      rdfHSPairMoment ρ σ m j (r-t) := by
  have he := rdfHSPairMoment_recentered_outer_renewal ρ σ hσ δ hδ hb i j
    (r-edgeHi σ i j) (sub_nonneg.mpr hr)
  simp only [add_sub_cancel] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro m _
  apply congrArg (fun x => ρ m*x)
  have hw := dpSeedQ_contact_window z ρ σ (fun i => (hσ i).le) m i j
    (r-edgeHi σ i j) (rdfHSPairMoment ρ σ m j)
  simpa only [add_sub_cancel] using hw.symm

/-- Only actual zero-order radial OZ remains: the other three reference
fields are supplied by the actual pair-contact construction and this budget. -/
theorem rdfHSPairCandidate_valid_of_radial_OZ {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 < σ i) (δ : ℝ)
    (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1)
    (hOZ : ∀ i j, rdfHSPairCandidate ρ σ i j =ᵐ[volume.restrict (Ioi 0)]
      fun r => rdfActualHS z ρ σ i j r+
        radialMixtureConv (rdfActualHS z ρ σ) (rdfHSPairCandidate ρ σ) ρ i j r) :
    ValidRadialHSReference z ρ σ (rdfHSPairCandidate ρ σ) := by
  refine ⟨rdfHSPairCandidate_radius_measurable ρ σ,
    rdfHSPairCandidate_radius_integrable_of_weighted_budget ρ σ δ hδ hb, ?_, hOZ⟩
  intro i j r hr hR
  exact rdfHSPairCandidate_hardcore ρ σ i j r hr hR

end FMSA.ExactMSA.MultiTailMixture
