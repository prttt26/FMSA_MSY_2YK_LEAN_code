import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearDecay

/-! One actual nonlinear mixture RDF, using each pair's additive contact.
Its hard core and decay are proved; the radial OZ identification is separate. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def nonlinearCausalG (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (r : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => nonlinearRDFExcess z ρ σ Dt G r i j+r+edgeHi σ i j)

theorem nonlinearCausalG_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    Continuous (nonlinearCausalG z ρ σ Dt G) := by
  apply continuous_matrix
  intro i j
  exact (((nonlinearRDFExcess_continuous z ρ σ Dt G).matrix_elem i j).add continuous_id).add_const _

theorem nonlinearCausalG_renewal (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    nonlinearCausalG z ρ σ Dt G r i j=nonlinearGSource z ρ σ Dt G r i j+
      ∑ m, ∫ t in (0 : ℝ)..r, nonlinearCausalG z ρ σ Dt G t i m*
        nonlinearCausalKernel z ρ σ Dt G (r-t) m j := by
  have he (m : Fin N) : (∫ t in (0 : ℝ)..r, nonlinearCausalG z ρ σ Dt G t i m*
      nonlinearCausalKernel z ρ σ Dt G (r-t) m j) =
      (∫ t in (0 : ℝ)..r, nonlinearRDFExcess z ρ σ Dt G t i m*
        nonlinearCausalKernel z ρ σ Dt G (r-t) m j)+
        ρ m*∫ t in (0 : ℝ)..r, nonlinearRecenteredQ z ρ σ Dt G m j (r-t)*(t+edgeHi σ i m) := by
    have hi0 : IntervalIntegrable (fun t => nonlinearRDFExcess z ρ σ Dt G t i m*
        nonlinearCausalKernel z ρ σ Dt G (r-t) m j) volume 0 r :=
      (((nonlinearRDFExcess_continuous z ρ σ Dt G).matrix_elem i m).mul
        (((nonlinearCausalKernel_continuous z ρ σ Dt G).matrix_elem m j).comp
          (continuous_const.sub continuous_id))).intervalIntegrable 0 r
    have hi1 : IntervalIntegrable (fun t => ρ m*(nonlinearRecenteredQ z ρ σ Dt G m j (r-t)*
        (t+edgeHi σ i m))) volume 0 r := by
      apply Continuous.intervalIntegrable
      exact (((nonlinearRecenteredQ_continuous z ρ σ Dt G m j).comp
        (continuous_const.sub continuous_id)).mul (continuous_id.add_const _)).const_mul _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi0 hi1]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [nonlinearCausalG, nonlinearCausalKernel, Matrix.of_apply]
    ring
  change nonlinearRDFExcess z ρ σ Dt G r i j+r+edgeHi σ i j =
    nonlinearGSource z ρ σ Dt G r i j+
      ∑ m, ∫ t in (0 : ℝ)..r, nonlinearCausalG z ρ σ Dt G t i m*
        nonlinearCausalKernel z ρ σ Dt G (r-t) m j
  rw [nonlinearRDFExcess_renewal z ρ σ Dt G i j r hr]
  simp only [he, Finset.sum_add_distrib, nonlinearExcessSource, Matrix.of_apply]
  ring

def nonlinearRDFMoment (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) : ℝ :=
  (Ioo (-edgeHi σ i j) (edgeHi σ i j)).indicator (fun r => -r) r+
    causalShift (fun u => nonlinearRDFExcess z ρ σ Dt G u i j) (edgeHi σ i j) r-
      causalShift (fun u => nonlinearRDFExcess z ρ σ Dt G u i j) (edgeHi σ i j) (-r)

def nonlinearH (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) : ℝ := nonlinearRDFMoment z ρ σ Dt G i j r/r

def nonlinearG (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) : ℝ :=
  if r < edgeHi σ i j then 0 else nonlinearCausalG z ρ σ Dt G (r-edgeHi σ i j) i j/r

theorem nonlinearG_hardcore (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : r < edgeHi σ i j) : nonlinearG z ρ σ Dt G i j r=0 := by
  simp [nonlinearG, hr]

theorem nonlinearRDFMoment_core (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : r ∈ Ioo (-edgeHi σ i j) (edgeHi σ i j)) :
    nonlinearRDFMoment z ρ σ Dt G i j r= -r := by
  rw [nonlinearRDFMoment, indicator_of_mem hr, causalShift_eq_zero_below _ _ _ hr.2,
    causalShift_eq_zero_below _ _ _ (show -r < edgeHi σ i j from by linarith [hr.1])]
  ring

theorem nonlinearRDFMoment_outer (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) (hR : 0 < edgeHi σ i j) (r : ℝ) (hr : edgeHi σ i j ≤ r) :
    nonlinearRDFMoment z ρ σ Dt G i j r=nonlinearRDFExcess z ρ σ Dt G (r-edgeHi σ i j) i j := by
  rw [nonlinearRDFMoment, indicator_of_notMem
    (show r ∉ Ioo (-edgeHi σ i j) (edgeHi σ i j) from fun h => not_lt_of_ge hr h.2),
    causalShift_eq_zero_below _ _ _ (show -r < edgeHi σ i j from by linarith)]
  unfold causalShift causalFull
  rw [indicator_of_mem (show r-edgeHi σ i j ∈ Ici (0 : ℝ) from sub_nonneg.mpr hr)]
  ring

theorem nonlinearH_hardcore (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : 0 < r) (hR : r < edgeHi σ i j) :
    nonlinearH z ρ σ Dt G i j r= -1 := by
  rw [nonlinearH, nonlinearRDFMoment_core z ρ σ Dt G i j r ⟨by linarith, hR⟩]
  field_simp [hr.ne']

theorem nonlinearG_eq_one_add_h (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) (hR : 0 < edgeHi σ i j) (r : ℝ) (hr : 0 < r) :
    nonlinearG z ρ σ Dt G i j r=1+nonlinearH z ρ σ Dt G i j r := by
  by_cases h : r < edgeHi σ i j
  · rw [nonlinearG_hardcore z ρ σ Dt G i j r h, nonlinearH_hardcore z ρ σ Dt G i j r hr h]
    ring
  · rw [nonlinearG, if_neg h, nonlinearH, nonlinearRDFMoment_outer z ρ σ Dt G i j hR r (not_lt.mp h)]
    simp only [nonlinearCausalG, Matrix.of_apply]
    field_simp [hr.ne']
    ring

theorem nonlinearRDFMoment_measurable (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) : Measurable (nonlinearRDFMoment z ρ σ Dt G i j) := by
  have hc : Measurable (causalShift (fun u => nonlinearRDFExcess z ρ σ Dt G u i j) (edgeHi σ i j)) :=
    (((nonlinearRDFExcess_continuous z ρ σ Dt G).matrix_elem i j).measurable.indicator measurableSet_Ici).comp
      (by fun_prop)
  exact ((measurable_id.neg.indicator measurableSet_Ioo).add hc).sub (hc.comp measurable_neg)

theorem nonlinearRDFMoment_integrable_of_weighted_budget (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (i j : Fin N) :
    Integrable (nonlinearRDFMoment z ρ σ Dt G i j) := by
  have ho := causalShift_integrable _
    (nonlinearRDFExcess_integrable_of_weighted_budget z ρ σ Dt G hz hσ hv δ hδ hδz hb i j) (edgeHi σ i j)
  have hn := (Measure.measurePreserving_neg volume).integrable_comp_of_integrable ho
  have hc : Integrable ((Ioo (-edgeHi σ i j) (edgeHi σ i j)).indicator (fun r : ℝ => -r)) :=
    (continuous_id.neg.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  exact (hc.add ho).sub hn

theorem nonlinearH_radius_integrable_of_weighted_budget (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (i j : Fin N) :
    Integrable (fun r => r*nonlinearH z ρ σ Dt G i j r) := by
  apply (nonlinearRDFMoment_integrable_of_weighted_budget z ρ σ Dt G hz hσ hv δ hδ hδz hb i j).congr
  filter_upwards [volume.ae_ne (0 : ℝ)] with r hr
  unfold nonlinearH
  field_simp

end FMSA.ExactMSA.MultiTailMixture
