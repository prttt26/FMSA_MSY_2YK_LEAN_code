import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearSource

/-! Actual nonlinear pair-contact RDF construction and weighted decay.
No RDF moment, hard-core property or OZ equation is supplied as a premise. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def nonlinearCausalKernel (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (t : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => ρ i*nonlinearRecenteredQ z ρ σ Dt G i j t)

theorem nonlinearCausalKernel_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    Continuous (nonlinearCausalKernel z ρ σ Dt G) :=
  continuous_matrix (fun i j => (nonlinearRecenteredQ_continuous z ρ σ Dt G i j).const_mul (ρ i))

theorem nonlinearCausalKernelTranspose_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    Continuous (fun t => (nonlinearCausalKernel z ρ σ Dt G t).transpose) :=
  continuous_matrix (fun i j => (nonlinearCausalKernel_continuous z ρ σ Dt G).matrix_elem j i)

theorem nonlinearRecenteredQ_weighted_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i) (δ : ℝ) (hδz : ∀ u, δ < z u)
    (i j : Fin N) : IntegrableOn (fun t => exp (δ*t)*nonlinearRecenteredQ z ρ σ Dt G i j t) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (hσ i)]
  apply IntegrableOn.union
  · exact ((by fun_prop : Continuous (fun t : ℝ => exp (δ*t))).mul
      (nonlinearRecenteredQ_continuous z ρ σ Dt G i j)).integrableOn_Ioc
  · have hi : IntegrableOn (fun t => ∑ u, nonlinearTailAmplitude z ρ σ Dt G u i j*
        exp (-(z u-δ)*t)) (Ioi (σ i)) :=
      integrable_finsetSum _ (fun u _ =>
        (integrableOn_exp_mul_Ioi (by linarith [hδz u] : -(z u-δ) < 0) (σ i)).const_mul _)
    apply hi.congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [nonlinearRecenteredQ_tail z ρ σ Dt G i j t ht.le, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    have he : exp (δ*t)*exp (-z u*t)=exp (-(z u-δ)*t) := by
      rw [← exp_add]; congr 1; ring
    linear_combination -nonlinearTailAmplitude z ρ σ Dt G u i j*he

theorem nonlinearCausalKernel_weighted_entry_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i) (δ : ℝ) (hδz : ∀ u, δ < z u)
    (i j : Fin N) : IntegrableOn (fun t => exp (δ*t)*|nonlinearCausalKernel z ρ σ Dt G t i j|) (Ioi 0) := by
  have hi : IntegrableOn (fun t => ‖ρ i*(exp (δ*t)*nonlinearRecenteredQ z ρ σ Dt G i j t)‖) (Ioi 0) :=
    ((nonlinearRecenteredQ_weighted_integrable z ρ σ Dt G hσ δ hδz i j).const_mul (ρ i)).norm
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  dsimp only
  simp only [nonlinearCausalKernel, Matrix.of_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  ring

theorem nonlinearCausalKernel_weighted_absSum_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i) (δ : ℝ) (hδz : ∀ u, δ < z u) :
    IntegrableOn (fun t => exp (δ*t)*FMSA.matrixAbsSum (nonlinearCausalKernel z ρ σ Dt G t)) (Ioi 0) := by
  have hi : IntegrableOn (fun t => ∑ i, ∑ j, exp (δ*t)*|nonlinearCausalKernel z ρ σ Dt G t i j|) (Ioi 0) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      nonlinearCausalKernel_weighted_entry_integrable z ρ σ Dt G hσ δ hδz i j))
  simpa only [FMSA.matrixAbsSum, Finset.mul_sum] using hi

def nonlinearWeightedKernelBudget (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (δ : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), exp (δ*t)*FMSA.matrixAbsSum (nonlinearCausalKernel z ρ σ Dt G t)

def nonlinearRDFExcess (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (t : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (FMSA.MixtureOzStar.matBaxterPsiOuterFun 0
    (fun t => (nonlinearCausalKernel z ρ σ Dt G t).transpose)
    (fun t => (nonlinearExcessSource z ρ σ Dt G t).transpose)
    (nonlinearCausalKernelTranspose_continuous z ρ σ Dt G)
    (continuous_matrix (fun i j => (nonlinearExcessSource_continuous z ρ σ Dt G).matrix_elem j i)) t).transpose

theorem nonlinearRDFExcess_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    Continuous (nonlinearRDFExcess z ρ σ Dt G) :=
  continuous_matrix (fun i j =>
    (FMSA.MixtureOzStar.matBaxterPsiOuterFun_continuous 0 _ _ _ _).matrix_elem j i)

theorem nonlinearRDFExcess_renewal (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    nonlinearRDFExcess z ρ σ Dt G r i j=nonlinearExcessSource z ρ σ Dt G r i j+
      ∑ m, ∫ t in (0 : ℝ)..r, nonlinearRDFExcess z ρ σ Dt G t i m*
        nonlinearCausalKernel z ρ σ Dt G (r-t) m j := by
  have he := FMSA.MixtureOzStar.matBaxterPsiOuter_matRenewalEq 0
    (fun t => (nonlinearCausalKernel z ρ σ Dt G t).transpose)
    (fun t => (nonlinearExcessSource z ρ σ Dt G t).transpose)
    (nonlinearCausalKernelTranspose_continuous z ρ σ Dt G)
    (continuous_matrix (fun i j => (nonlinearExcessSource_continuous z ρ σ Dt G).matrix_elem j i)) j i r hr
  simpa only [nonlinearRDFExcess, Matrix.transpose_apply, mul_comm] using he

theorem nonlinearRDFExcess_integrable_of_weighted_budget (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (i j : Fin N) :
    IntegrableOn (fun t => nonlinearRDFExcess z ρ σ Dt G t i j) (Ioi 0) := by
  obtain ⟨B, hB, hf⟩ := nonlinearExcessSource_weighted_bounded z ρ σ Dt G hz hσ hv δ (fun u => (hδz u).le)
  apply FMSA.matrixRenewal_entry_integrable_of_weighted_budget
    (fun t => (nonlinearCausalKernel z ρ σ Dt G t).transpose)
    (fun t => (nonlinearExcessSource z ρ σ Dt G t).transpose)
    (fun t => (nonlinearRDFExcess z ρ σ Dt G t).transpose)
    (nonlinearCausalKernelTranspose_continuous z ρ σ Dt G)
    (continuous_matrix (fun i j => (nonlinearRDFExcess_continuous z ρ σ Dt G).matrix_elem j i))
    δ (nonlinearWeightedKernelBudget z ρ σ Dt G δ) B hδ
    (by simpa only [FMSA.matrixAbsSum_transpose] using
      nonlinearCausalKernel_weighted_absSum_integrable z ρ σ Dt G hσ δ hδz)
    (by simp only [FMSA.matrixAbsSum_transpose, nonlinearWeightedKernelBudget]; exact le_refl _)
    hb hB (by simpa only [FMSA.matrixAbsSum_transpose] using hf) _ j i
  intro j i r hr
  simpa only [Matrix.transpose_apply, mul_comm] using nonlinearRDFExcess_renewal z ρ σ Dt G i j r hr

end FMSA.ExactMSA.MultiTailMixture
