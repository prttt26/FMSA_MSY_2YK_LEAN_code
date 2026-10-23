import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearRDF

/-! Actual real half-line Laplace transforms for the nonlinear mixture RDF. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def realCausalLaplace (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), exp (-s*t)*f t

def realMatrixLaplace (f : ℝ → Matrix (Fin N) (Fin N) ℝ) (s : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => realCausalLaplace (fun t => f t i j) s)

theorem realCausalLaplace_convolution (q y : ℝ → ℝ) (s : ℝ)
    (hiq : IntegrableOn (fun t => exp (-s*t)*q t) (Ioi 0))
    (hiy : IntegrableOn (fun t => exp (-s*t)*y t) (Ioi 0)) :
    IntegrableOn (fun r => exp (-s*r)*causalIntervalConv q y r) (Ioi 0) ∧
      realCausalLaplace (causalIntervalConv q y) s=realCausalLaplace y s*realCausalLaplace q s := by
  let qw := fun t => exp (-s*t)*q t
  let yw := fun t => exp (-s*t)*y t
  have he : ∀ r, 0 < r → exp (-s*r)*causalIntervalConv q y r=
      posConvolution yw qw (ContinuousLinearMap.mul ℝ ℝ) volume r := by
    intro r hr
    rw [posConvolution, indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr),
      causalIntervalConv, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [ContinuousLinearMap.mul_apply', qw, yw, causalIntervalConv]
    have hx : exp (-s*t)*exp (-s*(r-t))=exp (-s*r) := by
      rw [← exp_add]; congr 1; ring
    linear_combination -(q (r-t)*y t)*hx
  have hi : IntegrableOn (posConvolution yw qw (ContinuousLinearMap.mul ℝ ℝ) volume) (Ioi 0) :=
    (integrable_posConvolution hiy hiq (ContinuousLinearMap.mul ℝ ℝ)).integrableOn
  constructor
  · exact hi.congr_fun (fun r hr => (he r hr).symm) measurableSet_Ioi
  · unfold realCausalLaplace
    rw [setIntegral_congr_fun measurableSet_Ioi (fun r hr => he r hr)]
    have hh : (∫ r in Ioi (0 : ℝ), posConvolution yw qw (ContinuousLinearMap.mul ℝ ℝ) volume r) =
        ∫ r in Ioi (0 : ℝ), ∫ t in (0 : ℝ)..r, yw t*qw (r-t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      simp [posConvolution, indicator_of_mem hr, ContinuousLinearMap.mul_apply']
    rw [hh]
    simpa only [ContinuousLinearMap.mul_apply', qw, yw] using
      (integral_posConvolution hiy hiq (ContinuousLinearMap.mul ℝ ℝ))

theorem realMatrixLaplace_right_renewal (q f y : ℝ → Matrix (Fin N) (Fin N) ℝ) (s : ℝ)
    (hiq : ∀ i j, IntegrableOn (fun t => exp (-s*t)*q t i j) (Ioi 0))
    (hif : ∀ i j, IntegrableOn (fun t => exp (-s*t)*f t i j) (Ioi 0))
    (hiy : ∀ i j, IntegrableOn (fun t => exp (-s*t)*y t i j) (Ioi 0))
    (heq : ∀ i j r, 0 ≤ r → y r i j=f r i j+
      ∑ m, ∫ t in (0 : ℝ)..r, y t i m*q (r-t) m j) :
    realMatrixLaplace y s*(1-realMatrixLaplace q s)=realMatrixLaplace f s := by
  have ht (i j : Fin N) : realCausalLaplace (fun r => y r i j) s=
      realCausalLaplace (fun r => f r i j) s+
        ∑ m, realCausalLaplace (fun r => y r i m) s*realCausalLaplace (fun r => q r m j) s := by
    have he : (∫ r in Ioi (0 : ℝ), exp (-s*r)*y r i j)=
        ∫ r in Ioi (0 : ℝ), exp (-s*r)*f r i j+
          ∑ m, exp (-s*r)*causalIntervalConv (fun t => q t m j) (fun t => y t i m) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [heq i j r hr.le, mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      unfold causalIntervalConv
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      ring
    unfold realCausalLaplace
    rw [he, integral_add (hif i j) (integrable_finsetSum _ (fun m _ =>
      (realCausalLaplace_convolution _ _ s (hiq m j) (hiy i m)).1)),
      integral_finsetSum _ (fun m _ => (realCausalLaplace_convolution _ _ s (hiq m j) (hiy i m)).1)]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    exact (realCausalLaplace_convolution _ _ s (hiq m j) (hiy i m)).2
  rw [mul_sub, Matrix.mul_one]
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, realMatrixLaplace, Matrix.of_apply]
  exact sub_eq_iff_eq_add.mpr (ht i j)

theorem nonlinearCausalKernel_laplace_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (s : ℝ) (hs : 0 < s) (i j : Fin N) :
    IntegrableOn (fun t => exp (-s*t)*nonlinearCausalKernel z ρ σ Dt G t i j) (Ioi 0) := by
  have hi : IntegrableOn (fun t => ρ i*(exp (-s*t)*nonlinearRecenteredQ z ρ σ Dt G i j t)) (Ioi 0) :=
    (nonlinearRecenteredQ_weighted_integrable z ρ σ Dt G hσ (-s)
      (fun u => by linarith [hz u]) i j).const_mul (ρ i)
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  simp only [nonlinearCausalKernel, Matrix.of_apply]
  ring

theorem nonlinearGSource_laplace_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (s : ℝ) (hs : 0 < s) (i j : Fin N) :
    IntegrableOn (fun t => exp (-s*t)*nonlinearGSource z ρ σ Dt G t i j) (Ioi 0) := by
  have hi : IntegrableOn (fun t => (amplitudeA z ρ σ Dt G j*(t*exp (-s*t))+
      amplitudeQp z ρ σ Dt G i j*exp (-s*t)+
      ∑ u, (z u*C z ρ σ Dt G u i j)*exp (-(s+z u)*t))/(2*π)) (Ioi 0) :=
    (((FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg hs).const_mul _).add
      ((integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0).const_mul _) |>.add
      (integrable_finsetSum _ (fun u _ =>
        (integrableOn_exp_mul_Ioi (by linarith [hz u] : -(s+z u) < 0) 0).const_mul _))).div_const _
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  simp only [nonlinearGSource, Matrix.of_apply]
  rw [← mul_div_assoc, mul_add, mul_add, Finset.mul_sum]
  congr 1
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro u _
    have he : exp (-(s+z u)*t)=exp (-s*t)*exp (-z u*t) := by rw [← exp_add]; congr 1; ring
    rw [he]
    ring

theorem realLaplace_weight_integrable_of_L1 (f : ℝ → ℝ) (hi : IntegrableOn f (Ioi 0))
    (s : ℝ) (hs : 0 ≤ s) : IntegrableOn (fun t => exp (-s*t)*f t) (Ioi 0) := by
  have hh : IntegrableOn (fun t => f t*exp (-s*t)) (Ioi 0) := hi.mul_bdd
    (by apply Continuous.aestronglyMeasurable; fun_prop)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) ht.le))
  exact hh.congr_fun (fun t _ => by dsimp only; ring) measurableSet_Ioi

theorem nonlinearCausalG_laplace_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (s : ℝ) (hs : 0 < s) (i j : Fin N) :
    IntegrableOn (fun t => exp (-s*t)*nonlinearCausalG z ρ σ Dt G t i j) (Ioi 0) := by
  have hiE := realLaplace_weight_integrable_of_L1 _
    (nonlinearRDFExcess_integrable_of_weighted_budget z ρ σ Dt G hz hσ hv δ hδ hδz hb i j) s hs.le
  have hi : IntegrableOn (fun t => exp (-s*t)*nonlinearRDFExcess z ρ σ Dt G t i j+
      t*exp (-s*t)+edgeHi σ i j*exp (-s*t)) (Ioi 0) :=
    (hiE.add (FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg hs)).add
      ((integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0).const_mul _)
  exact hi.congr_fun (fun t _ => by simp only [nonlinearCausalG, Matrix.of_apply]; ring) measurableSet_Ioi

/-- The full nonlinear Laplace renewal follows from the constructed RDF and
actual kernel; its marginal L1 hypotheses are discharged by the budget. -/
theorem nonlinearCausalG_actual_laplace_renewal (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (s : ℝ) (hs : 0 < s) :
    realMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s*
      (1-realMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s)=
        realMatrixLaplace (nonlinearGSource z ρ σ Dt G) s :=
  realMatrixLaplace_right_renewal _ _ _ s
    (nonlinearCausalKernel_laplace_integrable z ρ σ Dt G hz hσ s hs)
    (nonlinearGSource_laplace_integrable z ρ σ Dt G hz s hs)
    (nonlinearCausalG_laplace_integrable z ρ σ Dt G hz hσ hv δ hδ hδz hb s hs)
    (nonlinearCausalG_renewal z ρ σ Dt G)

theorem nonlinearGSource_actual_laplace (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (s : ℝ) (hs : 0 < s) (i j : Fin N) :
    realMatrixLaplace (nonlinearGSource z ρ σ Dt G) s i j=
      (amplitudeA z ρ σ Dt G j/s^2+amplitudeQp z ρ σ Dt G i j/s+
        ∑ u, z u*C z ρ σ Dt G u i j/(s+z u))/(2*π) := by
  have hA : IntegrableOn (fun t => amplitudeA z ρ σ Dt G j*(t*exp (-s*t))) (Ioi 0) :=
    (FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg hs).const_mul _
  have hQ : IntegrableOn (fun t => amplitudeQp z ρ σ Dt G i j*exp (-s*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0).const_mul _
  have hu (u : ι) : IntegrableOn (fun t => (z u*C z ρ σ Dt G u i j)*exp (-(s+z u)*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith [hz u] : -(s+z u) < 0) 0).const_mul _
  have hsum : IntegrableOn (fun t => ∑ u, (z u*C z ρ σ Dt G u i j)*exp (-(s+z u)*t)) (Ioi 0) :=
    integrable_finsetSum _ (fun u _ => hu u)
  have hAQ : IntegrableOn (fun t => amplitudeA z ρ σ Dt G j*(t*exp (-s*t))+
      amplitudeQp z ρ σ Dt G i j*exp (-s*t)) (Ioi 0) := hA.add hQ
  have he : (fun t => exp (-s*t)*nonlinearGSource z ρ σ Dt G t i j) = fun t =>
      (amplitudeA z ρ σ Dt G j*(t*exp (-s*t))+amplitudeQp z ρ σ Dt G i j*exp (-s*t)+
        ∑ u, (z u*C z ρ σ Dt G u i j)*exp (-(s+z u)*t))/(2*π) := by
    funext t
    simp only [nonlinearGSource, Matrix.of_apply]
    rw [← mul_div_assoc, mul_add, mul_add, Finset.mul_sum]
    congr 1
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro u _
      have hx : exp (-(s+z u)*t)=exp (-s*t)*exp (-z u*t) := by rw [← exp_add]; congr 1; ring
      rw [hx]; ring
  simp only [realMatrixLaplace, Matrix.of_apply, realCausalLaplace]
  rw [he, integral_div, integral_add hAQ hsum, integral_add hA hQ,
    integral_const_mul, integral_const_mul,
    FMSA.ExactMSA.integral_Ioi_id_mul_exp_neg hs,
    integral_exp_mul_Ioi (by linarith : -s < 0),
    integral_finsetSum _ (fun u _ => hu u)]
  simp only [mul_zero, exp_zero, one_div_neg, neg_neg]
  congr 1
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro u _
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [hz u] : -(s+z u) < 0)]
    simp only [mul_zero, exp_zero, mul_one]
    rw [neg_div_neg_eq]
    ring

end FMSA.ExactMSA.MultiTailMixture
