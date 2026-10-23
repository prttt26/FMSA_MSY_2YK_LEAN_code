import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearCertificate
import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFCausalFourier

/-! Actual complex nonlinear renewal transforms. Positive real-part damping
handles the affine background before a separate Fourier boundary step. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem complexCausalLaplace_weighted_convolution (q y : ℝ → ℝ)
    (hq : Continuous q) (hy : Continuous y) (s : ℂ)
    (hiq : IntegrableOn (fun t => exp (-s.re*t)*q t) (Ioi 0))
    (hiy : IntegrableOn (fun t => exp (-s.re*t)*y t) (Ioi 0)) :
    IntegrableOn (fun r => (causalIntervalConv q y r : ℂ)*Complex.exp (-s*r)) (Ioi 0) ∧
      FMSA.causalComplexLaplace (causalIntervalConv q y) s=
        FMSA.causalComplexLaplace y s*FMSA.causalComplexLaplace q s := by
  let yw := fun t => (y t : ℂ)*Complex.exp (-s*t)
  let qw := fun t => (q t : ℂ)*Complex.exp (-s*t)
  have hyc : IntegrableOn yw (Ioi 0) := FMSA.complex_laplace_integrable y hy.continuousOn s hiy
  have hqc : IntegrableOn qw (Ioi 0) := FMSA.complex_laplace_integrable q hq.continuousOn s hiq
  have he (r : ℝ) : (causalIntervalConv q y r : ℂ)*Complex.exp (-s*r)=
      ∫ t in (0 : ℝ)..r, yw t*qw (r-t) := by
    unfold causalIntervalConv
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [yw, qw]
    push_cast
    have hx : Complex.exp (-s*(t : ℂ))*Complex.exp (-s*((r-t : ℝ) : ℂ))=
        Complex.exp (-s*r) := by rw [← Complex.exp_add]; push_cast; congr 1; ring
    push_cast at hx
    linear_combination -(q (r-t) : ℂ)*(y t : ℂ)*hx
  constructor
  · apply (integrable_posConvolution hyc hqc (ContinuousLinearMap.mul ℝ ℂ)).integrableOn.congr_fun
      _ measurableSet_Ioi
    intro r hr
    simp only [posConvolution, indicator_of_mem hr, ContinuousLinearMap.mul_apply']
    exact (he r).symm
  · unfold FMSA.causalComplexLaplace
    simp_rw [he]
    simpa only [ContinuousLinearMap.mul_apply', yw, qw] using
      integral_posConvolution hyc hqc (ContinuousLinearMap.mul ℝ ℂ)

theorem complexMatrixLaplace_right_renewal (q f y : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hq : Continuous q) (hf : Continuous f) (hy : Continuous y) (s : ℂ)
    (hiq : ∀ i j, IntegrableOn (fun t => exp (-s.re*t)*q t i j) (Ioi 0))
    (hif : ∀ i j, IntegrableOn (fun t => exp (-s.re*t)*f t i j) (Ioi 0))
    (hiy : ∀ i j, IntegrableOn (fun t => exp (-s.re*t)*y t i j) (Ioi 0))
    (heq : ∀ i j r, 0 ≤ r → y r i j=f r i j+
      ∑ m, causalIntervalConv (fun t => q t m j) (fun t => y t i m) r) :
    rdfMatrixLaplace y s*(1-rdfMatrixLaplace q s)=rdfMatrixLaplace f s := by
  have hv (i j m : Fin N) := complexCausalLaplace_weighted_convolution
    (fun t => q t m j) (fun t => y t i m) (hq.matrix_elem m j) (hy.matrix_elem i m)
    s (hiq m j) (hiy i m)
  have ht (i j : Fin N) : FMSA.causalComplexLaplace (fun t => y t i j) s=
      FMSA.causalComplexLaplace (fun t => f t i j) s+
        ∑ m, FMSA.causalComplexLaplace (fun t => y t i m) s*
          FMSA.causalComplexLaplace (fun t => q t m j) s := by
    unfold FMSA.causalComplexLaplace
    have he : (∫ r in Ioi (0 : ℝ), (y r i j : ℂ)*Complex.exp (-s*r))=
        ∫ r in Ioi (0 : ℝ), (f r i j : ℂ)*Complex.exp (-s*r)+
          ∑ m, (causalIntervalConv (fun t => q t m j) (fun t => y t i m) r : ℂ)*Complex.exp (-s*r) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [heq i j r hr.le]
      push_cast
      simp only [add_mul, Finset.sum_mul]
    rw [he, integral_add (FMSA.complex_laplace_integrable _ (hf.matrix_elem i j).continuousOn s (hif i j))
      (integrable_finsetSum _ (fun m _ => (hv i j m).1)),
      integral_finsetSum _ (fun m _ => (hv i j m).1)]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    exact (hv i j m).2
  rw [Matrix.mul_sub, Matrix.mul_one]
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, rdfMatrixLaplace, Matrix.of_apply]
  exact sub_eq_iff_eq_add.mpr (ht i j)

theorem nonlinearCausalG_actual_complex_laplace_renewal (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (s : ℂ) (hs : 0 < s.re) :
    rdfMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s*
      (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s)=
        rdfMatrixLaplace (nonlinearGSource z ρ σ Dt G) s := by
  apply complexMatrixLaplace_right_renewal _ _ _
    (nonlinearCausalKernel_continuous z ρ σ Dt G) (nonlinearGSource_continuous z ρ σ Dt G)
    (nonlinearCausalG_continuous z ρ σ Dt G) s
    (nonlinearCausalKernel_laplace_integrable z ρ σ Dt G hz hσ s.re hs)
    (nonlinearGSource_laplace_integrable z ρ σ Dt G hz s.re hs)
    (nonlinearCausalG_laplace_integrable z ρ σ Dt G hz hσ hv δ hδ hδz hb s.re hs)
  intro i j r hr
  simpa only [causalIntervalConv, mul_comm] using nonlinearCausalG_renewal z ρ σ Dt G i j r hr

def nonlinearComplexJ (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
      (amplitudeA z ρ σ Dt G j : ℂ)/s^2+(amplitudeQp z ρ σ Dt G i j : ℂ)/s+
        ∑ u, (z u : ℂ)*(C z ρ σ Dt G u i j : ℂ)/(s+(z u : ℂ)))

theorem nonlinearGSource_actual_complex_laplace (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (s : ℂ) (hs : 0 < s.re) (i j : Fin N) :
    rdfMatrixLaplace (nonlinearGSource z ρ σ Dt G) s i j=
      nonlinearComplexJ z ρ σ Dt G s i j/(2*Real.pi) := by
  let A := amplitudeA z ρ σ Dt G j
  let qp := amplitudeQp z ρ σ Dt G i j
  let T := fun u => C z ρ σ Dt G u i j
  have he : (fun r : ℝ => (nonlinearGSource z ρ σ Dt G r i j : ℂ)*Complex.exp (-s*r))=
      fun r : ℝ => ((A : ℂ)*((r : ℂ)*Complex.exp (-s*r))+(qp : ℂ)*Complex.exp (-s*r)+
        ∑ u, ((z u : ℂ)*(T u : ℂ))*Complex.exp (-(s+(z u : ℂ))*r))/(2*Real.pi) := by
    funext r
    simp only [nonlinearGSource, Matrix.of_apply]
    push_cast
    rw [div_mul_eq_mul_div, add_mul, add_mul, Finset.sum_mul]
    congr 1
    congr 1
    · dsimp only [A, qp]; ring
    · apply Finset.sum_congr rfl
      intro u _
      rw [show -(s+(z u : ℂ))*r=(-(z u*r : ℝ) : ℂ)+ -s*r by push_cast; ring,
        Complex.exp_add]
      push_cast
      simp only [T, neg_mul, mul_assoc]
  have ha : IntegrableOn (fun r : ℝ => (A : ℂ)*((r : ℂ)*Complex.exp (-s*r))) (Ioi 0) :=
    (FMSA.complex_first_integrable hs).const_mul _
  have hqp : IntegrableOn (fun r : ℝ => (qp : ℂ)*Complex.exp (-s*r)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs) 0).const_mul _
  have hu (u : ι) : IntegrableOn (fun r : ℝ => ((z u : ℂ)*(T u : ℂ))*Complex.exp (-(s+(z u : ℂ))*r)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (a := -(s+(z u : ℂ))) (by
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]; linarith [hz u]) 0).const_mul _
  have hAQ : IntegrableOn (fun r : ℝ => (A : ℂ)*((r : ℂ)*Complex.exp (-s*r))+
      (qp : ℂ)*Complex.exp (-s*r)) (Ioi 0) := ha.add hqp
  have hsum : IntegrableOn (fun r : ℝ => ∑ u, ((z u : ℂ)*(T u : ℂ))*Complex.exp (-(s+(z u : ℂ))*r)) (Ioi 0) :=
    integrable_finsetSum _ (fun u _ => hu u)
  simp only [rdfMatrixLaplace, Matrix.of_apply, FMSA.causalComplexLaplace]
  rw [he, integral_div, integral_add hAQ hsum, integral_add ha hqp,
    integral_finsetSum _ (fun u _ => hu u)]
  simp only [integral_const_mul]
  rw [FMSA.complex_first_Ioi hs, integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_neg]
  have hp (u : ι) : (∫ r : ℝ in Ioi 0, Complex.exp (-(s+(z u : ℂ))*r))=1/(s+(z u : ℂ)) := by
    simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg] using
      integral_exp_mul_complex_Ioi (a := -(s+(z u : ℂ))) (by
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]; linarith [hz u]) 0
  simp_rw [hp]
  simp only [nonlinearComplexJ, Matrix.of_apply, A, qp, T, mul_div_assoc, mul_one,
    neg_div, neg_neg]
  congr 1
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro u _
    ring

def nonlinearComplexBackground (σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => 1/s^2+(edgeHi σ i j : ℂ)/s)

theorem nonlinearCausalG_complex_background (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (s : ℂ) (hs : 0 < s.re) :
    rdfMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s=
      rdfMatrixLaplace (nonlinearRDFExcess z ρ σ Dt G) s+nonlinearComplexBackground σ s := by
  ext i j
  have hi := FMSA.complex_laplace_integrable_of_L1 _
    ((nonlinearRDFExcess_continuous z ρ σ Dt G).matrix_elem i j).continuousOn
    (nonlinearRDFExcess_integrable_of_weighted_budget z ρ σ Dt G hz hσ hv δ hδ hδz hb i j) hs.le
  have hid := FMSA.complex_first_integrable hs
  have hic : IntegrableOn (fun t : ℝ => (edgeHi σ i j : ℂ)*Complex.exp (-s*t)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs) 0).const_mul _
  have hEI : IntegrableOn (fun t : ℝ =>
      (nonlinearRDFExcess z ρ σ Dt G t i j : ℂ)*Complex.exp (-s*t)+
        (t : ℂ)*Complex.exp (-s*t)) (Ioi 0) := hi.add hid
  have he : (fun t : ℝ => (nonlinearCausalG z ρ σ Dt G t i j : ℂ)*Complex.exp (-s*t))=
      fun t : ℝ => ((nonlinearRDFExcess z ρ σ Dt G t i j : ℂ)*Complex.exp (-s*t)+
        (t : ℂ)*Complex.exp (-s*t))+(edgeHi σ i j : ℂ)*Complex.exp (-s*t) := by
    funext t
    simp only [nonlinearCausalG, Matrix.of_apply]
    push_cast
    ring
  simp only [rdfMatrixLaplace, Matrix.of_apply, Matrix.add_apply, nonlinearComplexBackground,
    FMSA.causalComplexLaplace]
  rw [he, integral_add hEI hic, integral_add hi hid,
    FMSA.complex_first_Ioi hs, integral_const_mul,
    integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, mul_one]
  ring

end FMSA.ExactMSA.MultiTailMixture
