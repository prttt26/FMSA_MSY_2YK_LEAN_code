import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFCausal
import LeanCode.Analysis.CausalLaplaceComplex

/-! Actual half-line transforms of the constructed two-sided RDF renewal.
L1 of the actual constructed renewal functions is explicit; Fourier
identification and convolution Fubini are proved rather than assumed. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def causalIntervalConv (q y : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..r, q (r-t)*y t

theorem causalIntervalConv_weighted_integrable (q y : ℝ → ℝ)
    (hq : Continuous q) (hy : Continuous y)
    (hiq : IntegrableOn q (Ioi 0)) (hiy : IntegrableOn y (Ioi 0))
    (s : ℂ) (hs : 0 ≤ s.re) :
    IntegrableOn (fun r => (causalIntervalConv q y r : ℂ)*Complex.exp (-s*r)) (Ioi 0) := by
  let qw := fun u => (q u : ℂ)*Complex.exp (-s*u)
  let yw := fun u => (y u : ℂ)*Complex.exp (-s*u)
  have hqint : IntegrableOn qw (Ioi 0) := FMSA.complex_laplace_integrable_of_L1 q hq.continuousOn hiq hs
  have hyint : IntegrableOn yw (Ioi 0) := FMSA.complex_laplace_integrable_of_L1 y hy.continuousOn hiy hs
  apply (integrable_posConvolution hyint hqint (ContinuousLinearMap.mul ℝ ℂ)).integrableOn.congr_fun
    _ measurableSet_Ioi
  intro r hr
  simp only [posConvolution, indicator_of_mem hr, ContinuousLinearMap.mul_apply']
  unfold causalIntervalConv
  rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [qw, yw]
  push_cast
  have he : Complex.exp (-s*(t : ℂ))*Complex.exp (-s*((r-t : ℝ) : ℂ)) = Complex.exp (-s*r) := by
    rw [← Complex.exp_add]
    push_cast
    congr 1
    ring
  push_cast at he
  linear_combination (q (r-t) : ℂ)*(y t : ℂ)*he

theorem causalIntervalConv_laplace (q y : ℝ → ℝ)
    (hq : Continuous q) (hy : Continuous y)
    (hiq : IntegrableOn q (Ioi 0)) (hiy : IntegrableOn y (Ioi 0))
    (s : ℂ) (hs : 0 ≤ s.re) :
    FMSA.causalComplexLaplace (causalIntervalConv q y) s =
      FMSA.causalComplexLaplace q s*FMSA.causalComplexLaplace y s := by
  let qw := fun u => (q u : ℂ)*Complex.exp (-s*u)
  let yw := fun u => (y u : ℂ)*Complex.exp (-s*u)
  have hqint : IntegrableOn qw (Ioi 0) := FMSA.complex_laplace_integrable_of_L1 q hq.continuousOn hiq hs
  have hyint : IntegrableOn yw (Ioi 0) := FMSA.complex_laplace_integrable_of_L1 y hy.continuousOn hiy hs
  have he : ∀ r, 0 < r →
      (causalIntervalConv q y r : ℂ)*Complex.exp (-s*r) =
        ∫ t in (0 : ℝ)..r, yw t*qw (r-t) := by
    intro r _
    unfold causalIntervalConv
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [qw, yw]
    push_cast
    have he : Complex.exp (-s*(t : ℂ))*Complex.exp (-s*((r-t : ℝ) : ℂ)) = Complex.exp (-s*r) := by
      rw [← Complex.exp_add]
      push_cast
      congr 1
      ring
    push_cast at he
    linear_combination -(q (r-t) : ℂ)*(y t : ℂ)*he
  unfold FMSA.causalComplexLaplace
  simp_rw [setIntegral_congr_fun measurableSet_Ioi (fun r hr => he r hr)]
  have hi := integral_posConvolution hyint hqint (ContinuousLinearMap.mul ℝ ℂ)
  simp only [ContinuousLinearMap.mul_apply'] at hi
  rw [hi]
  ring

theorem rdfRecenteredHSQ_integrableOn (ρ σ : Fin N → ℝ) (i j : Fin N) :
    IntegrableOn (rdfRecenteredHSQ ρ σ i j) (Ioi 0) := by
  have hi := ((rdfRecenteredHSQ_continuous ρ σ i j).integrableOn_Icc (μ := volume)
    (a := 0) (b := max (σ i) 0)).integrable_indicator measurableSet_Icc
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  by_cases hb : t ≤ max (σ i) 0
  · exact indicator_of_mem (show t ∈ Icc 0 (max (σ i) 0) from ⟨ht.le, hb⟩) _
  · have hm : σ i ≤ t := (le_max_left (σ i) 0).trans (not_le.mp hb).le
    simp [indicator_of_notMem (show t ∉ Icc 0 (max (σ i) 0) from fun h => hb h.2),
      rdfRecenteredHSQ, min_eq_right hm]

theorem rdfCausalKernel_entry_integrableOn (ρ σ : Fin N → ℝ) (i j : Fin N) :
    IntegrableOn (fun t => rdfCausalKernel ρ σ t i j) (Ioi 0) :=
  (rdfRecenteredHSQ_integrableOn ρ σ i j).const_mul (ρ i)

theorem rdfCausalSource_entry_integrableOn (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) (i j : Fin N) :
    IntegrableOn (fun t => rdfCausalSource z ρ σ K t i j) (Ioi 0) := by
  exact integrable_finsetSum Finset.univ (fun u _ =>
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (hz u)) 0).const_mul (dpBareAmplitude z ρ σ K u i j))

def rdfMatrixLaplace (f : ℝ → Matrix (Fin N) (Fin N) ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => FMSA.causalComplexLaplace (fun r => f r i j) s)

def rdfRecenteredFactor (ρ σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  1-rdfMatrixLaplace (rdfCausalKernel ρ σ) s

/-- Actual finite-species renewal transform, entrywise without a matrix-norm
integral convention. All convolution Fubini conditions follow from L1. -/
theorem matrixCausalRenewal_laplace (q f y : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hq : Continuous q) (hf : Continuous f) (hy : Continuous y)
    (hiq : ∀ i j, IntegrableOn (fun r => q r i j) (Ioi 0))
    (hif : ∀ i j, IntegrableOn (fun r => f r i j) (Ioi 0))
    (hiy : ∀ i j, IntegrableOn (fun r => y r i j) (Ioi 0))
    (heq : ∀ i j r, 0 ≤ r → y r i j = f r i j+
      ∑ m, causalIntervalConv (fun t => q t i m) (fun t => y t m j) r)
    (s : ℂ) (hs : 0 ≤ s.re) :
    (1-rdfMatrixLaplace q s)*rdfMatrixLaplace y s = rdfMatrixLaplace f s := by
  have ht (i j : Fin N) : FMSA.causalComplexLaplace (fun r => y r i j) s =
      FMSA.causalComplexLaplace (fun r => f r i j) s+
        ∑ m, FMSA.causalComplexLaplace (fun r => q r i m) s*
          FMSA.causalComplexLaplace (fun r => y r m j) s := by
    unfold FMSA.causalComplexLaplace
    have he : (∫ r in Ioi (0 : ℝ), (y r i j : ℂ)*Complex.exp (-s*r)) =
        ∫ r in Ioi (0 : ℝ), (f r i j : ℂ)*Complex.exp (-s*r)+
          ∑ m, (causalIntervalConv (fun t => q t i m) (fun t => y t m j) r : ℂ)*Complex.exp (-s*r) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [heq i j r hr.le]
      push_cast
      simp only [add_mul, Finset.sum_mul]
    rw [he, integral_add
      (FMSA.complex_laplace_integrable_of_L1 _ (hf.matrix_elem i j).continuousOn (hif i j) hs)
      (integrable_finsetSum _ (fun m _ => causalIntervalConv_weighted_integrable _ _
        (hq.matrix_elem i m) (hy.matrix_elem m j) (hiq i m) (hiy m j) s hs)),
      integral_finsetSum _ (fun m _ => causalIntervalConv_weighted_integrable _ _
        (hq.matrix_elem i m) (hy.matrix_elem m j) (hiq i m) (hiy m j) s hs)]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    exact causalIntervalConv_laplace _ _ (hq.matrix_elem i m) (hy.matrix_elem m j)
      (hiq i m) (hiy m j) s hs
  rw [sub_mul, Matrix.one_mul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, rdfMatrixLaplace, Matrix.of_apply]
  exact sub_eq_iff_eq_add.mpr (ht i j)

theorem rdfMatrixLaplace_transpose (f : ℝ → Matrix (Fin N) (Fin N) ℝ) (s : ℂ) :
    rdfMatrixLaplace (fun t => (f t).transpose) s = (rdfMatrixLaplace f s).transpose := rfl

theorem rdfCausalLeft_laplace (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hY : ∀ i j, IntegrableOn (fun r => rdfCausalLeft z ρ σ K r i j) (Ioi 0))
    (s : ℂ) (hs : 0 ≤ s.re) :
    (rdfRecenteredFactor ρ σ s).transpose*rdfMatrixLaplace (rdfCausalLeft z ρ σ K) s =
      rdfMatrixLaplace (rdfCausalSource z ρ σ K) s := by
  have he := matrixCausalRenewal_laplace
    (fun t => (rdfCausalKernel ρ σ t).transpose) (rdfCausalSource z ρ σ K) (rdfCausalLeft z ρ σ K)
    (rdfCausalKernelTranspose_continuous ρ σ) (rdfCausalSource_continuous z ρ σ K)
    (rdfCausalLeft_continuous z ρ σ K)
    (fun i j => rdfCausalKernel_entry_integrableOn ρ σ j i)
    (rdfCausalSource_entry_integrableOn z hz ρ σ K) hY
    (rdfCausalLeft_renewal z ρ σ K) s hs
  simpa only [rdfRecenteredFactor, Matrix.transpose_sub, Matrix.transpose_one, rdfMatrixLaplace_transpose] using he

theorem rdfCausalTwoSided_laplace (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hY : ∀ i j, IntegrableOn (fun r => rdfCausalLeft z ρ σ K r i j) (Ioi 0))
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (s : ℂ) (hs : 0 ≤ s.re) :
    rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) s*rdfRecenteredFactor ρ σ s =
      rdfMatrixLaplace (rdfCausalLeft z ρ σ K) s := by
  have hc : Continuous (fun r => (rdfCausalTwoSided z ρ σ K r).transpose) :=
    continuous_matrix (fun i j => (rdfCausalTwoSided_continuous z ρ σ K).matrix_elem j i)
  have he := matrixCausalRenewal_laplace
    (fun t => (rdfCausalKernel ρ σ t).transpose)
    (fun t => (rdfCausalLeft z ρ σ K t).transpose)
    (fun t => (rdfCausalTwoSided z ρ σ K t).transpose)
    (rdfCausalKernelTranspose_continuous ρ σ) (rdfCausalLeftTranspose_continuous z ρ σ K) hc
    (fun i j => rdfCausalKernel_entry_integrableOn ρ σ j i)
    (fun i j => hY j i) (fun i j => hU j i)
    (fun i j r hr => by
      have ht := rdfCausalTwoSided_renewal z ρ σ K j i r hr
      simpa only [Matrix.transpose_apply, causalIntervalConv, mul_comm] using ht) s hs
  have ht := congrArg Matrix.transpose he
  simpa only [rdfRecenteredFactor, Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_one, rdfMatrixLaplace_transpose, Matrix.transpose_transpose] using ht

/-- Actual two-sided causal RDF transform. The only analytic premises are
entry L1 of the constructed solutions and invertibility of the HS factor. -/
theorem rdfCausalTwoSided_laplace_sandwich (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hY : ∀ i j, IntegrableOn (fun r => rdfCausalLeft z ρ σ K r i j) (Ioi 0))
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (s : ℂ) (hs : 0 ≤ s.re) (hdet : IsUnit (rdfRecenteredFactor ρ σ s).det) :
    rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) s =
      ((rdfRecenteredFactor ρ σ s).transpose)⁻¹*
        rdfMatrixLaplace (rdfCausalSource z ρ σ K) s*(rdfRecenteredFactor ρ σ s)⁻¹ := by
  have hL := rdfCausalLeft_laplace z hz ρ σ K hY s hs
  have hR := rdfCausalTwoSided_laplace z ρ σ K hY hU s hs
  have hiL := Matrix.nonsing_inv_mul (rdfRecenteredFactor ρ σ s).transpose
    (by simpa only [Matrix.det_transpose] using hdet)
  have hiR := Matrix.mul_nonsing_inv (rdfRecenteredFactor ρ σ s) hdet
  calc
    _ = rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) s*
        (rdfRecenteredFactor ρ σ s*(rdfRecenteredFactor ρ σ s)⁻¹) := by rw [hiR, Matrix.mul_one]
    _ = rdfMatrixLaplace (rdfCausalLeft z ρ σ K) s*(rdfRecenteredFactor ρ σ s)⁻¹ := by
      rw [← Matrix.mul_assoc, hR]
    _ = _ := by
      rw [← hL, ← Matrix.mul_assoc, hiL, Matrix.one_mul]

theorem causalIntervalConv_integrableOn (q y : ℝ → ℝ)
    (hq : Continuous q) (hy : Continuous y)
    (hiq : IntegrableOn q (Ioi 0)) (hiy : IntegrableOn y (Ioi 0)) :
    IntegrableOn (causalIntervalConv q y) (Ioi 0) := by
  have hi := causalIntervalConv_weighted_integrable q y hq hy hiq hiy 0 (by simp)
  have hir : IntegrableOn (fun r =>
      ((causalIntervalConv q y r : ℂ)*Complex.exp (-0*r)).re) (Ioi 0) := hi.re
  simpa using hir

/-- L1 of the final constructed two-sided solution already supplies L1 of
the intermediate solution; it is not a second independent decay premise. -/
theorem rdfCausalLeft_integrableOn_of_twoSided (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (i j : Fin N) : IntegrableOn (fun r => rdfCausalLeft z ρ σ K r i j) (Ioi 0) := by
  have hi : IntegrableOn (fun r => ∑ m, causalIntervalConv
      (fun t => rdfCausalKernel ρ σ t m j) (fun t => rdfCausalTwoSided z ρ σ K t i m) r) (Ioi 0) :=
    integrable_finsetSum _ (fun m _ => causalIntervalConv_integrableOn _ _
      ((rdfCausalKernel_continuous ρ σ).matrix_elem m j)
      ((rdfCausalTwoSided_continuous z ρ σ K).matrix_elem i m)
      (rdfCausalKernel_entry_integrableOn ρ σ m j) (hU i m))
  apply ((hU i j).sub hi).congr_fun _ measurableSet_Ioi
  intro r hr
  have he := rdfCausalTwoSided_renewal z ρ σ K i j r hr.le
  simp only [Pi.sub_apply]
  simp only [causalIntervalConv, mul_comm] at he ⊢
  linarith

theorem rdfCausalTwoSided_laplace_sandwich_of_L1 (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (s : ℂ) (hs : 0 ≤ s.re) (hdet : IsUnit (rdfRecenteredFactor ρ σ s).det) :
    rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) s =
      ((rdfRecenteredFactor ρ σ s).transpose)⁻¹*
        rdfMatrixLaplace (rdfCausalSource z ρ σ K) s*(rdfRecenteredFactor ρ σ s)⁻¹ :=
  rdfCausalTwoSided_laplace_sandwich z hz ρ σ K
    (rdfCausalLeft_integrableOn_of_twoSided z ρ σ K hU) hU s hs hdet

end FMSA.ExactMSA.MultiTailMixture
