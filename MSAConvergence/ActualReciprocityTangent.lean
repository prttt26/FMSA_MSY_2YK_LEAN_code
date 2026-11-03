import MSAConvergence.SymplecticTangent
import MSAConvergence.ActualHBoundaryResponse

/-! Genuine source-reciprocity tangents at arbitrary actual BH roots,
from first-order symplectic completion of the actual U/V certificates. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Convergence.ActualReciprocityTangent
open FMSA.Paper FMSA.Paper.JacobianExterior FMSA.ExactMSA.MultiTailMixture MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.ActualLaplaceJets FMSA.Convergence.ActualSourceBoundary
open FMSA.Convergence.ActualHBoundaryResponse FMSA.Convergence.ActualRDFTangent
open FMSA.Convergence.SymplecticTangent FMSA.Convergence.ComplexWronskianJets

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Actual source-reciprocity residual entries are smooth off root in all
amplitudes, with no frequency or canonical-state premise. -/
theorem reciprocity_residual_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (s : ℂ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearComplexReciprocityResidual z rho sigma a.1 a.2 s i j) := by
  simp only [nonlinearComplexReciprocityResidual, Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  fun_prop

/-- Actual U/V values vanish at a symmetric-strength BH root by the
already proved automatic finite certificate, without any decay budget. -/
theorem actual_root_wronskian_values_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re = 0) :
    actualWronskianU z rho sigma p s = 0 ∧ actualWronskianV z rho sigma p s = 0 := by
  classical
  have hscaled : ∀ u i j, (t • K) u i j = (t • K) u j i := by
    intro u i j
    simp only [Pi.smul_apply, smul_eq_mul, hK u i j]
  have hw := nonlinearRoot_automatic_finite_wronskian z rho sigma (t • K) p.1 p.2 hz hv hroot hscaled
  exact nonlinear_finite_wronskian_residuals_zero z rho sigma p.1 p.2 hz hw s hs hsre

/-- The separate actual source-reciprocity residual has zero genuine
Frechet variation along every actual BH-Jacobian kernel vector. The
first-order symplectic proof uses actual U/V values and derivatives, not
a presumed root curve or differentiation of a root-only implication. -/
theorem actual_kernel_reciprocity_value_and_derivative_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : FMSA.Paper.JacobianExterior.amplitudeJacobian z rho sigma K t p v = 0)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re = 0) :
    nonlinearComplexReciprocityResidual z rho sigma p.1 p.2 s = 0 ∧
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearComplexReciprocityResidual z rho sigma a.1 a.2 s) p v = 0 := by
  classical
  let P : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (rho i : ℂ))
  let Jf := fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 s
  let Lf := fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexL z rho sigma a.1 a.2 s
  let Jm := fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 (-s)
  let Lm := fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexL z rho sigma a.1 a.2 (-s)
  let Af := fun a => 1-s⁻¹ • (P*Lf a)
  let Df := fun a => 1+s⁻¹ • (Lm a*P)
  let Bf := fun a => s⁻¹ • Jf a
  let Mf := fun a => -(s⁻¹ • (P*Jm a*P))
  let U := fun a => actualWronskianU z rho sigma a s
  let V := fun a => actualWronskianV z rho sigma a s
  let Vm := fun a => actualWronskianV z rho sigma a (-s)
  let Rf := fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexReciprocityResidual z rho sigma a.1 a.2 s
  have hP := entry_diff_const P p
  have hI := entry_diff_const (1 : Matrix (Fin N) (Fin N) ℂ) p
  have hJ : EntryDiff Jf p := fun i j => (complexJ_entry_contDiff z rho sigma s i j).differentiable (by simp) p
  have hL : EntryDiff Lf p := fun i j => (complexL_entry_contDiff z rho sigma s i j).differentiable (by simp) p
  have hJm : EntryDiff Jm p := fun i j => (complexJ_entry_contDiff z rho sigma (-s) i j).differentiable (by simp) p
  have hLm : EntryDiff Lm p := fun i j => (complexL_entry_contDiff z rho sigma (-s) i j).differentiable (by simp) p
  have hA : EntryDiff Af p := entry_diff_sub _ _ p hI (entry_diff_smul _ _ p (entry_diff_mul _ _ p hP hL))
  have hD : EntryDiff Df p := entry_diff_add _ _ p hI (entry_diff_smul _ _ p (entry_diff_mul _ _ p hLm hP))
  have hB : EntryDiff Bf p := entry_diff_smul _ _ p hJ
  have hM : EntryDiff Mf p := entry_diff_neg _ p (entry_diff_smul _ _ p
    (entry_diff_mul _ _ p (entry_diff_mul _ _ p hP hJm) hP))
  have hU : EntryDiff U p := fun i j => (actualWronskianU_entry_contDiff z rho sigma s i j).differentiable (by simp) p
  have hV : EntryDiff V p := fun i j => (actualWronskianV_entry_contDiff z rho sigma s i j).differentiable (by simp) p
  have hVm : EntryDiff Vm p := fun i j => (actualWronskianV_entry_contDiff z rho sigma (-s) i j).differentiable (by simp) p
  have hR : EntryDiff Rf p := fun i j => (reciprocity_residual_entry_contDiff z rho sigma s i j).differentiable (by simp) p
  obtain ⟨hu0, hv0⟩ := actual_root_wronskian_values_zero z hz rho sigma K hK hv t p hroot s hs hsre
  have hvm0 := (actual_root_wronskian_values_zero z hz rho sigma K hK hv t p hroot (-s)
    (neg_ne_zero.mpr hs) (by simp [hsre])).2
  have hdU : matrixDerivative U p v = 0 := by
    ext i j
    exact (actual_kernel_complex_wronskian_fderiv_zero z rho sigma K hK hz hv t p v hroot hjac i j s hs hsre).1
  have hdV : matrixDerivative V p v = 0 := by
    ext i j
    exact (actual_kernel_complex_wronskian_fderiv_zero z rho sigma K hK hz hv t p v hroot hjac i j s hs hsre).2
  have hdVm : matrixDerivative Vm p v = 0 := by
    ext i j
    exact (actual_kernel_complex_wronskian_fderiv_zero z rho sigma K hK hz hv t p v hroot hjac i j (-s)
      (neg_ne_zero.mpr hs) (by simp [hsre])).2
  have hPT : P.transpose = P := Matrix.diagonal_transpose _
  have e11 (a : TailMatrix T N × TailMatrix T N) : Af a*(Mf a).transpose-Mf a*(Af a).transpose = s⁻¹ • (P*Vm a*P) := by
    simp only [Af, Mf, Vm, actualWronskianV, Jf, Jm, Lf, Lm, nonlinearWronskianV,
      neg_neg, Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_mul, hPT, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.add_mul, Matrix.mul_add, neg_inv]
    simp only [P, Matrix.mul_assoc]
    module
  have e12 (a : TailMatrix T N × TailMatrix T N) : Af a*(Df a).transpose-Mf a*(Bf a).transpose = 1+s⁻¹ • (P*U a) := by
    simp only [Af, Df, Mf, Bf, U, actualWronskianU, Jf, Jm, Lf, Lm, nonlinearWronskianU,
      Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, hPT,
      Matrix.sub_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.mul_sub]
    simp only [P, Matrix.mul_assoc]
    module
  have e22 (a : TailMatrix T N × TailMatrix T N) : Bf a*(Df a).transpose-Df a*(Bf a).transpose = s⁻¹ • V a := by
    simp only [Df, Bf, V, actualWronskianV, Jf, Lf, Lm, nonlinearWronskianV,
      Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, hPT,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    simp only [P, Matrix.mul_assoc]
    module
  have he11 : (fun a => Af a*(Mf a).transpose-Mf a*(Af a).transpose) = fun a => s⁻¹ • (P*Vm a*P) := funext e11
  have he12 : (fun a => Af a*(Df a).transpose-Mf a*(Bf a).transpose) = fun a => 1+s⁻¹ • (P*U a) := funext e12
  have he22 : (fun a => Bf a*(Df a).transpose-Df a*(Bf a).transpose) = fun a => s⁻¹ • V a := funext e22
  have hPVm := entry_diff_mul (fun _ => P) Vm p hP hVm
  have hd11 : matrixDerivative (fun a => Af a*(Mf a).transpose-Mf a*(Af a).transpose) p v = 0 := by
    rw [he11, matrix_derivative_smul _ _ p v (entry_diff_mul _ _ p hPVm hP),
      matrix_derivative_mul_const _ P p v hPVm, matrix_derivative_const_mul P Vm p v hVm, hdVm]
    simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero]
  have hPU := entry_diff_mul (fun _ => P) U p hP hU
  have hd12 : matrixDerivative (fun a => Af a*(Df a).transpose-Mf a*(Bf a).transpose) p v = 0 := by
    rw [he12, matrix_derivative_add _ _ p v hI (entry_diff_smul _ _ p hPU), matrix_derivative_const,
      matrix_derivative_smul _ _ p v hPU, matrix_derivative_const_mul P U p v hU, hdU]
    simp only [Matrix.mul_zero, smul_zero, add_zero]
  have hd22 : matrixDerivative (fun a => Bf a*(Df a).transpose-Df a*(Bf a).transpose) p v = 0 := by
    rw [he22, matrix_derivative_smul _ _ p v hV, hdV, smul_zero]
  have hb11 : Af p*(Mf p).transpose-Mf p*(Af p).transpose = 0 := by
    rw [e11, show Vm p = 0 from hvm0, Matrix.mul_zero, Matrix.zero_mul, smul_zero]
  have hb12 : Af p*(Df p).transpose-Mf p*(Bf p).transpose = 1 := by
    rw [e12, show U p = 0 from hu0, Matrix.mul_zero, smul_zero, add_zero]
  have hb22 : Bf p*(Df p).transpose-Df p*(Bf p).transpose = 0 := by
    rw [e22, show V p = 0 from hv0, smul_zero]
  have hout := blocks_family_reciprocity_derivative Af Bf Mf Df p v hA hB hM hD hb11 hb12 hb22 hd11 hd12 hd22
  have er (a : TailMatrix T N × TailMatrix T N) : (Af a).transpose*Bf a-(Bf a).transpose*Af a = s⁻¹ • Rf a := by
    simp only [Af, Bf, Rf, Jf, Lf, nonlinearComplexReciprocityResidual,
      Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, Matrix.transpose_mul, hPT,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    simp only [P, Matrix.mul_assoc]
    module
  have her : (fun a => (Af a).transpose*Bf a-(Bf a).transpose*Af a) = fun a => s⁻¹ • Rf a := funext er
  have hb := blocks_transpose_symplectic (Af p) (Bf p) (Mf p) (Df p) hb11 hb12 hb22
  have he := congrArg (fun X : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ => X.toBlocks₁₁) hb
  simp only [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
    Matrix.one_mul, add_zero, zero_add, Matrix.toBlocks_fromBlocks₁₁] at he
  have hbR : (Af p).transpose*Bf p-(Bf p).transpose*Af p = 0 := by
    linear_combination (norm := noncomm_ring) -he
  rw [er] at hbR
  rw [her, matrix_derivative_smul _ Rf p v hR] at hout
  exact ⟨(smul_eq_zero.mp hbR).resolve_left (inv_ne_zero hs),
    (smul_eq_zero.mp hout).resolve_left (inv_ne_zero hs)⟩

/-- Matrix derivative projection of the joint actual value/tangent proof. -/
theorem actual_kernel_reciprocity_matrix_derivative_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : FMSA.Paper.JacobianExterior.amplitudeJacobian z rho sigma K t p v = 0)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re = 0) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearComplexReciprocityResidual z rho sigma a.1 a.2 s) p v = 0 :=
  (actual_kernel_reciprocity_value_and_derivative_zero z hz rho sigma K hK hv t p v hroot hjac s hs hsre).2

/-- Entrywise actual reciprocity derivative consequence of the completed
matrix proof, usable without a root curve or nonzero species densities. -/
theorem actual_kernel_reciprocity_fderiv_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : FMSA.Paper.JacobianExterior.amplitudeJacobian z rho sigma K t p v = 0)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re = 0) (i j : Fin N) :
    fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearComplexReciprocityResidual z rho sigma a.1 a.2 s i j) p v = 0 :=
  congrFun (congrFun (actual_kernel_reciprocity_matrix_derivative_zero z hz rho sigma K hK hv t p v hroot hjac s hs hsre) i) j

/-- Actual source reciprocity value at a symmetric-strength BH root,
from the density-free frozen symplectic completion. -/
theorem actual_root_reciprocity_residual_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re = 0) :
    nonlinearComplexReciprocityResidual z rho sigma p.1 p.2 s = 0 := by
  exact (actual_kernel_reciprocity_value_and_derivative_zero z hz rho sigma K hK hv t p 0 hroot
    (by simp only [map_zero]) s hs hsre).1

/-- Finite completed source symbol. This is NOT an assertion that the
uncancelled affine G has an actual Laplace integral on the imaginary axis. -/
def completedJSymbol (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  nonlinearComplexJ z rho sigma p.1 p.2 s*
    (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹

/-- The finite completed symbol is genuinely locally amplitude-smooth
at a fixed unit frequency, with the actual kernel integral dictionary. -/
theorem completed_symbol_entry_contDiffAt
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (hre : 0 ≤ s.re)
    (hu : IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (i j : Fin N) :
    ContDiffAt ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s i j) p := by
  have hA (i j : Fin N) : ContDiffAt ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s) i j) p :=
    contDiffAt_const.sub (kernel_laplace_closed_right_contDiff z hz rho sigma s hre i j).contDiffAt
  have hi := matrix_inv_entry_contDiffAt
    (fun a : TailMatrix T N × TailMatrix T N => 1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s) p hA hu
  simp only [completedJSymbol, Matrix.mul_apply]
  exact ContDiffAt.sum (fun k _ => (complexJ_entry_contDiff z rho sigma s i k).contDiffAt.mul (hi k j))

/-- The finite completed symbol's genuine derivative is its ordered
right-renewal response. Local unit control is derived at this frequency,
not assumed for a nearby canonical state or a curve of BH roots. -/
theorem completed_symbol_matrix_derivative
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hre : 0 ≤ s.re)
    (hu : IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s) p v =
      (jVariation z rho sigma p v s+completedJSymbol z rho sigma p s*
        rdfMatrixLaplace (fun r => Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)) s)*
          (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹ := by
  let q := fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s
  let Jf := fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 s
  let Y := fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s
  have hA (i j : Fin N) : ContDiffAt ℝ ∞ (fun a => (1-q a) i j) p :=
    contDiffAt_const.sub (kernel_laplace_closed_right_contDiff z hz rho sigma s hre i j).contDiffAt
  have hdet := (matrix_det_contDiffAt (fun a => 1-q a) p hA).continuousAt
  have hnz : (1-q p).det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hnear : ∀ᶠ a in 𝓝 p, (1-q a).det ≠ 0 := hdet.eventually_ne hnz
  have he : ∀ᶠ a in 𝓝 p, Y a*(1-q a) = Jf a := by
    filter_upwards [hnear] with a ha
    change (Jf a*(1-q a)⁻¹)*(1-q a) = Jf a
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ha), Matrix.mul_one]
  have hd := matrix_renewal_family_fderiv q Jf Y p v
    (fun i j => (kernel_laplace_closed_right_contDiff z hz rho sigma s hre i j).differentiable (by simp) p)
    (fun i j => (complexJ_entry_contDiff z rho sigma s i j).differentiable (by simp) p)
    (fun i j => (completed_symbol_entry_contDiffAt z hz rho sigma p s hre hu i j).differentiableAt (by simp)) he
  change matrixDerivative Y p v*(1-q p) = matrixDerivative Jf p v+Y p*matrixDerivative q p v at hd
  have hq : matrixDerivative q p v =
      rdfMatrixLaplace (fun r => Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)) s := by
    ext i j
    exact (kernel_variation_laplace_fderiv_closed_right z hz rho sigma p v s hre i j).symm
  have hj : matrixDerivative Jf p v = jVariation z rho sigma p v s := rfl
  have hc := Matrix.mul_nonsing_inv_cancel_right (1-q p) (matrixDerivative Y p v)
    ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  rw [hd, hq, hj] at hc
  exact hc.symm


/-- At a fixed unit imaginary frequency, genuine source reciprocity and
its kernel-direction derivative transfer to the completed symbol and its
actual finite-family derivative. No root curve is used. -/
theorem actual_kernel_completed_symbol_reciprocity
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : FMSA.Paper.JacobianExterior.amplitudeJacobian z rho sigma K t p v = 0)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re = 0)
    (hu : IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    (completedJSymbol z rho sigma p s).transpose = completedJSymbol z rho sigma p s ∧
    (matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s) p v).transpose =
      matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s) p v := by
  classical
  have hre : 0 ≤ s.re := hsre.ge
  let q := fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s
  let A := fun a : TailMatrix T N × TailMatrix T N => 1-q a
  let Jf := fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 s
  let Y := fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s
  have hq : EntryDiff q p := fun i j =>
    (kernel_laplace_closed_right_contDiff z hz rho sigma s hre i j).differentiable (by simp) p
  have hA : EntryDiff A p := entry_diff_sub (fun _ => 1) q p (entry_diff_const _ p) hq
  have hJ : EntryDiff Jf p := fun i j => (complexJ_entry_contDiff z rho sigma s i j).differentiable (by simp) p
  have hdA : matrixDerivative A p v = -matrixDerivative q p v := by
    rw [show A = fun a => 1-q a from rfl, matrix_derivative_sub _ _ p v (entry_diff_const _ p) hq,
      matrix_derivative_const, zero_sub]
  have hYA : Y p*A p = Jf p := by
    change (Jf p*(A p)⁻¹)*A p = Jf p
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.mul_one]
  have hdY := completed_symbol_matrix_derivative z hz rho sigma p v s hre hu
  have hdq : matrixDerivative q p v =
      rdfMatrixLaplace (fun r => Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)) s := by
    ext i j
    exact (kernel_variation_laplace_fderiv_closed_right z hz rho sigma p v s hre i j).symm
  have hdJ : matrixDerivative Jf p v = jVariation z rho sigma p v s := rfl
  have hdYA : matrixDerivative Y p v*A p+Y p*matrixDerivative A p v = matrixDerivative Jf p v := by
    change matrixDerivative Y p v = (jVariation z rho sigma p v s+Y p*
      rdfMatrixLaplace (fun r => Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)) s)*(A p)⁻¹ at hdY
    rw [hdY, ← hdq, ← hdJ, hdA, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.mul_one]
    noncomm_ring
  have eR : (fun a => (A a).transpose*Jf a-(Jf a).transpose*A a) =
      fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexReciprocityResidual z rho sigma a.1 a.2 s := by
    funext a
    exact (nonlinearComplexReciprocityResidual_actual_factor z rho sigma a.1 a.2 hz hsigma s hs hre).symm
  obtain ⟨hR, hdR⟩ := actual_kernel_reciprocity_value_and_derivative_zero z hz rho sigma K hK hv t p v hroot hjac s hs hsre
  have hbR : (A p).transpose*Jf p-(Jf p).transpose*A p = 0 := by
    rw [congrFun eR p]
    exact hR
  have hdfR : matrixDerivative (fun a => (A a).transpose*Jf a-(Jf a).transpose*A a) p v = 0 := by
    rw [eR]
    exact hdR
  rw [matrix_derivative_mul_sub_mul _ _ _ _ p v (entry_diff_transpose _ p hA) hJ
    (entry_diff_transpose _ p hJ) hA, matrix_derivative_transpose, matrix_derivative_transpose] at hdfR
  simp only [sub_add_eq_sub_sub] at hdfR
  exact source_renewal_reciprocity_tangent (A p) (Jf p) (Y p)
    (matrixDerivative A p v) (matrixDerivative Jf p v) (matrixDerivative Y p v) hu hYA hdYA hbR hdfR

/-- The honest actual h-tangent transform is the contact-phase sandwich
of the genuine finite completed-symbol derivative. This does not claim
amplitude differentiation under a whole-h boundary integral. -/
theorem actual_h_tangent_laplace_completed_derivative
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) :
    rdfMatrixLaplace (fun r => Matrix.of (fun i j => r*hVariation z rho sigma p v i j r)) s =
      (2*(π : ℂ))⁻¹ • (rdfPhase sigma s*
        matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s) p v*rdfPhase sigma s) := by
  rw [actual_h_tangent_finite_boundary_response z hz rho sigma hsigma hv p v hcanon s hs hre,
    completed_symbol_matrix_derivative z hz rho sigma p v s hre (hcanon s hre)]
  simp only [completedJSymbol, ← smul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

/-- Actual h boundary-tangent reciprocity at every nonzero imaginary
frequency along every genuine BH Jacobian-kernel direction. Densities
may vanish: no inverse density or neighbouring root family is assumed. -/
theorem actual_kernel_h_tangent_boundary_reciprocity
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : FMSA.Paper.JacobianExterior.amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re = 0) :
    (rdfMatrixLaplace (fun r => Matrix.of (fun i j => r*hVariation z rho sigma p v i j r)) s).transpose =
      rdfMatrixLaplace (fun r => Matrix.of (fun i j => r*hVariation z rho sigma p v i j r)) s := by
  have hdY := (actual_kernel_completed_symbol_reciprocity z hz rho sigma (fun i => (hsigma i).le)
    K hK hv t p v hroot hjac s hs hsre (hcanon s hsre.ge)).2
  rw [actual_h_tangent_laplace_completed_derivative z hz rho sigma hsigma hv p v hcanon s hs hsre.ge]
  simp only [Matrix.transpose_smul, Matrix.transpose_mul, show (rdfPhase sigma s).transpose = rdfPhase sigma s from Matrix.diagonal_transpose _,
    hdY, Matrix.mul_assoc]

end FMSA.Convergence.ActualReciprocityTangent

/-- info: 'FMSA.Convergence.ActualReciprocityTangent.reciprocity_residual_entry_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualReciprocityTangent.reciprocity_residual_entry_contDiff

/-- info: 'FMSA.Convergence.ActualReciprocityTangent.actual_root_wronskian_values_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualReciprocityTangent.actual_root_wronskian_values_zero

/-- info: 'FMSA.Convergence.ActualReciprocityTangent.actual_kernel_reciprocity_value_and_derivative_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualReciprocityTangent.actual_kernel_reciprocity_value_and_derivative_zero

/-- info: 'FMSA.Convergence.ActualReciprocityTangent.actual_kernel_reciprocity_matrix_derivative_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualReciprocityTangent.actual_kernel_reciprocity_matrix_derivative_zero

/-- info: 'FMSA.Convergence.ActualReciprocityTangent.actual_kernel_reciprocity_fderiv_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualReciprocityTangent.actual_kernel_reciprocity_fderiv_zero

/-- info: 'FMSA.Convergence.ActualReciprocityTangent.actual_root_reciprocity_residual_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualReciprocityTangent.actual_root_reciprocity_residual_zero

/-- info: 'FMSA.Convergence.ActualReciprocityTangent.completed_symbol_entry_contDiffAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualReciprocityTangent.completed_symbol_entry_contDiffAt

/-- info: 'FMSA.Convergence.ActualReciprocityTangent.completed_symbol_matrix_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualReciprocityTangent.completed_symbol_matrix_derivative

/-- info: 'FMSA.Convergence.ActualReciprocityTangent.actual_kernel_completed_symbol_reciprocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualReciprocityTangent.actual_kernel_completed_symbol_reciprocity

/-- info: 'FMSA.Convergence.ActualReciprocityTangent.actual_h_tangent_laplace_completed_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualReciprocityTangent.actual_h_tangent_laplace_completed_derivative

/-- info: 'FMSA.Convergence.ActualReciprocityTangent.actual_kernel_h_tangent_boundary_reciprocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualReciprocityTangent.actual_kernel_h_tangent_boundary_reciprocity
