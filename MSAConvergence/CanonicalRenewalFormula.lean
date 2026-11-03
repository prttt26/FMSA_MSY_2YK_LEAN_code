import MSAConvergence.CanonicalVolterraResolvent

/-! Genuine right variation of constants for the existing matrix Volterra
constructor, with an actual-excess specialization. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators

namespace FMSA.Convergence.CanonicalRenewalFormula
open FMSA.Paper FMSA.ExactMSA.MultiTailMixture MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.RDFExponentialOrder FMSA.Convergence.ActualLaplaceJets
open FMSA.Convergence.CanonicalResolventAnalysis FMSA.Convergence.CanonicalFourierLaplace
open FMSA.Convergence.CanonicalVolterraResolvent

variable {N : ℕ}

/-- The actual scalar causal interval convolution is continuous on real time. -/
theorem causal_convolution_continuous (q f : ℝ → ℝ) (hq : Continuous q) (hf : Continuous f) :
    Continuous (causalIntervalConv q f) := by
  unfold causalIntervalConv
  have hc : Continuous (Function.uncurry (fun r t : ℝ => q (r-t)*f t)) :=
    (hq.comp (continuous_fst.sub continuous_snd)).mul (hf.comp continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hc continuous_id

/-- Correctly ordered source plus source-times-resolvent convolution.
The species indices encode F*r; no matrix products are commuted. -/
def sourceResolventResponse (f r : ℝ → Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ := Matrix.of (fun i j => f t i j+
      ∑ m, causalIntervalConv (fun u => r u m j) (fun u => f u i m) t)

/-- Both actual fields are continuous, so the explicit source response is. -/
theorem source_resolvent_response_continuous
    (f r : ℝ → Matrix (Fin N) (Fin N) ℝ) (hf : Continuous f) (hr : Continuous r) :
    Continuous (sourceResolventResponse f r) := by
  apply continuous_matrix
  intro i j
  simp only [sourceResolventResponse, Matrix.of_apply]
  exact (hf.matrix_elem i j).add (continuous_finsetSum _ (fun m _ =>
    causal_convolution_continuous _ _ (hr.matrix_elem m j) (hf.matrix_elem i m)))

/-- The actual explicit source response has genuine complex Laplace L1 and
transform Fhat+Fhat*rhat whenever the two real damped inputs are L1. -/
theorem source_resolvent_response_laplace
    (f r : ℝ → Matrix (Fin N) (Fin N) ℝ) (hf : Continuous f) (hr : Continuous r) (s : ℂ)
    (hif : ∀ i j, IntegrableOn (fun t : ℝ => exp (-s.re*t)*f t i j) (Ioi 0))
    (hir : ∀ i j, IntegrableOn (fun t : ℝ => exp (-s.re*t)*r t i j) (Ioi 0)) :
    (∀ i j, IntegrableOn (fun t : ℝ => (sourceResolventResponse f r t i j : ℂ)*Complex.exp (-s*(t : ℂ))) (Ioi 0)) ∧
      rdfMatrixLaplace (sourceResolventResponse f r) s = rdfMatrixLaplace f s+
        rdfMatrixLaplace f s*rdfMatrixLaplace r s := by
  have hv (i j m : Fin N) := complexCausalLaplace_weighted_convolution
    (fun t => r t m j) (fun t => f t i m) (hr.matrix_elem m j) (hf.matrix_elem i m) s (hir m j) (hif i m)
  have hfi (i j : Fin N) := FMSA.complex_laplace_integrable _ (hf.matrix_elem i j).continuousOn s (hif i j)
  have he (i j : Fin N) : (fun t : ℝ => (sourceResolventResponse f r t i j : ℂ)*Complex.exp (-s*(t : ℂ))) =
      fun t : ℝ => (f t i j : ℂ)*Complex.exp (-s*(t : ℂ))+
        ∑ m, (causalIntervalConv (fun u => r u m j) (fun u => f u i m) t : ℂ)*Complex.exp (-s*(t : ℂ)) := by
    funext t
    simp only [sourceResolventResponse, Matrix.of_apply, Complex.ofReal_add, Complex.ofReal_sum, add_mul, Finset.sum_mul]
  constructor
  · intro i j
    rw [he]
    exact (hfi i j).add (integrable_finsetSum _ (fun m _ => (hv i j m).1))
  · have hentry (i j : Fin N) : FMSA.causalComplexLaplace (fun t => sourceResolventResponse f r t i j) s =
        FMSA.causalComplexLaplace (fun t => f t i j) s+
          ∑ m, FMSA.causalComplexLaplace (fun t => f t i m) s*FMSA.causalComplexLaplace (fun t => r t m j) s := by
      unfold FMSA.causalComplexLaplace
      rw [he, integral_add (hfi i j) (integrable_finsetSum _ (fun m _ => (hv i j m).1)),
        integral_finsetSum _ (fun m _ => (hv i j m).1)]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      exact (hv i j m).2
    ext i j
    simpa only [rdfMatrixLaplace, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply] using hentry i j

/-- Computed exponential order of the actual right Volterra solution for
an affine source and bounded kernel; no physical small budget is assumed. -/
theorem right_volterra_exponential_order
    (q f : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q) (hf : Continuous f)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hk : ∀ t, 0 ≤ t → FMSA.matrixAbsSum (q t) ≤ M)
    (hb : ∀ t, 0 ≤ t → FMSA.matrixAbsSum (f t) ≤ B*(1+t)) :
    ∀ t, 0 ≤ t → exp (-(M+1)*t)*FMSA.matrixAbsSum (rightVolterra q f hq hf t) ≤ B*(M+1) := by
  have hqt : Continuous (fun t => (q t).transpose) := continuous_matrix fun i j => hq.matrix_elem j i
  have hyt : Continuous (fun t => (rightVolterra q f hq hf t).transpose) :=
    continuous_matrix fun i j => (right_volterra_continuous q f hq hf).matrix_elem j i
  have h := matrix_renewal_exponential_order (fun t => (q t).transpose) (fun t => (f t).transpose)
    (fun t => (rightVolterra q f hq hf t).transpose) hqt hyt M B hM hB
    (fun t ht => by simpa only [FMSA.matrixAbsSum_transpose] using hk t ht)
    (fun t ht => by simpa only [FMSA.matrixAbsSum_transpose] using hb t ht)
    (fun i j t ht => by simpa only [Matrix.transpose_apply, mul_comm] using right_volterra_renewal q f hq hf j i t ht)
  simpa only [FMSA.matrixAbsSum_transpose] using h

/-- The actual right Volterra entries have real damped L1 beyond their
computed growth cutoff. -/
theorem right_volterra_damped_integrable
    (q f : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q) (hf : Continuous f)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hk : ∀ t, 0 ≤ t → FMSA.matrixAbsSum (q t) ≤ M)
    (hb : ∀ t, 0 ≤ t → FMSA.matrixAbsSum (f t) ≤ B*(1+t))
    (c : ℝ) (hc : M+1 < c) (i j : Fin N) :
    IntegrableOn (fun t : ℝ => exp (-c*t)*rightVolterra q f hq hf t i j) (Ioi 0) :=
  matrix_exp_order_damped_integrable _ (right_volterra_continuous q f hq hf) (M+1) (B*(M+1))
    (right_volterra_exponential_order q f hq hf M B hM hB hk hb) c hc i j

/-- Affine source growth gives genuine real damped L1, using an internally
proved unit growth bound, not an integrability premise. -/
theorem affine_matrix_damped_integrable
    (f : ℝ → Matrix (Fin N) (Fin N) ℝ) (hf : Continuous f) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t, 0 ≤ t → FMSA.matrixAbsSum (f t) ≤ B*(1+t))
    (c : ℝ) (hc : 1 < c) (i j : Fin N) :
    IntegrableOn (fun t : ℝ => exp (-c*t)*f t i j) (Ioi 0) := by
  apply exp_order_real_integrable _ (hf.matrix_elem i j).aestronglyMeasurable 1 B c _ hc
  intro t ht
  simpa only [neg_mul, one_mul] using affine_damping_bound (fun t => f t i j) B hB
    (fun t ht => (FMSA.matrixAbsSum_entry_le (f t) i j).trans (hb t ht)) t ht.le

/-- The actual right Volterra transform is Fhat times the genuine inverse,
with convergence and unit control computed in a far-right half-plane. -/
theorem right_volterra_laplace_eq
    (q f : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q) (hf : Continuous f)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hk : ∀ t, 0 ≤ t → FMSA.matrixAbsSum (q t) ≤ M)
    (hb : ∀ t, 0 ≤ t → FMSA.matrixAbsSum (f t) ≤ B*(1+t)) (s : ℂ) (hs : M+1 < s.re) :
    rdfMatrixLaplace (rightVolterra q f hq hf) s = rdfMatrixLaplace f s*(1-rdfMatrixLaplace q s)⁻¹ := by
  have hq0 : ∀ t, 0 ≤ t → exp (-(0 : ℝ)*t)*FMSA.matrixAbsSum (q t) ≤ M := by
    simpa only [neg_zero, zero_mul, exp_zero, one_mul] using hk
  have hqi (i j : Fin N) : IntegrableOn (fun t : ℝ => exp (-s.re*t)*q t i j) (Ioi 0) :=
    matrix_exp_order_damped_integrable q hq 0 M hq0 s.re (by linarith) i j
  have hfi := affine_matrix_damped_integrable f hf B hB hb s.re (by linarith)
  have hY := complexMatrixLaplace_right_renewal q f (rightVolterra q f hq hf) hq hf
    (right_volterra_continuous q f hq hf) s hqi hfi
    (right_volterra_damped_integrable q f hq hf M B hM hB hk hb s.re hs)
    (fun i j t ht => by simpa only [causalIntervalConv, mul_comm] using right_volterra_renewal q f hq hf i j t ht)
  have hu := bounded_matrix_laplace_isUnit q hq M hk s (by linarith) (by linarith)
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have he := Matrix.mul_nonsing_inv_cancel_right (1-rdfMatrixLaplace q s)
    (rdfMatrixLaplace (rightVolterra q f hq hf) s) hd
  rw [hY] at he
  exact he.symm

/-- The concrete right Volterra solution is the genuine source response
on the closed causal half-line. The common damping is computed from the
kernel bound; there is no independent renewal-uniqueness premise. -/
theorem right_volterra_variation_of_constants
    (q f : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q) (hf : Continuous f)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hk : ∀ t, 0 ≤ t → FMSA.matrixAbsSum (q t) ≤ M)
    (hb : ∀ t, 0 ≤ t → FMSA.matrixAbsSum (f t) ≤ B*(1+t)) :
    ∀ t, 0 ≤ t → rightVolterra q f hq hf t =
      sourceResolventResponse f (kernelResolvent q hq) t := by
  let y := rightVolterra q f hq hf
  let r := kernelResolvent q hq
  let v := sourceResolventResponse f r
  have hy : Continuous y := right_volterra_continuous q f hq hf
  have hr : Continuous r := kernel_resolvent_continuous q hq
  have hv : Continuous v := source_resolvent_response_continuous f r hf hr
  let gamma := M+2
  have hgamma : M+1 < gamma := by dsimp [gamma]; linarith
  have hfL (s : ℂ) (hs : M+1 < s.re) :=
    affine_matrix_damped_integrable f hf B hB hb s.re (by linarith)
  have hrL (s : ℂ) (hs : M+1 < s.re) :=
    kernel_resolvent_damped_integrable q hq M hM hk s.re hs
  have htransform (s : ℂ) (hs : M+1 < s.re) :
      rdfMatrixLaplace y s = rdfMatrixLaplace v s := by
    rw [show rdfMatrixLaplace y s = rdfMatrixLaplace f s*(1-rdfMatrixLaplace q s)⁻¹ from
      right_volterra_laplace_eq q f hq hf M B hM hB hk hb s hs]
    rw [(source_resolvent_response_laplace f r hf hr s (hfL s hs) (hrL s hs)).2]
    rw [show rdfMatrixLaplace r s = (1-rdfMatrixLaplace q s)⁻¹-1 from
      kernel_resolvent_laplace_eq q hq M hM hk s hs]
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  have hentry (i j : Fin N) : EqOn (fun t : ℝ => (y t i j : ℂ))
      (fun t : ℝ => (v t i j : ℂ)) (Ici (0 : ℝ)) := by
    apply causal_laplace_injective _ _ gamma
      (Complex.continuous_ofReal.comp (hy.matrix_elem i j)).continuousOn
      (Complex.continuous_ofReal.comp (hv.matrix_elem i j)).continuousOn
      (ofReal_damped_integrable _ gamma
        (right_volterra_damped_integrable q f hq hf M B hM hB hk hb gamma hgamma i j))
    · have hi := (source_resolvent_response_laplace f r hf hr (gamma : ℂ)
        (hfL (gamma : ℂ) (by simpa using hgamma))
        (hrL (gamma : ℂ) (by simpa using hgamma))).1 i j
      change Integrable (fun t : ℝ => (v t i j : ℂ)*Complex.exp (-(gamma : ℂ)*(t : ℂ)))
        (volume.restrict (Ioi 0)) at hi
      change Integrable (fun t : ℝ => Complex.exp (-(gamma : ℂ)*(t : ℂ))*(v t i j : ℂ))
        (volume.restrict (Ioi 0))
      simpa only [mul_comm] using hi
    · intro xi
      let s := verticalPoint gamma (2*π*xi)
      have hs : M+1 < s.re := by simpa [s, verticalPoint] using hgamma
      change rdfMatrixLaplace y s i j = rdfMatrixLaplace v s i j
      exact congrFun (congrFun (htransform s hs) i) j
  intro t ht
  ext i j
  exact Complex.ofReal_injective (hentry i j (show t ∈ Ici (0 : ℝ) from ht))

/-- The actual excess uses exactly the existing right Volterra constructor.
Only proof irrelevance is needed to match the continuity witnesses. -/
theorem actual_excess_eq_right_volterra {T : Type*} [Fintype T]
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (p : TailMatrix T N × TailMatrix T N) :
    nonlinearRDFExcess z rho sigma p.1 p.2 =
      rightVolterra (nonlinearCausalKernel z rho sigma p.1 p.2)
        (nonlinearExcessSource z rho sigma p.1 p.2)
        (nonlinearCausalKernel_continuous z rho sigma p.1 p.2)
        (nonlinearExcessSource_continuous z rho sigma p.1 p.2) := rfl

/-- Actual excess variation of constants, with the free-volume condition
needed to bound the already background-cancelled source. No canonical
inverse or small physical kernel budget is assumed for this identity. -/
theorem actual_excess_resolvent_formula {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p : TailMatrix T N × TailMatrix T N) :
    ∀ t, 0 ≤ t → nonlinearRDFExcess z rho sigma p.1 p.2 t =
      sourceResolventResponse (nonlinearExcessSource z rho sigma p.1 p.2)
        (actualKernelResolvent z rho sigma p) t := by
  obtain ⟨M, _C, hM, _hC, hlocal⟩ := actual_kernel_source_local_bounds z hz rho sigma hsigma p
  obtain ⟨B, hB, hsource⟩ := nonlinearExcessSource_weighted_bounded z rho sigma p.1 p.2
    hz hsigma hv 0 (fun u => (hz u).le)
  have hb (t : ℝ) (ht : 0 ≤ t) :
      FMSA.matrixAbsSum (nonlinearExcessSource z rho sigma p.1 p.2 t) ≤ B*(1+t) := by
    have he : FMSA.matrixAbsSum (nonlinearExcessSource z rho sigma p.1 p.2 t) ≤ B := by
      simpa only [zero_mul, exp_zero, one_mul] using hsource t ht
    exact he.trans (by nlinarith)
  rw [actual_excess_eq_right_volterra]
  exact right_volterra_variation_of_constants _ _
    (nonlinearCausalKernel_continuous z rho sigma p.1 p.2)
    (nonlinearExcessSource_continuous z rho sigma p.1 p.2) M B hM hB
    (fun t ht => (hlocal.self_of_nhds t ht).1) hb

end FMSA.Convergence.CanonicalRenewalFormula

/-- info: 'FMSA.Convergence.CanonicalRenewalFormula.causal_convolution_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalRenewalFormula.causal_convolution_continuous

/-- info: 'FMSA.Convergence.CanonicalRenewalFormula.source_resolvent_response_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalRenewalFormula.source_resolvent_response_continuous

/-- info: 'FMSA.Convergence.CanonicalRenewalFormula.source_resolvent_response_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalRenewalFormula.source_resolvent_response_laplace

/-- info: 'FMSA.Convergence.CanonicalRenewalFormula.right_volterra_exponential_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalRenewalFormula.right_volterra_exponential_order

/-- info: 'FMSA.Convergence.CanonicalRenewalFormula.right_volterra_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalRenewalFormula.right_volterra_damped_integrable

/-- info: 'FMSA.Convergence.CanonicalRenewalFormula.affine_matrix_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalRenewalFormula.affine_matrix_damped_integrable

/-- info: 'FMSA.Convergence.CanonicalRenewalFormula.right_volterra_laplace_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalRenewalFormula.right_volterra_laplace_eq

/-- info: 'FMSA.Convergence.CanonicalRenewalFormula.right_volterra_variation_of_constants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalRenewalFormula.right_volterra_variation_of_constants

/-- info: 'FMSA.Convergence.CanonicalRenewalFormula.actual_excess_eq_right_volterra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalRenewalFormula.actual_excess_eq_right_volterra

/-- info: 'FMSA.Convergence.CanonicalRenewalFormula.actual_excess_resolvent_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalRenewalFormula.actual_excess_resolvent_formula
