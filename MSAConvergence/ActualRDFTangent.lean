import FMSAPaper.ActualRDFParameters
import FMSAPaper.JacobianExterior

/-! Actual amplitude derivatives satisfy the linearized compact renewal.
No residual kernel is assumed to integrate to a curve of roots. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Convergence.ActualRDFTangent
open FMSA.Paper
open VolterraResolvent ActualRDFParameters
open ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture

section General
variable {E P : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup P] [NormedSpace ℝ P] {R : ℝ}

/-- The actual parameter derivative, with the kernel/source derivatives supplied
by the chain rule rather than postulated as independent tangent data. -/
theorem parametrized_solve_fderiv (hR : 0 ≤ R) (q g : P → C(Icc (0 : ℝ) R, E))
    (p v : P) (hq : DifferentiableAt ℝ q p) (hg : DifferentiableAt ℝ g p) :
    residualOperator hR (q p) (fderiv ℝ (fun a => solve hR (q a) (g a)) p v) =
      fderiv ℝ g p v + kernelOperator hR (fderiv ℝ q p v) (solve hR (q p) (g p)) := by
  have hj : HasFDerivAt
      (fun a : C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E) => solve hR a.1 a.2)
      (fderiv ℝ (fun a : C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E) => solve hR a.1 a.2)
        (q p, g p)) (q p, g p) :=
    ((solve_contDiff (E := E) hR).differentiable (by simp) (q p, g p)).hasFDerivAt
  have hp : HasFDerivAt (fun a => (q a, g a))
      ((fderiv ℝ q p).prod (fderiv ℝ g p)) p := hq.hasFDerivAt.prodMk hg.hasFDerivAt
  have hc := HasFDerivAt.comp (𝕜 := ℝ) (E := P)
    (F := C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E))
    (G := C(Icc (0 : ℝ) R, E))
    (f := fun a => (q a, g a))
    (g := fun a : C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E) => solve hR a.1 a.2) p hj hp
  have he := congrArg (fun L : P →L[ℝ] C(Icc (0 : ℝ) R, E) => L v) hc.fderiv
  change fderiv ℝ (fun a => solve hR (q a) (g a)) p v =
    fderiv ℝ (fun a : C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E) => solve hR a.1 a.2)
      (q p, g p) (fderiv ℝ q p v, fderiv ℝ g p v) at he
  rw [he]
  exact solve_fderiv_equation hR (q p) (g p) (fderiv ℝ q p v) (fderiv ℝ g p v)

/-- A bounded observation of a Banach-valued family commutes with its genuine
Frechet derivative; this will observe actual RDF entries and radial values. -/
theorem observe_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : C(Icc (0 : ℝ) R, E) →L[ℝ] F) (f : P → C(Icc (0 : ℝ) R, E))
    (p v : P) (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun a => L (f a)) p v = L (fderiv ℝ f p v) := by
  have hL : HasFDerivAt (fun x : C(Icc (0 : ℝ) R, E) => L x) L (f p) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := C(Icc (0 : ℝ) R, E)) (F := F) L
  have hc := HasFDerivAt.comp (𝕜 := ℝ) (E := P) (F := C(Icc (0 : ℝ) R, E))
    (G := F) (f := f) (g := fun x => L x) p hL hf.hasFDerivAt
  exact congrArg (fun A : P →L[ℝ] F => A v) hc.fderiv
end General

variable {N : ℕ} {T : Type*} [Fintype T] {R : ℝ}

def causalVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N =>
    nonlinearCausalG z rho sigma a.1 a.2 r i j) p v

def kernelVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N =>
    nonlinearCausalKernel z rho sigma a.1 a.2 r i j) p v

def sourceVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N =>
    nonlinearGSource z rho sigma a.1 a.2 r i j) p v

def causalTangentBundle (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) : C(Icc (0 : ℝ) R, BaxterMatrix N) :=
  fderiv ℝ (causalGBundle hR z rho sigma) p v

def kernelTangentBundle (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) : C(Icc (0 : ℝ) R, BaxterMatrix N) :=
  fderiv ℝ (kernelBundle hR z rho sigma) p v

def sourceTangentBundle (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) : C(Icc (0 : ℝ) R, BaxterMatrix N) :=
  fderiv ℝ (gBundle hR z rho sigma) p v

theorem actual_tangent_operator_equation (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) :
    residualOperator hR (kernelBundle hR z rho sigma p) (causalTangentBundle hR z rho sigma p v) =
      sourceTangentBundle hR z rho sigma p v +
        kernelOperator hR (kernelTangentBundle hR z rho sigma p v) (causalGBundle hR z rho sigma p) := by
  exact parametrized_solve_fderiv hR (kernelBundle hR z rho sigma) (gBundle hR z rho sigma) p v
    ((kernelBundle_contDiff hR z rho sigma).differentiable (by simp) p)
    ((gBundle_contDiff hR z rho sigma).differentiable (by simp) p)

/-- The compact Banach derivative is the existing scalar actual G derivative. -/
theorem causalTangentBundle_entry (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (r : Icc (0 : ℝ) R) (i j : Fin N) :
    matrixEntry j i (causalTangentBundle hR z rho sigma p v r) = causalVariation z rho sigma p v i j r := by
  let L : C(Icc (0 : ℝ) R, BaxterMatrix N) →L[ℝ] ℝ :=
    (matrixEntry j i).comp (ContinuousMap.evalCLM ℝ r)
  have he : (fun a => L (causalGBundle hR z rho sigma a)) =
      fun a : TailMatrix T N × TailMatrix T N => nonlinearCausalG z rho sigma a.1 a.2 r i j := by
    funext a
    change matrixEntry j i (causalGBundle hR z rho sigma a r) = _
    rw [causalGBundle_apply, matrixEntry_ofMatrix]
    rfl
  have h := observe_fderiv (E := BaxterMatrix N) L (causalGBundle hR z rho sigma) p v
    ((causalGBundle_contDiff hR z rho sigma).differentiable (by simp) p)
  rw [he] at h
  exact h.symm

theorem kernelTangentBundle_entry (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (r : Icc (0 : ℝ) R) (i j : Fin N) :
    matrixEntry j i (kernelTangentBundle hR z rho sigma p v r) = kernelVariation z rho sigma p v i j r := by
  let L : C(Icc (0 : ℝ) R, BaxterMatrix N) →L[ℝ] ℝ :=
    (matrixEntry j i).comp (ContinuousMap.evalCLM ℝ r)
  have he : (fun a => L (kernelBundle hR z rho sigma a)) =
      fun a : TailMatrix T N × TailMatrix T N => nonlinearCausalKernel z rho sigma a.1 a.2 r i j := by
    funext a
    change matrixEntry j i (kernelBundle hR z rho sigma a r) = _
    rw [kernelBundle_apply, matrixEntry_ofMatrix]
    rfl
  have h := observe_fderiv (E := BaxterMatrix N) L (kernelBundle hR z rho sigma) p v
    ((kernelBundle_contDiff hR z rho sigma).differentiable (by simp) p)
  rw [he] at h
  exact h.symm

theorem sourceTangentBundle_entry (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (r : Icc (0 : ℝ) R) (i j : Fin N) :
    matrixEntry j i (sourceTangentBundle hR z rho sigma p v r) = sourceVariation z rho sigma p v i j r := by
  let L : C(Icc (0 : ℝ) R, BaxterMatrix N) →L[ℝ] ℝ :=
    (matrixEntry j i).comp (ContinuousMap.evalCLM ℝ r)
  have he : (fun a => L (gBundle hR z rho sigma a)) =
      fun a : TailMatrix T N × TailMatrix T N => nonlinearGSource z rho sigma a.1 a.2 r i j := by
    funext a
    change matrixEntry j i (gBundle hR z rho sigma a r) = _
    rw [gBundle_apply, matrixEntry_ofMatrix]
    rfl
  have h := observe_fderiv (E := BaxterMatrix N) L (gBundle hR z rho sigma) p v
    ((gBundle_contDiff hR z rho sigma).differentiable (by simp) p)
  rw [he] at h
  exact h.symm

/-- Species expansion of the bounded compact convolution. -/
theorem kernelOperator_entry (hR : 0 ≤ R)
    (q u : C(Icc (0 : ℝ) R, BaxterMatrix N)) (r : Icc (0 : ℝ) R) (i j : Fin N) :
    matrixEntry i j (kernelOperator hR q u r) =
      ∑ k, ∫ t in (0 : ℝ)..(r : ℝ), matrixEntry i k (Set.IccExtend hR q ((r : ℝ) - t)) *
        matrixEntry k j (Set.IccExtend hR u t) := by
  rw [kernelOperator_apply]
  exact matrixEntry_integral_mul
    (fun t => Set.IccExtend hR q ((r : ℝ) - t)) (Set.IccExtend hR u)
    (q.continuous.Icc_extend'.comp (continuous_const.sub continuous_id))
    u.continuous.Icc_extend' 0 r i j

theorem kernel_actual_tangent_convolution (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (r : Icc (0 : ℝ) R) (i j : Fin N) :
    matrixEntry j i (kernelOperator hR (kernelBundle hR z rho sigma p)
      (causalTangentBundle hR z rho sigma p v) r) =
      ∑ m, ∫ t in (0 : ℝ)..(r : ℝ), nonlinearCausalKernel z rho sigma p.1 p.2 ((r : ℝ)-t) m j *
        causalVariation z rho sigma p v i m t := by
  rw [kernelOperator_entry]
  apply Finset.sum_congr rfl
  intro m _
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le r.2.1] at ht
  dsimp only
  rw [Set.IccExtend_of_mem hR _
      (show (r : ℝ)-t ∈ Icc (0 : ℝ) R from by constructor <;> linarith [ht.1, ht.2, r.2.2]),
    Set.IccExtend_of_mem hR _ (show t ∈ Icc (0 : ℝ) R from ⟨ht.1, ht.2.trans r.2.2⟩),
    kernelBundle_apply, matrixEntry_ofMatrix, causalTangentBundle_entry]
  rfl

theorem tangent_kernel_actual_convolution (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (r : Icc (0 : ℝ) R) (i j : Fin N) :
    matrixEntry j i (kernelOperator hR (kernelTangentBundle hR z rho sigma p v)
      (causalGBundle hR z rho sigma p) r) =
      ∑ m, ∫ t in (0 : ℝ)..(r : ℝ), kernelVariation z rho sigma p v m j ((r : ℝ)-t) *
        nonlinearCausalG z rho sigma p.1 p.2 t i m := by
  rw [kernelOperator_entry]
  apply Finset.sum_congr rfl
  intro m _
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le r.2.1] at ht
  dsimp only
  rw [Set.IccExtend_of_mem hR _
      (show (r : ℝ)-t ∈ Icc (0 : ℝ) R from by constructor <;> linarith [ht.1, ht.2, r.2.2]),
    Set.IccExtend_of_mem hR _ (show t ∈ Icc (0 : ℝ) R from ⟨ht.1, ht.2.trans r.2.2⟩),
    kernelTangentBundle_entry, causalGBundle_apply, matrixEntry_ofMatrix]
  rfl

/-- Actual off-root linearized species renewal, with all derivative/integral
interchanges discharged through the compact bounded operators. -/
theorem actual_tangent_renewal_on_compact (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (r : Icc (0 : ℝ) R) (i j : Fin N) :
    causalVariation z rho sigma p v i j r = sourceVariation z rho sigma p v i j r +
      (∑ m, ∫ t in (0 : ℝ)..(r : ℝ), nonlinearCausalKernel z rho sigma p.1 p.2 ((r : ℝ)-t) m j *
        causalVariation z rho sigma p v i m t) +
      ∑ m, ∫ t in (0 : ℝ)..(r : ℝ), kernelVariation z rho sigma p v m j ((r : ℝ)-t) *
        nonlinearCausalG z rho sigma p.1 p.2 t i m := by
  have h := congrArg (fun f : C(Icc (0 : ℝ) R, BaxterMatrix N) => matrixEntry j i (f r))
    (actual_tangent_operator_equation hR z rho sigma p v)
  change matrixEntry j i (causalTangentBundle hR z rho sigma p v r -
      kernelOperator hR (kernelBundle hR z rho sigma p) (causalTangentBundle hR z rho sigma p v) r) =
    matrixEntry j i (sourceTangentBundle hR z rho sigma p v r +
      kernelOperator hR (kernelTangentBundle hR z rho sigma p v) (causalGBundle hR z rho sigma p) r) at h
  rw [map_sub, map_add, causalTangentBundle_entry, sourceTangentBundle_entry,
    kernel_actual_tangent_convolution, tangent_kernel_actual_convolution] at h
  linarith

/-- The actual renewal derivative at every finite nonnegative radius, with
no compactness, root curve, differentiability or smallness premise supplied. -/
theorem actual_tangent_renewal (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    causalVariation z rho sigma p v i j r = sourceVariation z rho sigma p v i j r +
      (∑ m, ∫ t in (0 : ℝ)..r, nonlinearCausalKernel z rho sigma p.1 p.2 (r-t) m j *
        causalVariation z rho sigma p v i m t) +
      ∑ m, ∫ t in (0 : ℝ)..r, kernelVariation z rho sigma p v m j (r-t) *
        nonlinearCausalG z rho sigma p.1 p.2 t i m :=
  actual_tangent_renewal_on_compact hr z rho sigma p v ⟨r, hr, le_rfl⟩ i j

theorem causalVariation_continuousOn_compact (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    ContinuousOn (causalVariation z rho sigma p v i j) (Icc (0 : ℝ) R) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have h : Continuous (fun r : Icc (0 : ℝ) R =>
      matrixEntry j i (causalTangentBundle hR z rho sigma p v r)) :=
    (matrixEntry j i).continuous.comp (causalTangentBundle hR z rho sigma p v).continuous
  convert h using 1
  funext r
  exact (causalTangentBundle_entry hR z rho sigma p v r i j).symm

theorem kernelVariation_continuousOn_compact (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    ContinuousOn (kernelVariation z rho sigma p v i j) (Icc (0 : ℝ) R) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have h : Continuous (fun r : Icc (0 : ℝ) R =>
      matrixEntry j i (kernelTangentBundle hR z rho sigma p v r)) :=
    (matrixEntry j i).continuous.comp (kernelTangentBundle hR z rho sigma p v).continuous
  convert h using 1
  funext r
  exact (kernelTangentBundle_entry hR z rho sigma p v r i j).symm

theorem sourceVariation_continuousOn_compact (hR : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    ContinuousOn (sourceVariation z rho sigma p v i j) (Icc (0 : ℝ) R) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have h : Continuous (fun r : Icc (0 : ℝ) R =>
      matrixEntry j i (sourceTangentBundle hR z rho sigma p v r)) :=
    (matrixEntry j i).continuous.comp (sourceTangentBundle hR z rho sigma p v).continuous
  convert h using 1
  funext r
  exact (sourceTangentBundle_entry hR z rho sigma p v r i j).symm

def excessVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N =>
    nonlinearRDFExcess z rho sigma a.1 a.2 r i j) p v

theorem excessVariation_eq_causalVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    excessVariation z rho sigma p v i j r = causalVariation z rho sigma p v i j r := by
  simp only [causalVariation, nonlinearCausalG, Matrix.of_apply, fderiv_add_const, excessVariation]

/-- The actual weighted h tangent outside the hard core is the actual shifted
causal derivative. Its existence was established in 1.0.17, not assumed here. -/
theorem actual_weighted_hVariation_outer (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N)
    (hR : 0 < edgeHi sigma i j) (r : ℝ) (hr : edgeHi sigma i j ≤ r) :
    r * JacobianExterior.hVariation z rho sigma p v i j r =
      causalVariation z rho sigma p v i j (r-edgeHi sigma i j) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => r * nonlinearH z rho sigma a.1 a.2 i j r) =
      fun a : TailMatrix T N × TailMatrix T N => nonlinearRDFExcess z rho sigma a.1 a.2
        (r-edgeHi sigma i j) i j := by
    funext a
    rw [nonlinearH, nonlinearRDFMoment_outer z rho sigma a.1 a.2 i j hR r hr]
    field_simp [(hR.trans_le hr).ne']
  have hd := (h_hasFDerivAt z rho sigma p i j r).const_mul r
  rw [he] at hd
  have h := congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ => L v) hd.fderiv
  change excessVariation z rho sigma p v i j (r-edgeHi sigma i j) =
    r * JacobianExterior.hVariation z rho sigma p v i j r at h
  rw [excessVariation_eq_causalVariation] at h
  exact h.symm

/-- The fixed hard-core breakpoint accounts for the entire positive-radial
weighted h tangent. No endpoint Dirac term is generated by varying amplitudes. -/
theorem actual_weighted_hVariation_positive (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N)
    (hR : 0 < edgeHi sigma i j) (r : ℝ) (hr : 0 < r) :
    r * JacobianExterior.hVariation z rho sigma p v i j r =
      if r < edgeHi sigma i j then 0 else causalVariation z rho sigma p v i j (r-edgeHi sigma i j) := by
  by_cases hc : r < edgeHi sigma i j
  · rw [if_pos hc, JacobianExterior.hVariation_core_zero z rho sigma p v i j r hr hc, mul_zero]
  · rw [if_neg hc]
    exact actual_weighted_hVariation_outer z rho sigma p v i j hR r (not_lt.mp hc)

theorem kernel_tangent_intervalIntegrable (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j m : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    IntervalIntegrable (fun t => nonlinearCausalKernel z rho sigma p.1 p.2 (r-t) m j *
      causalVariation z rho sigma p v i m t) volume 0 r := by
  apply ContinuousOn.intervalIntegrable_of_Icc hr
  exact ((((nonlinearCausalKernel_continuous z rho sigma p.1 p.2).matrix_elem m j).comp
    (continuous_const.sub continuous_id)).continuousOn).mul
    (causalVariation_continuousOn_compact hr z rho sigma p v i m)

theorem tangent_kernel_intervalIntegrable (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j m : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    IntervalIntegrable (fun t => kernelVariation z rho sigma p v m j (r-t) *
      nonlinearCausalG z rho sigma p.1 p.2 t i m) volume 0 r := by
  apply ContinuousOn.intervalIntegrable_of_Icc hr
  have hk : ContinuousOn (fun t : ℝ => kernelVariation z rho sigma p v m j (r-t)) (Icc (0 : ℝ) r) :=
    (kernelVariation_continuousOn_compact hr z rho sigma p v m j).comp
      (continuous_const.sub continuous_id).continuousOn (by
        intro t ht
        constructor <;> linarith [ht.1, ht.2])
  exact hk.mul ((nonlinearCausalG_continuous z rho sigma p.1 p.2).matrix_elem i m).continuousOn

/-- Fully transcribed actual tangent renewal with a single species convolution;
its two summands are proved integrable on each finite radial interval. -/
theorem actual_tangent_renewal_integral (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    causalVariation z rho sigma p v i j r = sourceVariation z rho sigma p v i j r +
      ∑ m, ∫ t in (0 : ℝ)..r,
        (nonlinearCausalKernel z rho sigma p.1 p.2 (r-t) m j * causalVariation z rho sigma p v i m t +
          kernelVariation z rho sigma p v m j (r-t) * nonlinearCausalG z rho sigma p.1 p.2 t i m) := by
  rw [actual_tangent_renewal z rho sigma p v i j r hr, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  exact (intervalIntegral.integral_add (kernel_tangent_intervalIntegrable z rho sigma p v i j m r hr)
    (tangent_kernel_intervalIntegrable z rho sigma p v i j m r hr)).symm

/-- Every actual weighted h tangent is locally in every radial Lp, including
L2 and Linfinity. The still-open global tail control is not supplied here. -/
theorem actual_weighted_hVariation_memLp_compact (hS : 0 ≤ R) (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (hR : 0 < edgeHi sigma i j) (q : ENNReal) :
    MemLp (fun r => r * JacobianExterior.hVariation z rho sigma p v i j r) q
      (volume.restrict (Icc (0 : ℝ) R)) := by
  let U := causalTangentBundle hS z rho sigma p v
  let u : C(Icc (0 : ℝ) R, ℝ) := ⟨fun r => matrixEntry j i (U r),
    (matrixEntry j i).continuous.comp U.continuous⟩
  let f : ℝ → ℝ := fun r => Set.IccExtend hS u (r-edgeHi sigma i j)
  have hf : Continuous f := u.continuous.Icc_extend'.comp
    (continuous_id.sub continuous_const)
  have hb (r : ℝ) : ‖f r‖ ≤ ‖u‖ := u.norm_coe_le_norm _
  have hm : MemLp ((Ici (edgeHi sigma i j)).indicator f) q (volume.restrict (Icc (0 : ℝ) R)) :=
    (MemLp.of_bound hf.aestronglyMeasurable ‖u‖ (ae_of_all _ hb)).indicator measurableSet_Ici
  apply MemLp.ae_eq (hf_Lp := hm)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  by_cases hz : r = 0
  · subst r
    rw [indicator_of_notMem (show (0 : ℝ) ∉ Ici (edgeHi sigma i j) from not_le.mpr hR)]
    simp
  · have hr0 : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hz)
    rw [actual_weighted_hVariation_positive z rho sigma p v i j hR r hr0]
    by_cases hc : r < edgeHi sigma i j
    · rw [if_pos hc, indicator_of_notMem (show r ∉ Ici (edgeHi sigma i j) from not_le.mpr hc)]
    · rw [if_neg hc, indicator_of_mem (show r ∈ Ici (edgeHi sigma i j) from not_lt.mp hc)]
      dsimp only [f]
      rw [Set.IccExtend_of_mem hS u (show r-edgeHi sigma i j ∈ Icc (0 : ℝ) R from by
        constructor <;> linarith [hr.2, hR])]
      exact causalTangentBundle_entry hS z rho sigma p v _ i j

end FMSA.Convergence.ActualRDFTangent

/-- info: 'FMSA.Convergence.ActualRDFTangent.parametrized_solve_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.parametrized_solve_fderiv
/-- info: 'FMSA.Convergence.ActualRDFTangent.observe_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.observe_fderiv
/-- info: 'FMSA.Convergence.ActualRDFTangent.actual_tangent_operator_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.actual_tangent_operator_equation
/-- info: 'FMSA.Convergence.ActualRDFTangent.causalTangentBundle_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.causalTangentBundle_entry
/-- info: 'FMSA.Convergence.ActualRDFTangent.kernelTangentBundle_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.kernelTangentBundle_entry
/-- info: 'FMSA.Convergence.ActualRDFTangent.sourceTangentBundle_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.sourceTangentBundle_entry
/-- info: 'FMSA.Convergence.ActualRDFTangent.kernelOperator_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.kernelOperator_entry
/-- info: 'FMSA.Convergence.ActualRDFTangent.kernel_actual_tangent_convolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.kernel_actual_tangent_convolution
/-- info: 'FMSA.Convergence.ActualRDFTangent.tangent_kernel_actual_convolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.tangent_kernel_actual_convolution
/-- info: 'FMSA.Convergence.ActualRDFTangent.actual_tangent_renewal_on_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.actual_tangent_renewal_on_compact
/-- info: 'FMSA.Convergence.ActualRDFTangent.actual_tangent_renewal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.actual_tangent_renewal
/-- info: 'FMSA.Convergence.ActualRDFTangent.causalVariation_continuousOn_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.causalVariation_continuousOn_compact
/-- info: 'FMSA.Convergence.ActualRDFTangent.kernelVariation_continuousOn_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.kernelVariation_continuousOn_compact
/-- info: 'FMSA.Convergence.ActualRDFTangent.sourceVariation_continuousOn_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.sourceVariation_continuousOn_compact
/-- info: 'FMSA.Convergence.ActualRDFTangent.excessVariation_eq_causalVariation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.excessVariation_eq_causalVariation
/-- info: 'FMSA.Convergence.ActualRDFTangent.actual_weighted_hVariation_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.actual_weighted_hVariation_outer
/-- info: 'FMSA.Convergence.ActualRDFTangent.actual_weighted_hVariation_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.actual_weighted_hVariation_positive
/-- info: 'FMSA.Convergence.ActualRDFTangent.kernel_tangent_intervalIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.kernel_tangent_intervalIntegrable
/-- info: 'FMSA.Convergence.ActualRDFTangent.tangent_kernel_intervalIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.tangent_kernel_intervalIntegrable
/-- info: 'FMSA.Convergence.ActualRDFTangent.actual_tangent_renewal_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.actual_tangent_renewal_integral
/-- info: 'FMSA.Convergence.ActualRDFTangent.actual_weighted_hVariation_memLp_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRDFTangent.actual_weighted_hVariation_memLp_compact
