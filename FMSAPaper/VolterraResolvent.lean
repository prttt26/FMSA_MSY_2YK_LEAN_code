import LeanCode.Analysis.VolterraBanach
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Banach

/-! Compact Volterra resolvents as genuine bounded linear operators.
Their invertibility is proved from unconditional Volterra uniqueness, with
no smallness assumption on the convolution kernel. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped ContDiff BigOperators

namespace FMSA.Paper.VolterraResolvent
open FMSA.VolterraBanach
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
variable {R : ℝ}

/-- Homogeneous convolution on a fixed compact interval, using the existing
continuous extension convention of the actual Volterra construction. -/
def convolution (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q)
    (u : C(Icc (0 : ℝ) R, E)) : C(Icc (0 : ℝ) R, E) :=
  volterraTE hR q 0 hq continuous_const u

theorem convolution_apply (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q)
    (u : C(Icc (0 : ℝ) R, E)) (r : Icc (0 : ℝ) R) :
    convolution hR q hq u r = ∫ t in (0 : ℝ)..(r : ℝ), q ((r : ℝ) - t) * IccExtend hR u t := by
  simp [convolution, volterraTE]

theorem convolution_add (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q)
    (u v : C(Icc (0 : ℝ) R, E)) :
    convolution hR q hq (u + v) = convolution hR q hq u + convolution hR q hq v := by
  ext r
  simp only [convolution_apply, ContinuousMap.add_apply]
  have hi (w : C(Icc (0 : ℝ) R, E)) : IntervalIntegrable
      (fun t => q ((r : ℝ) - t) * IccExtend hR w t) volume 0 r :=
    ((hq.comp (continuous_const.sub continuous_id)).mul w.continuous.Icc_extend').intervalIntegrable 0 r
  rw [← intervalIntegral.integral_add (hi u) (hi v)]
  apply intervalIntegral.integral_congr
  intro t _
  simp [IccExtend, mul_add]

theorem convolution_smul (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q)
    (c : ℝ) (u : C(Icc (0 : ℝ) R, E)) :
    convolution hR q hq (c • u) = c • convolution hR q hq u := by
  ext r
  simp only [convolution_apply, ContinuousMap.smul_apply]
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t _
  simp [IccExtend]

def convolutionLinear (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q) :
    C(Icc (0 : ℝ) R, E) →ₗ[ℝ] C(Icc (0 : ℝ) R, E) where
  toFun := convolution hR q hq
  map_add' := convolution_add hR q hq
  map_smul' := convolution_smul hR q hq

theorem convolution_norm_bound (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : C(Icc (0 : ℝ) R, E), ‖convolution hR q hq u‖ ≤ B * ‖u‖ := by
  obtain ⟨M, hm⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-R) R) hq.continuousOn
  refine ⟨max M 0 * R, mul_nonneg (le_max_right _ _) hR, fun u => ?_⟩
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro r
  rw [convolution_apply]
  have hb : ‖∫ t in (0 : ℝ)..(r : ℝ), q ((r : ℝ) - t) * IccExtend hR u t‖ ≤
      (max M 0 * ‖u‖) * |(r : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le r.2.1] at ht
    apply (norm_mul_le _ _).trans
    apply mul_le_mul _ _ (norm_nonneg _) (le_max_right _ _)
    · exact (hm _ (by constructor <;> linarith [r.2.1, r.2.2, ht.1, ht.2])).trans (le_max_left _ _)
    · exact u.norm_coe_le_norm _
  calc
    _ ≤ (max M 0 * ‖u‖) * (r : ℝ) := by simpa only [sub_zero, abs_of_nonneg r.2.1] using hb
    _ ≤ (max M 0 * ‖u‖) * R := mul_le_mul_of_nonneg_left r.2.2 (by positivity)
    _ = _ := by ring

/-- A bounded operator, not merely a pointwise integral formula. -/
def convolutionCLM (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q) :
    C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E) :=
  (convolutionLinear hR q hq).mkContinuous (convolution_norm_bound hR q hq).choose
    (convolution_norm_bound hR q hq).choose_spec.2

theorem convolutionCLM_apply (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q)
    (u : C(Icc (0 : ℝ) R, E)) (r : Icc (0 : ℝ) R) :
    convolutionCLM hR q hq u r = ∫ t in (0 : ℝ)..(r : ℝ), q ((r : ℝ) - t) * IccExtend hR u t :=
  convolution_apply hR q hq u r

/-- The actual compact-interval Volterra residual operator. -/
def residualCLM (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q) :
    C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E) :=
  ContinuousLinearMap.id ℝ _ - convolutionCLM hR q hq

theorem residualCLM_apply (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q)
    (u : C(Icc (0 : ℝ) R, E)) (r : Icc (0 : ℝ) R) :
    residualCLM hR q hq u r = u r - ∫ t in (0 : ℝ)..(r : ℝ), q ((r : ℝ) - t) * IccExtend hR u t := by
  simp [residualCLM, convolutionCLM_apply]

theorem residualCLM_bijective (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q) :
    Function.Bijective (residualCLM hR q hq) := by
  have hsol (g : C(Icc (0 : ℝ) R, E)) : ∃! u, residualCLM hR q hq u = g := by
    have hg : Continuous (IccExtend hR g) := g.continuous.Icc_extend'
    obtain ⟨u, hu, huniq⟩ := volterra_convolution_existsUniqueE hR q (IccExtend hR g) hq hg
    have he (v : C(Icc (0 : ℝ) R, E)) : residualCLM hR q hq v = g ↔
        ∀ r : Icc (0 : ℝ) R, v r = IccExtend hR g r +
          ∫ t in (0 : ℝ)..(r : ℝ), q ((r : ℝ) - t) * IccExtend hR v t := by
      rw [ContinuousMap.ext_iff]
      apply forall_congr'
      intro r
      rw [residualCLM_apply, IccExtend_of_mem hR g r.2]
      constructor
      · intro h
        exact (sub_eq_iff_eq_add).mp h
      · intro h
        exact (sub_eq_iff_eq_add).mpr h
    exact ⟨u, (he u).mpr hu, fun v hv => huniq v ((he v).mp hv)⟩
  constructor
  · intro u v huv
    obtain ⟨w, hw, huniq⟩ := hsol (residualCLM hR q hq u)
    exact (huniq u rfl).trans (huniq v huv.symm).symm
  · intro g
    exact (hsol g).exists

/-- Unconditional invertibility of the compact Volterra residual. -/
theorem residualCLM_isUnit (hR : 0 ≤ R) (q : ℝ → E) (hq : Continuous q) :
    IsUnit (residualCLM hR q hq) :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr (residualCLM_bijective hR q hq)

/-- Compactly bundled kernels allow a bounded linear dependence of the
convolution operator on its kernel. -/
def compactConvolution (hR : 0 ≤ R) (q u : C(Icc (0 : ℝ) R, E)) : C(Icc (0 : ℝ) R, E) :=
  convolution hR (IccExtend hR q) q.continuous.Icc_extend' u

theorem compactConvolution_kernel_add (hR : 0 ≤ R) (q v u : C(Icc (0 : ℝ) R, E)) :
    compactConvolution hR (q + v) u = compactConvolution hR q u + compactConvolution hR v u := by
  ext r
  simp only [compactConvolution, convolution_apply, ContinuousMap.add_apply]
  have hi (w : C(Icc (0 : ℝ) R, E)) : IntervalIntegrable
      (fun t => IccExtend hR w ((r : ℝ) - t) * IccExtend hR u t) volume 0 r :=
    ((w.continuous.Icc_extend'.comp (continuous_const.sub continuous_id)).mul
      u.continuous.Icc_extend').intervalIntegrable 0 r
  rw [← intervalIntegral.integral_add (hi q) (hi v)]
  apply intervalIntegral.integral_congr
  intro t _
  simp [IccExtend, add_mul]

theorem compactConvolution_kernel_smul (hR : 0 ≤ R) (c : ℝ) (q u : C(Icc (0 : ℝ) R, E)) :
    compactConvolution hR (c • q) u = c • compactConvolution hR q u := by
  ext r
  simp only [compactConvolution, convolution_apply, ContinuousMap.smul_apply]
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t _
  simp [IccExtend]

def compactConvolutionBilinear (hR : 0 ≤ R) :
    C(Icc (0 : ℝ) R, E) →ₗ[ℝ] C(Icc (0 : ℝ) R, E) →ₗ[ℝ] C(Icc (0 : ℝ) R, E) :=
  LinearMap.mk₂ ℝ (compactConvolution hR)
    (compactConvolution_kernel_add hR) (compactConvolution_kernel_smul hR)
    (fun q u v => convolution_add hR _ _ u v)
    (fun c q u => convolution_smul hR _ _ c u)

theorem compactConvolution_norm_bound (hR : 0 ≤ R) (q u : C(Icc (0 : ℝ) R, E)) :
    ‖compactConvolution hR q u‖ ≤ R * ‖q‖ * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro r
  rw [compactConvolution, convolution_apply]
  have hb : ‖∫ t in (0 : ℝ)..(r : ℝ), IccExtend hR q ((r : ℝ) - t) * IccExtend hR u t‖ ≤
      (‖q‖ * ‖u‖) * |(r : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    exact (norm_mul_le _ _).trans (mul_le_mul (q.norm_coe_le_norm _) (u.norm_coe_le_norm _)
      (norm_nonneg _) (norm_nonneg _))
  calc
    _ ≤ (‖q‖ * ‖u‖) * (r : ℝ) := by simpa only [sub_zero, abs_of_nonneg r.2.1] using hb
    _ ≤ (‖q‖ * ‖u‖) * R := mul_le_mul_of_nonneg_left r.2.2 (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- Bounded bilinear convolution, as a linear map from kernels to operators. -/
def kernelOperator (hR : 0 ≤ R) :
    C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E) :=
  (compactConvolutionBilinear hR).mkContinuous₂ R (by
    intro q u
    change ‖compactConvolution hR q u‖ ≤ R * ‖q‖ * ‖u‖
    exact compactConvolution_norm_bound hR q u)

theorem kernelOperator_apply (hR : 0 ≤ R) (q u : C(Icc (0 : ℝ) R, E)) (r : Icc (0 : ℝ) R) :
    kernelOperator hR q u r = ∫ t in (0 : ℝ)..(r : ℝ), IccExtend hR q ((r : ℝ) - t) * IccExtend hR u t :=
  convolution_apply hR (IccExtend hR q) q.continuous.Icc_extend' u r

def residualOperator (hR : 0 ≤ R) (q : C(Icc (0 : ℝ) R, E)) :
    C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E) :=
  ContinuousLinearMap.id ℝ _ - kernelOperator hR q

theorem residualOperator_isUnit (hR : 0 ≤ R) (q : C(Icc (0 : ℝ) R, E)) :
    IsUnit (residualOperator hR q) :=
  residualCLM_isUnit hR (IccExtend hR q) q.continuous.Icc_extend'

/-- The actual inverse operator on a compact interval, always evaluated at a unit. -/
def solve (hR : 0 ≤ R) (q g : C(Icc (0 : ℝ) R, E)) : C(Icc (0 : ℝ) R, E) :=
  Ring.inverse (residualOperator hR q) g

theorem solve_spec (hR : 0 ≤ R) (q g : C(Icc (0 : ℝ) R, E)) :
    residualOperator hR q (solve hR q g) = g := by
  have he := congrArg (fun A : C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E) => A g)
    (Ring.mul_inverse_cancel (residualOperator hR q) (residualOperator_isUnit hR q))
  exact he

theorem solve_renewal (hR : 0 ≤ R) (q g : C(Icc (0 : ℝ) R, E)) (r : Icc (0 : ℝ) R) :
    solve hR q g r = g r + ∫ t in (0 : ℝ)..(r : ℝ),
      IccExtend hR q ((r : ℝ) - t) * IccExtend hR (solve hR q g) t := by
  have he := congrArg (fun f : C(Icc (0 : ℝ) R, E) => f r) (solve_spec hR q g)
  change solve hR q g r - kernelOperator hR q (solve hR q g) r = g r at he
  rw [kernelOperator_apply] at he
  exact sub_eq_iff_eq_add.mp he

def restrict (hR : 0 ≤ R) (f : ℝ → E) (hf : Continuous f) : C(Icc (0 : ℝ) R, E) :=
  ⟨fun r => f r, hf.comp continuous_subtype_val⟩

theorem solve_eq_volterraSolE (hR : 0 ≤ R) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g) :
    solve hR (restrict hR q hq) (restrict hR g hg) = volterraSolE hR q g hq hg := by
  apply volterraSolE_unique
  intro r
  rw [solve_renewal]
  change g r + _ = g r + _
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le r.2.1] at ht
  dsimp only
  rw [IccExtend_of_mem hR _ (show (r : ℝ) - t ∈ Icc (0 : ℝ) R from by
    constructor <;> linarith [ht.1, ht.2, r.2.1, r.2.2])]
  rfl

theorem global_eq_solve (hR : 0 ≤ R) (q g : ℝ → E) (hq : Continuous q) (hg : Continuous g)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
    volterraGlobalE 0 q g hq hg r = solve hR (restrict hR q hq) (restrict hR g hg) ⟨r, hr⟩ := by
  rw [volterraGlobalE_eq_sol hR q g hq hg r hr, solve_eq_volterraSolE]

set_option backward.isDefEq.respectTransparency false in
/-- The compact solution is C-infinity jointly in the entire kernel and source.
No operator invertibility or norm-smallness premise is left to the caller. -/
theorem solve_contDiff (hR : 0 ≤ R) :
    ContDiff ℝ ∞ (fun p : C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E) => solve hR p.1 p.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hk : ContDiff ℝ ∞ (kernelOperator hR : C(Icc (0 : ℝ) R, E) →
      C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E)) := by
    exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (E := C(Icc (0 : ℝ) R, E))
      (F := C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E))
      (kernelOperator (E := E) hR)
  have ha : ContDiffAt ℝ ∞
      (fun a : C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E) => residualOperator hR a.1) p := by
    change ContDiffAt ℝ ∞ (fun a : C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E) =>
      ContinuousLinearMap.id ℝ _ - kernelOperator hR a.1) p
    exact contDiffAt_const.sub (hk.contDiffAt.comp p contDiffAt_fst)
  have hi : ContDiffAt ℝ ∞ Ring.inverse (residualOperator hR p.1) := by
    obtain ⟨u, hu⟩ := residualOperator_isUnit hR p.1
    rw [← hu]
    exact contDiffAt_ringInverse ℝ (R := C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E)) u
  exact (hi.comp p ha).clm_apply contDiffAt_snd

/-- Smooth parameter families of kernels and sources produce a smooth family
of compact solutions. -/
theorem solve_contDiff_parametrized {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (hR : 0 ≤ R) (q g : P → C(Icc (0 : ℝ) R, E))
    (hq : ContDiff ℝ ∞ q) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p => solve hR (q p) (g p)) := by
  exact ContDiff.comp (𝕜 := ℝ) (E := P)
    (F := C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E))
    (G := C(Icc (0 : ℝ) R, E))
    (g := fun a : C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E) => solve hR a.1 a.2)
    (f := fun p : P => (q p, g p)) (solve_contDiff (E := E) hR) (hq.prodMk hg)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine Fréchet derivative solves the linearized renewal equation.
This differentiates the bounded inverse identity, without an interchange
of pointwise differentiation and integration. -/
theorem solve_fderiv_equation (hR : 0 ≤ R) (q g dq dg : C(Icc (0 : ℝ) R, E)) :
    residualOperator hR q
      (fderiv ℝ (fun a : C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E) => solve hR a.1 a.2)
        (q, g) (dq, dg)) = dg + kernelOperator hR dq (solve hR q g) := by
  letI : AddCommGroup (C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E)) :=
    ContinuousLinearMap.addCommGroup
  letI : IsTopologicalAddGroup (C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E)) :=
    ContinuousLinearMap.topologicalAddGroup
  let P := C(Icc (0 : ℝ) R, E) × C(Icc (0 : ℝ) R, E)
  let K : P →L[ℝ] C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E) :=
    (kernelOperator (E := E) hR).comp
      (ContinuousLinearMap.fst ℝ C(Icc (0 : ℝ) R, E) C(Icc (0 : ℝ) R, E))
  have hk : HasFDerivAt (fun a : P => kernelOperator hR a.1) K (q, g) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := P)
      (F := C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E)) K
  have hc : HasFDerivAt (fun _ : P => ContinuousLinearMap.id ℝ C(Icc (0 : ℝ) R, E))
      (0 : P →L[ℝ] C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E)) (q, g) :=
    hasFDerivAt_const _ _
  have ha := HasFDerivAt.sub (𝕜 := ℝ) (E := P)
    (F := C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E)) hc hk
  change HasFDerivAt (fun a : P => residualOperator hR a.1) _ (q, g) at ha
  have hy := ((solve_contDiff (E := E) hR).differentiable (by simp) (q, g)).hasFDerivAt
  have hd := ha.clm_apply hy
  have he : (fun a : P => residualOperator hR a.1 (solve hR a.1 a.2)) = fun a : P => a.2 :=
    funext fun a => solve_spec hR a.1 a.2
  rw [he] at hd
  have hh := congrArg (fun L : P →L[ℝ] C(Icc (0 : ℝ) R, E) => L (dq, dg))
    (hd.unique hasFDerivAt_snd)
  let DK : P →L[ℝ] C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E) :=
    (0 : P →L[ℝ] C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E)) - K
  have hz : DK = -K := by exact zero_sub K
  have hterm : DK.flip (solve hR q g) (dq, dg) =
      -kernelOperator hR dq (solve hR q g) := by
    calc
      _ = DK (dq, dg) (solve hR q g) := rfl
      _ = (-K) (dq, dg) (solve hR q g) := congrArg
        (fun L : P →L[ℝ] C(Icc (0 : ℝ) R, E) →L[ℝ] C(Icc (0 : ℝ) R, E) =>
          L (dq, dg) (solve hR q g)) hz
      _ = -(K (dq, dg) (solve hR q g)) := rfl
      _ = _ := rfl
  change residualOperator hR q
    (fderiv ℝ (fun a : P => solve hR a.1 a.2) (q, g) (dq, dg)) +
      DK.flip (solve hR q g) (dq, dg) = dg at hh
  rw [hterm] at hh
  exact sub_eq_iff_eq_add.mp (by simpa only [sub_eq_add_neg] using hh)


end FMSA.Paper.VolterraResolvent

/-- info: 'FMSA.Paper.VolterraResolvent.convolution_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.convolution_apply
/-- info: 'FMSA.Paper.VolterraResolvent.convolution_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.convolution_add
/-- info: 'FMSA.Paper.VolterraResolvent.convolution_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.convolution_smul
/-- info: 'FMSA.Paper.VolterraResolvent.convolution_norm_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.convolution_norm_bound
/-- info: 'FMSA.Paper.VolterraResolvent.convolutionCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.convolutionCLM_apply
/-- info: 'FMSA.Paper.VolterraResolvent.residualCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.residualCLM_apply
/-- info: 'FMSA.Paper.VolterraResolvent.residualCLM_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.residualCLM_bijective
/-- info: 'FMSA.Paper.VolterraResolvent.residualCLM_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.residualCLM_isUnit
/-- info: 'FMSA.Paper.VolterraResolvent.compactConvolution_kernel_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.compactConvolution_kernel_add
/-- info: 'FMSA.Paper.VolterraResolvent.compactConvolution_kernel_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.compactConvolution_kernel_smul
/-- info: 'FMSA.Paper.VolterraResolvent.compactConvolution_norm_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.compactConvolution_norm_bound
/-- info: 'FMSA.Paper.VolterraResolvent.kernelOperator_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.kernelOperator_apply
/-- info: 'FMSA.Paper.VolterraResolvent.residualOperator_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.residualOperator_isUnit
/-- info: 'FMSA.Paper.VolterraResolvent.solve_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.solve_spec
/-- info: 'FMSA.Paper.VolterraResolvent.solve_renewal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.solve_renewal
/-- info: 'FMSA.Paper.VolterraResolvent.solve_eq_volterraSolE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.solve_eq_volterraSolE
/-- info: 'FMSA.Paper.VolterraResolvent.global_eq_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.global_eq_solve
/-- info: 'FMSA.Paper.VolterraResolvent.solve_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.solve_contDiff
/-- info: 'FMSA.Paper.VolterraResolvent.solve_contDiff_parametrized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.solve_contDiff_parametrized
/-- info: 'FMSA.Paper.VolterraResolvent.solve_fderiv_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.VolterraResolvent.solve_fderiv_equation
