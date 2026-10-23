import FMSAPaper.HomogeneousJets
import FMSAPaper.LocalBranch

/-! A single smooth branch in all strengths, and actual homogeneous jets. -/
noncomputable section
open Filter Topology Module
open scoped ContDiff BigOperators

namespace FMSA.Paper.MultivariateStrength

open ExactMSA.MultiTailMixture ExactMSA.BSource
variable {N : ℕ} {T : Type*} [Fintype T]

def strengthResidual (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × (TailMatrix T N × TailMatrix T N)) :
    TailMatrix T N × TailMatrix T N := residual z rho sigma p.1 (1, p.2)

theorem strengthResidual_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ) :
    ContDiff ℝ ∞ (strengthResidual z rho sigma) := by
  have he : strengthResidual z rho sigma = fun p =>
      residual z rho sigma 0 (0, p.2) -
        ((fun u i j => 2 * Real.pi * p.1 u i j / z u), 0) := by
    funext p
    apply Prod.ext <;> funext u i j
    all_goals simp [strengthResidual, ExactMSA.MultiTailMixture.residual]
  rw [he]
  apply ContDiff.sub
  · exact (residual_contDiff z rho sigma 0).comp (contDiff_const.prodMk contDiff_snd)
  · apply ContDiff.prodMk
    · apply contDiff_pi.mpr; intro u
      apply contDiff_pi.mpr; intro i
      apply contDiff_pi.mpr; intro j
      change ContDiff ℝ ∞ (fun p : TailMatrix T N × (TailMatrix T N × TailMatrix T N) =>
        2 * Real.pi * entry u i j p.1 / z u)
      have hc : ContDiff ℝ ∞ (fun p : TailMatrix T N × (TailMatrix T N × TailMatrix T N) =>
          entry u i j p.1) := (entry u i j).contDiff.comp contDiff_fst
      simpa only [div_eq_mul_inv] using (contDiff_const.mul hc).mul contDiff_const
    · exact contDiff_const

theorem strengthResidual_zero_slice (z : T → ℝ) (rho sigma : Fin N → ℝ) :
    (fun x => strengthResidual z rho sigma (0, x)) =
      (fun x => residual z rho sigma 0 (0, x)) := by
  funext x
  simp [strengthResidual, ExactMSA.MultiTailMixture.residual]

theorem strengthResidual_partial_eq (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (x : TailMatrix T N × TailMatrix T N) :
    (fderiv ℝ (strengthResidual z rho sigma) (0, x)).comp
        (ContinuousLinearMap.inr ℝ (TailMatrix T N) (TailMatrix T N × TailMatrix T N)) =
      (fderiv ℝ (residual z rho sigma 0) (0, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N)) := by
  have hD := ((strengthResidual_contDiff z rho sigma).contDiffAt.differentiableAt
    (by simp)).hasFDerivAt.comp x
      (ContinuousLinearMap.inr ℝ (TailMatrix T N) (TailMatrix T N × TailMatrix T N)).hasFDerivAt
  have hS := ((residual_contDiff z rho sigma 0).contDiffAt.differentiableAt
    (by simp)).hasFDerivAt.comp x
      (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N)).hasFDerivAt
  change HasFDerivAt (fun y => strengthResidual z rho sigma (0, y)) _ x at hD
  rw [strengthResidual_zero_slice] at hD
  exact hD.unique hS

/-- One multivariate root germ, independent of the ray K. Physical assumptions
discharge its seed equation and amplitude-Jacobian invertibility internally. -/
theorem exists_smooth_strength_root
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hrho : ∀ i, 0 <= rho i) (hsigma : ∀ i, 0 < sigma i) :
    ∃ v : TailMatrix T N → TailMatrix T N × TailMatrix T N,
      v 0 = (0, baseSeed z rho sigma) ∧ ContDiffAt ℝ ∞ v 0 ∧
      ∀ᶠ K in 𝓝 (0 : TailMatrix T N), IsRoot z rho sigma K (v K).1 (v K).2 := by
  let x : TailMatrix T N × TailMatrix T N := (0, baseSeed z rho sigma)
  have hc := (strengthResidual_contDiff z rho sigma).contDiffAt (x := (0, x))
  have hi : ((fderiv ℝ (strengthResidual z rho sigma) (0, x)).comp
      (ContinuousLinearMap.inr ℝ (TailMatrix T N) (TailMatrix T N × TailMatrix T N))).IsInvertible := by
    rw [strengthResidual_partial_eq, residual_partial_triangular]
    exact triangular_isInvertible _ _
      (baseFirst_isUnit_det z rho sigma hz hv hrho hsigma)
      (baseSecond_isUnit_det z rho sigma hz hv hrho hsigma) _
  have hbase : strengthResidual z rho sigma (0, x) = 0 := by
    rw [congrFun (strengthResidual_zero_slice z rho sigma) x]
    exact residual_base z rho sigma 0 (baseSecond_isUnit_det z rho sigma hz hv hrho hsigma)
  refine ⟨hc.implicitFunction (by simp) hi, hc.implicitFunction_apply_self (by simp) hi,
    hc.contDiffAt_implicitFunction (by simp) hi, ?_⟩
  filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with K hK
  rw [← one_smul ℝ K]
  apply (residual_eq_zero_iff z rho sigma K _ _ 1).mp
  simp only [one_smul]
  exact hK.trans hbase

def strengthCoordinates : TailMatrix T N ≃ₗ[ℝ] (T × Fin N × Fin N → ℝ) where
  toFun K h := K h.1 h.2.1 h.2.2
  invFun a u i j := a (u, i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def strengthBasis : Basis (T × Fin N × Fin N) ℝ (TailMatrix T N) :=
  Basis.ofEquivFun strengthCoordinates

/-- For each component and every order, one coefficient table works for all
strength vectors. Every displayed monomial has exactly n strength factors. -/
theorem component_ray_jet_polynomial
    (v : TailMatrix T N → TailMatrix T N × TailMatrix T N)
    (hv : ContDiffAt ℝ ∞ v 0) (n : ℕ) (u : T) (i j : Fin N) :
    ∃ cD cG : (Fin n → T × Fin N × Fin N) → ℝ, ∀ K : TailMatrix T N,
      jet (fun t : ℝ => (v (t • K)).1 u i j) n =
        ∑ h : Fin n → T × Fin N × Fin N, cD h * ∏ k, K (h k).1 (h k).2.1 (h k).2.2 ∧
      jet (fun t : ℝ => (v (t • K)).2 u i j) n =
        ∑ h : Fin n → T × Fin N × Fin N, cG h * ∏ k, K (h k).1 (h k).2.1 (h k).2.2 := by
  have hD : ContDiffAt ℝ n (fun K => (v K).1 u i j) 0 := by
    have hh : ContDiffAt ℝ ∞ (fun K => (v K).1 u i j) 0 := by fun_prop
    exact hh.of_le (by exact_mod_cast le_top)
  have hG : ContDiffAt ℝ n (fun K => (v K).2 u i j) 0 := by
    have hh : ContDiffAt ℝ ∞ (fun K => (v K).2 u i j) 0 := by fun_prop
    exact hh.of_le (by exact_mod_cast le_top)
  obtain ⟨cD, hcD⟩ := HomogeneousJets.ray_jets_are_homogeneous_polynomials strengthBasis _ n hD
  obtain ⟨cG, hcG⟩ := HomogeneousJets.ray_jets_are_homogeneous_polynomials strengthBasis _ n hG
  refine ⟨cD, cG, fun K => ?_⟩
  simpa [strengthBasis, strengthCoordinates] using And.intro (hcD K) (hcG K)

end FMSA.Paper.MultivariateStrength

/-- info: 'FMSA.Paper.MultivariateStrength.strengthResidual_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MultivariateStrength.strengthResidual_contDiff

/-- info: 'FMSA.Paper.MultivariateStrength.strengthResidual_zero_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MultivariateStrength.strengthResidual_zero_slice

/-- info: 'FMSA.Paper.MultivariateStrength.strengthResidual_partial_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MultivariateStrength.strengthResidual_partial_eq

/-- info: 'FMSA.Paper.MultivariateStrength.exists_smooth_strength_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MultivariateStrength.exists_smooth_strength_root

/-- info: 'FMSA.Paper.MultivariateStrength.component_ray_jet_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MultivariateStrength.component_ray_jet_polynomial
