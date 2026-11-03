import MSAConvergence.ComplexRectangularCoordinates
import MSAConvergence.ComplexPolynomialSystem
import MSAConvergence.ParametricContraction

/-! Constructing continuous regular complex polynomial root lifts on exact
componentwise rectangles from verified Newton self-maps and true row bounds. -/
noncomputable section
namespace FMSA.Convergence.ComplexRectangleNewton
open FMSA.Convergence.ComplexRectangularCoordinates
open FMSA.Convergence.ComplexPolynomialSystem
open FMSA.Convergence.ParametricContraction
open Filter Topology Set
open scoped BigOperators
variable {I : Type*} [Fintype I]
local instance : DecidableEq I := Classical.decEq _

/-- The matrix used by a root-box certificate is the genuine complex
amplitude derivative of the exact polynomial system. -/
theorem polynomial_amplitude_hasFDerivAt
    (F : I → MvPolynomial (Option I) ℝ) (t : ℂ) (z : I → ℂ) :
    HasFDerivAt (fun a => complexResidual F (t,a))
      (Matrix.toLin' (complexJacobian F (t,z))).toContinuousLinearMap z := by
  have hR := (complexResidual_analyticAt F (t,z)).differentiableAt.hasFDerivAt
  have hline : HasFDerivAt (fun w : I → ℂ => (t,w))
      (ContinuousLinearMap.inr ℂ ℂ (I → ℂ)) z := by
    convert! (hasFDerivAt_const (𝕜 := ℂ) t z).prodMk (hasFDerivAt_id (𝕜 := ℂ) z) using 1
  have hp := hR.comp z hline
  have heq : complexPartial F (t,z) =
      (Matrix.toLin' (complexJacobian F (t,z))).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro h
    exact (complex_partial_mulVec F (t,z) h).symm
  change HasFDerivAt (fun a => complexResidual F (t,a)) (complexPartial F (t,z)) z at hp
  rw [heq] at hp
  exact hp

section Defect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A strict Newton derivative defect proves injectivity of the true
Jacobian without a supplied inverse or finite-dimensional assumption. -/
theorem jacobian_injective_of_defect (L J : E →L[ℝ] E)
    (hdef : ‖ContinuousLinearMap.id ℝ E - L.comp J‖ < 1) : Function.Injective J := by
  intro x y hxy
  have hj : J (x-y)=0 := by simp [map_sub,hxy]
  have hb := (ContinuousLinearMap.id ℝ E - L.comp J).le_opNorm (x-y)
  change ‖(x-y)-L (J (x-y))‖ ≤ ‖ContinuousLinearMap.id ℝ E - L.comp J‖*‖x-y‖ at hb
  rw [hj,map_zero,sub_zero] at hb
  have hn : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end Defect

/-- Rectangle-coordinate defect bounds prove the ORIGINAL complex matrix
regular, internally; no complex or real inverse premise is given. -/
theorem complex_det_ne_zero_of_rectangle_defect
    (w : Bool × I → ℝ) (hw : ∀ j, w j ≠ 0) (C J : Matrix I I ℂ)
    (q : ℝ) (hq : q < 1) (hq0 : 0 ≤ q)
    (hrow : ∀ i, ∑ j, |normalizedRealMatrix w (1 - C * J) i j| ≤ q) : J.det ≠ 0 := by
  have hdef := (normalized_newton_defect_opNorm_le w hw C J q hq0 hrow).trans_lt hq
  have hi := jacobian_injective_of_defect _ _ hdef
  have hJ : Function.Injective (Matrix.mulVec J) := by
    intro a b hab
    apply (normalizedCoordinates w hw).injective
    apply hi
    change normalizedCoordinates w hw
      (Matrix.mulVec J ((normalizedCoordinates w hw).symm (normalizedCoordinates w hw a))) =
      normalizedCoordinates w hw
        (Matrix.mulVec J ((normalizedCoordinates w hw).symm (normalizedCoordinates w hw b)))
    simpa only [(normalizedCoordinates w hw).symm_apply_apply] using
      congrArg (normalizedCoordinates w hw) hab
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det J).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hJ))


variable {S : Type*} [TopologicalSpace S]

/-- Verified whole-rectangle Newton self-maps and true weighted row defects
CONSTRUCT a continuous unique REGULAR polynomial root lift. No root curve,
root continuity, determinant witness, complex germ or inverse is supplied. -/
theorem exists_continuous_regular_polynomial_lift_on_rectangle
    (F : I → MvPolynomial (Option I) ℝ) (gamma : S → ℂ) (hgamma : Continuous gamma)
    (c : I → ℂ) (w : Bool × I → ℝ) (hw : ∀ j, 0 < w j) (C : Matrix I I ℂ)
    (q : NNReal) (hq : q < 1)
    (hrow : ∀ s z,
      normalizedCoordinates w (fun j => (hw j).ne') (z - c) ∈ Metric.closedBall 0 1 →
      ∀ i, ∑ j, |normalizedRealMatrix w (1 - C * complexJacobian F (gamma s, z)) i j| ≤ (q : ℝ))
    (hmap : ∀ s z,
      normalizedCoordinates w (fun j => (hw j).ne') (z - c) ∈ Metric.closedBall 0 1 →
      normalizedCoordinates w (fun j => (hw j).ne')
        (z - Matrix.mulVec C (complexResidual F (gamma s, z)) - c) ∈ Metric.closedBall 0 1) :
    ∃ p : S → (I → ℂ), Continuous p ∧ ∀ s,
      normalizedCoordinates w (fun j => (hw j).ne') (p s-c) ∈ Metric.closedBall 0 1 ∧
      complexResidual F (gamma s, p s)=0 ∧ (complexJacobian F (gamma s, p s)).det ≠ 0 ∧
      ∀ z, normalizedCoordinates w (fun j => (hw j).ne') (z - c) ∈ Metric.closedBall 0 1 →
        complexResidual F (gamma s, z)=0 → z=p s := by
  let e := normalizedCoordinates w (fun j => (hw j).ne')
  let L := normalizedConjugate w (fun j => (hw j).ne') (Matrix.toLin' C).toContinuousLinearMap
  let f : S → (Bool × I → ℝ) → (Bool × I → ℝ) :=
    fun s x => e (complexResidual F (gamma s,c+e.symm x))
  let J : S → (Bool × I → ℝ) → (Bool × I → ℝ) →L[ℝ] (Bool × I → ℝ) :=
    fun s x => normalizedConjugate w (fun j => (hw j).ne')
      (Matrix.toLin' (complexJacobian F (gamma s,c+e.symm x))).toContinuousLinearMap
  have hchart (x : Bool × I → ℝ) : e ((c+e.symm x)-c)=x := by
    rw [add_sub_cancel_left,e.apply_symm_apply]
  have hf s x (_hx : x ∈ Metric.closedBall (0 : Bool × I → ℝ) 1) :
      HasFDerivAt (f s) (J s x) x :=
    normalized_hasFDerivAt w (fun j => (hw j).ne')
      (fun a => complexResidual F (gamma s,a))
      (Matrix.toLin' (complexJacobian F (gamma s,c+e.symm x))).toContinuousLinearMap c x
      (polynomial_amplitude_hasFDerivAt F (gamma s) (c+e.symm x))
  have hdef s x (hx : x ∈ Metric.closedBall (0 : Bool × I → ℝ) 1) :
      ‖ContinuousLinearMap.id ℝ (Bool × I → ℝ)-L.comp (J s x)‖ ≤ (q : ℝ) := by
    apply normalized_newton_defect_opNorm_le w (fun j => (hw j).ne') C
      (complexJacobian F (gamma s,c+e.symm x)) (q : ℝ) q.property
    exact hrow s (c+e.symm x) (by change e ((c+e.symm x)-c) ∈ _; rw [hchart]; exact hx)
  have hself s : Set.MapsTo (newtonMap L (f s)) (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
    intro x hx
    change x - L (f s x) ∈ Metric.closedBall 0 1
    rw [← normalized_newton_map_eq w (fun j => (hw j).ne') C
      (fun a => complexResidual F (gamma s,a)) c x]
    exact hmap s (c+e.symm x) (by change e ((c+e.symm x)-c) ∈ _; rw [hchart]; exact hx)
  have hRcont : Continuous (complexResidual F) :=
    continuous_iff_continuousAt.mpr fun z => (complexResidual_analyticAt F z).continuousAt
  have hcont x (_hx : x ∈ Metric.closedBall (0 : Bool × I → ℝ) 1) :
      Continuous (fun s => f s x) :=
    e.continuous.comp (hRcont.comp (hgamma.prodMk continuous_const))
  obtain ⟨a,hac,ha⟩ := exists_continuous_newton_root_family_of_mapsTo
    (0 : Bool × I → ℝ) 1 (by norm_num) q hq L f J hf hdef hself hcont
  let p : S → (I → ℂ) := fun s => c+e.symm (a s)
  have hpc : Continuous p := continuous_const.add (e.symm.continuous.comp hac)
  refine ⟨p,hpc,?_⟩
  intro s
  have hbox : e (p s-c) ∈ Metric.closedBall 0 1 := by
    change e ((c+e.symm (a s)) - c) ∈ _
    rw [hchart]
    exact (ha s).1
  have hroot : complexResidual F (gamma s, p s)=0 := by
    apply e.injective
    simpa only [map_zero] using (ha s).2.1
  have hdet : (complexJacobian F (gamma s, p s)).det ≠ 0 :=
    complex_det_ne_zero_of_rectangle_defect w (fun j => (hw j).ne') C _ (q : ℝ)
      (by exact_mod_cast hq) q.property (hrow s (p s) hbox)
  refine ⟨hbox,hroot,hdet,?_⟩
  intro z hz hzr
  have hzid : c+e.symm (e (z - c))=z := by rw [e.symm_apply_apply]; abel
  have hzf : f s (e (z - c))=0 := by
    change e (complexResidual F (gamma s,c+e.symm (e (z - c))))=0
    rw [hzid,hzr,map_zero]
  have heq := (ha s).2.2 (e (z - c)) hz hzf
  have hzc : z-c=e.symm (a s) := by
    simpa only [e.symm_apply_apply] using congrArg e.symm heq
  change z=c+e.symm (a s)
  calc
    z = (z - c)+c := (sub_add_cancel z c).symm
    _ = e.symm (a s)+c := congrArg (fun v => v+c) hzc
    _ = c+e.symm (a s) := add_comm _ _

end FMSA.Convergence.ComplexRectangleNewton

/-- info: 'FMSA.Convergence.ComplexRectangleNewton.polynomial_amplitude_hasFDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangleNewton.polynomial_amplitude_hasFDerivAt
/-- info: 'FMSA.Convergence.ComplexRectangleNewton.jacobian_injective_of_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangleNewton.jacobian_injective_of_defect
/-- info: 'FMSA.Convergence.ComplexRectangleNewton.complex_det_ne_zero_of_rectangle_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangleNewton.complex_det_ne_zero_of_rectangle_defect
/-- info: 'FMSA.Convergence.ComplexRectangleNewton.exists_continuous_regular_polynomial_lift_on_rectangle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexRectangleNewton.exists_continuous_regular_polynomial_lift_on_rectangle
