import Mathlib

/-!
# A transverse fold cannot admit a differentiable root continuation

This is the local analytic obstruction needed by F2. It does not assume or
prove a square-root normal form. The power-series identification and radius
comparison are separate obligations.
-/
noncomputable section
open Filter Topology

namespace FMSA.Paper.Fold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiating an actual local root curve forces the coupling derivative
of the residual into the range of the amplitude Jacobian. -/
theorem coupling_derivative_mem_range
    (R : ℝ × E → F) (L : (ℝ × E) →L[ℝ] F) (u : ℝ → E) (v : E) (t : ℝ)
    (hR : HasFDerivAt R L (t, u t)) (hu : HasDerivAt u v t)
    (hroot : (fun s => R (s, u s)) =ᶠ[𝓝 t] (fun _ => 0)) :
    L (1, 0) ∈ Set.range (fun w : E => L (0, w)) := by
  have hd := hR.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hu)
  have hz : L (1, v) = 0 :=
    (hd.congr_of_eventuallyEq hroot.symm).unique (hasDerivAt_const t (0 : F))
  refine ⟨-v, ?_⟩
  have hsplit : L (1, v) = L (1, 0) + L (0, v) := by
    rw [← map_add]
    simp
  have hneg : L (0, -v) = -L (0, v) := by
    simpa only [Prod.neg_mk, neg_zero] using L.map_neg (0, v)
  change L (0, -v) = L (1, 0)
  rw [hneg]
  rw [hsplit] at hz
  exact (eq_neg_of_add_eq_zero_left hz).symm

/-- The range transversality condition rules out even a differentiable root
curve, and therefore rules out a real-analytic continuation through the fold. -/
theorem not_differentiable_root
    (R : ℝ × E → F) (L : (ℝ × E) →L[ℝ] F) (u : ℝ → E) (t : ℝ)
    (hR : HasFDerivAt R L (t, u t))
    (htransverse : L (1, 0) ∉ Set.range (fun w : E => L (0, w)))
    (hroot : (fun s => R (s, u s)) =ᶠ[𝓝 t] (fun _ => 0)) :
    ¬ DifferentiableAt ℝ u t := by
  intro hu
  exact htransverse (coupling_derivative_mem_range R L u (deriv u t) t hR
    hu.hasDerivAt hroot)

theorem not_analytic_root
    (R : ℝ × E → F) (L : (ℝ × E) →L[ℝ] F) (u : ℝ → E) (t : ℝ)
    (hR : HasFDerivAt R L (t, u t))
    (htransverse : L (1, 0) ∉ Set.range (fun w : E => L (0, w)))
    (hroot : (fun s => R (s, u s)) =ᶠ[𝓝 t] (fun _ => 0)) :
    ¬ AnalyticAt ℝ u t := by
  intro hu
  exact not_differentiable_root R L u t hR htransverse hroot hu.differentiableAt

end FMSA.Paper.Fold

/-! Axiom-footprint gates for every theorem in this extension module. -/

/-- info: 'FMSA.Paper.Fold.coupling_derivative_mem_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Fold.coupling_derivative_mem_range

/-- info: 'FMSA.Paper.Fold.not_differentiable_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Fold.not_differentiable_root

/-- info: 'FMSA.Paper.Fold.not_analytic_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.Fold.not_analytic_root
