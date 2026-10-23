import LeanCode.YukawaOZMix.MSABSourceHierarchy
import Mathlib

/-! Local multivariate smooth maps have homogeneous polynomial ray jets. -/
noncomputable section
open Filter Topology Module
open scoped ContDiff BigOperators

namespace FMSA.Paper.HomogeneousJets

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A local version of the linear chain rule for arbitrary finite order. -/
theorem iteratedFDeriv_comp_linear_at
    (f : E → F) (g : G →L[ℝ] E) (x : G) (n : ℕ)
    (hf : ContDiffAt ℝ n f (g x)) :
    iteratedFDeriv ℝ n (f ∘ g) x =
      (iteratedFDeriv ℝ n f (g x)).compContinuousLinearMap (fun _ => g) := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  have hgu : IsOpen (g ⁻¹' u) := hu.preimage g.continuous
  have hcomp : ContDiffAt ℝ n (f ∘ g) x := hf.comp x g.contDiff.contDiffAt
  have h := g.iteratedFDerivWithin_comp_right (hfs.mono hus)
    hu.uniqueDiffOn hgu.uniqueDiffOn hxu (le_refl (n : WithTop ℕ∞))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hgu.uniqueDiffOn hcomp hxu,
    iteratedFDerivWithin_eq_iteratedFDeriv hu.uniqueDiffOn hf hxu] at h
  exact h

/-- Normalized derivatives along strength rays are diagonals of a fixed
continuous multilinear map, independent of the chosen strength vector. -/
theorem ray_jet_eq_multilinear
    (f : E → ℝ) (n : ℕ) (hf : ContDiffAt ℝ n f 0) (v : E) :
    ExactMSA.BSource.jet (fun t : ℝ => f (t • v)) n =
      (iteratedFDeriv ℝ n f 0 (fun _ => v)) / (n.factorial : ℝ) := by
  have hf' : ContDiffAt ℝ n f ((ContinuousLinearMap.toSpanSingleton ℝ v) 0) := by
    simpa using hf
  have h := iteratedFDeriv_comp_linear_at f (ContinuousLinearMap.toSpanSingleton ℝ v) 0 n hf'
  have he := congrArg (fun L => L (fun _ => (1 : ℝ))) h
  simpa only [ExactMSA.BSource.jet, iteratedDeriv, Function.comp_def,
    ContinuousLinearMap.toSpanSingleton_apply, zero_smul,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, one_smul] using
    congrArg (fun a : ℝ => a / (n.factorial : ℝ)) he

/-- Expanding a multilinear diagonal in a finite basis gives a finite sum
of monomials of exactly n factors, including n=0. -/
theorem multilinear_diagonal_expansion
    {I : Type*} [Fintype I] (b : Basis I ℝ E) (n : ℕ)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) (v : E) :
    L (fun _ => v) = ∑ h : Fin n → I,
      (∏ k, b.repr v (h k)) * L (fun k => b (h k)) := by
  classical
  have he := L.toMultilinearMap.map_sum (fun (_ : Fin n) i => b.repr v i • b i)
  simpa only [b.sum_repr, MultilinearMap.map_smul_univ, smul_eq_mul,
    ContinuousMultilinearMap.coe_coe] using he

/-- Explicit homogeneous polynomial coefficients for all strength vectors,
stronger than a raywise rescaling identity. -/
theorem ray_jets_are_homogeneous_polynomials
    {I : Type*} [Fintype I] (b : Basis I ℝ E) (f : E → ℝ) (n : ℕ)
    (hf : ContDiffAt ℝ n f 0) :
    ∃ c : (Fin n → I) → ℝ, ∀ v : E,
      ExactMSA.BSource.jet (fun t : ℝ => f (t • v)) n =
        ∑ h : Fin n → I, c h * ∏ k, b.repr v (h k) := by
  classical
  refine ⟨fun h => (iteratedFDeriv ℝ n f 0 (fun k => b (h k))) / (n.factorial : ℝ), ?_⟩
  intro v
  rw [ray_jet_eq_multilinear f n hf v, multilinear_diagonal_expansion b n, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  ring

end FMSA.Paper.HomogeneousJets

/-- info: 'FMSA.Paper.HomogeneousJets.iteratedFDeriv_comp_linear_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.HomogeneousJets.iteratedFDeriv_comp_linear_at

/-- info: 'FMSA.Paper.HomogeneousJets.ray_jet_eq_multilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.HomogeneousJets.ray_jet_eq_multilinear

/-- info: 'FMSA.Paper.HomogeneousJets.multilinear_diagonal_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.HomogeneousJets.multilinear_diagonal_expansion

/-- info: 'FMSA.Paper.HomogeneousJets.ray_jets_are_homogeneous_polynomials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.HomogeneousJets.ray_jets_are_homogeneous_polynomials
