import FMSAPaper.FoldObstruction

/-! Uniqueness along a regular real root branch and the obstruction at its fold. -/
noncomputable section
open Filter Topology
open scoped ContDiff

namespace FMSA.Paper.RegularContinuation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Continuous roots which agree once agree on a connected parameter set as
long as the amplitude derivative along the first root stays invertible.
Continuity and invertibility are relative to the set; endpoints are allowed. -/
theorem roots_eqOn_of_preconnected
    (R : ℝ × E → E) (p q : ℝ → E) (s : Set ℝ) (t0 : ℝ)
    (hs : IsPreconnected s) (ht0 : t0 ∈ s)
    (hp : ContinuousOn p s) (hq : ContinuousOn q s) (heq : p t0 = q t0)
    (hpr : ∀ t ∈ s, R (t, p t) = 0) (hqr : ∀ t ∈ s, R (t, q t) = 0)
    (hR : ∀ t ∈ s, ContDiffAt ℝ ∞ R (t, p t))
    (hinv : ∀ t ∈ s,
      ((fderiv ℝ R (t, p t)).comp (ContinuousLinearMap.inr ℝ ℝ E)).IsInvertible) :
    Set.EqOn p q s := by
  letI : PreconnectedSpace s := Subtype.preconnectedSpace hs
  let A : Set s := {t | p t = q t}
  have hc : IsClosed A := isClosed_eq hp.restrict hq.restrict
  have ho : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hu := (hR t t.property).eventually_apply_eq_iff_implicitFunction
      (by simp) (hinv t t.property)
    have htp : Tendsto (fun v : s => ((v : ℝ), p v)) (𝓝 t) (𝓝 ((t : ℝ), p t)) :=
      (continuous_subtype_val.prodMk hp.restrict).continuousAt.tendsto
    have htq : Tendsto (fun v : s => ((v : ℝ), q v)) (𝓝 t) (𝓝 ((t : ℝ), p t)) := by
      simpa only [show p t = q t from ht, Set.restrict_apply] using
        (continuous_subtype_val.prodMk hq.restrict).continuousAt.tendsto (x := t)
    filter_upwards [htp.eventually hu, htq.eventually hu] with v hP hQ
    exact (hP.mp ((hpr v v.property).trans (hpr t t.property).symm)).symm.trans
      (hQ.mp ((hqr v v.property).trans (hpr t t.property).symm))
  have hall : A = Set.univ := (show IsClopen A from ⟨hc, ho⟩).eq_univ ⟨⟨t0, ht0⟩, heq⟩
  intro t ht
  have hm : (⟨t, ht⟩ : s) ∈ A := by rw [hall]; trivial
  exact hm

/-- Equality on the regular half-open branch determines its limiting fold
state by continuity. No uniqueness is assumed at the singular endpoint. -/
theorem roots_eq_at_endpoint
    (R : ℝ × E → E) (p q : ℝ → E) (f : ℝ) (hf : 0 < f)
    (hp : ContinuousOn p (Set.Icc 0 f)) (hq : ContinuousOn q (Set.Icc 0 f))
    (heq : p 0 = q 0)
    (hpr : ∀ t ∈ Set.Ico 0 f, R (t, p t) = 0)
    (hqr : ∀ t ∈ Set.Ico 0 f, R (t, q t) = 0)
    (hR : ∀ t ∈ Set.Ico 0 f, ContDiffAt ℝ ∞ R (t, p t))
    (hinv : ∀ t ∈ Set.Ico 0 f,
      ((fderiv ℝ R (t, p t)).comp (ContinuousLinearMap.inr ℝ ℝ E)).IsInvertible) :
    p f = q f := by
  have he := roots_eqOn_of_preconnected R p q (Set.Ico 0 f) 0
    (convex_Ico 0 f).isPreconnected ⟨le_rfl, hf⟩
    (hp.mono Set.Ico_subset_Icc_self) (hq.mono Set.Ico_subset_Icc_self) heq hpr hqr hR hinv
  have hclosure : closure (Set.Ico 0 f) = Set.Icc 0 f := closure_Ico hf.ne
  exact he.of_subset_closure hp hq Set.Ico_subset_Icc_self
    (by rw [hclosure]) ⟨hf.le, le_rfl⟩

/-- A differentiable root candidate through a transverse fold cannot start
on the same seed and follow a continuous branch regular before the fold. -/
theorem no_differentiable_extension
    (R : ℝ × E → E) (p q : ℝ → E) (f : ℝ) (hf : 0 < f)
    (hp : ContinuousOn p (Set.Icc 0 f)) (hq : ContinuousOn q (Set.Icc 0 f))
    (heq : p 0 = q 0)
    (hpr : ∀ t ∈ Set.Ico 0 f, R (t, p t) = 0)
    (hqr : ∀ t ∈ Set.Ico 0 f, R (t, q t) = 0)
    (hR : ∀ t ∈ Set.Ico 0 f, ContDiffAt ℝ ∞ R (t, p t))
    (hinv : ∀ t ∈ Set.Ico 0 f,
      ((fderiv ℝ R (t, p t)).comp (ContinuousLinearMap.inr ℝ ℝ E)).IsInvertible)
    (L : (ℝ × E) →L[ℝ] E) (hL : HasFDerivAt R L (f, p f))
    (htransverse : L (1, 0) ∉ Set.range (fun w : E => L (0, w)))
    (hqroot : (fun t => R (t, q t)) =ᶠ[𝓝 f] (fun _ => 0)) :
    ¬ DifferentiableAt ℝ q f := by
  have hmatch := roots_eq_at_endpoint R p q f hf hp hq heq hpr hqr hR hinv
  rw [hmatch] at hL
  exact Fold.not_differentiable_root R L q f hL htransverse hqroot

end FMSA.Paper.RegularContinuation

/-- info: 'FMSA.Paper.RegularContinuation.roots_eqOn_of_preconnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RegularContinuation.roots_eqOn_of_preconnected

/-- info: 'FMSA.Paper.RegularContinuation.roots_eq_at_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RegularContinuation.roots_eq_at_endpoint

/-- info: 'FMSA.Paper.RegularContinuation.no_differentiable_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RegularContinuation.no_differentiable_extension
