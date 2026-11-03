import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Continuous root lifts constructed from uniformly contracting families.
This removes a supplied continuity assumption from future interval-Newton
path certificates. The family is continuous only pointwise in the parameter. -/
noncomputable section
open Filter Topology
namespace FMSA.Convergence.ParametricContraction
variable {S X : Type*} [TopologicalSpace S] [MetricSpace X] [CompleteSpace X] [Nonempty X]

def parameterFixed (q : NNReal) (T : S → X → X) (hT : ∀ s, ContractingWith q (T s)) (s : S) : X :=
  ContractingWith.fixedPoint (T s) (hT s)

omit [TopologicalSpace S] in
/-- The parameter family constructs a genuine fixed point at EVERY parameter. -/
theorem parameterFixed_isFixedPt (q : NNReal) (T : S → X → X)
    (hT : ∀ s, ContractingWith q (T s)) (s : S) :
    T s (parameterFixed q T hT s)=parameterFixed q T hT s :=
  ContractingWith.fixedPoint_isFixedPt (hT s)

omit [TopologicalSpace S] in
/-- Uniqueness is supplied by the contraction, not by a presumed branch. -/
theorem parameterFixed_unique (q : NNReal) (T : S → X → X)
    (hT : ∀ s, ContractingWith q (T s)) (s : S) (x : X) (hx : T s x=x) :
    x=parameterFixed q T hT s :=
  ContractingWith.fixedPoint_unique (hT s) hx

omit [TopologicalSpace S] in
/-- The two constructed fixed points are controlled by a difference of the
maps at ONE fixed point; a uniform supremum over all x is not required. -/
theorem parameterFixed_dist_le (q : NNReal) (T : S → X → X)
    (hT : ∀ s, ContractingWith q (T s)) (s t : S) :
    dist (parameterFixed q T hT s) (parameterFixed q T hT t)≤
      dist (T s (parameterFixed q T hT t)) (T t (parameterFixed q T hT t))/(1-(q : ℝ)) := by
  have h := ContractingWith.dist_fixedPoint_le (hT s) (parameterFixed q T hT t)
  calc
    _ = dist (parameterFixed q T hT t) (parameterFixed q T hT s) := dist_comm _ _
    _ ≤ dist (parameterFixed q T hT t) (T s (parameterFixed q T hT t))/(1-(q : ℝ)) := h
    _ = _ := by rw [parameterFixed_isFixedPt q T hT t]; rw [dist_comm]

/-- Pointwise parameter continuity plus one uniform contraction coefficient
CONSTRUCTS a continuous fixed-point lift on the entire parameter space. -/
theorem parameterFixed_continuous (q : NNReal) (T : S → X → X)
    (hT : ∀ s, ContractingWith q (T s))
    (hcont : ∀ x, Continuous (fun s => T s x)) : Continuous (parameterFixed q T hT) := by
  rw [continuous_iff_continuousAt]
  intro t
  change Tendsto (parameterFixed q T hT) (𝓝 t) (𝓝 (parameterFixed q T hT t))
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hq : (q : ℝ)<1 := (hT t).1
  have hden : 0<1-(q : ℝ) := sub_pos.mpr hq
  have hsmall : ∀ᶠ s in 𝓝 t,
      dist (T s (parameterFixed q T hT t)) (T t (parameterFixed q T hT t))<epsilon*(1-(q : ℝ)) :=
    Metric.tendsto_nhds.mp (hcont (parameterFixed q T hT t)).continuousAt.tendsto _ (mul_pos hepsilon hden)
  filter_upwards [hsmall] with s hs
  exact lt_of_le_of_lt (parameterFixed_dist_le q T hT s t) ((div_lt_iff₀ hden).mpr hs)

section Newton
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def newtonMap (L : E →L[ℝ] E) (f : E → E) (x : E) : E := x-L (f x)

/-- True derivative defect bounds imply the Newton map is Lipschitz on the
whole closed ball. No pointwise-only or sampled derivative estimate is used. -/
theorem newton_lipschitzOn_closedBall
    (c : E) (r : ℝ) (q : NNReal) (L : E →L[ℝ] E) (f : E → E) (J : E → E →L[ℝ] E)
    (hf : ∀ x ∈ Metric.closedBall c r, HasFDerivAt f (J x) x)
    (hdef : ∀ x ∈ Metric.closedBall c r, ‖ContinuousLinearMap.id ℝ E-L.comp (J x)‖≤(q : ℝ)) :
    LipschitzOnWith q (newtonMap L f) (Metric.closedBall c r) := by
  have hd x (hx : x ∈ Metric.closedBall c r) :
      HasFDerivAt (newtonMap L f) (ContinuousLinearMap.id ℝ E-L.comp (J x)) x :=
    (hasFDerivAt_id x).sub (L.hasFDerivAt.comp x (hf x hx))
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hd x hx).hasFDerivWithinAt) hdef (convex_closedBall c r) hy hx

private theorem newton_mapsTo_closedBall
    (c : E) (r : ℝ) (hr : 0≤r) (q : NNReal) (L : E →L[ℝ] E) (f : E → E)
    (hlip : LipschitzOnWith q (newtonMap L f) (Metric.closedBall c r))
    (hcenter : ‖L (f c)‖≤(1-(q : ℝ))*r) :
    Set.MapsTo (newtonMap L f) (Metric.closedBall c r) (Metric.closedBall c r) := by
  have hc : c ∈ Metric.closedBall c r := Metric.mem_closedBall_self hr
  have hGc : ‖newtonMap L f c-c‖=‖L (f c)‖ := by
    rw [newtonMap,sub_sub_cancel_left,norm_neg]
  intro x hx
  have hrad : ‖x-c‖≤r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
  have hb : ‖newtonMap L f x-c‖≤r := by
    calc
      _ = ‖(newtonMap L f x-newtonMap L f c)+(newtonMap L f c-c)‖ := by congr 1; abel
      _ ≤ ‖newtonMap L f x-newtonMap L f c‖+‖newtonMap L f c-c‖ := norm_add_le _ _
      _ ≤ (q : ℝ)*‖x-c‖+‖L (f c)‖ := add_le_add
        ((lipschitzOnWith_iff_norm_sub_le.mp hlip) hx hc) hGc.le
      _ ≤ (q : ℝ)*r+(1-(q : ℝ))*r := add_le_add (mul_le_mul_of_nonneg_left hrad q.property) hcenter
      _ = r := by ring
  simpa only [Metric.mem_closedBall,dist_eq_norm] using hb

/-- In FINITE dimension the Newton defect itself proves injectivity of the
preconditioner. No preconditioner inverse is supplied. -/
theorem preconditioner_injective_of_defect [FiniteDimensional ℝ E]
    (L J : E →L[ℝ] E) (hdef : ‖ContinuousLinearMap.id ℝ E-L.comp J‖<1) :
    Function.Injective L := by
  have hz (x : E) (hx : L (J x)=0) : x=0 := by
    have hb := (ContinuousLinearMap.id ℝ E-L.comp J).le_opNorm x
    change ‖x-L (J x)‖≤‖ContinuousLinearMap.id ℝ E-L.comp J‖*‖x‖ at hb
    rw [hx,sub_zero] at hb
    have hn : ‖x‖=0 := by
      by_contra h
      have hp : 0<‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm h)
      have ht := mul_lt_mul_of_pos_right hdef hp
      nlinarith
    exact norm_eq_zero.mp hn
  have hi : Function.Injective (L.comp J) := by
    intro x y hxy
    have hh : L (J (x-y))=0 := by simpa only [ContinuousLinearMap.comp_apply,map_sub,sub_eq_zero] using hxy
    exact sub_eq_zero.mp (hz (x-y) hh)
  have hs : Function.Surjective (L.comp J) := LinearMap.injective_iff_surjective.mp hi
  have hLs : Function.Surjective L := by
    intro y
    obtain ⟨x,hx⟩ := hs y
    exact ⟨J x,hx⟩
  exact LinearMap.injective_iff_surjective.mpr hLs

/-- A closed-ball Newton certificate CONSTRUCTS its unique root from true
derivatives, uniform defects and the center residual. No root/inverse given. -/
theorem exists_unique_newton_root_closedBall [FiniteDimensional ℝ E]
    (c : E) (r : ℝ) (hr : 0≤r) (q : NNReal) (hq : q<1)
    (L : E →L[ℝ] E) (f : E → E) (J : E → E →L[ℝ] E)
    (hf : ∀ x ∈ Metric.closedBall c r, HasFDerivAt f (J x) x)
    (hdef : ∀ x ∈ Metric.closedBall c r, ‖ContinuousLinearMap.id ℝ E-L.comp (J x)‖≤(q : ℝ))
    (hcenter : ‖L (f c)‖≤(1-(q : ℝ))*r) :
    ∃! x : E, x ∈ Metric.closedBall c r ∧ f x=0 := by
  let B := Metric.closedBall c r
  let G := newtonMap L f
  have hc : c ∈ B := Metric.mem_closedBall_self hr
  have hlip := newton_lipschitzOn_closedBall c r q L f J hf hdef
  have hmap : Set.MapsTo G B B := newton_mapsTo_closedBall c r hr q L f hlip hcenter
  have hctr : ContractingWith q (hmap.restrict G B B) := ⟨hq,fun x y => hlip x.property y.property⟩
  obtain ⟨x,hx,hfix,_,_⟩ := ContractingWith.exists_fixedPoint'
    ((Metric.isClosed_closedBall : IsClosed B).isComplete : IsComplete B) hmap hctr hc (edist_ne_top _ _)
  have hqR : (q : ℝ)<1 := by exact_mod_cast hq
  have hL := preconditioner_injective_of_defect L (J c) ((hdef c hc).trans_lt hqR)
  have hfx : f x=0 := by
    apply hL
    have hh : L (f x)=0 := sub_eq_self.mp hfix
    simpa only [map_zero] using hh
  refine ⟨x,⟨hx,hfx⟩,?_⟩
  intro y hy
  have hfy : G y=y := by simp [G,newtonMap,hy.2]
  have hn := (lipschitzOnWith_iff_norm_sub_le.mp hlip) hy.1 hx
  change ‖G y-G x‖≤(q : ℝ)*‖y-x‖ at hn
  rw [hfy,hfix] at hn
  have hzero : ‖y-x‖=0 := by
    by_contra h
    have hp : 0<‖y-x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    have ht := mul_lt_mul_of_pos_right hqR hp
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Uniform whole-ball Newton bounds and parameter continuity CONSTRUCT a
continuous family of unique honest roots. No branch, root, inverse or root
continuity is a hypothesis. -/
theorem exists_continuous_newton_root_family [FiniteDimensional ℝ E]
    (c : E) (r : ℝ) (hr : 0≤r) (q : NNReal) (hq : q<1) (L : E →L[ℝ] E)
    (f : S → E → E) (J : S → E → E →L[ℝ] E)
    (hf : ∀ s x, x ∈ Metric.closedBall c r → HasFDerivAt (f s) (J s x) x)
    (hdef : ∀ s x, x ∈ Metric.closedBall c r → ‖ContinuousLinearMap.id ℝ E-L.comp (J s x)‖≤(q : ℝ))
    (hcenter : ∀ s, ‖L (f s c)‖≤(1-(q : ℝ))*r)
    (hcont : ∀ x ∈ Metric.closedBall c r, Continuous (fun s => f s x)) :
    ∃ p : S → E, Continuous p ∧ ∀ s, p s ∈ Metric.closedBall c r ∧ f s (p s)=0 ∧
      ∀ x ∈ Metric.closedBall c r, f s x=0 → x=p s := by
  let B := Metric.closedBall c r
  have hc : c ∈ B := Metric.mem_closedBall_self hr
  letI : Nonempty B := ⟨⟨c,hc⟩⟩
  letI : CompleteSpace B := ((Metric.isClosed_closedBall : IsClosed B).isComplete : IsComplete B).completeSpace_coe
  have hlip s := newton_lipschitzOn_closedBall c r q L (f s) (J s) (hf s) (hdef s)
  have hmap s : Set.MapsTo (newtonMap L (f s)) B B :=
    newton_mapsTo_closedBall c r hr q L (f s) (hlip s) (hcenter s)
  let T : S → B → B := fun s => (hmap s).restrict (newtonMap L (f s)) B B
  have hT s : ContractingWith q (T s) := ⟨hq,fun x y => hlip s x.property y.property⟩
  have hTc (x : B) : Continuous (fun s => T s x) := by
    apply Continuous.subtype_mk
    exact continuous_const.sub (L.continuous.comp (hcont x.val x.property))
  let p : S → E := fun s => (parameterFixed q T hT s).val
  have hpc : Continuous p := continuous_subtype_val.comp (parameterFixed_continuous q T hT hTc)
  refine ⟨p,hpc,fun s => ⟨(parameterFixed q T hT s).property,?_,?_⟩⟩
  · have hfix : newtonMap L (f s) (p s)=p s :=
      congrArg Subtype.val (parameterFixed_isFixedPt q T hT s)
    have hqR : (q : ℝ)<1 := by exact_mod_cast hq
    have hL := preconditioner_injective_of_defect L (J s c) ((hdef s c hc).trans_lt hqR)
    apply hL
    have hh : L (f s (p s))=0 := sub_eq_self.mp hfix
    simpa only [map_zero] using hh
  · intro x hx hfx
    have hfix : T s ⟨x,hx⟩=⟨x,hx⟩ := by
      apply Subtype.ext
      simp [T,newtonMap,hfx]
    exact congrArg Subtype.val (parameterFixed_unique q T hT s ⟨x,hx⟩ hfix)

/-- A directly certified Newton self-map can replace the scalar center
budget. This retains componentwise interval/Krawczyk cancellations and still
CONSTRUCTS continuous unique roots without a supplied root branch. -/
theorem exists_continuous_newton_root_family_of_mapsTo [FiniteDimensional ℝ E]
    (c : E) (r : ℝ) (hr : 0≤r) (q : NNReal) (hq : q<1) (L : E →L[ℝ] E)
    (f : S → E → E) (J : S → E → E →L[ℝ] E)
    (hf : ∀ s x, x ∈ Metric.closedBall c r → HasFDerivAt (f s) (J s x) x)
    (hdef : ∀ s x, x ∈ Metric.closedBall c r → ‖ContinuousLinearMap.id ℝ E-L.comp (J s x)‖≤(q : ℝ))
    (hmap : ∀ s, Set.MapsTo (newtonMap L (f s)) (Metric.closedBall c r) (Metric.closedBall c r))
    (hcont : ∀ x ∈ Metric.closedBall c r, Continuous (fun s => f s x)) :
    ∃ p : S → E, Continuous p ∧ ∀ s, p s ∈ Metric.closedBall c r ∧ f s (p s)=0 ∧
      ∀ x ∈ Metric.closedBall c r, f s x=0 → x=p s := by
  let B := Metric.closedBall c r
  have hc : c ∈ B := Metric.mem_closedBall_self hr
  letI : Nonempty B := ⟨⟨c,hc⟩⟩
  letI : CompleteSpace B := ((Metric.isClosed_closedBall : IsClosed B).isComplete : IsComplete B).completeSpace_coe
  have hlip s := newton_lipschitzOn_closedBall c r q L (f s) (J s) (hf s) (hdef s)
  let T : S → B → B := fun s => (hmap s).restrict (newtonMap L (f s)) B B
  have hT s : ContractingWith q (T s) := ⟨hq,fun x y => hlip s x.property y.property⟩
  have hTc (x : B) : Continuous (fun s => T s x) := by
    apply Continuous.subtype_mk
    exact continuous_const.sub (L.continuous.comp (hcont x.val x.property))
  let p : S → E := fun s => (parameterFixed q T hT s).val
  have hpc : Continuous p := continuous_subtype_val.comp (parameterFixed_continuous q T hT hTc)
  refine ⟨p,hpc,fun s => ⟨(parameterFixed q T hT s).property,?_,?_⟩⟩
  · have hfix : newtonMap L (f s) (p s)=p s :=
      congrArg Subtype.val (parameterFixed_isFixedPt q T hT s)
    have hqR : (q : ℝ)<1 := by exact_mod_cast hq
    have hL := preconditioner_injective_of_defect L (J s c) ((hdef s c hc).trans_lt hqR)
    apply hL
    have hh : L (f s (p s))=0 := sub_eq_self.mp hfix
    simpa only [map_zero] using hh
  · intro x hx hfx
    have hfix : T s ⟨x,hx⟩=⟨x,hx⟩ := by
      apply Subtype.ext
      simp [T,newtonMap,hfx]
    exact congrArg Subtype.val (parameterFixed_unique q T hT s ⟨x,hx⟩ hfix)

end Newton
/-- info: 'FMSA.Convergence.ParametricContraction.parameterFixed_isFixedPt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ParametricContraction.parameterFixed_isFixedPt
/-- info: 'FMSA.Convergence.ParametricContraction.parameterFixed_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ParametricContraction.parameterFixed_unique
/-- info: 'FMSA.Convergence.ParametricContraction.parameterFixed_dist_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ParametricContraction.parameterFixed_dist_le
/-- info: 'FMSA.Convergence.ParametricContraction.parameterFixed_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ParametricContraction.parameterFixed_continuous
/-- info: 'FMSA.Convergence.ParametricContraction.newton_lipschitzOn_closedBall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ParametricContraction.newton_lipschitzOn_closedBall
/-- info: 'FMSA.Convergence.ParametricContraction.preconditioner_injective_of_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ParametricContraction.preconditioner_injective_of_defect
/-- info: 'FMSA.Convergence.ParametricContraction.exists_unique_newton_root_closedBall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ParametricContraction.exists_unique_newton_root_closedBall
/-- info: 'FMSA.Convergence.ParametricContraction.exists_continuous_newton_root_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ParametricContraction.exists_continuous_newton_root_family
/-- info: 'FMSA.Convergence.ParametricContraction.exists_continuous_newton_root_family_of_mapsTo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ParametricContraction.exists_continuous_newton_root_family_of_mapsTo
end FMSA.Convergence.ParametricContraction
