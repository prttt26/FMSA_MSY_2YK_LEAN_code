import MSAConvergence.PureFluidActualDressingCoordinates

set_option linter.style.header false

/-! The inverse dressing coordinates of an ACTUAL pure-fluid BH root
obey the pole coefficients required by the H-function candidate.
Coincident rates are collected before taking the punctured real-axis
limit. These local data do not yet identify the global finite sums. -/

noncomputable section
open Real Filter Topology Set
namespace FMSA.Convergence.PureFluidActualDressingPoles
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidNodeResidues
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidCandidateResidueLimit
open FMSA.Convergence.PureFluidCoincidentPoleLimits
open FMSA.Convergence.PureFluidActualDressingCoordinates
variable {T : Type*} [Fintype T]

/-- Total dressed strength of all tail indices with the same rate. -/
def collectedStrength (xi : ℝ) (z D G : T → ℝ) (t : T) : ℝ :=
  ∑ u ∈ Finset.univ.filter (fun u => z u = z t), dressedStrength xi z D G u

/-- For distinct rates, the collected strength is one node strength. -/
theorem collectedStrength_eq_of_injective
    (xi : ℝ) (z D G : T → ℝ) (hzinj : Function.Injective z) (t : T) :
    collectedStrength xi z D G t = dressedStrength xi z D G t := by
  classical
  unfold collectedStrength
  have hset : Finset.univ.filter (fun u => z u = z t) = {t} := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨fun h => hzinj h,fun hu => by rw [hu]⟩
  rw [hset]
  simp

/-- The actual rational BH pole coefficient factors through the total
strength at one distinct rate value. -/
theorem actual_rational_collected_pole_limit
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    Tendsto (fun s => (s+z t)*rationalPart xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (-(collectedStrength xi z D G t*
        exponentialPart xi z D G (z t)))) := by
  have hlim := actual_rational_coincident_pole_limit xi z K D G hz hroot hF t
  have hsum :
      (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        -(dressedStrength xi z D G u*exponentialPart xi z D G (z u))) =
      -(collectedStrength xi z D G t*exponentialPart xi z D G (z t)) := by
    rw [Finset.sum_neg_distrib]
    unfold collectedStrength
    rw [Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [(Finset.mem_filter.mp hu).2]
  rw [hsum] at hlim
  exact hlim

/-- Companion factorization of the actual exponential BH pole coefficient. -/
theorem actual_exponential_collected_pole_limit
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    Tendsto (fun s => (s+z t)*exponentialPart xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (-(collectedStrength xi z D G t*
        rationalPart xi z D G (z t)))) := by
  have hlim := actual_exponential_coincident_pole_limit xi z K D G hz hroot hF t
  have hsum :
      (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        -(dressedStrength xi z D G u*rationalPart xi z D G (z u))) =
      -(collectedStrength xi z D G t*rationalPart xi z D G (z t)) := by
    rw [Finset.sum_neg_distrib]
    unfold collectedStrength
    rw [Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [(Finset.mem_filter.mp hu).2]
  rw [hsum] at hlim
  exact hlim

/-- The PY rational basis reflected across the origin is regular
at a nonzero negative rate. -/
theorem hardP_neg_continuousAt (xi z : ℝ) (hz : z ≠ 0) :
    ContinuousAt (fun s : ℝ => hardP xi (-s)) (-z) := by
  have hneg : ContinuousAt (fun s : ℝ => -s) (-z) := by fun_prop
  have hp : ContinuousAt (hardP xi) (- -z) := by
    simpa only [neg_neg] using hardP_continuousAt xi z hz
  simpa only [Function.comp_def,neg_neg] using
    hp.comp hneg

/-- The reflected PY exponential basis is regular there as well. -/
theorem hardShat_neg_continuousAt (xi z : ℝ) (hz : z ≠ 0) :
    ContinuousAt (fun s : ℝ => hardShat xi (-s)) (-z) := by
  have hneg : ContinuousAt (fun s : ℝ => -s) (-z) := by fun_prop
  have hp : ContinuousAt (hardShat xi) (- -z) := by
    simpa only [neg_neg] using hardShat_continuousAt xi z hz
  simpa only [Function.comp_def,neg_neg] using
    hp.comp hneg

/-- The ACTUAL inverse U coordinate obeys the combined H-function
pole relation at every positive rate. -/
theorem actualU_collected_pole_limit
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    Tendsto (fun s => (s+z t)*actualU xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (-(collectedStrength xi z D G t*actualU xi z D G (z t)))) := by
  let l := 𝓝[≠] (-z t)
  have hs0 : -z t ≠ 0 := neg_ne_zero.mpr (hz t).ne'
  have hP := actual_rational_collected_pole_limit xi z K D G hz hroot hF t
  have hS := actual_exponential_collected_pole_limit xi z K D G hz hroot hF t
  have hPp : Tendsto (fun s => hardP xi s) l (𝓝 (hardP xi (-z t))) :=
    (hardP_continuousAt xi (-z t) hs0).tendsto.mono_left nhdsWithin_le_nhds
  have hSp : Tendsto (fun s => hardShat xi s) l (𝓝 (hardShat xi (-z t))) :=
    (hardShat_continuousAt xi (-z t) hs0).tendsto.mono_left nhdsWithin_le_nhds
  have hPm : Tendsto (fun s => hardP xi (-s)) l (𝓝 (hardP xi (z t))) :=
    by simpa only [neg_neg] using
      (hardP_neg_continuousAt xi (z t) (hz t).ne').tendsto.mono_left
        nhdsWithin_le_nhds
  have hSm : Tendsto (fun s => hardShat xi (-s)) l
      (𝓝 (hardShat xi (z t))) :=
    by simpa only [neg_neg] using
      (hardShat_neg_continuousAt xi (z t) (hz t).ne').tendsto.mono_left
        nhdsWithin_le_nhds
  have hlim := (((hPm.mul hP).sub (hSm.mul hS)).add
    ((hPp.mul hS).sub (hSp.mul hP)))
  convert hlim using 1
  · funext s
    unfold actualU dressingU dressingD
    ring_nf
  · unfold actualU dressingU dressingD
    ring_nf

/-- The ACTUAL inverse g coordinate obeys the companion combined
pole relation at every positive rate. -/
theorem actualG_collected_pole_limit
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    Tendsto (fun s => (s+z t)*actualG xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (collectedStrength xi z D G t*
        (z t*actualU xi z D G (z t)-actualG xi z D G (z t)))) := by
  let l := 𝓝[≠] (-z t)
  have hs0 : -z t ≠ 0 := neg_ne_zero.mpr (hz t).ne'
  have hP := actual_rational_collected_pole_limit xi z K D G hz hroot hF t
  have hS := actual_exponential_collected_pole_limit xi z K D G hz hroot hF t
  have hPp : Tendsto (fun s => hardP xi s) l (𝓝 (hardP xi (-z t))) :=
    (hardP_continuousAt xi (-z t) hs0).tendsto.mono_left nhdsWithin_le_nhds
  have hSp : Tendsto (fun s => hardShat xi s) l (𝓝 (hardShat xi (-z t))) :=
    (hardShat_continuousAt xi (-z t) hs0).tendsto.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun s : ℝ => s) l (𝓝 (-z t)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim := hid.mul ((hPp.mul hS).sub (hSp.mul hP))
  convert hlim using 1
  · funext s
    unfold actualG dressingG dressingD
    ring_nf
  · unfold actualU actualG dressingU dressingG dressingD
    ring_nf

/-- At distinct rates the actual U pole coefficient is -Lambda_t U(z_t). -/
theorem actualU_simple_pole_limit
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    Tendsto (fun s => (s+z t)*actualU xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (-(dressedStrength xi z D G t*actualU xi z D G (z t)))) := by
  simpa only [collectedStrength_eq_of_injective xi z D G hzinj t] using
    actualU_collected_pole_limit xi z K D G hz hroot hF t

/-- At distinct rates the actual g pole coefficient is
Lambda_t (z_t U(z_t)-g(z_t)). -/
theorem actualG_simple_pole_limit
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    Tendsto (fun s => (s+z t)*actualG xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (dressedStrength xi z D G t*
        (z t*actualU xi z D G (z t)-actualG xi z D G (z t)))) := by
  simpa only [collectedStrength_eq_of_injective xi z D G hzinj t] using
    actualG_collected_pole_limit xi z K D G hz hroot hF t

end FMSA.Convergence.PureFluidActualDressingPoles
/-- info: 'FMSA.Convergence.PureFluidActualDressingPoles.collectedStrength_eq_of_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingPoles.collectedStrength_eq_of_injective
/-- info: 'FMSA.Convergence.PureFluidActualDressingPoles.actual_rational_collected_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingPoles.actual_rational_collected_pole_limit
/-- info: 'FMSA.Convergence.PureFluidActualDressingPoles.actual_exponential_collected_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingPoles.actual_exponential_collected_pole_limit
/-- info: 'FMSA.Convergence.PureFluidActualDressingPoles.hardP_neg_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingPoles.hardP_neg_continuousAt
/-- info: 'FMSA.Convergence.PureFluidActualDressingPoles.hardShat_neg_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingPoles.hardShat_neg_continuousAt
/-- info: 'FMSA.Convergence.PureFluidActualDressingPoles.actualU_collected_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingPoles.actualU_collected_pole_limit
/-- info: 'FMSA.Convergence.PureFluidActualDressingPoles.actualG_collected_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingPoles.actualG_collected_pole_limit
/-- info: 'FMSA.Convergence.PureFluidActualDressingPoles.actualU_simple_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingPoles.actualU_simple_pole_limit
/-- info: 'FMSA.Convergence.PureFluidActualDressingPoles.actualG_simple_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingPoles.actualG_simple_pole_limit
