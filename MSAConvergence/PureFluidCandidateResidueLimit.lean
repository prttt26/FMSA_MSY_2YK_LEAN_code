import MSAConvergence.PureFluidCandidatePoleCoefficients

set_option linter.style.header false

/-! Genuine real-axis punctured-neighborhood residue limits of the
candidate pure-fluid dressing at each distinct positive tail rate.
The matching coefficients were algebraic in the preceding module;
here continuity of every other term upgrades them to actual limits. -/
noncomputable section
open Real Filter Topology Set
namespace FMSA.Convergence.PureFluidCandidateResidueLimit
open FMSA.Convergence.PureFluidCandidatePoleCoefficients
open FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidNodeResidues
open FMSA.Convergence.PureFluidExactResidueForm
variable {T : Type*} [Fintype T]

/-- A regular term plus a single rational pole has the expected
punctured-neighborhood scaled limit. -/
theorem simple_pole_tendsto (a : ℝ) (reg num : ℝ → ℝ)
    (hreg : ContinuousAt reg a) (hnum : ContinuousAt num a) :
    Tendsto (fun s => (s-a)*(reg s+num s/(s-a))) (𝓝[≠] a) (𝓝 (num a)) := by
  have hne : ∀ᶠ s : ℝ in 𝓝[≠] a, s-a ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsa : s ≠ a := by simpa only [mem_compl_iff, mem_singleton_iff] using hs
    exact sub_ne_zero.mpr hsa
  have heq : (fun s => (s-a)*(reg s+num s/(s-a))) =ᶠ[𝓝[≠] a]
      (fun s => (s-a)*reg s+num s) := by
    filter_upwards [hne] with s hs
    field_simp [hs]
  have hzero : Tendsto (fun s : ℝ => s-a) (𝓝[≠] a) (𝓝 (0:ℝ)) := by
    have hc : ContinuousAt (fun s : ℝ => s-a) a := by fun_prop
    simpa only [sub_self] using
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hlim : Tendsto (fun s => (s-a)*reg s+num s) (𝓝[≠] a) (𝓝 (num a)) := by
    convert (hzero.mul (hreg.tendsto.mono_left nhdsWithin_le_nhds)).add
      (hnum.tendsto.mono_left nhdsWithin_le_nhds) using 1
    simp
  exact hlim.congr' heq.symm

/-- Finite sums of simple poles have the expected scaled limit at one
isolated pole when all numerators and the head are continuous there. -/
theorem finite_simple_pole_tendsto
    (z : T → ℝ) (num : T → ℝ → ℝ) (head : ℝ → ℝ) (t : T)
    (hz_inj : Function.Injective z)
    (hhead : ContinuousAt head (-z t))
    (hnum : ∀ u, ContinuousAt (num u) (-z t)) :
    Tendsto (fun s => (s+z t)*(head s+∑ u, num u s/(s+z u)))
      (𝓝[≠] (-z t)) (𝓝 (num t (-z t))) := by
  classical
  let reg : ℝ → ℝ := fun s => head s+
    ∑ u ∈ (Finset.univ.erase t), num u s/(s+z u)
  have hterm (u : T) (hu : u ∈ Finset.univ.erase t) :
      ContinuousAt (fun s : ℝ => num u s/(s+z u)) (-z t) := by
    have hnot : u ≠ t := (Finset.mem_erase.mp hu).1
    have hzu : z u ≠ z t := fun he => hnot (hz_inj he)
    have hden : -z t+z u ≠ 0 := by intro he; apply hzu; linarith
    exact (hnum u).div (by fun_prop) hden
  have hsum : ContinuousAt
      (fun s : ℝ => ∑ u ∈ (Finset.univ.erase t), num u s/(s+z u)) (-z t) := by
    exact tendsto_finsetSum (Finset.univ.erase t) (fun u hu => (hterm u hu).tendsto)
  have hreg : ContinuousAt reg (-z t) := hhead.add hsum
  have hdecomp (s : ℝ) : head s+∑ u, num u s/(s+z u) =
      reg s+num t s/(s+z t) := by
    dsimp only [reg]
    rw [← Finset.sum_erase_add Finset.univ (fun u => num u s/(s+z u))
      (Finset.mem_univ t)]
    ring
  have hlim := simple_pole_tendsto (-z t) reg (num t) hreg (hnum t)
  convert hlim using 1
  · funext s
    rw [hdecomp]
    ring

/-- The actual PY rational basis is continuous away from the origin. -/
theorem hardP_continuousAt (xi s : ℝ) (hs : s ≠ 0) :
    ContinuousAt (hardP xi) s := by
  unfold hardP
  fun_prop (disch := simp [hs])

/-- The actual PY exponential basis is continuous away from the origin. -/
theorem hardShat_continuousAt (xi s : ℝ) (hs : s ≠ 0) :
    ContinuousAt (hardShat xi) s := by
  unfold hardShat
  fun_prop (disch := simp [hs])

/-- The candidate rational piece's genuine real-axis residue limit at
`-z_t` equals its previously defined formal coefficient. -/
theorem candidateRational_residue_limit
    (xi : ℝ) (z w r : T → ℝ) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z) (t : T) :
    Tendsto (fun s => (s+z t)*
      candidateRational xi s (candidateU z w s) (candidateG z w r s))
      (𝓝[≠] (-z t)) (𝓝 (formalPoleP xi (z t) (w t) (r t))) := by
  have hs0 : -z t ≠ 0 := neg_ne_zero.mpr (hz t).ne'
  have hhead : ContinuousAt (hardP xi) (-z t) :=
    hardP_continuousAt xi (-z t) hs0
  have hnum (u : T) : ContinuousAt
      (fun s => poleNumeratorP xi s (z u) (w u) (r u)) (-z t) := by
    unfold poleNumeratorP hardP hardShat
    fun_prop (disch := simp [hs0, (hz t).ne'])
  have hlim := finite_simple_pole_tendsto z
    (fun u s => poleNumeratorP xi s (z u) (w u) (r u))
    (hardP xi) t hzinj hhead hnum
  rw [poleNumeratorP_at_pole xi (z t) (w t) (r t) (hz t).ne'] at hlim
  have hfun : (fun s => (s+z t)*
      (hardP xi s+∑ u, poleNumeratorP xi s (z u) (w u) (r u)/(s+z u))) =
      (fun s => (s+z t)*
        candidateRational xi s (candidateU z w s) (candidateG z w r s)) := by
    funext s
    rw [candidateRational_partial_fraction]
  rw [hfun] at hlim
  exact hlim

/-- Companion genuine residue limit for the candidate exponential piece. -/
theorem candidateExponential_residue_limit
    (xi : ℝ) (z w r : T → ℝ) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z) (t : T) :
    Tendsto (fun s => (s+z t)*
      candidateExponential xi s (candidateU z w s) (candidateG z w r s))
      (𝓝[≠] (-z t)) (𝓝 (formalPoleS xi (z t) (w t) (r t))) := by
  have hs0 : -z t ≠ 0 := neg_ne_zero.mpr (hz t).ne'
  have hhead : ContinuousAt (hardShat xi) (-z t) :=
    hardShat_continuousAt xi (-z t) hs0
  have hnum (u : T) : ContinuousAt
      (fun s => poleNumeratorS xi s (z u) (w u) (r u)) (-z t) := by
    unfold poleNumeratorS hardP hardShat
    fun_prop (disch := simp [hs0, (hz t).ne'])
  have hlim := finite_simple_pole_tendsto z
    (fun u s => poleNumeratorS xi s (z u) (w u) (r u))
    (hardShat xi) t hzinj hhead hnum
  rw [poleNumeratorS_at_pole xi (z t) (w t) (r t) (hz t).ne'] at hlim
  have hfun : (fun s => (s+z t)*
      (hardShat xi s+∑ u, poleNumeratorS xi s (z u) (w u) (r u)/(s+z u))) =
      (fun s => (s+z t)*
        candidateExponential xi s (candidateU z w s) (candidateG z w r s)) := by
    funext s
    rw [candidateExponential_partial_fraction]
  rw [hfun] at hlim
  exact hlim

/-- The genuine candidate rational residue is the Step 1 cross-node
coefficient `-(w_t/U_t) Shat_cand(z_t)`. -/
theorem candidateRational_residue_cross_node
    (xi : ℝ) (z w r : T → ℝ) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z) (hlin : nodeRLinearEquation z w r)
    (t : T) (hU : candidateU z w (z t) ≠ 0) :
    Tendsto (fun s => (s+z t)*
      candidateRational xi s (candidateU z w s) (candidateG z w r s))
      (𝓝[≠] (-z t))
      (𝓝 (-(w t/candidateU z w (z t))*
        candidateExponential xi (z t) (candidateU z w (z t))
          (candidateG z w r (z t)))) := by
  rw [← formalPoleP_eq_candidate_node xi z w r hlin t (hz t).ne' hU]
  exact candidateRational_residue_limit xi z w r hz hzinj t

/-- Companion cross-node residue for the candidate exponential piece. -/
theorem candidateExponential_residue_cross_node
    (xi : ℝ) (z w r : T → ℝ) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z) (hlin : nodeRLinearEquation z w r)
    (t : T) (hU : candidateU z w (z t) ≠ 0) :
    Tendsto (fun s => (s+z t)*
      candidateExponential xi s (candidateU z w s) (candidateG z w r s))
      (𝓝[≠] (-z t))
      (𝓝 (-(w t/candidateU z w (z t))*
        candidateRational xi (z t) (candidateU z w (z t))
          (candidateG z w r (z t)))) := by
  rw [← formalPoleS_eq_candidate_node xi z w r hlin t (hz t).ne' hU]
  exact candidateExponential_residue_limit xi z w r hz hzinj t

/-- Actual BH rational-pole head, regular at every negative positive rate. -/
def actualPHead (xi : ℝ) (z D G : T → ℝ) (s : ℝ) : ℝ :=
  1-rhoOf xi*MultiTail.amplitudeA xi z D G/s^3+
    rhoOf xi*(MultiTail.amplitudeA xi z D G-
      MultiTail.amplitudeQp xi z D G)/s^2+
    (rhoOf xi*(MultiTail.amplitudeQp xi z D G-
      MultiTail.amplitudeA xi z D G/2)-poleMass xi z D G)/s

/-- Actual BH exponential-pole head, regular at every negative positive rate. -/
def actualSHead (xi : ℝ) (z D G : T → ℝ) (s : ℝ) : ℝ :=
  rhoOf xi*MultiTail.amplitudeA xi z D G/s^3+
    rhoOf xi*MultiTail.amplitudeQp xi z D G/s^2+
    poleMass xi z D G/s

/-- The ACTUAL rational BH factor has the cross-node scaled limit at
each isolated negative tail rate. -/
theorem actual_rational_residue_limit
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    Tendsto (fun s => (s+z t)*rationalPart xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (-(dressedStrength xi z D G t*
        exponentialPart xi z D G (z t)))) := by
  have hs0 : -z t ≠ 0 := neg_ne_zero.mpr (hz t).ne'
  have hhead : ContinuousAt (actualPHead xi z D G) (-z t) := by
    unfold actualPHead
    fun_prop (disch := first | exact pow_ne_zero _ hs0 | exact hs0)
  have hnum (u : T) : ContinuousAt
      (fun _ : ℝ => -(dressedStrength xi z D G u*
        exponentialPart xi z D G (z u))) (-z t) := by fun_prop
  have hlim := finite_simple_pole_tendsto z
    (fun u _ => -(dressedStrength xi z D G u*
      exponentialPart xi z D G (z u)))
    (actualPHead xi z D G) t hzinj hhead hnum
  have hfun : (fun s => (s+z t)*
      (actualPHead xi z D G s+
        ∑ u, (-(dressedStrength xi z D G u*
          exponentialPart xi z D G (z u)))/(s+z u))) =
      (fun s => (s+z t)*rationalPart xi z D G s) := by
    funext s
    rw [actual_rational_residue_form xi z K D G hz hroot hF s]
    unfold actualPHead
    simp only [neg_div, Finset.sum_neg_distrib]
    ring
  rw [hfun] at hlim
  exact hlim

/-- Companion ACTUAL BH exponential-factor scaled limit. -/
theorem actual_exponential_residue_limit
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    Tendsto (fun s => (s+z t)*exponentialPart xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (-(dressedStrength xi z D G t*
        rationalPart xi z D G (z t)))) := by
  have hs0 : -z t ≠ 0 := neg_ne_zero.mpr (hz t).ne'
  have hhead : ContinuousAt (actualSHead xi z D G) (-z t) := by
    unfold actualSHead
    fun_prop (disch := first | exact pow_ne_zero _ hs0 | exact hs0)
  have hnum (u : T) : ContinuousAt
      (fun _ : ℝ => -(dressedStrength xi z D G u*
        rationalPart xi z D G (z u))) (-z t) := by fun_prop
  have hlim := finite_simple_pole_tendsto z
    (fun u _ => -(dressedStrength xi z D G u*
      rationalPart xi z D G (z u)))
    (actualSHead xi z D G) t hzinj hhead hnum
  have hfun : (fun s => (s+z t)*
      (actualSHead xi z D G s+
        ∑ u, (-(dressedStrength xi z D G u*
          rationalPart xi z D G (z u)))/(s+z u))) =
      (fun s => (s+z t)*exponentialPart xi z D G s) := by
    funext s
    rw [actual_exponential_residue_form xi z K D G hz hroot hF s]
    unfold actualSHead
    simp only [neg_div, Finset.sum_neg_distrib]
    ring
  rw [hfun] at hlim
  exact hlim

end FMSA.Convergence.PureFluidCandidateResidueLimit

/-- info: 'FMSA.Convergence.PureFluidCandidateResidueLimit.simple_pole_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateResidueLimit.simple_pole_tendsto
/-- info: 'FMSA.Convergence.PureFluidCandidateResidueLimit.finite_simple_pole_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateResidueLimit.finite_simple_pole_tendsto
/-- info: 'FMSA.Convergence.PureFluidCandidateResidueLimit.hardP_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateResidueLimit.hardP_continuousAt
/-- info: 'FMSA.Convergence.PureFluidCandidateResidueLimit.hardShat_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateResidueLimit.hardShat_continuousAt
/-- info: 'FMSA.Convergence.PureFluidCandidateResidueLimit.candidateRational_residue_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateResidueLimit.candidateRational_residue_limit
/-- info: 'FMSA.Convergence.PureFluidCandidateResidueLimit.candidateExponential_residue_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateResidueLimit.candidateExponential_residue_limit
/-- info: 'FMSA.Convergence.PureFluidCandidateResidueLimit.candidateRational_residue_cross_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateResidueLimit.candidateRational_residue_cross_node
/-- info: 'FMSA.Convergence.PureFluidCandidateResidueLimit.candidateExponential_residue_cross_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateResidueLimit.candidateExponential_residue_cross_node

/-- info: 'FMSA.Convergence.PureFluidCandidateResidueLimit.actual_rational_residue_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateResidueLimit.actual_rational_residue_limit
/-- info: 'FMSA.Convergence.PureFluidCandidateResidueLimit.actual_exponential_residue_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateResidueLimit.actual_exponential_residue_limit
