import MSAConvergence.PureFluidCandidateResidueLimit

set_option linter.style.header false

/-! Finite pole limits with coincident Yukawa rates. Every tail at the
same rate contributes to one combined scaled limit; no injectivity of
the rate map is required. Both candidate and actual BH factor pieces
are covered. The limits are along the punctured real axis. -/

noncomputable section
open Real Filter Topology Set
namespace FMSA.Convergence.PureFluidCoincidentPoleLimits
open FMSA.Convergence.PureFluidCandidateResidueLimit
open FMSA.Convergence.PureFluidCandidatePoleCoefficients
open FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidExactResidueForm
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidNodeResidues
open FMSA.ExactMSA
variable {T : Type*} [Fintype T]

/-- A finite sum of simple rational poles has a combined scaled limit at
one rate, equal to the sum of numerators over all matching rates. -/
theorem finite_coincident_pole_tendsto
    (z : T → ℝ) (num : T → ℝ → ℝ) (head : ℝ → ℝ) (t : T)
    (hhead : ContinuousAt head (-z t))
    (hnum : ∀ u, ContinuousAt (num u) (-z t)) :
    Tendsto (fun s => (s+z t)*(head s+∑ u, num u s/(s+z u)))
      (𝓝[≠] (-z t))
      (𝓝 (∑ u ∈ Finset.univ.filter (fun u => z u = z t), num u (-z t))) := by
  classical
  let same : Finset T := Finset.univ.filter (fun u => z u = z t)
  let other : Finset T := Finset.univ.filter (fun u => z u ≠ z t)
  let reg : ℝ → ℝ := fun s => head s+other.sum (fun u => num u s/(s+z u))
  let cluster : ℝ → ℝ := fun s => same.sum (fun u => num u s)
  have hterm (u : T) (hu : u ∈ other) :
      ContinuousAt (fun s : ℝ => num u s/(s+z u)) (-z t) := by
    have hzu : z u ≠ z t := (Finset.mem_filter.mp hu).2
    have hden : -z t+z u ≠ 0 := by intro he; apply hzu; linarith
    exact (hnum u).div (by fun_prop) hden
  have hsum : ContinuousAt (fun s : ℝ =>
      other.sum (fun u => num u s/(s+z u))) (-z t) := by
    exact tendsto_finsetSum other (fun u hu => (hterm u hu).tendsto)
  have hreg : ContinuousAt reg (-z t) := hhead.add hsum
  have hcluster : ContinuousAt cluster (-z t) := by
    exact tendsto_finsetSum same (fun u hu => (hnum u).tendsto)
  have hdecomp (s : ℝ) :
      head s+∑ u, num u s/(s+z u) = reg s+cluster s/(s+z t) := by
    have hs : same.sum (fun u => num u s/(s+z u)) = cluster s/(s+z t) := by
      dsimp only [cluster]
      calc
        same.sum (fun u => num u s/(s+z u)) =
            same.sum (fun u => num u s/(s+z t)) := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [(Finset.mem_filter.mp hu).2]
        _ = (same.sum (fun u => num u s))/(s+z t) := by rw [Finset.sum_div]
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun u => z u = z t) (fun u => num u s/(s+z u))
    dsimp only [reg]
    change same.sum (fun u => num u s/(s+z u))+
      other.sum (fun u => num u s/(s+z u)) =
      ∑ u, num u s/(s+z u) at hsplit
    rw [← hsplit, hs]
    ring
  have hlim := simple_pole_tendsto (-z t) reg cluster hreg hcluster
  convert hlim using 1
  · funext s
    rw [hdecomp]
    ring

/-- Combined real-axis pole limit for the candidate rational piece. -/
theorem candidateRational_coincident_pole_limit
    (xi : ℝ) (z w r : T → ℝ) (hz : ∀ u, 0 < z u) (t : T) :
    Tendsto (fun s => (s+z t)*
      candidateRational xi s (candidateU z w s) (candidateG z w r s))
      (𝓝[≠] (-z t))
      (𝓝 (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        formalPoleP xi (z u) (w u) (r u))) := by
  have hs0 : -z t ≠ 0 := neg_ne_zero.mpr (hz t).ne'
  have hhead : ContinuousAt (hardP xi) (-z t) :=
    hardP_continuousAt xi (-z t) hs0
  have hnum (u : T) : ContinuousAt
      (fun s => poleNumeratorP xi s (z u) (w u) (r u)) (-z t) := by
    unfold poleNumeratorP hardP hardShat
    fun_prop (disch := simp [hs0, (hz t).ne'])
  have hlim := finite_coincident_pole_tendsto z
    (fun u s => poleNumeratorP xi s (z u) (w u) (r u))
    (hardP xi) t hhead hnum
  have htarget :
      (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        poleNumeratorP xi (-z t) (z u) (w u) (r u)) =
      (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        formalPoleP xi (z u) (w u) (r u)) := by
    apply Finset.sum_congr rfl
    intro u hu
    have he : z u = z t := (Finset.mem_filter.mp hu).2
    rw [← he, poleNumeratorP_at_pole xi (z u) (w u) (r u) (hz u).ne']
  rw [htarget] at hlim
  have hfun : (fun s => (s+z t)*
      (hardP xi s+∑ u, poleNumeratorP xi s (z u) (w u) (r u)/(s+z u))) =
      (fun s => (s+z t)*
        candidateRational xi s (candidateU z w s) (candidateG z w r s)) := by
    funext s
    rw [candidateRational_partial_fraction]
  rw [hfun] at hlim
  exact hlim

/-- Combined real-axis pole limit for the candidate exponential piece. -/
theorem candidateExponential_coincident_pole_limit
    (xi : ℝ) (z w r : T → ℝ) (hz : ∀ u, 0 < z u) (t : T) :
    Tendsto (fun s => (s+z t)*
      candidateExponential xi s (candidateU z w s) (candidateG z w r s))
      (𝓝[≠] (-z t))
      (𝓝 (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        formalPoleS xi (z u) (w u) (r u))) := by
  have hs0 : -z t ≠ 0 := neg_ne_zero.mpr (hz t).ne'
  have hhead : ContinuousAt (hardShat xi) (-z t) :=
    hardShat_continuousAt xi (-z t) hs0
  have hnum (u : T) : ContinuousAt
      (fun s => poleNumeratorS xi s (z u) (w u) (r u)) (-z t) := by
    unfold poleNumeratorS hardP hardShat
    fun_prop (disch := simp [hs0, (hz t).ne'])
  have hlim := finite_coincident_pole_tendsto z
    (fun u s => poleNumeratorS xi s (z u) (w u) (r u))
    (hardShat xi) t hhead hnum
  have htarget :
      (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        poleNumeratorS xi (-z t) (z u) (w u) (r u)) =
      (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        formalPoleS xi (z u) (w u) (r u)) := by
    apply Finset.sum_congr rfl
    intro u hu
    have he : z u = z t := (Finset.mem_filter.mp hu).2
    rw [← he, poleNumeratorS_at_pole xi (z u) (w u) (r u) (hz u).ne']
  rw [htarget] at hlim
  have hfun : (fun s => (s+z t)*
      (hardShat xi s+∑ u, poleNumeratorS xi s (z u) (w u) (r u)/(s+z u))) =
      (fun s => (s+z t)*
        candidateExponential xi s (candidateU z w s) (candidateG z w r s)) := by
    funext s
    rw [candidateExponential_partial_fraction]
  rw [hfun] at hlim
  exact hlim

/-- The combined candidate rational limit equals the sum of its
cross-node coefficients under the r system. -/
theorem candidateRational_coincident_cross_node
    (xi : ℝ) (z w r : T → ℝ) (hz : ∀ u, 0 < z u)
    (hlin : nodeRLinearEquation z w r) (t : T)
    (hU : ∀ u, z u = z t → candidateU z w (z u) ≠ 0) :
    Tendsto (fun s => (s+z t)*
      candidateRational xi s (candidateU z w s) (candidateG z w r s))
      (𝓝[≠] (-z t))
      (𝓝 (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        -(w u/candidateU z w (z u))*
          candidateExponential xi (z u) (candidateU z w (z u))
            (candidateG z w r (z u)))) := by
  have hlim := candidateRational_coincident_pole_limit xi z w r hz t
  convert hlim using 1
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  exact (formalPoleP_eq_candidate_node xi z w r hlin u (hz u).ne'
    (hU u (Finset.mem_filter.mp hu).2)).symm

/-- The companion combined candidate exponential cross-node limit. -/
theorem candidateExponential_coincident_cross_node
    (xi : ℝ) (z w r : T → ℝ) (hz : ∀ u, 0 < z u)
    (hlin : nodeRLinearEquation z w r) (t : T)
    (hU : ∀ u, z u = z t → candidateU z w (z u) ≠ 0) :
    Tendsto (fun s => (s+z t)*
      candidateExponential xi s (candidateU z w s) (candidateG z w r s))
      (𝓝[≠] (-z t))
      (𝓝 (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        -(w u/candidateU z w (z u))*
          candidateRational xi (z u) (candidateU z w (z u))
            (candidateG z w r (z u)))) := by
  have hlim := candidateExponential_coincident_pole_limit xi z w r hz t
  convert hlim using 1
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  exact (formalPoleS_eq_candidate_node xi z w r hlin u (hz u).ne'
    (hU u (Finset.mem_filter.mp hu).2)).symm

/-- Combined pole limit for the ACTUAL rational BH root piece. -/
theorem actual_rational_coincident_pole_limit
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    Tendsto (fun s => (s+z t)*rationalPart xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        -(dressedStrength xi z D G u*
          exponentialPart xi z D G (z u)))) := by
  have hs0 : -z t ≠ 0 := neg_ne_zero.mpr (hz t).ne'
  have hhead : ContinuousAt (actualPHead xi z D G) (-z t) := by
    unfold actualPHead
    fun_prop (disch := first | exact pow_ne_zero _ hs0 | exact hs0)
  have hnum (u : T) : ContinuousAt
      (fun _ : ℝ => -(dressedStrength xi z D G u*
        exponentialPart xi z D G (z u))) (-z t) := by fun_prop
  have hlim := finite_coincident_pole_tendsto z
    (fun u _ => -(dressedStrength xi z D G u*
      exponentialPart xi z D G (z u)))
    (actualPHead xi z D G) t hhead hnum
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

/-- Combined pole limit for the ACTUAL exponential BH root piece. -/
theorem actual_exponential_coincident_pole_limit
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    Tendsto (fun s => (s+z t)*exponentialPart xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        -(dressedStrength xi z D G u*
          rationalPart xi z D G (z u)))) := by
  have hs0 : -z t ≠ 0 := neg_ne_zero.mpr (hz t).ne'
  have hhead : ContinuousAt (actualSHead xi z D G) (-z t) := by
    unfold actualSHead
    fun_prop (disch := first | exact pow_ne_zero _ hs0 | exact hs0)
  have hnum (u : T) : ContinuousAt
      (fun _ : ℝ => -(dressedStrength xi z D G u*
        rationalPart xi z D G (z u))) (-z t) := by fun_prop
  have hlim := finite_coincident_pole_tendsto z
    (fun u _ => -(dressedStrength xi z D G u*
      rationalPart xi z D G (z u)))
    (actualSHead xi z D G) t hhead hnum
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

end FMSA.Convergence.PureFluidCoincidentPoleLimits
/-- info: 'FMSA.Convergence.PureFluidCoincidentPoleLimits.finite_coincident_pole_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCoincidentPoleLimits.finite_coincident_pole_tendsto
/-- info: 'FMSA.Convergence.PureFluidCoincidentPoleLimits.candidateRational_coincident_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCoincidentPoleLimits.candidateRational_coincident_pole_limit
/-- info: 'FMSA.Convergence.PureFluidCoincidentPoleLimits.candidateExponential_coincident_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCoincidentPoleLimits.candidateExponential_coincident_pole_limit
/-- info: 'FMSA.Convergence.PureFluidCoincidentPoleLimits.candidateRational_coincident_cross_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCoincidentPoleLimits.candidateRational_coincident_cross_node
/-- info: 'FMSA.Convergence.PureFluidCoincidentPoleLimits.candidateExponential_coincident_cross_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCoincidentPoleLimits.candidateExponential_coincident_cross_node
/-- info: 'FMSA.Convergence.PureFluidCoincidentPoleLimits.actual_rational_coincident_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCoincidentPoleLimits.actual_rational_coincident_pole_limit
/-- info: 'FMSA.Convergence.PureFluidCoincidentPoleLimits.actual_exponential_coincident_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCoincidentPoleLimits.actual_exponential_coincident_pole_limit
