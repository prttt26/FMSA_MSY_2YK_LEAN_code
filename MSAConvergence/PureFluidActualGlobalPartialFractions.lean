import MSAConvergence.PureFluidActualOriginRemoval

set_option linter.style.header false

/-! Global finite partial fractions for the inverse dressing of the
ORIGINAL pure-fluid finite-tail BH factor. The coefficients are explicit
linear expressions in the true W,C tail data. The proof uses exact
per-tail amplitude identities and PY unimodularity, with no root
hypothesis. Matching these coefficients to the paper's H-function node
weights is a subsequent true-root step. -/

noncomputable section
open Real
namespace FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidActualOriginRemoval
open FMSA.Convergence.PureFluidActualOriginMoments
open FMSA.Convergence.PureFluidLaurentJetAlgebra
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidDressingCandidates
variable {T : Type*} [Fintype T]

def tailM (z w c : ℝ) : ℝ := -(c*(1+z)+w)/z
def tailN (z w c : ℝ) : ℝ := (w+c*(1+z+z^2/2))/z^2
def tailA (a q z w c : ℝ) : ℝ :=
  a*tailM z w c+4*(a-q)*tailN z w c
def tailQ (a q z w c : ℝ) : ℝ :=
  q*tailM z w c+a*tailN z w c
def tailP (a q z w c s : ℝ) : ℝ :=
  -tailA a q z w c/s^3+
  (tailA a q z w c-tailQ a q z w c)/s^2+
  (tailQ a q z w c-tailA a q z w c/2-c)/s-w/(s+z)
def tailS (a q z w c s : ℝ) : ℝ :=
  tailA a q z w c/s^3+tailQ a q z w c/s^2+c/s-c/(s+z)
def tailU (a q z w c s : ℝ) : ℝ :=
  localHardP a q (-s)*tailP a q z w c s-
    localHardS a q (-s)*tailS a q z w c s+
    localHardP a q s*tailS a q z w c s-
    localHardS a q s*tailP a q z w c s
def tailG (a q z w c s : ℝ) : ℝ :=
  s*(localHardP a q s*tailS a q z w c s-
    localHardS a q s*tailP a q z w c s)

def tailAlpha (a q z w c : ℝ) : ℝ :=
  -(c*(a*z+2*a-2*q*z-4*q+2*z^2)+
    w*(-a*z+2*a+2*q*z-4*q+2*z^2))/(2*z^2)
def tailBeta (a q z w c : ℝ) : ℝ :=
  (c*(a*z^2+2*a*z+2*a-2*q*z^2-2*q*z+2*z^3)+
    w*(2*a-2*q*z))/(2*z^2)

theorem generic_tailU_partial_fraction
    (a q z w c s : ℝ) (hs : s ≠ 0) (hz : z ≠ 0)
    (hsz : s+z ≠ 0) :
    tailU a q z w c s = tailAlpha a q z w c/(s+z)+
      ((-c*z-2*c+w*z-2*w)*
        (a^2-4*a*q-8*a+4*q^2+8*q))/(4*s^2*z^2) := by
  unfold tailU tailP tailS tailA tailQ tailM tailN
    tailAlpha localHardP localHardS
  field_simp [hs,hz,hsz]
  ring

theorem generic_tailG_partial_fraction
    (a q z w c s : ℝ) (hs : s ≠ 0) (hz : z ≠ 0)
    (hsz : s+z ≠ 0) :
    tailG a q z w c s = tailBeta a q z w c/(s+z)-
      ((c*z^2+2*c*z+2*c+2*w)*
        (a^2-4*a*q-8*a+4*q^2+8*q))/(4*s^2*z^2) := by
  unfold tailG tailP tailS tailA tailQ tailM tailN
    tailBeta localHardP localHardS
  field_simp [hs,hz,hsz]
  ring

omit [Fintype T] in
theorem actual_tailM_identity (xi : ℝ) (z D G : T → ℝ)
    (t : T) (hz : z t ≠ 0) :
    tailM (z t) (rhoOf xi*MultiTail.W xi z D G t)
      (rhoOf xi*MultiTail.C xi z D G t) =
    D t*Mtil xi (z t) (G t) := by
  rw [momentM_tail_identity xi z D G t hz]
  unfold tailM
  ring

omit [Fintype T] in
theorem actual_tailN_identity (xi : ℝ) (z D G : T → ℝ)
    (t : T) (hz : z t ≠ 0) :
    tailN (z t) (rhoOf xi*MultiTail.W xi z D G t)
      (rhoOf xi*MultiTail.C xi z D G t) =
    D t*Ntil xi (z t) (G t) := by
  rw [momentN_tail_identity xi z D G t hz]
  unfold tailN
  ring

theorem actual_amplitudeA_tail_sum (xi : ℝ) (z D G : T → ℝ)
    (hz : ∀ t, z t ≠ 0) :
    rhoOf xi*MultiTail.amplitudeA xi z D G =
      hardA xi+∑ t, tailA (hardA xi) (hardQ xi) (z t)
        (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) := by
  have hM : MultiTail.momentM xi z D G =
      ∑ t, tailM (z t) (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) := by
    unfold MultiTail.momentM
    exact Finset.sum_congr rfl (fun t _ =>
      (actual_tailM_identity xi z D G t (hz t)).symm)
  have hN : MultiTail.momentN xi z D G =
      ∑ t, tailN (z t) (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) := by
    unfold MultiTail.momentN
    exact Finset.sum_congr rfl (fun t _ =>
      (actual_tailN_identity xi z D G t (hz t)).symm)
  unfold MultiTail.amplitudeA
  rw [hM,hN]
  simp only [tailA,Finset.sum_add_distrib,← Finset.mul_sum]
  have hb := hard_B_relation xi
  unfold hardA hardQ at hb ⊢
  linear_combination (∑ t, tailN (z t)
    (rhoOf xi*MultiTail.W xi z D G t)
    (rhoOf xi*MultiTail.C xi z D G t))*hb

theorem actual_amplitudeQ_tail_sum (xi : ℝ) (z D G : T → ℝ)
    (hz : ∀ t, z t ≠ 0) :
    rhoOf xi*MultiTail.amplitudeQp xi z D G =
      hardQ xi+∑ t, tailQ (hardA xi) (hardQ xi) (z t)
        (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) := by
  have hM : MultiTail.momentM xi z D G =
      ∑ t, tailM (z t) (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) := by
    unfold MultiTail.momentM
    exact Finset.sum_congr rfl (fun t _ =>
      (actual_tailM_identity xi z D G t (hz t)).symm)
  have hN : MultiTail.momentN xi z D G =
      ∑ t, tailN (z t) (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) := by
    unfold MultiTail.momentN
    exact Finset.sum_congr rfl (fun t _ =>
      (actual_tailN_identity xi z D G t (hz t)).symm)
  unfold MultiTail.amplitudeQp
  rw [hM,hN]
  simp only [tailQ,Finset.sum_add_distrib,← Finset.mul_sum]
  unfold hardA hardQ
  ring

theorem sum_tailP (a q s : ℝ) (z w c : T → ℝ) :
    (∑ t, tailP a q (z t) (w t) (c t) s) =
      -(∑ t, tailA a q (z t) (w t) (c t))/s^3+
      ((∑ t, tailA a q (z t) (w t) (c t))-
        (∑ t, tailQ a q (z t) (w t) (c t)))/s^2+
      ((∑ t, tailQ a q (z t) (w t) (c t))-
        (∑ t, tailA a q (z t) (w t) (c t))/2-
        (∑ t, c t))/s-
      ∑ t, w t/(s+z t) := by
  simp only [tailP,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_div]
  rw [Finset.sum_neg_distrib]

theorem sum_tailS (a q s : ℝ) (z w c : T → ℝ) :
    (∑ t, tailS a q (z t) (w t) (c t) s) =
      (∑ t, tailA a q (z t) (w t) (c t))/s^3+
      (∑ t, tailQ a q (z t) (w t) (c t))/s^2+
      (∑ t, c t)/s-
      ∑ t, c t/(s+z t) := by
  simp only [tailS,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_div]

theorem actual_rational_tail_sum (xi : ℝ) (z D G : T → ℝ)
    (hz : ∀ t, z t ≠ 0) (s : ℝ) :
    rationalPart xi z D G s = hardP xi s+
      ∑ t, tailP (hardA xi) (hardQ xi) (z t)
        (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) s := by
  let w : T → ℝ := fun t => rhoOf xi*MultiTail.W xi z D G t
  let c : T → ℝ := fun t => rhoOf xi*MultiTail.C xi z D G t
  have hA := actual_amplitudeA_tail_sum xi z D G hz
  have hQ := actual_amplitudeQ_tail_sum xi z D G hz
  have hterm (t : T) :
      rhoOf xi*(MultiTail.W xi z D G t/(s+z t)+
        MultiTail.C xi z D G t/s) = w t/(s+z t)+c t/s := by
    dsimp [w,c]
    ring
  rw [sum_tailP (hardA xi) (hardQ xi) s z w c]
  unfold rationalPart hardP
  dsimp
  simp_rw [hterm]
  rw [Finset.sum_add_distrib,← Finset.sum_div]
  dsimp [w,c]
  linear_combination (-1/s^3+1/s^2-1/(2*s))*hA+
    (-1/s^2+1/s)*hQ

theorem actual_exponential_tail_sum (xi : ℝ) (z D G : T → ℝ)
    (hz : ∀ t, z t ≠ 0) (s : ℝ) :
    exponentialPart xi z D G s = hardShat xi s+
      ∑ t, tailS (hardA xi) (hardQ xi) (z t)
        (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) s := by
  let w : T → ℝ := fun t => rhoOf xi*MultiTail.W xi z D G t
  let c : T → ℝ := fun t => rhoOf xi*MultiTail.C xi z D G t
  have hA := actual_amplitudeA_tail_sum xi z D G hz
  have hQ := actual_amplitudeQ_tail_sum xi z D G hz
  have hterm (t : T) :
      rhoOf xi*MultiTail.C xi z D G t*(1/s-1/(s+z t)) =
        c t/s-c t/(s+z t) := by
    dsimp [c]
    ring
  rw [sum_tailS (hardA xi) (hardQ xi) s z w c]
  unfold exponentialPart hardShat
  dsimp
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib,← Finset.sum_div]
  dsimp [w,c]
  linear_combination (1/s^3)*hA+(1/s^2)*hQ

theorem dressingU_sum (xi s P0 S0 : ℝ) (P S : T → ℝ) :
    dressingU xi s (P0+∑ t, P t) (S0+∑ t, S t) =
      dressingU xi s P0 S0+∑ t, dressingU xi s (P t) (S t) := by
  unfold dressingU dressingD
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

theorem dressingG_sum (xi s P0 S0 : ℝ) (P S : T → ℝ) :
    dressingG xi s (P0+∑ t, P t) (S0+∑ t, S t) =
      dressingG xi s P0 S0+∑ t, dressingG xi s (P t) (S t) := by
  unfold dressingG dressingD
  simp only [mul_add,Finset.mul_sum]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  ring

theorem hard_dressing_seed (xi s : ℝ) (hxi : xi ≠ 1) (hs : s ≠ 0) :
    dressingU xi s (hardP xi s) (hardShat xi s) = 1 ∧
      dressingG xi s (hardP xi s) (hardShat xi s) = 0 := by
  constructor
  · unfold dressingU dressingD
    linear_combination hard_unimodular xi s hxi hs
  · unfold dressingG dressingD
    ring

theorem tailU_eq_dressing (xi z w c s : ℝ) :
    tailU (hardA xi) (hardQ xi) z w c s =
      dressingU xi s (tailP (hardA xi) (hardQ xi) z w c s)
        (tailS (hardA xi) (hardQ xi) z w c s) := by
  unfold tailU dressingU dressingD localHardP localHardS hardP hardShat
  ring

theorem tailG_eq_dressing (xi z w c s : ℝ) :
    tailG (hardA xi) (hardQ xi) z w c s =
      dressingG xi s (tailP (hardA xi) (hardQ xi) z w c s)
        (tailS (hardA xi) (hardQ xi) z w c s) := by
  unfold tailG dressingG dressingD localHardP localHardS hardP hardShat
  ring

theorem actual_dressing_tail_sum (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, z t ≠ 0)
    (s : ℝ) (hs : s ≠ 0) :
    actualU xi z D G s = 1+
      ∑ t, tailU (hardA xi) (hardQ xi) (z t)
        (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) s ∧
    actualG xi z D G s =
      ∑ t, tailG (hardA xi) (hardQ xi) (z t)
        (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) s := by
  have hP := actual_rational_tail_sum xi z D G hz s
  have hS := actual_exponential_tail_sum xi z D G hz s
  have hseed := hard_dressing_seed xi s hxi hs
  constructor
  · unfold actualU
    rw [hP,hS,dressingU_sum,hseed.1]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    exact (tailU_eq_dressing xi (z t)
      (rhoOf xi*MultiTail.W xi z D G t)
      (rhoOf xi*MultiTail.C xi z D G t) s).symm
  · unfold actualG
    rw [hP,hS,dressingG_sum,hseed.2,zero_add]
    apply Finset.sum_congr rfl
    intro t _
    exact (tailG_eq_dressing xi (z t)
      (rhoOf xi*MultiTail.W xi z D G t)
      (rhoOf xi*MultiTail.C xi z D G t) s).symm

/-- Global finite partial-fraction representation of the inverse
coordinates of the ACTUAL BH factor, with no root hypothesis. -/
theorem actual_dressing_global_partial_fractions
    (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, z t ≠ 0)
    (s : ℝ) (hs : s ≠ 0) (hsz : ∀ t, s+z t ≠ 0) :
    actualU xi z D G s = 1+
      ∑ t, tailAlpha (hardA xi) (hardQ xi) (z t)
        (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t)/(s+z t) ∧
    actualG xi z D G s =
      ∑ t, tailBeta (hardA xi) (hardQ xi) (z t)
        (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t)/(s+z t) := by
  have hsum := actual_dressing_tail_sum xi z D G hxi hz s hs
  have hdet := hard_coefficient_relation xi hxi
  constructor
  · rw [hsum.1]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    simpa only [hdet,mul_zero,zero_div,add_zero] using
      (generic_tailU_partial_fraction (hardA xi) (hardQ xi) (z t)
        (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) s hs (hz t) (hsz t))
  · rw [hsum.2]
    apply Finset.sum_congr rfl
    intro t _
    simpa only [hdet,mul_zero,zero_div,sub_zero] using
      (generic_tailG_partial_fraction (hardA xi) (hardQ xi) (z t)
        (rhoOf xi*MultiTail.W xi z D G t)
        (rhoOf xi*MultiTail.C xi z D G t) s hs (hz t) (hsz t))

def actualWeight (xi : ℝ) (z D G : T → ℝ) (t : T) : ℝ :=
  -tailAlpha (hardA xi) (hardQ xi) (z t)
    (rhoOf xi*MultiTail.W xi z D G t)
    (rhoOf xi*MultiTail.C xi z D G t)

def actualGNumerator (xi : ℝ) (z D G : T → ℝ) (t : T) : ℝ :=
  tailBeta (hardA xi) (hardQ xi) (z t)
    (rhoOf xi*MultiTail.W xi z D G t)
    (rhoOf xi*MultiTail.C xi z D G t)

theorem actualU_eq_candidateU_explicit
    (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, z t ≠ 0)
    (s : ℝ) (hs : s ≠ 0) (hsz : ∀ t, s+z t ≠ 0) :
    actualU xi z D G s = candidateU z (actualWeight xi z D G) s := by
  have h := (actual_dressing_global_partial_fractions xi z D G hxi hz s hs hsz).1
  unfold candidateU actualWeight
  rw [h]
  simp only [neg_div,Finset.sum_neg_distrib,sub_neg_eq_add]

theorem actualG_eq_candidateG_of_coefficients
    (xi : ℝ) (z D G r : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, z t ≠ 0)
    (hcoeff : ∀ t, actualWeight xi z D G t*(z t-r t) =
      actualGNumerator xi z D G t)
    (s : ℝ) (hs : s ≠ 0) (hsz : ∀ t, s+z t ≠ 0) :
    actualG xi z D G s = candidateG z (actualWeight xi z D G) r s := by
  rw [(actual_dressing_global_partial_fractions xi z D G hxi hz s hs hsz).2]
  unfold candidateG
  exact Finset.sum_congr rfl (fun t _ => by rw [hcoeff t]; rfl)

end FMSA.Convergence.PureFluidActualGlobalPartialFractions

/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.generic_tailU_partial_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.generic_tailU_partial_fraction
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.generic_tailG_partial_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.generic_tailG_partial_fraction
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_tailM_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_tailM_identity
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_tailN_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_tailN_identity
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_amplitudeA_tail_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_amplitudeA_tail_sum
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_amplitudeQ_tail_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_amplitudeQ_tail_sum
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.sum_tailP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.sum_tailP
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.sum_tailS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.sum_tailS
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_rational_tail_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_rational_tail_sum
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_exponential_tail_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_exponential_tail_sum
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.dressingU_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.dressingU_sum
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.dressingG_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.dressingG_sum
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.hard_dressing_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.hard_dressing_seed
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.tailU_eq_dressing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.tailU_eq_dressing
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.tailG_eq_dressing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.tailG_eq_dressing
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_dressing_tail_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_dressing_tail_sum
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_dressing_global_partial_fractions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.actual_dressing_global_partial_fractions
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.actualU_eq_candidateU_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.actualU_eq_candidateU_explicit
/-- info: 'FMSA.Convergence.PureFluidActualGlobalPartialFractions.actualG_eq_candidateG_of_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualGlobalPartialFractions.actualG_eq_candidateG_of_coefficients
