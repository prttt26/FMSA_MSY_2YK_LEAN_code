import MSAConvergence.PureFluidActualOriginMoments

set_option linter.style.header false

/-! Exact local decomposition of the ACTUAL pure-fluid BH factor pieces
around zero frequency. The finite-tail denominators are expanded to
first order with a continuous rational remainder. This identifies the
regular-part constants used in the moment algebra; inverse dressing
continuity still requires an additional cancellation bridge. -/

noncomputable section
open Real
namespace FMSA.Convergence.PureFluidActualOriginExpansion
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidActualOriginMoments
variable {T : Type*} [Fintype T]

theorem inv_shift_second_order (s z : ℝ)
    (hz : z ≠ 0) (hsz : s+z ≠ 0) :
    1/(s+z)=1/z-s/z^2+s^2/(z^2*(s+z)) := by
  field_simp [hz,hsz]
  ring

def pRemainder (xi : ℝ) (z D G : T → ℝ) (s : ℝ) : ℝ :=
  -(∑ t, rhoOf xi*MultiTail.W xi z D G t/((z t)^2*(s+z t)))

def sRemainder (xi : ℝ) (z D G : T → ℝ) (s : ℝ) : ℝ :=
  -(∑ t, rhoOf xi*MultiTail.C xi z D G t/((z t)^2*(s+z t)))

theorem rationalPart_origin_expansion (xi : ℝ) (z D G : T → ℝ)
    (s : ℝ) (hz : ∀ t, z t ≠ 0) (hsz : ∀ t, s+z t ≠ 0) :
    rationalPart xi z D G s =
      -(rhoOf xi*MultiTail.amplitudeA xi z D G)/s^3+
      (rhoOf xi*MultiTail.amplitudeA xi z D G-
        rhoOf xi*MultiTail.amplitudeQp xi z D G)/s^2+
      (rhoOf xi*MultiTail.amplitudeQp xi z D G-
        rhoOf xi*MultiTail.amplitudeA xi z D G/2-cMass xi z D G)/s+
      pZero xi z D G+pOne xi z D G*s+s^2*pRemainder xi z D G s := by
  have hterm (t : T) :
      rhoOf xi*MultiTail.W xi z D G t/(s+z t) =
      rhoOf xi*MultiTail.W xi z D G t/z t-
        s*(rhoOf xi*MultiTail.W xi z D G t/(z t)^2)+
        s^2*(rhoOf xi*MultiTail.W xi z D G t/((z t)^2*(s+z t))) := by
    field_simp [hz t,hsz t]
    ring
  have hsum :
      (∑ t, rhoOf xi*MultiTail.W xi z D G t/(s+z t)) =
      (∑ t, rhoOf xi*MultiTail.W xi z D G t/z t)-
        s*(∑ t, rhoOf xi*MultiTail.W xi z D G t/(z t)^2)+
        s^2*(∑ t, rhoOf xi*MultiTail.W xi z D G t/((z t)^2*(s+z t))) := by
    calc
      _ = ∑ t, (rhoOf xi*MultiTail.W xi z D G t/z t-
          s*(rhoOf xi*MultiTail.W xi z D G t/(z t)^2)+
          s^2*(rhoOf xi*MultiTail.W xi z D G t/((z t)^2*(s+z t)))) :=
        Finset.sum_congr rfl (fun t _ => hterm t)
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
        simp only [← Finset.mul_sum]
  have hsplit (t : T) :
      rhoOf xi*(MultiTail.W xi z D G t/(s+z t)+
        MultiTail.C xi z D G t/s) =
      rhoOf xi*MultiTail.W xi z D G t/(s+z t)+
        rhoOf xi*MultiTail.C xi z D G t/s := by ring
  unfold rationalPart pZero pOne pRemainder cMass
  dsimp
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib,hsum,← Finset.sum_div]
  ring

theorem exponentialPart_origin_expansion (xi : ℝ) (z D G : T → ℝ)
    (s : ℝ) (hz : ∀ t, z t ≠ 0) (hsz : ∀ t, s+z t ≠ 0) :
    exponentialPart xi z D G s =
      (rhoOf xi*MultiTail.amplitudeA xi z D G)/s^3+
      (rhoOf xi*MultiTail.amplitudeQp xi z D G)/s^2+
      cMass xi z D G/s+
      sZero xi z D G+sOne xi z D G*s+s^2*sRemainder xi z D G s := by
  have hterm (t : T) :
      rhoOf xi*MultiTail.C xi z D G t/(s+z t) =
      rhoOf xi*MultiTail.C xi z D G t/z t-
        s*(rhoOf xi*MultiTail.C xi z D G t/(z t)^2)+
        s^2*(rhoOf xi*MultiTail.C xi z D G t/((z t)^2*(s+z t))) := by
    field_simp [hz t,hsz t]
    ring
  have hsum :
      (∑ t, rhoOf xi*MultiTail.C xi z D G t/(s+z t)) =
      (∑ t, rhoOf xi*MultiTail.C xi z D G t/z t)-
        s*(∑ t, rhoOf xi*MultiTail.C xi z D G t/(z t)^2)+
        s^2*(∑ t, rhoOf xi*MultiTail.C xi z D G t/((z t)^2*(s+z t))) := by
    calc
      _ = ∑ t, (rhoOf xi*MultiTail.C xi z D G t/z t-
          s*(rhoOf xi*MultiTail.C xi z D G t/(z t)^2)+
          s^2*(rhoOf xi*MultiTail.C xi z D G t/((z t)^2*(s+z t)))) :=
        Finset.sum_congr rfl (fun t _ => hterm t)
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
        simp only [← Finset.mul_sum]
  have hsplit (t : T) :
      rhoOf xi*MultiTail.C xi z D G t*(1/s-1/(s+z t)) =
      rhoOf xi*MultiTail.C xi z D G t/s-
        rhoOf xi*MultiTail.C xi z D G t/(s+z t) := by ring
  unfold exponentialPart sZero sOne sRemainder cMass
  dsimp
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib,Finset.sum_div,hsum]
  ring

theorem pRemainder_continuousAt_zero (xi : ℝ) (z D G : T → ℝ)
    (hz : ∀ t, z t ≠ 0) :
    ContinuousAt (pRemainder xi z D G) 0 := by
  unfold pRemainder
  fun_prop (disch := simp [hz])

theorem sRemainder_continuousAt_zero (xi : ℝ) (z D G : T → ℝ)
    (hz : ∀ t, z t ≠ 0) :
    ContinuousAt (sRemainder xi z D G) 0 := by
  unfold sRemainder
  fun_prop (disch := simp [hz])

end FMSA.Convergence.PureFluidActualOriginExpansion

/-- info: 'FMSA.Convergence.PureFluidActualOriginExpansion.inv_shift_second_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginExpansion.inv_shift_second_order
/-- info: 'FMSA.Convergence.PureFluidActualOriginExpansion.rationalPart_origin_expansion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginExpansion.rationalPart_origin_expansion
/-- info: 'FMSA.Convergence.PureFluidActualOriginExpansion.exponentialPart_origin_expansion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginExpansion.exponentialPart_origin_expansion
/-- info: 'FMSA.Convergence.PureFluidActualOriginExpansion.pRemainder_continuousAt_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginExpansion.pRemainder_continuousAt_zero
/-- info: 'FMSA.Convergence.PureFluidActualOriginExpansion.sRemainder_continuousAt_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginExpansion.sRemainder_continuousAt_zero
