import MSAConvergence.PureFluidActualInfinity
import MSAConvergence.PureFluidLaurentJetAlgebra

set_option linter.style.header false

/-! Actual BH moment relations governing the possible origin principal
parts of inverse hard-sphere dressing coordinates. The finite algebra
is connected to the true amplitude definitions. A later analytic step
must identify these formulas with Laurent coefficients of the actual
rational functions. -/

noncomputable section
open Real
namespace FMSA.Convergence.PureFluidActualOriginMoments
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidLaurentJetAlgebra
variable {T : Type*} [Fintype T]

def cMass (xi : ℝ) (z D G : T → ℝ) : ℝ :=
  ∑ t, rhoOf xi*MultiTail.C xi z D G t
def pZero (xi : ℝ) (z D G : T → ℝ) : ℝ :=
  1-∑ t, rhoOf xi*MultiTail.W xi z D G t/z t
def sZero (xi : ℝ) (z D G : T → ℝ) : ℝ :=
  -(∑ t, rhoOf xi*MultiTail.C xi z D G t/z t)
def pOne (xi : ℝ) (z D G : T → ℝ) : ℝ :=
  ∑ t, rhoOf xi*MultiTail.W xi z D G t/(z t)^2
def sOne (xi : ℝ) (z D G : T → ℝ) : ℝ :=
  ∑ t, rhoOf xi*MultiTail.C xi z D G t/(z t)^2

omit [Fintype T] in
theorem momentM_tail_identity (xi : ℝ) (z D G : T → ℝ)
    (t : T) (hz : z t ≠ 0) :
    D t*Mtil xi (z t) (G t) =
      -(rhoOf xi*(MultiTail.C xi z D G t*(1+z t)+
        MultiTail.W xi z D G t)/z t) := by
  unfold Mtil MultiTail.C MultiTail.W gam
  field_simp [hz]

omit [Fintype T] in
theorem momentN_tail_identity (xi : ℝ) (z D G : T → ℝ)
    (t : T) (hz : z t ≠ 0) :
    D t*Ntil xi (z t) (G t) =
      rhoOf xi*(MultiTail.W xi z D G t+
        MultiTail.C xi z D G t*(1+z t+(z t)^2/2))/(z t)^2 := by
  unfold Ntil MultiTail.C MultiTail.W gam
  field_simp [hz]

theorem momentM_eq_origin_coefficients (xi : ℝ) (z D G : T → ℝ)
    (hz : ∀ t, z t ≠ 0) :
    MultiTail.momentM xi z D G =
      pZero xi z D G+sZero xi z D G-1-cMass xi z D G := by
  have hterm (t : T) :
      -(rhoOf xi*(MultiTail.C xi z D G t*(1+z t)+
        MultiTail.W xi z D G t)/z t) =
      -rhoOf xi*MultiTail.W xi z D G t/z t-
        rhoOf xi*MultiTail.C xi z D G t/z t-
        rhoOf xi*MultiTail.C xi z D G t := by
    field_simp [hz t]
    ring
  have hW :
      (∑ t, -rhoOf xi*MultiTail.W xi z D G t/z t) =
        -(∑ t, rhoOf xi*MultiTail.W xi z D G t/z t) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  calc
    MultiTail.momentM xi z D G =
        ∑ t, -(rhoOf xi*(MultiTail.C xi z D G t*(1+z t)+
          MultiTail.W xi z D G t)/z t) := by
      unfold MultiTail.momentM
      exact Finset.sum_congr rfl (fun t _ => momentM_tail_identity xi z D G t (hz t))
    _ = ∑ t, (-rhoOf xi*MultiTail.W xi z D G t/z t-
        rhoOf xi*MultiTail.C xi z D G t/z t-
        rhoOf xi*MultiTail.C xi z D G t) := by
      exact Finset.sum_congr rfl (fun t _ => hterm t)
    _ = pZero xi z D G+sZero xi z D G-1-cMass xi z D G := by
      rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,hW]
      simp only [pZero,sZero,cMass]
      ring

theorem momentN_eq_origin_coefficients (xi : ℝ) (z D G : T → ℝ)
    (hz : ∀ t, z t ≠ 0) :
    MultiTail.momentN xi z D G =
      pOne xi z D G+sOne xi z D G-sZero xi z D G+cMass xi z D G/2 := by
  have hterm (t : T) :
      rhoOf xi*(MultiTail.W xi z D G t+
        MultiTail.C xi z D G t*(1+z t+(z t)^2/2))/(z t)^2 =
      rhoOf xi*MultiTail.W xi z D G t/(z t)^2+
        rhoOf xi*MultiTail.C xi z D G t/(z t)^2+
        rhoOf xi*MultiTail.C xi z D G t/z t+
        rhoOf xi*MultiTail.C xi z D G t/2 := by
    field_simp [hz t]
    ring
  calc
    MultiTail.momentN xi z D G =
        ∑ t, rhoOf xi*(MultiTail.W xi z D G t+
          MultiTail.C xi z D G t*(1+z t+(z t)^2/2))/(z t)^2 := by
      unfold MultiTail.momentN
      exact Finset.sum_congr rfl (fun t _ => momentN_tail_identity xi z D G t (hz t))
    _ = ∑ t, (rhoOf xi*MultiTail.W xi z D G t/(z t)^2+
        rhoOf xi*MultiTail.C xi z D G t/(z t)^2+
        rhoOf xi*MultiTail.C xi z D G t/z t+
        rhoOf xi*MultiTail.C xi z D G t/2) := by
      exact Finset.sum_congr rfl (fun t _ => hterm t)
    _ = pOne xi z D G+sOne xi z D G-sZero xi z D G+cMass xi z D G/2 := by
      simp only [pOne,sOne,sZero,cMass,Finset.sum_add_distrib,Finset.sum_div]
      ring

/-- The two potentially negative Laurent coefficients of each inverse
dressing coordinate vanish under the BH moment dictionary and the actual
PY determinant relation. This is finite algebra; analytic coefficient
extraction is separate. -/
theorem generic_origin_principal_algebra
    (a q m n c p0 v0 p1 v1 : ℝ)
    (hdet : a^2-4*a*q-8*a+4*q^2+8*q=0)
    (h0 : p0+v0=1+m+c)
    (h1 : p1+v1=n+v0-c/2) :
    let A := a*(1+m)+4*(a-q)*n
    let Q := q*(1+m)+a*n
    (A*q+2*A+2*c*a-Q*a-2*a*p0-2*a*v0)/2=0 ∧
    -(c*a-2*c*q-2*Q+2*a*p1-2*a*v0+2*a*v1+2*p0*q+2*q*v0)/2=0 ∧
    -(A*a-2*A*q-4*A+4*c*a-8*c*q-2*Q*a+4*Q*q-
      4*a*p0-4*a*v0+8*p0*q+8*q*v0)/4=0 ∧
    -(A-2*Q-a*p0-2*a*p1+a*v0-2*a*v1+
      2*p0*q+4*p1*q-2*q*v0+4*q*v1)/2=0 := by
  dsimp
  have hp0 : p0=1+m+c-v0 := by linarith
  have hp1 : p1=n+v0-c/2-v1 := by linarith
  subst p0
  subst p1
  constructor
  · linear_combination (-n/2)*hdet
  constructor
  · ring
  constructor
  · linear_combination (-(m+2*n+1)/4)*hdet
  · ring

/-- The same four candidate principal-part coefficients vanish for the
original BH moments, without imposing a root equation. -/
theorem actual_origin_principal_algebra
    (xi : ℝ) (z D G : T → ℝ) (hxi : xi ≠ 1)
    (hz : ∀ t, z t ≠ 0) :
    let a := hardA xi
    let q := hardQ xi
    let A := rhoOf xi*MultiTail.amplitudeA xi z D G
    let Q := rhoOf xi*MultiTail.amplitudeQp xi z D G
    let c := cMass xi z D G
    let p0 := pZero xi z D G
    let v0 := sZero xi z D G
    let p1 := pOne xi z D G
    let v1 := sOne xi z D G
    (A*q+2*A+2*c*a-Q*a-2*a*p0-2*a*v0)/2=0 ∧
    -(c*a-2*c*q-2*Q+2*a*p1-2*a*v0+2*a*v1+2*p0*q+2*q*v0)/2=0 ∧
    -(A*a-2*A*q-4*A+4*c*a-8*c*q-2*Q*a+4*Q*q-
      4*a*p0-4*a*v0+8*p0*q+8*q*v0)/4=0 ∧
    -(A-2*Q-a*p0-2*a*p1+a*v0-2*a*v1+
      2*p0*q+4*p1*q-2*q*v0+4*q*v1)/2=0 := by
  let a := hardA xi
  let q := hardQ xi
  let m := MultiTail.momentM xi z D G
  let n := MultiTail.momentN xi z D G
  let c := cMass xi z D G
  let p0 := pZero xi z D G
  let v0 := sZero xi z D G
  let p1 := pOne xi z D G
  let v1 := sOne xi z D G
  have h0 : p0+v0=1+m+c := by
    dsimp [p0,v0,m,c]
    linarith [momentM_eq_origin_coefficients xi z D G hz]
  have h1 : p1+v1=n+v0-c/2 := by
    dsimp [p1,v1,n,c,v0]
    linarith [momentN_eq_origin_coefficients xi z D G hz]
  have hA : rhoOf xi*MultiTail.amplitudeA xi z D G =
      a*(1+m)+4*(a-q)*n := by
    calc
      _ = (rhoOf xi*bA0 xi)*(1+m)+
          (-4*rhoOf xi*bB0 xi)*n := by
        simp only [MultiTail.amplitudeA,m,n]
        ring
      _ = _ := by
        rw [hard_B_relation xi]
        rfl
  have hQ : rhoOf xi*MultiTail.amplitudeQp xi z D G =
      q*(1+m)+a*n := by
    simp only [MultiTail.amplitudeQp,m,n,a,q,hardA,hardQ]
    ring
  have h := generic_origin_principal_algebra a q m n c p0 v0 p1 v1
    (hard_coefficient_relation xi hxi) h0 h1
  dsimp at h ⊢
  rw [← hA, ← hQ] at h
  exact h

end FMSA.Convergence.PureFluidActualOriginMoments

/-- info: 'FMSA.Convergence.PureFluidActualOriginMoments.momentM_tail_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginMoments.momentM_tail_identity
/-- info: 'FMSA.Convergence.PureFluidActualOriginMoments.momentN_tail_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginMoments.momentN_tail_identity
/-- info: 'FMSA.Convergence.PureFluidActualOriginMoments.momentM_eq_origin_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginMoments.momentM_eq_origin_coefficients
/-- info: 'FMSA.Convergence.PureFluidActualOriginMoments.momentN_eq_origin_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginMoments.momentN_eq_origin_coefficients
/-- info: 'FMSA.Convergence.PureFluidActualOriginMoments.generic_origin_principal_algebra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginMoments.generic_origin_principal_algebra
/-- info: 'FMSA.Convergence.PureFluidActualOriginMoments.actual_origin_principal_algebra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginMoments.actual_origin_principal_algebra
