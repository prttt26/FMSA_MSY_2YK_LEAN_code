import MSAConvergence.PureFluidActualOriginExpansion

set_option linter.style.header false

/-! The inverse dressing coordinates of the ORIGINAL finite-tail BH
factor have removable zero-frequency singularities. Exact local
P,Shat decompositions and actual moment relations remove all negative
powers, leaving explicit continuous functions at the origin. This
holds for arbitrary amplitudes and nonzero rates when the PY basis is
unimodular; no root equation is needed. -/

noncomputable section
open Real Filter Topology Set
namespace FMSA.Convergence.PureFluidActualOriginRemoval
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidActualOriginMoments
open FMSA.Convergence.PureFluidActualOriginExpansion
variable {T : Type*} [Fintype T]

def localP (A Q c p0 p1 rP s : ℝ) : ℝ :=
  -A/s^3+(A-Q)/s^2+(Q-A/2-c)/s+p0+p1*s+s^2*rP
def localS (A Q c v0 v1 rV s : ℝ) : ℝ :=
  A/s^3+Q/s^2+c/s+v0+v1*s+s^2*rV
def localHardP (a q s : ℝ) : ℝ :=
  1-a/s^3+(a-q)/s^2+(q-a/2)/s
def localHardS (a q s : ℝ) : ℝ := a/s^3+q/s^2

def localG (a q A Q c p0 v0 p1 v1 rP rV s : ℝ) : ℝ :=
  s*(localHardP a q s*localS A Q c v0 v1 rV s-
    localHardS a q s*localP A Q c p0 p1 rP s)
def localU (a q A Q c p0 v0 p1 v1 rP rV s : ℝ) : ℝ :=
  localHardP a q (-s)*localP A Q c p0 p1 rP s-
    localHardS a q (-s)*localS A Q c v0 v1 rV s+
    localHardP a q s*localS A Q c v0 v1 rV s-
    localHardS a q s*localP A Q c p0 p1 rP s

def gTwo (a q A Q c p0 v0 : ℝ) : ℝ :=
  (A*q+2*A+2*c*a-Q*a-2*a*p0-2*a*v0)/2
def gOne (a q _A Q c p0 v0 p1 v1 : ℝ) : ℝ :=
  -(c*a-2*c*q-2*Q+2*a*p1-2*a*v0+2*a*v1+2*p0*q+2*q*v0)/2
def uTwo (a q A Q c p0 v0 : ℝ) : ℝ :=
  -(A*a-2*A*q-4*A+4*c*a-8*c*q-2*Q*a+4*Q*q-
    4*a*p0-4*a*v0+8*p0*q+8*q*v0)/4
def uOne (a q A Q _c p0 v0 p1 v1 : ℝ) : ℝ :=
  -(A-2*Q-a*p0-2*a*p1+a*v0-2*a*v1+
    2*p0*q+4*p1*q-2*q*v0+4*q*v1)/2

def regularG (a q c _p0 v0 p1 v1 rP rV s : ℝ) : ℝ :=
  -(2*rP*a+2*rV*a+a*v0-2*a*v1-2*c+2*p1*q-2*q*v0+2*q*v1)/2+
  s*(-2*rP*q+2*rV*a-2*rV*q-a*v1+2*q*v1+2*v0)/2+
  s^2*(-rV*a+2*rV*q+2*v1)/2+s^3*rV

def regularU (a q p0 v0 p1 v1 rP rV s : ℝ) : ℝ :=
  (2*rP*a-4*rP*q+2*rV*a-4*rV*q+a*p1-a*v1+
    2*p0-2*p1*q+2*q*v1+2*v0)/2+
  s*(rP*a-2*rP*q-rV*a+2*rV*q+2*p1+2*v1)/2+
  s^2*(rP+rV)

theorem localG_decomposition (a q A Q c p0 v0 p1 v1 rP rV s : ℝ)
    (hs : s ≠ 0) :
    localG a q A Q c p0 v0 p1 v1 rP rV s =
      gTwo a q A Q c p0 v0/s^2+
      gOne a q A Q c p0 v0 p1 v1/s+
      regularG a q c p0 v0 p1 v1 rP rV s := by
  unfold localG localP localS localHardP localHardS gTwo gOne regularG
  field_simp [hs]
  ring

theorem localU_decomposition (a q A Q c p0 v0 p1 v1 rP rV s : ℝ)
    (hs : s ≠ 0) :
    localU a q A Q c p0 v0 p1 v1 rP rV s =
      uTwo a q A Q c p0 v0/s^2+
      uOne a q A Q c p0 v0 p1 v1/s+
      regularU a q p0 v0 p1 v1 rP rV s := by
  unfold localU localP localS localHardP localHardS uTwo uOne regularU
  field_simp [hs]
  ring

def actualRegularG (xi : ℝ) (z D G : T → ℝ) (s : ℝ) : ℝ :=
  regularG (hardA xi) (hardQ xi) (cMass xi z D G)
    (pZero xi z D G) (sZero xi z D G)
    (pOne xi z D G) (sOne xi z D G)
    (pRemainder xi z D G s) (sRemainder xi z D G s) s

def actualRegularU (xi : ℝ) (z D G : T → ℝ) (s : ℝ) : ℝ :=
  regularU (hardA xi) (hardQ xi)
    (pZero xi z D G) (sZero xi z D G)
    (pOne xi z D G) (sOne xi z D G)
    (pRemainder xi z D G s) (sRemainder xi z D G s) s

theorem actualG_eq_regular (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, z t ≠ 0)
    (s : ℝ) (hs : s ≠ 0) (hsz : ∀ t, s+z t ≠ 0) :
    actualG xi z D G s = actualRegularG xi z D G s := by
  let a := hardA xi
  let q := hardQ xi
  let A := rhoOf xi*MultiTail.amplitudeA xi z D G
  let Q := rhoOf xi*MultiTail.amplitudeQp xi z D G
  let c := cMass xi z D G
  let p0 := pZero xi z D G
  let v0 := sZero xi z D G
  let p1 := pOne xi z D G
  let v1 := sOne xi z D G
  let rP := pRemainder xi z D G s
  let rV := sRemainder xi z D G s
  have hP := rationalPart_origin_expansion xi z D G s hz hsz
  have hS := exponentialPart_origin_expansion xi z D G s hz hsz
  have hcoeff := actual_origin_principal_algebra xi z D G hxi hz
  dsimp at hcoeff
  obtain ⟨hg2,hg1,_hu2,_hu1⟩ := hcoeff
  have hzero2 : gTwo a q A Q c p0 v0 = 0 := by
    simpa only [gTwo,a,q,A,Q,c,p0,v0] using hg2
  have hzero1 : gOne a q A Q c p0 v0 p1 v1 = 0 := by
    simpa only [gOne,a,q,A,Q,c,p0,v0,p1,v1] using hg1
  calc
    actualG xi z D G s = localG a q A Q c p0 v0 p1 v1 rP rV s := by
      unfold actualG dressingG dressingD localG
      rw [hP,hS]
      simp only [localP,localS,localHardP,localHardS,
        hardP,hardShat,a,q,A,Q,c,p0,v0,p1,v1,rP,rV]
    _ = regularG a q c p0 v0 p1 v1 rP rV s := by
      rw [localG_decomposition a q A Q c p0 v0 p1 v1 rP rV s hs,
        hzero2,hzero1]
      ring
    _ = actualRegularG xi z D G s := rfl

theorem actualU_eq_regular (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, z t ≠ 0)
    (s : ℝ) (hs : s ≠ 0) (hsz : ∀ t, s+z t ≠ 0) :
    actualU xi z D G s = actualRegularU xi z D G s := by
  let a := hardA xi
  let q := hardQ xi
  let A := rhoOf xi*MultiTail.amplitudeA xi z D G
  let Q := rhoOf xi*MultiTail.amplitudeQp xi z D G
  let c := cMass xi z D G
  let p0 := pZero xi z D G
  let v0 := sZero xi z D G
  let p1 := pOne xi z D G
  let v1 := sOne xi z D G
  let rP := pRemainder xi z D G s
  let rV := sRemainder xi z D G s
  have hP := rationalPart_origin_expansion xi z D G s hz hsz
  have hS := exponentialPart_origin_expansion xi z D G s hz hsz
  have hcoeff := actual_origin_principal_algebra xi z D G hxi hz
  dsimp at hcoeff
  obtain ⟨_hg2,_hg1,hu2,hu1⟩ := hcoeff
  have hzero2 : uTwo a q A Q c p0 v0 = 0 := by
    simpa only [uTwo,a,q,A,Q,c,p0,v0] using hu2
  have hzero1 : uOne a q A Q c p0 v0 p1 v1 = 0 := by
    simpa only [uOne,a,q,A,Q,c,p0,v0,p1,v1] using hu1
  calc
    actualU xi z D G s = localU a q A Q c p0 v0 p1 v1 rP rV s := by
      unfold actualU dressingU dressingD localU
      rw [hP,hS]
      simp only [localP,localS,localHardP,localHardS,
        hardP,hardShat,a,q,A,Q,c,p0,v0,p1,v1,rP,rV]
      ring
    _ = regularU a q p0 v0 p1 v1 rP rV s := by
      rw [localU_decomposition a q A Q c p0 v0 p1 v1 rP rV s hs,
        hzero2,hzero1]
      ring
    _ = actualRegularU xi z D G s := rfl

theorem actualRegularG_continuousAt_zero (xi : ℝ) (z D G : T → ℝ)
    (hz : ∀ t, z t ≠ 0) :
    ContinuousAt (actualRegularG xi z D G) 0 := by
  have hp := pRemainder_continuousAt_zero xi z D G hz
  have hv := sRemainder_continuousAt_zero xi z D G hz
  unfold actualRegularG regularG
  fun_prop

theorem actualRegularU_continuousAt_zero (xi : ℝ) (z D G : T → ℝ)
    (hz : ∀ t, z t ≠ 0) :
    ContinuousAt (actualRegularU xi z D G) 0 := by
  have hp := pRemainder_continuousAt_zero xi z D G hz
  have hv := sRemainder_continuousAt_zero xi z D G hz
  unfold actualRegularU regularU
  fun_prop

theorem eventually_no_tail_pole (z : T → ℝ) (hz : ∀ t, z t ≠ 0) :
    ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), ∀ t, s+z t ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro t
  have hcont : ContinuousAt (fun s : ℝ => s+z t) 0 := by fun_prop
  exact hcont.eventually_ne (by simpa using hz t)

theorem actualG_tendsto_regular_origin (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, z t ≠ 0) :
    Tendsto (actualG xi z D G) (𝓝[≠] (0 : ℝ))
      (𝓝 (actualRegularG xi z D G 0)) := by
  have hreg := (actualRegularG_continuousAt_zero xi z D G hz).tendsto
  have hreg' : Tendsto (actualRegularG xi z D G)
      (𝓝[≠] (0 : ℝ)) (𝓝 (actualRegularG xi z D G 0)) :=
    hreg.mono_left nhdsWithin_le_nhds
  have heq : actualG xi z D G =ᶠ[𝓝[≠] (0 : ℝ)] actualRegularG xi z D G := by
    have hnonzero : ∀ᶠ s : ℝ in 𝓝[≠] (0 : ℝ), s ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
    have htail : ∀ᶠ s : ℝ in 𝓝[≠] (0 : ℝ), ∀ t, s+z t ≠ 0 :=
      (eventually_no_tail_pole z hz).filter_mono nhdsWithin_le_nhds
    filter_upwards [hnonzero,htail] with s hs hsz
    exact actualG_eq_regular xi z D G hxi hz s hs hsz
  exact hreg'.congr' heq.symm

theorem actualU_tendsto_regular_origin (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, z t ≠ 0) :
    Tendsto (actualU xi z D G) (𝓝[≠] (0 : ℝ))
      (𝓝 (actualRegularU xi z D G 0)) := by
  have hreg := (actualRegularU_continuousAt_zero xi z D G hz).tendsto
  have hreg' : Tendsto (actualRegularU xi z D G)
      (𝓝[≠] (0 : ℝ)) (𝓝 (actualRegularU xi z D G 0)) :=
    hreg.mono_left nhdsWithin_le_nhds
  have heq : actualU xi z D G =ᶠ[𝓝[≠] (0 : ℝ)] actualRegularU xi z D G := by
    have hnonzero : ∀ᶠ s : ℝ in 𝓝[≠] (0 : ℝ), s ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
    have htail : ∀ᶠ s : ℝ in 𝓝[≠] (0 : ℝ), ∀ t, s+z t ≠ 0 :=
      (eventually_no_tail_pole z hz).filter_mono nhdsWithin_le_nhds
    filter_upwards [hnonzero,htail] with s hs hsz
    exact actualU_eq_regular xi z D G hxi hz s hs hsz
  exact hreg'.congr' heq.symm

end FMSA.Convergence.PureFluidActualOriginRemoval

/-- info: 'FMSA.Convergence.PureFluidActualOriginRemoval.localG_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginRemoval.localG_decomposition
/-- info: 'FMSA.Convergence.PureFluidActualOriginRemoval.localU_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginRemoval.localU_decomposition
/-- info: 'FMSA.Convergence.PureFluidActualOriginRemoval.actualG_eq_regular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginRemoval.actualG_eq_regular
/-- info: 'FMSA.Convergence.PureFluidActualOriginRemoval.actualU_eq_regular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginRemoval.actualU_eq_regular
/-- info: 'FMSA.Convergence.PureFluidActualOriginRemoval.actualRegularG_continuousAt_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginRemoval.actualRegularG_continuousAt_zero
/-- info: 'FMSA.Convergence.PureFluidActualOriginRemoval.actualRegularU_continuousAt_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginRemoval.actualRegularU_continuousAt_zero
/-- info: 'FMSA.Convergence.PureFluidActualOriginRemoval.eventually_no_tail_pole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginRemoval.eventually_no_tail_pole
/-- info: 'FMSA.Convergence.PureFluidActualOriginRemoval.actualG_tendsto_regular_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginRemoval.actualG_tendsto_regular_origin
/-- info: 'FMSA.Convergence.PureFluidActualOriginRemoval.actualU_tendsto_regular_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualOriginRemoval.actualU_tendsto_regular_origin
