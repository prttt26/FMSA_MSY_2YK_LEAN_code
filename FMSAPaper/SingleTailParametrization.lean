import LeanCode.YukawaOZMix.MSAMultiTailMixtureFamily
import FMSAPaper.SingleTailExpBounds

/-! The actual exact-MSA Blum–Høye system for one hard-sphere species and one
Yukawa tail, written as two scalar equations. The tail index type is any type
with exactly one element. -/
noncomputable section
open Real FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators

namespace FMSA.Paper.SingleTail
open ExactMSA.MultiTailMixture

variable {T : Type*} [Fintype T] [Unique T]

/-- The constant tail matrix with every entry `x`. -/
def sc (x : ℝ) : TailMatrix T 1 := fun _ _ _ => x

section scalar
variable (zz r s : ℝ)

/-- `E = exp (-z σ)`. -/
def Ez : ℝ := exp (-zz * s)

def xi2S : ℝ := r * s ^ 2
def vacS : ℝ := 1 - π / 6 * (r * s ^ 3)
def Q0S : ℝ := 2 * π / vacS r s * (s + π * xi2S r s * s * s / (4 * vacS r s))
def QppS : ℝ := 2 * π / vacS r s * (1 + π * xi2S r s * s / (2 * vacS r s))

variable (d g : ℝ)

def gamS : ℝ := 1 - 2 * π * r * g * Ez zz s / zz
def CtS : ℝ := gamS zz r s g * d
def WtS : ℝ := 2 * π / zz * (r * g * d)
def MS : ℝ := -(1 / zz) * (r * (WtS zz r d g + (1 + zz * s) * CtS zz r s d g))
def NS : ℝ := r * (1 / zz ^ 2 * WtS zz r d g +
  (1 + zz * s + (zz * s) ^ 2 / 2) / zz ^ 2 * CtS zz r s d g)
def AS : ℝ := QppS r s + (QppS r s * MS zz r s d g +
  2 * π ^ 2 * xi2S r s / vacS r s ^ 2 * NS zz r s d g)
def qpS : ℝ := Q0S r s + (Q0S r s * MS zz r s d g + QppS r s * NS zz r s d g)
def QhS : ℝ :=
  (1 - zz * s - Ez zz s) / zz ^ 2 * qpS zz r s d g +
    (1 - zz * s + (zz * s) ^ 2 / 2 - Ez zz s) / zz ^ 3 * AS zz r s d g +
    (WtS zz r d g / (zz + zz) + CtS zz r s d g * (1 - Ez zz s) / zz) +
    CtS zz r s d g * Ez zz s / (zz + zz)

/-- First scalar Blum–Høye equation, left side. -/
def firstS : ℝ := d * (1 - r * QhS zz r s d g)
/-- Second scalar Blum–Høye equation, left side minus right side. -/
def secondS : ℝ := 2 * π * g * (1 - r * QhS zz r s d g) -
  (AS zz r s d g + zz * qpS zz r s d g + zz ^ 2 * zz / (zz + zz) * CtS zz r s d g) / zz ^ 2

end scalar

section param
variable (zz r s k : ℝ)

def xS : ℝ := zz * s
def etaS : ℝ := π / 6 * (r * s ^ 3)
def JS : ℝ := Ez zz s * (xS zz s + 2) + xS zz s - 2
def HS : ℝ := Ez zz s * (2 * xS zz s + 2) + xS zz s ^ 2 - 2
def HtS : ℝ := 2 - 2 * xS zz s + Ez zz s * (xS zz s ^ 2 - 2)
/-- `P = 18 η² J + 6 η (1-η) H + x³ (1-η)²`. -/
def PS : ℝ := 18 * etaS r s ^ 2 * JS zz s + 6 * etaS r s * vacS r s * HS zz s +
  xS zz s ^ 3 * vacS r s ^ 2
/-- Seed root `a = -P`. -/
def aS : ℝ := -PS zz r s
/-- Second root `b`. -/
def bS : ℝ := -18 * etaS r s ^ 2 * JS zz s + 6 * etaS r s * vacS r s * HtS zz s -
  Ez zz s * xS zz s ^ 3 * vacS r s ^ 2
/-- `D = (1-η) x² (1-E) + 6 η J`. -/
def DdS : ℝ := vacS r s * xS zz s ^ 2 * (1 - Ez zz s) + 6 * etaS r s * JS zz s
def LamS : ℝ := s / (6 * k * etaS r s * xS zz s ^ 6 * vacS r s ^ 6 * DdS zz r s ^ 2)

variable (u : ℝ)

/-- Coupling as a quartic in the parameter `u`. -/
def tauS : ℝ := -LamS zz r s k * u ^ 2 * (u - aS zz r s) * (u - bS zz r s)
def DtS : ℝ := -(π * s ^ 2 * u * (u - aS zz r s)) /
  (3 * etaS r s * xS zz s ^ 3 * vacS r s ^ 3 * DdS zz r s)
def GS : ℝ := s ^ 2 * xS zz s / (12 * etaS r s * DdS zz r s) *
  ((etaS r s * xS zz s ^ 2 + 6 * etaS r s * xS zz s + 12 * etaS r s - xS zz s ^ 2) -
    vacS r s ^ 3 * xS zz s ^ 5 / u)

theorem firstS_param (hz : zz ≠ 0) (hs : s ≠ 0) (hr : r ≠ 0) (hw : vacS r s ≠ 0)
    (hk : k ≠ 0) (hD : DdS zz r s ≠ 0) (hu : u ≠ 0) :
    firstS zz r s (DtS zz r s u) (GS zz r s u) = 2 * π * (tauS zz r s k u * k) / zz := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have heta : etaS r s ≠ 0 := by unfold etaS; positivity
  have hx : xS zz s ≠ 0 := mul_ne_zero hz hs
  simp only [firstS, QhS, AS, qpS, MS, NS, WtS, CtS, gamS, QppS, Q0S, xi2S, tauS, LamS, DtS, GS]
  rw [show vacS r s = vacS r s from rfl] at hw
  field_simp
  simp only [vacS, etaS, xS, DdS, aS, bS, PS, JS, HS, HtS] at *
  ring

theorem secondS_param (hz : zz ≠ 0) (hs : s ≠ 0) (hr : r ≠ 0) (hw : vacS r s ≠ 0)
    (hD : DdS zz r s ≠ 0) (hu : u ≠ 0) :
    secondS zz r s (DtS zz r s u) (GS zz r s u) = 0 := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have heta : etaS r s ≠ 0 := by unfold etaS; positivity
  have hx : xS zz s ≠ 0 := mul_ne_zero hz hs
  simp only [secondS, QhS, AS, qpS, MS, NS, WtS, CtS, gamS, QppS, Q0S, xi2S, DtS, GS]
  field_simp
  simp only [vacS, etaS, xS, DdS, aS, bS, PS, JS, HS, HtS] at *
  ring

end param

variable (z : T → ℝ) (rho sigma : Fin 1 → ℝ)

theorem firstLHS_sc (d g : ℝ) (u : T) (i j : Fin 1) :
    firstLHS z rho sigma (sc d) (sc g) u i j =
      firstS (z default) (rho 0) (sigma 0) d g := by
  have hu : u = default := Subsingleton.elim _ _
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hu hi hj
  simp only [firstLHS, firstS, dressedQhat, Qhat, QhS, amplitudeA, amplitudeQp, W, C, sc,
    mixDA, mixDqp, mixM, mixN, Wt, Ct, gam, sigMix, edgeLo, edgeHi,
    Finset.univ_unique, Finset.sum_singleton, Qppphys, Q0phys, xi2, vacMix, etaMix,
    QppS, Q0S, xi2S, vacS, AS, qpS, MS, NS, WtS, CtS, gamS, Ez, if_true, sub_self, zero_div,
    mul_zero, Real.exp_zero, one_mul, mul_one, Fin.default_eq_zero, add_self_div_two]
  ring_nf

theorem secondLHS_sub_sc (d g : ℝ) (u : T) (i j : Fin 1) :
    secondLHS z rho sigma (sc d) (sc g) u i j - secondRHS z rho sigma (sc d) (sc g) u i j =
      secondS (z default) (rho 0) (sigma 0) d g := by
  have hu : u = default := Subsingleton.elim _ _
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hu hi hj
  simp only [secondLHS, secondRHS, secondS, dressedQhat, Qhat, QhS, amplitudeA, amplitudeQp,
    W, C, sc, mixDA, mixDqp, mixM, mixN, Wt, Ct, gam, sigMix, edgeLo, edgeHi,
    Finset.univ_unique, Finset.sum_singleton, Qppphys, Q0phys, xi2, vacMix, etaMix,
    QppS, Q0S, xi2S, vacS, AS, qpS, MS, NS, WtS, CtS, gamS, Ez, if_true, sub_self, zero_div,
    mul_zero, Real.exp_zero, one_mul, mul_one, Fin.default_eq_zero, add_self_div_two]
  ring_nf

theorem baseSecond_sc (u : T) (l j : Fin 1) :
    baseSecond z rho sigma u l j = 1 - rho 0 * QhS (z default) (rho 0) (sigma 0) 0 0 := by
  have hu : u = default := Subsingleton.elim _ _
  have hl : l = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hu hl hj
  simp only [baseSecond, secondBlock, dressedQhat, Qhat, QhS, amplitudeA, amplitudeQp, W, C,
    mixDA, mixDqp, mixM, mixN, Wt, Ct, gam, sigMix, edgeLo, edgeHi,
    Finset.univ_unique, Finset.sum_singleton, Qppphys, Q0phys, xi2, vacMix, etaMix,
    QppS, Q0S, xi2S, vacS, AS, qpS, MS, NS, WtS, CtS, gamS, Ez, if_true, sub_self, zero_div,
    mul_zero, Real.exp_zero, one_mul, mul_one, Fin.default_eq_zero, add_self_div_two,
    Pi.zero_apply, zero_mul, add_zero]

/-- The PY seed of one species and one tail. -/
def seedS (zz r s : ℝ) : ℝ :=
  (QppS r s + zz * Q0S r s) / zz ^ 2 / (2 * π * (1 - r * QhS zz r s 0 0))

theorem baseSeed_sc (u : T) (i j : Fin 1) :
    baseSeed z rho sigma u i j = seedS (z default) (rho 0) (sigma 0) := by
  have hu : u = default := Subsingleton.elim _ _
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hu hi hj
  have hB := baseSecond_sc z rho sigma default 0 0
  simp only [baseSeed, Pi.smul_apply, smul_eq_mul, rightBlock_apply, inverseBlocks,
    Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero, Matrix.inv_def,
    Matrix.det_fin_one, Matrix.adjugate_fin_one, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.of_apply, hB, baseSource, Qppphys, Q0phys, xi2, vacMix, etaMix, seedS, QppS, Q0S,
    xi2S, vacS, Ring.inverse_eq_inv', smul_eq_mul, mul_one]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem isRoot_param (K : TailMatrix T 1) (k : ℝ) (hK : ∀ u i j, K u i j = k)
    (hz : z default ≠ 0) (hs : sigma 0 ≠ 0) (hr : rho 0 ≠ 0) (hw : vacS (rho 0) (sigma 0) ≠ 0)
    (hk : k ≠ 0) (hD : DdS (z default) (rho 0) (sigma 0) ≠ 0) (v : ℝ) (hv : v ≠ 0) :
    IsRoot z rho sigma (tauS (z default) (rho 0) (sigma 0) k v • K)
      (sc (DtS (z default) (rho 0) (sigma 0) v)) (sc (GS (z default) (rho 0) (sigma 0) v)) := by
  constructor
  · intro u i j
    have hu : u = default := Subsingleton.elim _ _
    rw [firstLHS_sc, firstS_param _ _ _ _ _ hz hs hr hw hk hD hv, hu]
    simp only [Pi.smul_apply, smul_eq_mul, hK]
  · intro u i j
    have h := secondLHS_sub_sc z rho sigma (DtS (z default) (rho 0) (sigma 0) v)
      (GS (z default) (rho 0) (sigma 0) v) u i j
    rw [secondS_param _ _ _ _ hz hs hr hw hD hv] at h
    linarith

theorem one_sub_QhS_zero (zz r s : ℝ) (hz : zz ≠ 0) (hs : s ≠ 0) (hw : vacS r s ≠ 0) :
    1 - r * QhS zz r s 0 0 = PS zz r s / (xS zz s ^ 3 * vacS r s ^ 2) := by
  have hx : xS zz s ≠ 0 := mul_ne_zero hz hs
  simp only [QhS, qpS, AS, MS, NS, WtS, CtS, gamS, QppS, Q0S, xi2S]
  field_simp
  simp only [vacS, etaS, xS, PS, JS, HS] at *
  ring

theorem GS_seed (zz r s : ℝ) (hz : zz ≠ 0) (hs : s ≠ 0) (hr : r ≠ 0) (hw : vacS r s ≠ 0)
    (hD : DdS zz r s ≠ 0) (hP : PS zz r s ≠ 0) :
    GS zz r s (aS zz r s) = seedS zz r s := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have heta : etaS r s ≠ 0 := by unfold etaS; positivity
  have hx : xS zz s ≠ 0 := mul_ne_zero hz hs
  rw [seedS, one_sub_QhS_zero zz r s hz hs hw]
  simp only [GS, aS, QppS, Q0S, xi2S]
  field_simp
  simp only [vacS, etaS, xS, DdS, PS, JS, HS] at *
  ring

theorem DtS_seed (zz r s : ℝ) : DtS zz r s (aS zz r s) = 0 := by
  simp [DtS]

/-- `c_D = 2 π k σ x³ (1-η)³ D`. -/
def cDS (zz r s k : ℝ) : ℝ := 2 * π * k * s * xS zz s ^ 3 * vacS r s ^ 3 * DdS zz r s

theorem DtS_eq_tau (zz r s k : ℝ) (hz : zz ≠ 0) (hs : s ≠ 0) (hr : r ≠ 0) (hw : vacS r s ≠ 0)
    (hk : k ≠ 0) (hD : DdS zz r s ≠ 0) (v : ℝ) (hv : v ≠ 0) (hvb : v ≠ bS zz r s) :
    DtS zz r s v = cDS zz r s k * tauS zz r s k v * ((0 - v)⁻¹ * (bS zz r s - v)⁻¹) := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have heta : etaS r s ≠ 0 := by unfold etaS; positivity
  have hx : xS zz s ≠ 0 := mul_ne_zero hz hs
  have h1 : (0 - v) ≠ 0 := by simpa using hv
  have h2 : bS zz r s - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hvb)
  simp only [DtS, cDS, tauS, LamS]
  field_simp
  ring

theorem GS_eq (zz r s v : ℝ) :
    GS zz r s v = s ^ 2 * xS zz s / (12 * etaS r s * DdS zz r s) *
        (etaS r s * xS zz s ^ 2 + 6 * etaS r s * xS zz s + 12 * etaS r s - xS zz s ^ 2) +
      s ^ 2 * xS zz s / (12 * etaS r s * DdS zz r s) * (vacS r s ^ 3 * xS zz s ^ 5) * (0 - v)⁻¹ := by
  simp only [GS, zero_sub, inv_neg]; ring

section signs
open SingleTailExpBounds
theorem Ez_eq (zz s : ℝ) : Ez zz s = exp (-xS zz s) := by simp [Ez, xS, neg_mul]

variable (zz r s : ℝ) (hz : 0 < zz) (hs : 0 < s) (hr : 0 < r) (hw : 0 < vacS r s)
include hz hs

theorem xS_pos : 0 < xS zz s := mul_pos hz hs

theorem Ez_lt_one : Ez zz s < 1 := by
  rw [Ez_eq]; exact expNeg_lt_one _ (xS_pos zz s hz hs)

theorem JS_pos : 0 < JS zz s := by
  have := J_pos _ (xS_pos zz s hz hs)
  simpa [JS, Ez_eq zz s] using this

theorem HS_pos : 0 < HS zz s := by
  have := H_pos _ (xS_pos zz s hz hs)
  simpa [HS, Ez_eq zz s] using this

theorem HtS_neg : HtS zz s < 0 := by
  have := Hrefl_neg _ (xS_pos zz s hz hs)
  simpa [HtS, Ez_eq zz s] using this

include hr hw

omit hz hw in
theorem etaS_pos : 0 < etaS r s := by unfold etaS; positivity

theorem DdS_pos : 0 < DdS zz r s := by
  have h1 := Ez_lt_one zz s hz hs
  have h2 := JS_pos zz s hz hs
  have h3 := etaS_pos r s hs hr
  have h4 := xS_pos zz s hz hs
  unfold DdS
  have : 0 < 1 - Ez zz s := by linarith
  positivity

theorem bS_neg : bS zz r s < 0 := by
  have h2 := JS_pos zz s hz hs
  have h3 := etaS_pos r s hs hr
  have h4 := xS_pos zz s hz hs
  have h5 := HtS_neg zz s hz hs
  have hE : 0 < Ez zz s := exp_pos _
  unfold bS
  have t1 : 0 < 18 * etaS r s ^ 2 * JS zz s := by positivity
  have t2 : 6 * etaS r s * vacS r s * HtS zz s < 0 :=
    mul_neg_of_pos_of_neg (by positivity) h5
  have t3 : 0 < Ez zz s * xS zz s ^ 3 * vacS r s ^ 2 := by positivity
  linarith

omit hz hs hr hw in
theorem bS_sub_aS : bS zz r s - aS zz r s =
    6 * etaS r s * vacS r s * (xS zz s * JS zz s) +
      xS zz s ^ 3 * vacS r s ^ 2 * (1 - Ez zz s) := by
  simp only [bS, aS, PS, JS, HS, HtS]; ring

theorem aS_lt_bS : aS zz r s < bS zz r s := by
  have h1 := Ez_lt_one zz s hz hs
  have h2 := JS_pos zz s hz hs
  have h3 := etaS_pos r s hs hr
  have h4 := xS_pos zz s hz hs
  have h := bS_sub_aS zz r s
  have : 0 < 1 - Ez zz s := by linarith
  have : 0 < bS zz r s - aS zz r s := by rw [h]; positivity
  linarith

theorem aS_neg : aS zz r s < 0 :=
  (aS_lt_bS zz r s hz hs hr hw).trans (bS_neg zz r s hz hs hr hw)

end signs

end FMSA.Paper.SingleTail

/-- info: 'FMSA.Paper.SingleTail.firstS_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.firstS_param

/-- info: 'FMSA.Paper.SingleTail.secondS_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.secondS_param

/-- info: 'FMSA.Paper.SingleTail.firstLHS_sc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.firstLHS_sc

/-- info: 'FMSA.Paper.SingleTail.secondLHS_sub_sc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.secondLHS_sub_sc

/-- info: 'FMSA.Paper.SingleTail.baseSecond_sc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.baseSecond_sc

/-- info: 'FMSA.Paper.SingleTail.baseSeed_sc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.baseSeed_sc

/-- info: 'FMSA.Paper.SingleTail.isRoot_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.isRoot_param

/-- info: 'FMSA.Paper.SingleTail.one_sub_QhS_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.one_sub_QhS_zero

/-- info: 'FMSA.Paper.SingleTail.GS_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.GS_seed

/-- info: 'FMSA.Paper.SingleTail.DtS_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.DtS_seed

/-- info: 'FMSA.Paper.SingleTail.DtS_eq_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.DtS_eq_tau

/-- info: 'FMSA.Paper.SingleTail.GS_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.GS_eq

/-- info: 'FMSA.Paper.SingleTail.Ez_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.Ez_eq

/-- info: 'FMSA.Paper.SingleTail.xS_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.xS_pos

/-- info: 'FMSA.Paper.SingleTail.Ez_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.Ez_lt_one

/-- info: 'FMSA.Paper.SingleTail.JS_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.JS_pos

/-- info: 'FMSA.Paper.SingleTail.HS_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.HS_pos

/-- info: 'FMSA.Paper.SingleTail.HtS_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.HtS_neg

/-- info: 'FMSA.Paper.SingleTail.etaS_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.etaS_pos

/-- info: 'FMSA.Paper.SingleTail.DdS_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.DdS_pos

/-- info: 'FMSA.Paper.SingleTail.bS_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.bS_neg

/-- info: 'FMSA.Paper.SingleTail.bS_sub_aS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.bS_sub_aS

/-- info: 'FMSA.Paper.SingleTail.aS_lt_bS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.aS_lt_bS

/-- info: 'FMSA.Paper.SingleTail.aS_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTail.aS_neg
