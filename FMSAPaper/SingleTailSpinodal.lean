import FMSAPaper.SingleTailParametrization
import FMSAPaper.QuarticBranch
import FMSAPaper.SingleTailRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Single-tail zero-mode sign at the quartic fold. -/
noncomputable section
open Real Set Filter Topology

namespace FMSA.Paper.SingleTailSpinodal
open SingleTail QuarticBranch
open ExactMSA.MultiTailMixture TaylorRoot FoldRadius

def criticalPolynomial (a b u : ℝ) : ℝ :=
  4 * u ^ 2 - 3 * (a + b) * u + 2 * a * b

def spinNumerator (a b m u : ℝ) : ℝ :=
  2 * u ^ 2 - 2 * (a + b + m) * u + 2 * a * b + m * (a + b)

def expRemainder (x : ℝ) : ℝ :=
  4 * (1 - exp (-x)) ^ 2 - 3 * x * (1 - exp (-x) ^ 2) +
    2 * exp (-x) * x ^ 2

theorem exp_square_gap (x : ℝ) (hx : 0 < x) :
    0 < (1 - exp (-x)) ^ 2 - x ^ 2 * exp (-x) := by
  have hs : x / 2 < sinh (x / 2) := self_lt_sinh_iff.mpr (by linarith)
  have he : 0 < exp (-x / 2) := exp_pos _
  have h1 : exp (-x / 2) * exp (x / 2) = 1 := by
    rw [← exp_add]
    convert exp_zero using 1
    congr 1
    ring
  have h2 : exp (-x / 2) * exp (-(x / 2)) = exp (-x) := by
    rw [← exp_add]
    congr 1
    ring
  have hprod : 2 * exp (-x / 2) * sinh (x / 2) = 1 - exp (-x) := by
    rw [sinh_eq]
    nlinarith [h1, h2]
  have hlt : x * exp (-x / 2) < 1 - exp (-x) := by
    have hh := mul_lt_mul_of_pos_left hs (by positivity : 0 < 2 * exp (-x / 2))
    nlinarith
  have ha : 0 < x * exp (-x / 2) := mul_pos hx he
  have hsum : 0 < (1 - exp (-x)) + x * exp (-x / 2) := by linarith
  have hsq : (x * exp (-x / 2)) ^ 2 < (1 - exp (-x)) ^ 2 := by
    have hh := mul_pos (sub_pos.mpr hlt) hsum
    nlinarith
  have hpow : exp (-x / 2) ^ 2 = exp (-x) := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  rw [mul_pow, hpow] at hsq
  linarith

theorem expRemainder_neg (x : ℝ) (hx : 0 < x) : expRemainder x < 0 := by
  have hE : 0 < 1 - exp (-x) := sub_pos.mpr (exp_lt_one_iff.mpr (by linarith))
  have hJ := SingleTailExpBounds.J_pos x hx
  have hgap := exp_square_gap x hx
  have hid : expRemainder x =
      -3 * (1 - exp (-x)) * (exp (-x) * (x + 2) + x - 2) -
        2 * ((1 - exp (-x)) ^ 2 - x ^ 2 * exp (-x)) := by
    unfold expRemainder
    ring
  rw [hid]
  nlinarith [mul_pos hE hJ]

theorem spinNumerator_decomposition (a b m u : ℝ) :
    spinNumerator a b m u =
      (u + m) * (a + b - 2 * u) + criticalPolynomial a b u := by
  unfold spinNumerator criticalPolynomial
  ring

theorem c1_lt_of_critical_neg {a b u : ℝ} (hab : a < b) (hb : b < 0)
    (hu : criticalPolynomial a b u < 0) : c1 a b < u := by
  have hf := quad_factor hab hb u
  have hle := c1_le_c2 hab hb
  unfold criticalPolynomial at hu
  rw [hf] at hu
  by_contra h
  have h1 : 0 ≤ c1 a b - u := by linarith
  have h2 : 0 ≤ c2 a b - u := by linarith
  nlinarith [mul_nonneg h1 h2]

theorem c1_lt_midpoint {a b : ℝ} (hab : a < b) (hb : b < 0) :
    c1 a b < (a + b) / 2 := by
  apply c1_lt_of_critical_neg hab hb
  unfold criticalPolynomial
  have hsq : 0 < (a - b) ^ 2 := sq_pos_of_ne_zero (by linarith)
  nlinarith

theorem spinNumerator_fold_neg {a b m : ℝ} (hab : a < b) (hb : b < 0)
    (hm : criticalPolynomial a b (-m) < 0) :
    spinNumerator a b m (c1 a b) < 0 := by
  have hleft : c1 a b + m < 0 := by
    have := c1_lt_of_critical_neg hab hb hm
    linarith
  have hright : 0 < a + b - 2 * c1 a b := by
    have := c1_lt_midpoint hab hb
    linarith
  have hzero : criticalPolynomial a b (c1 a b) = 0 := by
    unfold criticalPolynomial
    rw [quad_factor hab hb]
    ring
  rw [spinNumerator_decomposition, hzero, add_zero]
  exact mul_neg_of_neg_of_pos hleft hright

def spinScale (zz r s : ℝ) : ℝ := (1 + 2 * etaS r s) * DdS zz r s

theorem AS_param (zz r s u : ℝ) (hz : zz ≠ 0) (hs : s ≠ 0) (hr : r ≠ 0)
    (hv : vacS r s ≠ 0) (hd : DdS zz r s ≠ 0) (hu : u ≠ 0) :
    AS zz r s (DtS zz r s u) (GS zz r s u) / (2 * π) =
      spinNumerator (aS zz r s) (bS zz r s) (spinScale zz r s) u /
        (xS zz s * vacS r s ^ 3 * DdS zz r s ^ 2) := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have heta : etaS r s ≠ 0 := by unfold etaS; positivity
  have hx : xS zz s ≠ 0 := mul_ne_zero hz hs
  simp only [AS, MS, NS, WtS, CtS, gamS, QppS, xi2S, DtS, GS,
    spinNumerator, spinScale]
  field_simp
  simp only [vacS, etaS, xS, DdS, aS, bS, PS, JS, HS, HtS] at *
  ring

theorem critical_neg_spinScale (zz r s : ℝ) (hz : 0 < zz) (hs : 0 < s)
    (hr : 0 < r) (hv : 0 < vacS r s) :
    criticalPolynomial (aS zz r s) (bS zz r s) (-spinScale zz r s) < 0 := by
  have he := etaS_pos r s hs hr
  have hx := xS_pos zz s hz hs
  have hj := JS_pos zz s hz hs
  have hE := Ez_lt_one zz s hz hs
  have hR0 : 4 * (1 - Ez zz s) ^ 2 - 3 * xS zz s * (1 - Ez zz s ^ 2) +
      2 * Ez zz s * xS zz s ^ 2 < 0 := by
    simpa only [expRemainder, ← Ez_eq zz s] using expRemainder_neg (xS zz s) hx
  have hR1 : -2 * JS zz s - 3 * xS zz s ^ 2 * (1 - Ez zz s) < 0 := by
    have hp : 0 ≤ 3 * xS zz s ^ 2 * (1 - Ez zz s) := by positivity
    linarith
  have hscale : 1 + 2 * etaS r s = vacS r s + 3 * etaS r s := by
    simp only [vacS, etaS]
    ring
  have hid : criticalPolynomial (aS zz r s) (bS zz r s) (-spinScale zz r s) =
      -36 * etaS r s ^ 2 * vacS r s ^ 2 * xS zz s ^ 2 * JS zz s ^ 2 +
      3 * etaS r s * vacS r s ^ 3 * xS zz s ^ 2 * JS zz s *
        (-2 * JS zz s - 3 * xS zz s ^ 2 * (1 - Ez zz s)) +
      vacS r s ^ 4 * xS zz s ^ 4 *
        (4 * (1 - Ez zz s) ^ 2 - 3 * xS zz s * (1 - Ez zz s ^ 2) +
          2 * Ez zz s * xS zz s ^ 2) := by
    simp only [criticalPolynomial, spinScale]
    rw [hscale]
    simp only [aS, bS, PS, DdS, JS, HS, HtS]
    ring
  have h1 : -36 * etaS r s ^ 2 * vacS r s ^ 2 * xS zz s ^ 2 * JS zz s ^ 2 < 0 := by
    have hp : 0 < 36 * etaS r s ^ 2 * vacS r s ^ 2 * xS zz s ^ 2 * JS zz s ^ 2 := by
      positivity
    linarith
  have h2 : 3 * etaS r s * vacS r s ^ 3 * xS zz s ^ 2 * JS zz s *
      (-2 * JS zz s - 3 * xS zz s ^ 2 * (1 - Ez zz s)) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hR1
  have h3 : vacS r s ^ 4 * xS zz s ^ 4 *
      (4 * (1 - Ez zz s) ^ 2 - 3 * xS zz s * (1 - Ez zz s ^ 2) +
        2 * Ez zz s * xS zz s ^ 2) < 0 := mul_neg_of_pos_of_neg (by positivity) hR0
  rw [hid]
  linarith

theorem AS_fold_neg (zz r s : ℝ) (hz : 0 < zz) (hs : 0 < s)
    (hr : 0 < r) (hv : 0 < vacS r s) :
    AS zz r s (DtS zz r s (c1 (aS zz r s) (bS zz r s)))
      (GS zz r s (c1 (aS zz r s) (bS zz r s))) < 0 := by
  have hab := aS_lt_bS zz r s hz hs hr hv
  have hb := bS_neg zz r s hz hs hr hv
  have hd := DdS_pos zz r s hz hs hr hv
  have hx := xS_pos zz s hz hs
  have hu : c1 (aS zz r s) (bS zz r s) ≠ 0 :=
    ne_of_lt ((crit_order hab hb).2.1.trans hb)
  have hp := AS_param zz r s (c1 (aS zz r s) (bS zz r s))
    hz.ne' hs.ne' hr.ne' hv.ne' hd.ne' hu
  have hn := spinNumerator_fold_neg hab hb (critical_neg_spinScale zz r s hz hs hr hv)
  have hden : 0 < xS zz s * vacS r s ^ 3 * DdS zz r s ^ 2 := by positivity
  have hquot : AS zz r s (DtS zz r s (c1 (aS zz r s) (bS zz r s)))
      (GS zz r s (c1 (aS zz r s) (bS zz r s))) / (2 * π) < 0 := by
    rw [hp]
    exact div_neg_of_neg_of_pos hn hden
  have hA := (div_lt_iff₀ (by positivity : 0 < 2 * π)).mp hquot
  simpa using hA

theorem AS_seed_pos (zz r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hv : 0 < vacS r s) :
    0 < AS zz r s (DtS zz r s (aS zz r s)) (GS zz r s (aS zz r s)) := by
  rw [DtS_seed]
  simp only [AS, MS, NS, WtS, CtS, mul_zero, add_zero]
  unfold QppS xi2S
  positivity

theorem exists_zeroMode_parameter (zz r s : ℝ) (hz : 0 < zz) (hs : 0 < s)
    (hr : 0 < r) (hv : 0 < vacS r s) :
    ∃ u ∈ Ioo (aS zz r s) (c1 (aS zz r s) (bS zz r s)),
      AS zz r s (DtS zz r s u) (GS zz r s u) = 0 := by
  have hab := aS_lt_bS zz r s hz hs hr hv
  have hb := bS_neg zz r s hz hs hr hv
  have hd := DdS_pos zz r s hz hs hr hv
  have hx := xS_pos zz s hz hs
  have ha0 := aS_neg zz r s hz hs hr hv
  have hac := (crit_order hab hb).1
  have hden : 0 < xS zz s * vacS r s ^ 3 * DdS zz r s ^ 2 := by positivity
  have hn0 : 0 < spinNumerator (aS zz r s) (bS zz r s) (spinScale zz r s) (aS zz r s) := by
    have hp := AS_param zz r s (aS zz r s) hz.ne' hs.ne' hr.ne' hv.ne' hd.ne' ha0.ne
    have hpos := div_pos (AS_seed_pos zz r s hr hs hv) (by positivity : 0 < 2 * π)
    rw [hp] at hpos
    exact (div_pos_iff_of_pos_right hden).mp hpos
  have hn1 := spinNumerator_fold_neg hab hb (critical_neg_spinScale zz r s hz hs hr hv)
  have hcont : ContinuousOn
      (spinNumerator (aS zz r s) (bS zz r s) (spinScale zz r s))
      (Icc (aS zz r s) (c1 (aS zz r s) (bS zz r s))) := by
    unfold spinNumerator
    fun_prop
  obtain ⟨u, hu, hzero⟩ := intermediate_value_Icc' hac.le hcont ⟨hn1.le, hn0.le⟩
  have hleft : aS zz r s < u := by
    by_contra h
    have heq : u = aS zz r s := by push Not at h; linarith [hu.1]
    rw [heq] at hzero
    linarith
  have hright : u < c1 (aS zz r s) (bS zz r s) := by
    by_contra h
    have heq : u = c1 (aS zz r s) (bS zz r s) := by push Not at h; linarith [hu.2]
    rw [heq] at hzero
    linarith
  refine ⟨u, ⟨hleft, hright⟩, ?_⟩
  have hu0 : u ≠ 0 := ne_of_lt (hright.trans ((crit_order hab hb).2.1.trans hb))
  have hp := AS_param zz r s u hz.ne' hs.ne' hr.ne' hv.ne' hd.ne' hu0
  rw [hzero, zero_div] at hp
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp at hp
  simpa using hp

theorem exists_zero_before_fold (zz r s k : ℝ) (hz : 0 < zz) (hs : 0 < s)
    (hr : 0 < r) (hv : 0 < vacS r s) (hk : 0 < k) :
    ∃ u ∈ Ioo (aS zz r s) (c1 (aS zz r s) (bS zz r s)),
      0 < tauS zz r s k u ∧
      tauS zz r s k u < foldTau (aS zz r s) (bS zz r s) (LamS zz r s k) ∧
      AS zz r s (DtS zz r s u) (GS zz r s u) = 0 := by
  obtain ⟨u, hu, hzero⟩ := exists_zeroMode_parameter zz r s hz hs hr hv
  have hab := aS_lt_bS zz r s hz hs hr hv
  have hb := bS_neg zz r s hz hs hr hv
  have he := etaS_pos r s hs hr
  have hx := xS_pos zz s hz hs
  have hd := DdS_pos zz r s hz hs hr hv
  have hL : 0 < LamS zz r s k := by unfold LamS; positivity
  have hmono := q_strictMonoOn hab hb hL
  have ha : aS zz r s ∈ Iic (c1 (aS zz r s) (bS zz r s)) := (crit_order hab hb).1.le
  have hu' : u ∈ Iic (c1 (aS zz r s) (bS zz r s)) := hu.2.le
  have hc : c1 (aS zz r s) (bS zz r s) ∈ Iic (c1 (aS zz r s) (bS zz r s)) := by simp
  have ht0 := hmono ha hu' hu.1
  have htf := hmono hu' hc hu.2
  refine ⟨u, hu, ?_, ?_, hzero⟩
  · simpa [tauS, QuarticBranch.q] using ht0
  · simpa [tauS, foldTau, QuarticBranch.q] using htf

section actual
variable {T : Type*} [Fintype T] [Unique T]
variable (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
variable (hz : 0 < z default) (hr : 0 < rho 0) (hs : 0 < sigma 0)
  (hv : 0 < MatrixQ0.vacMix rho sigma) (hk : 0 < K default 0 0)
include hz hr hs hv hk

theorem actual_single_tail_zero_before_fold :
    ∃ t : ℝ, 0 < t ∧ t < SingleTailRadius.foldCoupling z rho sigma K ∧
      IsRoot z rho sigma (t • K) (SingleTailRadius.physBranch z rho sigma K t).1
        (SingleTailRadius.physBranch z rho sigma K t).2 ∧
      AS (z default) (rho 0) (sigma 0)
        ((SingleTailRadius.physBranch z rho sigma K t).1 default 0 0)
        ((SingleTailRadius.physBranch z rho sigma K t).2 default 0 0) = 0 := by
  have hw := SingleTailRadius.hw z rho sigma hz hr hs hv
  obtain ⟨u, hu, ht0, htf, hzero⟩ :=
    exists_zero_before_fold (z default) (rho 0) (sigma 0) (K default 0 0) hz hs hr hw hk
  let t := tauS (z default) (rho 0) (sigma 0) (K default 0 0) u
  have hab := SingleTailRadius.hab z rho sigma hz hr hs hv
  have hb := SingleTailRadius.hb z rho sigma hz hr hs hv
  have hL := SingleTailRadius.hL z rho sigma K hz hr hs hv hk
  have hucc : u ∈ Icc (lowU (SingleTailRadius.aR z rho sigma))
      (c1 (SingleTailRadius.aR z rho sigma) (SingleTailRadius.bR z rho sigma)) := by
    constructor
    · unfold lowU
      linarith [hu.1]
    · exact hu.2.le
  have hbr : branch (SingleTailRadius.aR z rho sigma) (SingleTailRadius.bR z rho sigma)
      (SingleTailRadius.LR z rho sigma K) t = u := by
    dsimp only [t]
    rw [SingleTailRadius.tauS_eq_q]
    exact branch_q hab hb hL hucc
  have hlow := (SingleTailRadius.zero_mem_Ioo z rho sigma K hz hr hs hv hk).1
  have hroot := SingleTailRadius.physBranch_isRoot z rho sigma K hz hr hs hv hk
    (t := t) ⟨hlow.le.trans ht0.le, htf.le⟩
  refine ⟨t, ht0, htf, hroot, ?_⟩
  change AS (z default) (rho 0) (sigma 0)
    (DtS (z default) (rho 0) (sigma 0) (branch _ _ _ t))
    (GS (z default) (rho 0) (sigma 0) (branch _ _ _ t)) = 0
  rw [hbr]
  exact hzero

theorem actual_single_tail_zero_lt_radius
    (p : ℝ → TailMatrix T 1 × TailMatrix T 1)
    (hp : ContinuousAt p 0) (hp0 : p 0 = (0, baseSeed z rho sigma))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) :
    ∃ t : ℝ, 0 < t ∧ ENNReal.ofReal t < amplitudeRadius (branchCoefficients p) ∧
      IsRoot z rho sigma (t • K) (SingleTailRadius.physBranch z rho sigma K t).1
        (SingleTailRadius.physBranch z rho sigma K t).2 ∧
      AS (z default) (rho 0) (sigma 0)
        ((SingleTailRadius.physBranch z rho sigma K t).1 default 0 0)
        ((SingleTailRadius.physBranch z rho sigma K t).2 default 0 0) = 0 := by
  obtain ⟨t, ht0, htf, hrt, hA⟩ :=
    actual_single_tail_zero_before_fold z rho sigma K hz hr hs hv hk
  refine ⟨t, ht0, ?_, hrt, hA⟩
  rw [SingleTailRadius.single_tail_radius_eq_fold z rho sigma K hz hr hs hv hk p hp hp0 hroot]
  exact (ENNReal.ofReal_lt_ofReal_iff (ht0.trans htf)).mpr htf

end actual

end FMSA.Paper.SingleTailSpinodal

/-- info: 'FMSA.Paper.SingleTailSpinodal.exp_square_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.exp_square_gap

/-- info: 'FMSA.Paper.SingleTailSpinodal.expRemainder_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.expRemainder_neg

/-- info: 'FMSA.Paper.SingleTailSpinodal.spinNumerator_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.spinNumerator_decomposition

/-- info: 'FMSA.Paper.SingleTailSpinodal.c1_lt_of_critical_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.c1_lt_of_critical_neg

/-- info: 'FMSA.Paper.SingleTailSpinodal.c1_lt_midpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.c1_lt_midpoint

/-- info: 'FMSA.Paper.SingleTailSpinodal.spinNumerator_fold_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.spinNumerator_fold_neg

/-- info: 'FMSA.Paper.SingleTailSpinodal.AS_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.AS_param

/-- info: 'FMSA.Paper.SingleTailSpinodal.critical_neg_spinScale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.critical_neg_spinScale

/-- info: 'FMSA.Paper.SingleTailSpinodal.AS_fold_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.AS_fold_neg

/-- info: 'FMSA.Paper.SingleTailSpinodal.AS_seed_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.AS_seed_pos

/-- info: 'FMSA.Paper.SingleTailSpinodal.exists_zeroMode_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.exists_zeroMode_parameter

/-- info: 'FMSA.Paper.SingleTailSpinodal.exists_zero_before_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.exists_zero_before_fold

/-- info: 'FMSA.Paper.SingleTailSpinodal.actual_single_tail_zero_before_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.actual_single_tail_zero_before_fold

/-- info: 'FMSA.Paper.SingleTailSpinodal.actual_single_tail_zero_lt_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Paper.SingleTailSpinodal.actual_single_tail_zero_lt_radius
