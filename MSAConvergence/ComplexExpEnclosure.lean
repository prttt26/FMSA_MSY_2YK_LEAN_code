import MSAConvergence.ComplexTaylorModels
import Mathlib.Analysis.Complex.Exponential

/-! Executable enclosures of `exp (-i a)` and of complex rational expressions in it.

* `CExpr` is a small complex expression language with one input `E` and exact complex
  rational constants. Its interval evaluation is sound (`CExpr.enclose_sound`).
* `expBox` encloses `exp (-i a)` for a dyadic `a`. It takes `n` Taylor terms of `exp (-i a / 2^j)`,
  adds the `Complex.exp_bound` remainder, and squares `j` times. Every step is sound for every
  input; a numerical check only decides whether a particular box is tight enough. -/
noncomputable section
namespace FMSA.Convergence.ComplexExpEnclosure
open ScaledIntegerIntervals ComplexTaylorModels

variable {s : ℤ}

/-- Complex expressions in one input `E`, with constants `(a + b i) / d`. -/
inductive CExpr where
  | E : CExpr
  | q : ℤ → ℤ → ℕ → CExpr
  | add : CExpr → CExpr → CExpr
  | neg : CExpr → CExpr
  | mul : CExpr → CExpr → CExpr

namespace CExpr

def eval (x : ℂ) : CExpr → ℂ
  | E => x
  | q a b d => ⟨(a : ℝ) / (d : ℝ), (b : ℝ) / (d : ℝ)⟩
  | add e f => eval x e + eval x f
  | neg e => -eval x e
  | mul e f => eval x e * eval x f

def enclose (s : ℤ) (X : CBox) : CExpr → CBox
  | E => X
  | q a b d => ⟨Interval.rational s a d, Interval.rational s b d⟩
  | add e f => (enclose s X e).add (enclose s X f)
  | neg e => (enclose s X e).neg
  | mul e f => (enclose s X e).mul s (enclose s X f)

end CExpr

theorem CExpr.enclose_sound (hs : 0 < s) {X : CBox} {x : ℂ} (hx : CEnc s X x) :
    ∀ e : CExpr, CEnc s (enclose s X e) (eval x e)
  | E => hx
  | q a b d => ⟨rational_sound s a d hs, rational_sound s b d hs⟩
  | add e f => cadd_sound (CExpr.enclose_sound hs hx e) (CExpr.enclose_sound hs hx f)
  | neg e => cneg_sound (CExpr.enclose_sound hs hx e)
  | mul e f => cmul_sound hs (CExpr.enclose_sound hs hx e) (CExpr.enclose_sound hs hx f)

/-! ### The exponential -/

/-- Taylor terms `yᵐ / m!` for `y = -i b`, `b = an / 2^p`, built by exact multiplication. -/
def termBox (s : ℤ) (an : ℤ) (p : ℕ) : ℕ → CBox
  | 0 => CBox.one s
  | m + 1 => ((termBox s an p m).mul s ⟨Interval.point 0, Interval.rational s (-an) (2 ^ p)⟩).mul s
      ⟨Interval.rational s 1 (m + 1), Interval.point 0⟩

def sumBox (s : ℤ) (an : ℤ) (p : ℕ) : ℕ → CBox
  | 0 => CBox.zero
  | m + 1 => (sumBox s an p m).add (termBox s an p m)

def widen (r : ℤ) (A : CBox) : CBox := ⟨⟨A.re.lo - r, A.re.hi + r⟩, ⟨A.im.lo - r, A.im.hi + r⟩⟩

def sqIter (s : ℤ) : ℕ → CBox → CBox
  | 0, A => A
  | j + 1, A => sqIter s j (A.mul s A)

/-- The enclosure of `exp (-i an / 2^q)` with `n` terms, `j` squarings and remainder grid bound `r`. -/
def expBox (s : ℤ) (an : ℤ) (q j n : ℕ) (r : ℤ) : CBox := sqIter s j (widen r (sumBox s an (q + j) n))

/-- The executable side conditions: `|y| ≤ 1`, `n > 0`, and the remainder bound fits in `r`. -/
def expOK (s : ℤ) (an : ℤ) (q j n : ℕ) (r : ℤ) : Bool :=
  decide (|an| ≤ 2 ^ (q + j)) && decide (0 < n) &&
    decide (s * |an| ^ n * (n + 1) ≤ r * (2 ^ ((q + j) * n) * (n.factorial * n)))

theorem point_zero_enc (x : ℝ) (hx : x = 0) : Encloses s (Interval.point 0) x := by
  subst hx; simp [Encloses, Interval.point]

/-- The exact Taylor variable `-i an / 2^p`. -/
def yv (an : ℤ) (p : ℕ) : ℂ := ⟨0, -((an : ℝ) / ((2 ^ p : ℕ) : ℝ))⟩

theorem termBox_sound (hs : 0 < s) (an : ℤ) (p : ℕ) :
    ∀ m, CEnc s (termBox s an p m) (yv an p ^ m / (m.factorial : ℂ))
  | 0 => by simpa [termBox] using cone_sound hs
  | m + 1 => by
    have hy : CEnc s ⟨Interval.point 0, Interval.rational s (-an) (2 ^ p)⟩ (yv an p) := by
      refine ⟨point_zero_enc _ (by simp [yv]), ?_⟩
      have := rational_sound s (-an) (2 ^ p) hs
      simpa [yv, neg_div] using this
    have hk := cofReal_sound (rational_sound s 1 (m + 1) hs)
    have h := cmul_sound hs (cmul_sound hs (termBox_sound hs an p m) hy) hk
    have e : yv an p ^ (m + 1) / ((m + 1).factorial : ℂ) =
        yv an p ^ m / (m.factorial : ℂ) * yv an p * ((((1 : ℤ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
      rw [Nat.factorial_succ]; push_cast; field_simp; ring
    rw [e]
    exact h

theorem sumBox_sound (hs : 0 < s) (an : ℤ) (p : ℕ) :
    ∀ n, CEnc s (sumBox s an p n) (∑ m ∈ Finset.range n, yv an p ^ m / (m.factorial : ℂ))
  | 0 => by simpa [sumBox] using czero_sound
  | n + 1 => by
    rw [Finset.sum_range_succ]
    exact cadd_sound (sumBox_sound hs an p n) (termBox_sound hs an p n)

theorem widen_sound (hs : 0 < s) {A : CBox} {x y : ℂ} {r : ℤ} (hx : CEnc s A x)
    (hxy : ‖y - x‖ ≤ (r : ℝ) / (s : ℝ)) : CEnc s (widen r A) y := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hre : |y.re - x.re| ≤ (r : ℝ) / s := (Complex.abs_re_le_norm (y - x)).trans hxy
  have him : |y.im - x.im| ≤ (r : ℝ) / s := (Complex.abs_im_le_norm (y - x)).trans hxy
  rw [abs_le] at hre him
  have e1 : ((A.re.lo - r : ℤ) : ℝ) / s = A.re.lo / s - r / s := by push_cast; ring
  have e2 : ((A.re.hi + r : ℤ) : ℝ) / s = A.re.hi / s + r / s := by push_cast; ring
  have e3 : ((A.im.lo - r : ℤ) : ℝ) / s = A.im.lo / s - r / s := by push_cast; ring
  have e4 : ((A.im.hi + r : ℤ) : ℝ) / s = A.im.hi / s + r / s := by push_cast; ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [widen, e1, e2, e3, e4] <;>
    linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2, hre.1, hre.2, him.1, him.2]

theorem sqIter_sound (hs : 0 < s) : ∀ (j : ℕ) {A : CBox} {x : ℂ}, CEnc s A x →
    CEnc s (sqIter s j A) (x ^ (2 ^ j))
  | 0, A, x, h => by simpa [sqIter] using h
  | j + 1, A, x, h => by
    have := sqIter_sound hs j (cmul_sound hs h h)
    have e : x ^ (2 ^ (j + 1)) = (x * x) ^ (2 ^ j) := by rw [pow_succ, mul_comm, pow_mul, sq]
    rw [e]
    exact this

/-- **Sound enclosure of `exp (-i a)`**, `a = an / 2^q`. -/
theorem expBox_sound (hs : 0 < s) {an : ℤ} {q j n : ℕ} {r : ℤ} (h : expOK s an q j n r = true) :
    CEnc s (expBox s an q j n r) (Complex.exp (-(Complex.I * (((an : ℝ) / (2 ^ q : ℕ) : ℝ) : ℂ)))) := by
  simp only [expOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, hn⟩, hr⟩ := h
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hP : (0 : ℝ) < ((2 ^ (q + j) : ℕ) : ℝ) := by positivity
  have hyn : ‖yv an (q + j)‖ = |(an : ℝ)| / ((2 ^ (q + j) : ℕ) : ℝ) := by
    rw [yv, Complex.norm_def, Complex.normSq_apply]
    simp only [mul_zero, zero_add, neg_mul_neg]
    rw [Real.sqrt_mul_self_eq_abs, abs_div, Nat.abs_cast]
  have hy1 : ‖yv an (q + j)‖ ≤ 1 := by
    rw [hyn, div_le_one hP]; push_cast; exact_mod_cast h1
  have hbound := Complex.exp_bound hy1 hn
  have hPn : ((2 ^ (q + j) : ℕ) : ℝ) ^ n = ((2 ^ ((q + j) * n) : ℕ) : ℝ) := by push_cast; rw [← pow_mul]
  have hr' : (s : ℝ) * |(an : ℝ)| ^ n * (n + 1) ≤ r * (((2 ^ ((q + j) * n) : ℕ) : ℝ) * (n.factorial * n)) := by
    exact_mod_cast hr
  have hfn : (0 : ℝ) < (n.factorial : ℝ) * n := by positivity
  have hrem : ‖yv an (q + j)‖ ^ n * ((n.succ : ℝ) * ((n.factorial : ℝ) * n)⁻¹) ≤ (r : ℝ) / s := by
    rw [hyn, div_pow, hPn, le_div_iff₀ hsR]
    have hD : (0 : ℝ) < ((2 ^ ((q + j) * n) : ℕ) : ℝ) * (n.factorial * n) := by positivity
    calc |(an : ℝ)| ^ n / ((2 ^ ((q + j) * n) : ℕ) : ℝ) * ((n.succ : ℝ) * ((n.factorial : ℝ) * n)⁻¹) * s
        = ((s : ℝ) * |(an : ℝ)| ^ n * (n + 1)) / (((2 ^ ((q + j) * n) : ℕ) : ℝ) * (n.factorial * n)) := by
          push_cast; field_simp
      _ ≤ (r * (((2 ^ ((q + j) * n) : ℕ) : ℝ) * (n.factorial * n))) /
          (((2 ^ ((q + j) * n) : ℕ) : ℝ) * (n.factorial * n)) := by gcongr
      _ = r := by field_simp
  have hw := widen_sound hs (sumBox_sound hs an (q + j) n) (hbound.trans hrem)
  have hsq := sqIter_sound hs j hw
  rw [← Complex.exp_nat_mul] at hsq
  have e : Complex.exp (-(Complex.I * (((an : ℝ) / (2 ^ q : ℕ) : ℝ) : ℂ))) =
      Complex.exp (((2 ^ j : ℕ) : ℂ) * yv an (q + j)) := by
    congr 1
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.neg_re, Complex.neg_im, yv, Complex.natCast_re, Complex.natCast_im] <;>
      push_cast <;> field_simp <;> ring
  rw [e]
  exact hsq

/-- info: 'FMSA.Convergence.ComplexExpEnclosure.CExpr.enclose_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexExpEnclosure.CExpr.enclose_sound
/-- info: 'FMSA.Convergence.ComplexExpEnclosure.point_zero_enc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexExpEnclosure.point_zero_enc
/-- info: 'FMSA.Convergence.ComplexExpEnclosure.termBox_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexExpEnclosure.termBox_sound
/-- info: 'FMSA.Convergence.ComplexExpEnclosure.sumBox_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexExpEnclosure.sumBox_sound
/-- info: 'FMSA.Convergence.ComplexExpEnclosure.widen_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexExpEnclosure.widen_sound
/-- info: 'FMSA.Convergence.ComplexExpEnclosure.sqIter_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexExpEnclosure.sqIter_sound
/-- info: 'FMSA.Convergence.ComplexExpEnclosure.expBox_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ComplexExpEnclosure.expBox_sound
end FMSA.Convergence.ComplexExpEnclosure
