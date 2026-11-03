import MSAConvergence.PureFluidLaurentJetAlgebra

set_option linter.style.header false

/-! Polynomial numerator form of the proposed pure-fluid dressing. The
master identity proves every polar-shape constraint at the origin in one
stroke, for arbitrary polynomial U and g. Connecting arbitrary analytic
U,g to these polynomial jets remains separate. -/
noncomputable section
open Polynomial
namespace FMSA.Convergence.PureFluidLaurentPolynomialBridge
open FMSA.Convergence.PureFluidHardSphereUnimodular

/-- Twice the numerator of the PY rational part, avoiding fractions in the
coefficient ring. `a,q` are eventually constant polynomials from hardA,Q. -/
def p0Num2 (a q : ℝ[X]) : ℝ[X] :=
  2*X^3-2*a+2*(a-q)*X+(2*q-a)*X^2

def s0Num2 (a q : ℝ[X]) : ℝ[X] := 2*a+2*q*X

def p0NegNum2 (a q : ℝ[X]) : ℝ[X] :=
  2*X^3+2*a+2*(a-q)*X-(2*q-a)*X^2

def s0NegNum2 (a q : ℝ[X]) : ℝ[X] := -2*a+2*q*X

/-- `X^4` times twice the proposed dressed rational part. -/
def dressedPNum2 (a q U g : ℝ[X]) : ℝ[X] :=
  X*U*p0Num2 a q+g*(s0NegNum2 a q-p0Num2 a q)

/-- `X^4` times twice the proposed dressed exponential part. -/
def dressedSNum2 (a q U g : ℝ[X]) : ℝ[X] :=
  X*U*s0Num2 a q+g*(p0NegNum2 a q-s0Num2 a q)

/-- A single exact polynomial identity carries the entire required
origin-pole shape: the displayed combination is divisible by `X^4`.
It holds for arbitrary coefficient polynomials and arbitrary dressing
polynomials; no numerical or asymptotic argument enters. -/
theorem master_polar_identity (a q U g : ℝ[X]) :
    (2:ℝ[X])*dressedPNum2 a q U g+
      ((2:ℝ[X])-2*X+X^2)*dressedSNum2 a q U g =
        X^4*((2*q+4)*U+(a-2*q-4+2*X)*g) := by
  unfold dressedPNum2 dressedSNum2 p0Num2 s0Num2 p0NegNum2 s0NegNum2
  ring

/-- Consequently all coefficients below order four in the master
combination vanish. This is the formal Laurent polar-part relation. -/
theorem master_low_coeff_zero (a q U g : ℝ[X]) (n : ℕ) (hn : n < 4) :
    ((2:ℝ[X])*dressedPNum2 a q U g+
      ((2:ℝ[X])-2*X+X^2)*dressedSNum2 a q U g).coeff n = 0 := by
  rw [master_polar_identity, Polynomial.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hn]

/-- The same exact identity with coefficients fixed by the ORIGINAL
hard-sphere PY formulas. -/
theorem actual_hard_master_polar_identity (xi : ℝ) (U g : ℝ[X]) :
    (2:ℝ[X])*dressedPNum2 (C (hardA xi)) (C (hardQ xi)) U g+
      ((2:ℝ[X])-2*X+X^2)*dressedSNum2 (C (hardA xi)) (C (hardQ xi)) U g =
        X^4*((2*C (hardQ xi)+4)*U+
          (C (hardA xi)-2*C (hardQ xi)-4+2*X)*g) :=
  master_polar_identity _ _ U g

/-- The doubled cleared numerator evaluates to the ACTUAL rational PY
piece at every nonzero real frequency. -/
theorem eval_p0Num2 (xi s : ℝ) (hs : s ≠ 0) :
    (p0Num2 (C (hardA xi)) (C (hardQ xi))).eval s =
      2*s^3*hardP xi s := by
  simp [p0Num2, hardP]
  field_simp [hs]

theorem eval_s0Num2 (xi s : ℝ) (hs : s ≠ 0) :
    (s0Num2 (C (hardA xi)) (C (hardQ xi))).eval s =
      2*s^3*hardShat xi s := by
  simp [s0Num2, hardShat]
  field_simp [hs]

theorem eval_p0NegNum2 (xi s : ℝ) (hs : s ≠ 0) :
    (p0NegNum2 (C (hardA xi)) (C (hardQ xi))).eval s =
      2*s^3*hardP xi (-s) := by
  simp [p0NegNum2, hardP]
  field_simp [hs]
  ring

theorem eval_s0NegNum2 (xi s : ℝ) (hs : s ≠ 0) :
    (s0NegNum2 (C (hardA xi)) (C (hardQ xi))).eval s =
      2*s^3*hardShat xi (-s) := by
  simp [s0NegNum2, hardShat]
  field_simp [hs]

/-- The polynomial numerator is exactly `2 s^4` times the proposed
dressed rational part, for arbitrary polynomial U and g. -/
theorem eval_dressedPNum2 (xi s : ℝ) (U g : ℝ[X]) (hs : s ≠ 0) :
    (dressedPNum2 (C (hardA xi)) (C (hardQ xi)) U g).eval s =
      2*s^4*((U.eval s-g.eval s/s)*hardP xi s+
        (g.eval s/s)*hardShat xi (-s)) := by
  simp only [dressedPNum2, eval_add, eval_mul, eval_sub, eval_X]
  rw [eval_p0Num2 xi s hs, eval_s0NegNum2 xi s hs]
  field_simp [hs]
  ring

theorem eval_dressedSNum2 (xi s : ℝ) (U g : ℝ[X]) (hs : s ≠ 0) :
    (dressedSNum2 (C (hardA xi)) (C (hardQ xi)) U g).eval s =
      2*s^4*((U.eval s-g.eval s/s)*hardShat xi s+
        (g.eval s/s)*hardP xi (-s)) := by
  simp only [dressedSNum2, eval_add, eval_mul, eval_sub, eval_X]
  rw [eval_s0Num2 xi s hs, eval_p0NegNum2 xi s hs]
  field_simp [hs]
  ring

end FMSA.Convergence.PureFluidLaurentPolynomialBridge
/-- info: 'FMSA.Convergence.PureFluidLaurentPolynomialBridge.master_polar_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentPolynomialBridge.master_polar_identity
/-- info: 'FMSA.Convergence.PureFluidLaurentPolynomialBridge.master_low_coeff_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentPolynomialBridge.master_low_coeff_zero
/-- info: 'FMSA.Convergence.PureFluidLaurentPolynomialBridge.actual_hard_master_polar_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentPolynomialBridge.actual_hard_master_polar_identity
/-- info: 'FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_p0Num2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_p0Num2
/-- info: 'FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_s0Num2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_s0Num2
/-- info: 'FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_p0NegNum2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_p0NegNum2
/-- info: 'FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_s0NegNum2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_s0NegNum2
/-- info: 'FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_dressedPNum2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_dressedPNum2
/-- info: 'FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_dressedSNum2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentPolynomialBridge.eval_dressedSNum2
