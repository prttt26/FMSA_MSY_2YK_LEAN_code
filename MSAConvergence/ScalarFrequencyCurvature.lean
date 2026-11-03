import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Exact complex basis derivatives and the compressed scalar Fourier curvature
budget. Finite signed-tail sums, positive-frequency norm estimates and
derivative uniqueness give genuine real-frequency second-derivative bounds. -/

noncomputable section
namespace FMSA.Convergence.ScalarFrequencyCurvature

def e1 (s : ℂ) : ℂ := (1-s-Complex.exp (-s))/s^2
def e1Prime (s : ℂ) : ℂ := (-1+Complex.exp (-s))/s^2-2*((1-s-Complex.exp (-s))/s^3)
def e1Second (s : ℂ) : ℂ :=
  -Complex.exp (-s)/s^2-(2+4*Complex.exp (-s))/s^3+6*(1-Complex.exp (-s))/s^4

def e2 (s : ℂ) : ℂ := (1-s+s^2/2-Complex.exp (-s))/s^3
def e2Prime (s : ℂ) : ℂ :=
  (-1+s+Complex.exp (-s))/s^3-3*((1-s+s^2/2-Complex.exp (-s))/s^4)
def e2Second (s : ℂ) : ℂ :=
  (1-Complex.exp (-s))/s^3-6*(1+Complex.exp (-s))/s^4+12*(1-Complex.exp (-s))/s^5

def w (z : ℝ) (s : ℂ) : ℂ := 1/(s+(z : ℂ))
def wPrime (z : ℝ) (s : ℂ) : ℂ := -1/(s+(z : ℂ))^2
def wSecond (z : ℝ) (s : ℂ) : ℂ := 2/(s+(z : ℂ))^3

def c (z : ℝ) (s : ℂ) : ℂ :=
  (1-Complex.exp (-s))/s+Complex.exp (-s)/(s+(z : ℂ))
def cPrime (z : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-s)/s-(1-Complex.exp (-s))/s^2-
    Complex.exp (-s)/(s+(z : ℂ))-Complex.exp (-s)/(s+(z : ℂ))^2

def cSecond (z : ℝ) (s : ℂ) : ℂ :=
  -(z : ℂ)*Complex.exp (-s)/(s*(s+(z : ℂ)))-
    2*(z : ℂ)*Complex.exp (-s)*(2*s+(z : ℂ))/(s^2*(s+(z : ℂ))^2)+
    2*Complex.exp (-s)/(s+(z : ℂ))^3+2*(1-Complex.exp (-s))/s^3

private theorem exp_neg_hasDerivAt (s : ℂ) :
    HasDerivAt (fun x : ℂ => Complex.exp (-x)) (-Complex.exp (-s)) s := by
  apply (((hasDerivAt_id s).neg).cexp).congr_deriv
  simp

/-- Genuine first derivative of the first core transform. -/
theorem e1_hasDerivAt (s : ℂ) (hs : s ≠ 0) : HasDerivAt e1 (e1Prime s) s := by
  have hN := ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)).sub (exp_neg_hasDerivAt s)
  have h := hN.div ((hasDerivAt_id s).pow 2) (pow_ne_zero 2 hs)
  apply h.congr_deriv
  dsimp [e1Prime]
  field_simp [hs]
  ring

/-- Genuine second derivative, in the grouped form used by H2. -/
theorem e1Prime_hasDerivAt (s : ℂ) (hs : s ≠ 0) : HasDerivAt e1Prime (e1Second s) s := by
  have hE := exp_neg_hasDerivAt s
  have hN := ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)).sub hE
  have hA := ((hasDerivAt_const s (-1 : ℂ)).add hE).div ((hasDerivAt_id s).pow 2) (pow_ne_zero 2 hs)
  have hB := hN.div ((hasDerivAt_id s).pow 3) (pow_ne_zero 3 hs)
  have h := hA.sub (hB.const_mul 2)
  apply h.congr_deriv
  dsimp [e1Second]
  field_simp [hs]
  ring

/-- Genuine first derivative of the second core transform. -/
theorem e2_hasDerivAt (s : ℂ) (hs : s ≠ 0) : HasDerivAt e2 (e2Prime s) s := by
  have hN := (((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)).add
    (((hasDerivAt_id s).pow 2).div_const 2)).sub (exp_neg_hasDerivAt s)
  have h := hN.div ((hasDerivAt_id s).pow 3) (pow_ne_zero 3 hs)
  apply h.congr_deriv
  dsimp [e2Prime]
  field_simp [hs]
  ring

/-- Genuine second derivative of the second core transform. -/
theorem e2Prime_hasDerivAt (s : ℂ) (hs : s ≠ 0) : HasDerivAt e2Prime (e2Second s) s := by
  have hE := exp_neg_hasDerivAt s
  have hN := (((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)).add
    (((hasDerivAt_id s).pow 2).div_const 2)).sub hE
  have hA := (((hasDerivAt_const s (-1 : ℂ)).add (hasDerivAt_id s)).add hE).div
    ((hasDerivAt_id s).pow 3) (pow_ne_zero 3 hs)
  have hB := hN.div ((hasDerivAt_id s).pow 4) (pow_ne_zero 4 hs)
  have h := hA.sub (hB.const_mul 3)
  apply h.congr_deriv
  dsimp [e2Second]
  field_simp [hs]
  ring

/-- Genuine first derivative of a whole exponential tail transform. -/
theorem w_hasDerivAt (z : ℝ) (s : ℂ) (hz : s+(z : ℂ) ≠ 0) :
    HasDerivAt (w z) (wPrime z s) s := by
  have h := (hasDerivAt_const s (1 : ℂ)).div ((hasDerivAt_id s).add_const (z : ℂ)) hz
  apply h.congr_deriv
  dsimp [wPrime]
  field_simp [hz]
  ring

/-- Genuine second derivative of the whole exponential tail transform. -/
theorem wPrime_hasDerivAt (z : ℝ) (s : ℂ) (hz : s+(z : ℂ) ≠ 0) :
    HasDerivAt (wPrime z) (wSecond z s) s := by
  have h := (hasDerivAt_const s (-1 : ℂ)).div
    (((hasDerivAt_id s).add_const (z : ℂ)).pow 2) (pow_ne_zero 2 hz)
  apply h.congr_deriv
  dsimp [wSecond]
  field_simp [hz]
  ring

/-- The compact and shifted C pieces are differentiated TOGETHER. -/
theorem c_hasDerivAt (z : ℝ) (s : ℂ) (hs : s ≠ 0) (hz : s+(z : ℂ) ≠ 0) :
    HasDerivAt (c z) (cPrime z s) s := by
  have hE := exp_neg_hasDerivAt s
  have h := (((hasDerivAt_const s (1 : ℂ)).sub hE).div (hasDerivAt_id s) hs).add
    (hE.div ((hasDerivAt_id s).add_const (z : ℂ)) hz)
  apply h.congr_deriv
  dsimp [cPrime]
  field_simp [hs,hz]
  ring

/-- The true second derivative retains the cancellation used by compressedH2. -/
theorem cPrime_hasDerivAt (z : ℝ) (s : ℂ) (hs : s ≠ 0) (hz : s+(z : ℂ) ≠ 0) :
    HasDerivAt (cPrime z) (cSecond z s) s := by
  have hE := exp_neg_hasDerivAt s
  have h := (((hE.div (hasDerivAt_id s) hs).sub
    (((hasDerivAt_const s (1 : ℂ)).sub hE).div ((hasDerivAt_id s).pow 2) (pow_ne_zero 2 hs))).sub
    (hE.div ((hasDerivAt_id s).add_const (z : ℂ)) hz)).sub
    (hE.div (((hasDerivAt_id s).add_const (z : ℂ)).pow 2) (pow_ne_zero 2 hz))
  apply h.congr_deriv
  dsimp [cSecond]
  field_simp [hs,hz]
  ring

private theorem axis_norms (k : ℝ) (hk : 0<k) (z : ℝ) :
    let s : ℂ := Complex.I*(k : ℂ)
    s≠0 ∧ ‖s‖=k ∧ ‖Complex.exp (-s)‖=1 ∧
      ‖1-Complex.exp (-s)‖≤2 ∧ ‖1+Complex.exp (-s)‖≤2 ∧
      k≤‖s+(z : ℂ)‖ ∧ s+(z : ℂ)≠0 := by
  dsimp only
  have hn : ‖Complex.I*(k : ℂ)‖=k := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
  have he : ‖Complex.exp (-(Complex.I*(k : ℂ)))‖=1 := by
    rw [Complex.norm_exp]
    simp
  have hm : ‖1-Complex.exp (-(Complex.I*(k : ℂ)))‖≤2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖+‖Complex.exp (-(Complex.I*(k : ℂ)))‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one,he]; norm_num
  have hp : ‖1+Complex.exp (-(Complex.I*(k : ℂ)))‖≤2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖+‖Complex.exp (-(Complex.I*(k : ℂ)))‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one,he]; norm_num
  have hz : k≤‖Complex.I*(k : ℂ)+(z : ℂ)‖ := by
    simpa only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,sub_zero,add_zero,zero_add,
      abs_of_pos hk] using Complex.abs_im_le_norm (Complex.I*(k : ℂ)+(z : ℂ))
  refine ⟨mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk.ne'),hn,he,hm,hp,hz,?_⟩
  intro hzero
  rw [hzero,norm_zero] at hz
  linarith

private theorem norm_div_le (u v : ℂ) (A a : ℝ) (hu : ‖u‖≤A) (ha : 0<a) (hv : a≤‖v‖) :
    ‖u/v‖≤A/a := by
  rw [norm_div]
  exact (div_le_div_of_nonneg_left (norm_nonneg u) ha hv).trans
    (div_le_div_of_nonneg_right hu ha.le)

private theorem norm_div_pow_le (u v : ℂ) (A a : ℝ) (n : ℕ)
    (hu : ‖u‖≤A) (ha : 0<a) (hv : a≤‖v‖) : ‖u/v^n‖≤A/a^n := by
  apply norm_div_le u (v^n) A (a^n) hu (pow_pos ha n)
  rw [norm_pow]
  exact pow_le_pow_left₀ ha.le hv n

private theorem norm_nat_mul_le (n : ℕ) (u : ℂ) (A : ℝ) (hu : ‖u‖≤A) :
    ‖(n : ℂ)*u‖≤(n : ℝ)*A := by
  have hn : ‖(n : ℂ)‖=(n : ℝ) := by simp
  rw [norm_mul,hn]
  exact mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg n)

/-- Exact triangle budget for the true second first-core derivative on the
ENTIRE positive imaginary-frequency axis. -/
theorem e1Second_norm_le (k : ℝ) (hk : 0<k) :
    ‖e1Second (Complex.I*(k : ℂ))‖≤1/k^2+6/k^3+12/k^4 := by
  let s : ℂ := Complex.I*(k : ℂ)
  have hn : ‖s‖=k := (axis_norms k hk 0).2.1
  have he : ‖Complex.exp (-s)‖=1 := (axis_norms k hk 0).2.2.1
  have hm : ‖1-Complex.exp (-s)‖≤2 := (axis_norms k hk 0).2.2.2.1
  have hnum : ‖(2 : ℂ)+4*Complex.exp (-s)‖≤6 := by
    calc
      _ ≤ ‖(2 : ℂ)‖+‖(4 : ℂ)*Complex.exp (-s)‖ := norm_add_le _ _
      _ = 6 := by rw [norm_mul,he]; norm_num
  have h1 := norm_div_pow_le (-Complex.exp (-s)) s 1 k 2 (by simp only [norm_neg,he,le_refl]) hk hn.ge
  have h2 := norm_div_pow_le (2+4*Complex.exp (-s)) s 6 k 3 hnum hk hn.ge
  have h3 := norm_div_pow_le (6*(1-Complex.exp (-s))) s 12 k 4
    (by convert norm_nat_mul_le 6 (1-Complex.exp (-s)) 2 hm using 1 <;> norm_num) hk hn.ge
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add h1 h2)) h3)

/-- Exact second-core curvature triangle budget, including all inverse powers. -/
theorem e2Second_norm_le (k : ℝ) (hk : 0<k) :
    ‖e2Second (Complex.I*(k : ℂ))‖≤2/k^3+12/k^4+24/k^5 := by
  let s : ℂ := Complex.I*(k : ℂ)
  have hn : ‖s‖=k := (axis_norms k hk 0).2.1
  have hm : ‖1-Complex.exp (-s)‖≤2 := (axis_norms k hk 0).2.2.2.1
  have hp : ‖1+Complex.exp (-s)‖≤2 := (axis_norms k hk 0).2.2.2.2.1
  have h1 := norm_div_pow_le (1-Complex.exp (-s)) s 2 k 3 hm hk hn.ge
  have h2 := norm_div_pow_le (6*(1+Complex.exp (-s))) s 12 k 4
    (by convert norm_nat_mul_le 6 (1+Complex.exp (-s)) 2 hp using 1 <;> norm_num) hk hn.ge
  have h3 := norm_div_pow_le (12*(1-Complex.exp (-s))) s 24 k 5
    (by convert norm_nat_mul_le 12 (1-Complex.exp (-s)) 2 hm using 1 <;> norm_num) hk hn.ge
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add h1 h2)) h3)

/-- Whole-tail second derivative decays as the third inverse frequency power. -/
theorem wSecond_norm_le (z k : ℝ) (hk : 0<k) :
    ‖wSecond z (Complex.I*(k : ℂ))‖≤2/k^3 := by
  apply norm_div_pow_le 2 _ 2 k 3 (by norm_num) hk
  exact (axis_norms k hk z).2.2.2.2.2.1

/-- The combined compact/shifted C curvature has the EXACT grouped H2 bound.
No assumed ordering with the alternative C budget is used. -/
theorem cSecond_norm_le (z k : ℝ) (hz : 0<z) (hk : 0<k) :
    ‖cSecond z (Complex.I*(k : ℂ))‖≤z/k^2+(6+4*z)/k^3+2*z^2/k^4 := by
  let s : ℂ := Complex.I*(k : ℂ)
  have hn : ‖s‖=k := (axis_norms k hk z).2.1
  have he : ‖Complex.exp (-s)‖=1 := (axis_norms k hk z).2.2.1
  have hm : ‖1-Complex.exp (-s)‖≤2 := (axis_norms k hk z).2.2.2.1
  have hden : k≤‖s+(z : ℂ)‖ := (axis_norms k hk z).2.2.2.2.2.1
  have hd1 : k^2≤‖s*(s+(z : ℂ))‖ := by
    rw [norm_mul,hn]
    nlinarith [mul_le_mul_of_nonneg_left hden hk.le]
  have hd2 : k^4≤‖s^2*(s+(z : ℂ))^2‖ := by
    rw [norm_mul,norm_pow,norm_pow,hn]
    calc
      _ = k^2*k^2 := by ring
      _ ≤ k^2*‖s+(z : ℂ)‖^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk.le hden 2) (sq_nonneg k)
  have hlin : ‖2*s+(z : ℂ)‖≤2*k+z := by
    calc
      _ ≤ ‖(2 : ℂ)*s‖+‖(z : ℂ)‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul,hn]; simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz]
  have hnum1 : ‖-(z : ℂ)*Complex.exp (-s)‖≤z := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz,he]
  have hnum2 : ‖2*(z : ℂ)*Complex.exp (-s)*(2*s+(z : ℂ))‖≤2*z*(2*k+z) := by
    calc
      _ = (2*z)*‖2*s+(z : ℂ)‖ := by
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz,he]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hlin (by positivity)
  have h1 := norm_div_le (-(z : ℂ)*Complex.exp (-s)) (s*(s+(z : ℂ))) z (k^2)
    hnum1 (sq_pos_of_pos hk) hd1
  have h2 := norm_div_le (2*(z : ℂ)*Complex.exp (-s)*(2*s+(z : ℂ)))
    (s^2*(s+(z : ℂ))^2) (2*z*(2*k+z)) (k^4) hnum2 (pow_pos hk 4) hd2
  have h3 := norm_div_pow_le (2*Complex.exp (-s)) (s+(z : ℂ)) 2 k 3
    (by convert norm_nat_mul_le 2 (Complex.exp (-s)) 1 he.le using 1 <;> norm_num) hk hden
  have h4 := norm_div_pow_le (2*(1-Complex.exp (-s))) s 4 k 3
    (by convert norm_nat_mul_le 2 (1-Complex.exp (-s)) 2 hm using 1 <;> norm_num) hk hn.ge
  calc
    _ ≤ z/k^2+2*z*(2*k+z)/k^4+2/k^3+4/k^3 :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add
          ((norm_sub_le _ _).trans (add_le_add h1 h2)) h3)) h4)
    _ = _ := by field_simp [hk.ne']; ring

open scoped BigOperators
variable {T : Type*} [Fintype T]

def closedSymbol (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (s : ℂ) : ℂ :=
  e1 s*(qp : ℂ)+e2 s*(A : ℂ)+∑ u, (w (z u) s*(W u : ℂ)+c (z u) s*(C u : ℂ))

def firstSymbol (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (s : ℂ) : ℂ :=
  e1Prime s*(qp : ℂ)+e2Prime s*(A : ℂ)+
    ∑ u, (wPrime (z u) s*(W u : ℂ)+cPrime (z u) s*(C u : ℂ))

def secondSymbol (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (s : ℂ) : ℂ :=
  e1Second s*(qp : ℂ)+e2Second s*(A : ℂ)+
    ∑ u, (wSecond (z u) s*(W u : ℂ)+cSecond (z u) s*(C u : ℂ))

/-- Genuine complex derivative of the whole finite signed-tail transform. -/
theorem closedSymbol_hasDerivAt (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (s : ℂ) (hs : s≠0) (hz : ∀ u, s+(z u : ℂ)≠0) :
    HasDerivAt (closedSymbol z qp A W C) (firstSymbol z qp A W C s) s := by
  exact ((e1_hasDerivAt s hs).mul_const (qp : ℂ)).add
    ((e2_hasDerivAt s hs).mul_const (A : ℂ)) |>.add
      (HasDerivAt.fun_sum fun u _ =>
        ((w_hasDerivAt (z u) s (hz u)).mul_const (W u : ℂ)).add
          ((c_hasDerivAt (z u) s hs (hz u)).mul_const (C u : ℂ)))

/-- True second complex derivative; the C pieces remain grouped. -/
theorem firstSymbol_hasDerivAt (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (s : ℂ) (hs : s≠0) (hz : ∀ u, s+(z u : ℂ)≠0) :
    HasDerivAt (firstSymbol z qp A W C) (secondSymbol z qp A W C s) s := by
  exact ((e1Prime_hasDerivAt s hs).mul_const (qp : ℂ)).add
    ((e2Prime_hasDerivAt s hs).mul_const (A : ℂ)) |>.add
      (HasDerivAt.fun_sum fun u _ =>
        ((wPrime_hasDerivAt (z u) s (hz u)).mul_const (W u : ℂ)).add
          ((cPrime_hasDerivAt (z u) s hs (hz u)).mul_const (C u : ℂ)))

def curvatureBudget (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (k : ℝ) : ℝ :=
  |qp| *(1/k^2+6/k^3+12/k^4)+|A| *(2/k^3+12/k^4+24/k^5)+
    ∑ u, (|W u| *(2/k^3)+|C u| *(z u/k^2+(6+4*z u)/k^3+2*(z u)^2/k^4))

/-- The literal four inverse-power coefficient budget of compressedH2. -/
def groupedBudget (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (k : ℝ) : ℝ :=
  (|qp|+∑ u, z u*|C u|)/k^2+
    (6*|qp|+2*|A|+∑ u, (2*|W u|+6*|C u|+4*z u*|C u|))/k^3+
    (12*|qp|+12*|A|+∑ u, 2*(z u)^2*|C u|)/k^4+24*|A|/k^5

/-- Exact algebra, rather than a claimed ordering with another C budget. -/
theorem curvatureBudget_eq_groupedBudget (z : T → ℝ) (qp A : ℝ)
    (W C : T → ℝ) (k : ℝ) :
    curvatureBudget z qp A W C k=groupedBudget z qp A W C k := by
  have ht (u : T) :
      |W u| *(2/k^3)+|C u| *(z u/k^2+(6+4*z u)/k^3+2*(z u)^2/k^4)=
      z u*|C u|/k^2+(2*|W u|+6*|C u|+4*z u*|C u|)/k^3+
        2*(z u)^2*|C u|/k^4 := by ring
  unfold curvatureBudget groupedBudget
  simp_rw [ht]
  simp only [Finset.sum_add_distrib,Finset.sum_div,add_div]
  ring

private theorem norm_mul_real_le (u : ℂ) (a B : ℝ) (hu : ‖u‖≤B) :
    ‖u*(a : ℂ)‖≤|a| *B := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_comm]
  exact mul_le_mul_of_nonneg_left hu (abs_nonneg a)

/-- Internally constructed bound on the whole second transform. All finite
signed coefficients and repeated rates are allowed. -/
theorem secondSymbol_norm_le (z : T → ℝ) (hz : ∀ u, 0<z u)
    (qp A : ℝ) (W C : T → ℝ) (k : ℝ) (hk : 0<k) :
    ‖secondSymbol z qp A W C (Complex.I*(k : ℂ))‖≤groupedBudget z qp A W C k := by
  rw [← curvatureBudget_eq_groupedBudget]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      (norm_mul_real_le _ qp _ (e1Second_norm_le k hk))
      (norm_mul_real_le _ A _ (e2Second_norm_le k hk))))
    ((norm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun u _ =>
      (norm_add_le _ _).trans (add_le_add
        (norm_mul_real_le _ (W u) _ (wSecond_norm_le (z u) k hk))
        (norm_mul_real_le _ (C u) _ (cSecond_norm_le (z u) k (hz u) hk))))))

/-- Positive-frequency restriction of a genuine complex derivative. -/
theorem axis_hasDerivAt {f : ℂ → ℂ} {df : ℂ} (k : ℝ)
    (hf : HasDerivAt f df (Complex.I*(k : ℂ))) :
    HasDerivAt (fun x : ℝ => f (Complex.I*(x : ℂ))) (Complex.I*df) k := by
  have hreal : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) k := by
    change HasDerivAt Complex.ofRealCLM (Complex.ofRealCLM 1) k
    exact Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  have haxis : HasDerivAt (fun x : ℝ => Complex.I*(x : ℂ)) Complex.I k := by
    simpa only [mul_one] using hreal.const_mul Complex.I
  simpa only [Function.comp_def,smul_eq_mul] using hf.scomp k haxis

/-- The exact compressed budget decreases along the positive axis. -/
theorem groupedBudget_antitone (z : T → ℝ) (hz : ∀ u, 0<z u)
    (qp A : ℝ) (W C : T → ℝ) (a k : ℝ) (ha : 0<a) (hak : a≤k) :
    groupedBudget z qp A W C k≤groupedBudget z qp A W C a := by
  unfold groupedBudget
  have hs2 : 0≤∑ u, z u*|C u| := Finset.sum_nonneg fun u _ => mul_nonneg (hz u).le (abs_nonneg _)
  have hs3 : 0≤∑ u, (2*|W u|+6*|C u|+4*z u*|C u|) :=
    Finset.sum_nonneg fun u _ => by have hu := hz u; positivity
  have hs4 : 0≤∑ u, 2*(z u)^2*|C u| := Finset.sum_nonneg fun u _ => by positivity
  gcongr

/-- First derivative along real frequencies of the closed physical factor. -/
theorem closedFactor_hasDerivAt (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (rho k : ℝ) (hk : 0<k) :
    HasDerivAt (fun x : ℝ => 1-(rho : ℂ)*closedSymbol z qp A W C (Complex.I*(x : ℂ)))
      (-(rho : ℂ)*Complex.I*firstSymbol z qp A W C (Complex.I*(k : ℂ))) k := by
  have hs := (axis_norms k hk 0).1
  have hz u := (axis_norms k hk (z u)).2.2.2.2.2.2
  have h := (hasDerivAt_const k (1 : ℂ)).sub
    ((axis_hasDerivAt k (closedSymbol_hasDerivAt z qp A W C _ hs hz)).const_mul (rho : ℂ))
  exact h.congr_deriv (by ring)

/-- Real derivative of the closed first derivative. The I squared sign is
proved, rather than supplied as a Fourier differentiation premise. -/
theorem closedFirst_hasDerivAt (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (rho k : ℝ) (hk : 0<k) :
    HasDerivAt (fun x : ℝ => -(rho : ℂ)*Complex.I*firstSymbol z qp A W C (Complex.I*(x : ℂ)))
      ((rho : ℂ)*secondSymbol z qp A W C (Complex.I*(k : ℂ))) k := by
  have hs := (axis_norms k hk 0).1
  have hz u := (axis_norms k hk (z u)).2.2.2.2.2.2
  have h := (axis_hasDerivAt k (firstSymbol_hasDerivAt z qp A W C _ hs hz)).const_mul
    (-(rho : ℂ)*Complex.I)
  apply h.congr_deriv
  calc
    _ = -(rho : ℂ)*(Complex.I*Complex.I)*secondSymbol z qp A W C (Complex.I*(k : ℂ)) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

/-- Local closed-form equality identifies the TRUE derivative of any honest
factor. No derivative equality is assumed. -/
theorem firstDerivative_eq_of_closedFactor (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (rho : ℝ) (F : ℝ → ℂ) (D : ℝ → ℂ)
    (hF : ∀ k, HasDerivAt F (D k) k)
    (heq : ∀ k, 0<k → F k=1-(rho : ℂ)*closedSymbol z qp A W C (Complex.I*(k : ℂ)))
    (k : ℝ) (hk : 0<k) :
    D k=-(rho : ℂ)*Complex.I*firstSymbol z qp A W C (Complex.I*(k : ℂ)) := by
  apply (hF k).unique
  apply (closedFactor_hasDerivAt z qp A W C rho k hk).congr_of_eventuallyEq
  exact (eventually_gt_nhds hk).mono fun x hx => heq x hx

/-- The true second derivative is recovered using derivative uniqueness
and the neighborhood equality of first derivatives. -/
theorem secondDerivative_eq_of_closedFactor (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (rho : ℝ) (F D DD : ℝ → ℂ)
    (hF : ∀ k, HasDerivAt F (D k) k) (hD : ∀ k, HasDerivAt D (DD k) k)
    (heq : ∀ k, 0<k → F k=1-(rho : ℂ)*closedSymbol z qp A W C (Complex.I*(k : ℂ)))
    (k : ℝ) (hk : 0<k) : DD k=(rho : ℂ)*secondSymbol z qp A W C (Complex.I*(k : ℂ)) := by
  apply (hD k).unique
  apply (closedFirst_hasDerivAt z qp A W C rho k hk).congr_of_eventuallyEq
  exact (eventually_gt_nhds hk).mono fun x hx =>
    firstDerivative_eq_of_closedFactor z qp A W C rho F D hF heq x hx

/-- Coefficient-enclosure version of the literal compressedH2 polynomial.
No positivity of the numerical upper bounds is hidden in the definition. -/
def upperGroupedBudget (z : T → ℝ) (qpU AU : ℝ) (WU CU : T → ℝ) (k : ℝ) : ℝ :=
  (qpU+∑ u, z u*CU u)/k^2+
    (6*qpU+2*AU+∑ u, (2*WU u+6*CU u+4*z u*CU u))/k^3+
    (12*qpU+12*AU+∑ u, 2*(z u)^2*CU u)/k^4+24*AU/k^5

/-- Honest coefficient upper bounds give the saved enclosure budget. -/
theorem groupedBudget_le_of_bounds (z : T → ℝ) (hz : ∀ u, 0<z u)
    (qp A qpU AU : ℝ) (W C WU CU : T → ℝ)
    (hqp : |qp|≤qpU) (hA : |A|≤AU)
    (hW : ∀ u, |W u|≤WU u) (hC : ∀ u, |C u|≤CU u) (k : ℝ) (hk : 0<k) :
    groupedBudget z qp A W C k≤upperGroupedBudget z qpU AU WU CU k := by
  have h2 : (∑ u, z u*|C u|)≤∑ u, z u*CU u := by
    apply Finset.sum_le_sum
    intro u _
    exact mul_le_mul_of_nonneg_left (hC u) (hz u).le
  have h3 : (∑ u, (2*|W u|+6*|C u|+4*z u*|C u|))≤
      ∑ u, (2*WU u+6*CU u+4*z u*CU u) := by
    apply Finset.sum_le_sum
    intro u _
    have hu := hz u
    gcongr
    · exact hW u
    · exact hC u
    · exact hC u
  have h4 : (∑ u, 2*(z u)^2*|C u|)≤∑ u, 2*(z u)^2*CU u := by
    apply Finset.sum_le_sum
    intro u _
    exact mul_le_mul_of_nonneg_left (hC u) (by positivity)
  unfold groupedBudget upperGroupedBudget
  gcongr

/-- Monotonicity of a nonnegative coefficient enclosure along all k≥a>0. -/
theorem upperGroupedBudget_antitone (z : T → ℝ) (hz : ∀ u, 0<z u)
    (qpU AU : ℝ) (WU CU : T → ℝ) (hqp : 0≤qpU) (hA : 0≤AU)
    (hW : ∀ u, 0≤WU u) (hC : ∀ u, 0≤CU u)
    (a k : ℝ) (ha : 0<a) (hak : a≤k) :
    upperGroupedBudget z qpU AU WU CU k≤upperGroupedBudget z qpU AU WU CU a := by
  have h2 : 0≤∑ u, z u*CU u := Finset.sum_nonneg fun u _ => mul_nonneg (hz u).le (hC u)
  have h3 : 0≤∑ u, (2*WU u+6*CU u+4*z u*CU u) := by
    apply Finset.sum_nonneg
    intro u _
    have hu := hz u
    have hw := hW u
    have hc := hC u
    positivity
  have h4 : 0≤∑ u, 2*(z u)^2*CU u :=
    Finset.sum_nonneg fun u _ => mul_nonneg (by positivity) (hC u)
  unfold upperGroupedBudget
  gcongr

/-- The frequency curvature enclosure is intrinsically nonnegative. -/
theorem groupedBudget_nonneg (z : T → ℝ) (hz : ∀ u, 0<z u)
    (qp A : ℝ) (W C : T → ℝ) (k : ℝ) (hk : 0<k) :
    0≤groupedBudget z qp A W C k :=
  (norm_nonneg _).trans (secondSymbol_norm_le z hz qp A W C k hk)

/-- The true second derivative of a factor with the closed form has the
literal compressedH2 bound. All differentiation is proved in this module. -/
theorem secondDerivative_norm_le_of_closedFactor (z : T → ℝ) (hz : ∀ u, 0<z u)
    (rho qp A : ℝ) (hrho : 0≤rho) (W C : T → ℝ) (F D DD : ℝ → ℂ)
    (hF : ∀ k, HasDerivAt F (D k) k) (hD : ∀ k, HasDerivAt D (DD k) k)
    (heq : ∀ k, 0<k → F k=1-(rho : ℂ)*closedSymbol z qp A W C (Complex.I*(k : ℂ)))
    (k : ℝ) (hk : 0<k) : ‖DD k‖≤rho*groupedBudget z qp A W C k := by
  rw [secondDerivative_eq_of_closedFactor z qp A W C rho F D DD hF hD heq k hk,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrho]
  exact mul_le_mul_of_nonneg_left (secondSymbol_norm_le z hz qp A W C k hk) hrho

/-- Verified coefficient and density bounds control the true curvature on
EVERY k≥a>0, with exactly the compressed certificate's formula at a. -/
theorem secondDerivative_norm_le_of_closedFactor_bounds (z : T → ℝ) (hz : ∀ u, 0<z u)
    (rho rhoU qp A qpU AU : ℝ) (hrho : 0≤rho) (hrhoU : rho≤rhoU)
    (W C WU CU : T → ℝ) (hqp : |qp|≤qpU) (hA : |A|≤AU)
    (hW : ∀ u, |W u|≤WU u) (hC : ∀ u, |C u|≤CU u) (F D DD : ℝ → ℂ)
    (hF : ∀ k, HasDerivAt F (D k) k) (hD : ∀ k, HasDerivAt D (DD k) k)
    (heq : ∀ k, 0<k → F k=1-(rho : ℂ)*closedSymbol z qp A W C (Complex.I*(k : ℂ)))
    (a k : ℝ) (ha : 0<a) (hak : a≤k) :
    ‖DD k‖≤rhoU*upperGroupedBudget z qpU AU WU CU a := by
  have hb := (groupedBudget_antitone z hz qp A W C a k ha hak).trans
    (groupedBudget_le_of_bounds z hz qp A qpU AU W C WU CU hqp hA hW hC a ha)
  exact (secondDerivative_norm_le_of_closedFactor z hz rho qp A hrho W C F D DD hF hD heq
    k (ha.trans_le hak)).trans
      (mul_le_mul hrhoU hb (groupedBudget_nonneg z hz qp A W C k (ha.trans_le hak)) (hrho.trans hrhoU))


/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.e1_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.e1_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.e1Prime_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.e1Prime_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.e2_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.e2_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.e2Prime_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.e2Prime_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.w_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.w_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.wPrime_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.wPrime_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.c_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.c_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.cPrime_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.cPrime_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.e1Second_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.e1Second_norm_le
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.e2Second_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.e2Second_norm_le
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.wSecond_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.wSecond_norm_le
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.cSecond_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.cSecond_norm_le
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.closedSymbol_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.closedSymbol_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.firstSymbol_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.firstSymbol_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.curvatureBudget_eq_groupedBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.curvatureBudget_eq_groupedBudget
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.secondSymbol_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.secondSymbol_norm_le
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.axis_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.axis_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.groupedBudget_antitone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.groupedBudget_antitone
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.closedFactor_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.closedFactor_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.closedFirst_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.closedFirst_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.firstDerivative_eq_of_closedFactor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.firstDerivative_eq_of_closedFactor
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.secondDerivative_eq_of_closedFactor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.secondDerivative_eq_of_closedFactor
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.groupedBudget_le_of_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.groupedBudget_le_of_bounds
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.upperGroupedBudget_antitone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.upperGroupedBudget_antitone
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.groupedBudget_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.groupedBudget_nonneg
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.secondDerivative_norm_le_of_closedFactor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.secondDerivative_norm_le_of_closedFactor
/-- info: 'FMSA.Convergence.ScalarFrequencyCurvature.secondDerivative_norm_le_of_closedFactor_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFrequencyCurvature.secondDerivative_norm_le_of_closedFactor_bounds
end FMSA.Convergence.ScalarFrequencyCurvature
