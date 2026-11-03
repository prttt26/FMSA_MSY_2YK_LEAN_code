import MSAConvergence.CanonicalFirstLoss

/-! Explicit actual scalar Fourier tail bounds, retaining the origin
coefficient and every finite signed/repeated tail. No root premise or
external analytic enclosure is supplied. Unit diameter is the geometry of
the M1/M3 certificates; no Fourier formula is evaluated at zero. -/
noncomputable section
open Set Real
open scoped BigOperators
namespace FMSA.Convergence.ScalarFourierTail
open FMSA.ExactMSA.MultiTailMixture
variable {T : Type*} [Fintype T]

def origin (qp A : ℝ) (W C : T → ℝ) : ℝ :=
  -qp+A/2+∑ u, (W u+C u)

def secondBudget (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) : ℝ :=
  2*|qp|+|A|+∑ u, z u*(|W u|+|C u|)

def symbol (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (s : ℂ) : ℂ :=
  (1-s-Complex.exp (-s))/s^2*(qp : ℂ)+
    (1-s+s^2/2-Complex.exp (-s))/s^3*(A : ℂ)+
      ∑ u, ((W u : ℂ)/(s+(z u : ℂ))+
        (C u : ℂ)*((1-Complex.exp (-s))/s+Complex.exp (-s)/(s+(z u : ℂ))))

private theorem symbol_decomposition (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (s : ℂ) (hs : s ≠ 0) (hz : ∀ u, s+(z u : ℂ) ≠ 0) :
    symbol z qp A W C s = (origin qp A W C : ℂ)/s+
      ((qp : ℂ)*(1-Complex.exp (-s))/s^2-(A : ℂ)/s^2+
        (A : ℂ)*(1-Complex.exp (-s))/s^3)-
      ∑ u, ((z u : ℂ)*(W u : ℂ)+(z u : ℂ)*(C u : ℂ)*Complex.exp (-s))/
        (s*(s+(z u : ℂ))) := by
  have hp : (1-s-Complex.exp (-s))/s^2*(qp : ℂ) =
      -(qp : ℂ)/s+(qp : ℂ)*(1-Complex.exp (-s))/s^2 := by
    field_simp
    ring
  have ha : (1-s+s^2/2-Complex.exp (-s))/s^3*(A : ℂ) =
      (A : ℂ)/(2*s)-(A : ℂ)/s^2+(A : ℂ)*(1-Complex.exp (-s))/s^3 := by
    field_simp
    ring
  have ht (u : T) : (W u : ℂ)/(s+(z u : ℂ))+
      (C u : ℂ)*((1-Complex.exp (-s))/s+Complex.exp (-s)/(s+(z u : ℂ))) =
      ((W u : ℂ)+(C u : ℂ))/s-
      ((z u : ℂ)*(W u : ℂ)+(z u : ℂ)*(C u : ℂ)*Complex.exp (-s))/(s*(s+(z u : ℂ))) := by
    field_simp [hs,hz u]
    ring
  unfold symbol origin
  rw [hp,ha]
  simp_rw [ht]
  push_cast
  rw [Finset.sum_sub_distrib,← Finset.sum_div]
  field_simp
  ring

private theorem axis_norms (k : ℝ) (hk : k ≠ 0) (z : ℝ) :
    let s : ℂ := Complex.I*k
    s ≠ 0 ∧ ‖s‖ = |k| ∧ ‖Complex.exp (-s)‖ = 1 ∧
      ‖1-Complex.exp (-s)‖ ≤ 2 ∧ |k| ≤ ‖s+(z : ℂ)‖ ∧ s+(z : ℂ) ≠ 0 := by
  dsimp only
  have hs : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  have hn : ‖Complex.I*(k : ℂ)‖ = |k| := by simp [Complex.norm_real,Real.norm_eq_abs]
  have he : ‖Complex.exp (-(Complex.I*(k : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hdiff : ‖1-Complex.exp (-(Complex.I*(k : ℂ)))‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖+‖Complex.exp (-(Complex.I*(k : ℂ)))‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one,he]; norm_num
  have hz : |k| ≤ ‖Complex.I*(k : ℂ)+(z : ℂ)‖ := by
    simpa using Complex.abs_im_le_norm (Complex.I*(k : ℂ)+(z : ℂ))
  refine ⟨hs,hn,he,hdiff,hz,?_⟩
  intro h
  rw [h,norm_zero] at hz
  exact (abs_pos.mpr hk).not_ge hz

/-- The exact tail budget used in the external certificates, proved
for the honest Fourier integral at every nonzero real wave number. -/
theorem fourierQ_norm_le (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (qp A : ℝ) (W C : T → ℝ) (k : ℝ) (hk : k ≠ 0) :
    ‖fourierQ z (fun _ : Fin 1 => 1) (fun _ => A) (fun _ _ => qp)
      (fun u _ _ => W u) (fun u _ _ => C u) k 0 0‖ ≤
      |origin qp A W C|/|k|+secondBudget z qp A W C/|k|^2+2*|A|/|k|^3 := by
  let s : ℂ := Complex.I*k
  have hs : s ≠ 0 := (axis_norms k hk 0).1
  have hn : ‖s‖ = |k| := (axis_norms k hk 0).2.1
  have he : ‖Complex.exp (-s)‖ = 1 := (axis_norms k hk 0).2.2.1
  have hd : ‖1-Complex.exp (-s)‖ ≤ 2 := (axis_norms k hk 0).2.2.2.1
  have hzden (u : T) : |k| ≤ ‖s+(z u : ℂ)‖ := (axis_norms k hk (z u)).2.2.2.2.1
  have hz0 (u : T) : s+(z u : ℂ) ≠ 0 := (axis_norms k hk (z u)).2.2.2.2.2
  have hkpos : 0 < |k| := abs_pos.mpr hk
  have hsum (u : T) :
      ‖((z u : ℂ)*(W u : ℂ)+(z u : ℂ)*(C u : ℂ)*Complex.exp (-s))/(s*(s+(z u : ℂ)))‖ ≤
      z u*(|W u|+|C u|)/|k|^2 := by
    have hnum : ‖(z u : ℂ)*(W u : ℂ)+(z u : ℂ)*(C u : ℂ)*Complex.exp (-s)‖ ≤
        z u*(|W u|+|C u|) := by
      have h := norm_add_le ((z u : ℂ)*(W u : ℂ)) ((z u : ℂ)*(C u : ℂ)*Complex.exp (-s))
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hz u),he,mul_one,mul_add] using h
    rw [norm_div,norm_mul,hn]
    apply (div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hkpos) ?_).trans
      (div_le_div_of_nonneg_right hnum (sq_nonneg _))
    nlinarith [hzden u]
  have hp : ‖(qp : ℂ)*(1-Complex.exp (-s))/s^2‖ ≤ 2*|qp|/|k|^2 := by
    rw [norm_div,norm_mul,norm_pow,hn,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ |qp| * 2/|k|^2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd (abs_nonneg _)) (sq_nonneg _)
      _ = _ := by ring
  have ha : ‖(A : ℂ)/s^2‖ = |A|/|k|^2 := by
    rw [norm_div,norm_pow,hn,Complex.norm_real,Real.norm_eq_abs]
  have har : ‖(A : ℂ)*(1-Complex.exp (-s))/s^3‖ ≤ 2*|A|/|k|^3 := by
    rw [norm_div,norm_mul,norm_pow,hn,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ |A| * 2/|k|^3 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd (abs_nonneg _)) (by positivity)
      _ = _ := by ring
  have hcore : ‖(qp : ℂ)*(1-Complex.exp (-s))/s^2-(A : ℂ)/s^2+
      (A : ℂ)*(1-Complex.exp (-s))/s^3‖ ≤
      2*|qp|/|k|^2+|A|/|k|^2+2*|A|/|k|^3 := by
    exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hp ha.le)) har)
  have hbound : ‖symbol z qp A W C s‖ ≤
      |origin qp A W C|/|k|+secondBudget z qp A W C/|k|^2+2*|A|/|k|^3 := by
    rw [symbol_decomposition z qp A W C s hs hz0]
    have hlead : ‖(origin qp A W C : ℂ)/s‖ = |origin qp A W C|/|k| := by
      rw [norm_div,hn,Complex.norm_real,Real.norm_eq_abs]
    have h := (norm_sub_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add hlead.le hcore))
        ((norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun u _ => hsum u))))
    convert h using 1
    all_goals first | rfl | (simp only [secondBudget,add_div,Finset.sum_div]; ring)
  rw [fourierQ_eq_QhatComplex z hz _ _ _ _ _ (by intro i; norm_num) k hk 0 0]
  have hident : QhatComplex z (fun _ : Fin 1 => 1) (fun _ => A) (fun _ _ => qp)
      (fun u _ _ => W u) (fun u _ _ => C u) (Complex.I*k) 0 0 = symbol z qp A W C s := by
    simp [QhatComplex,MSAMixture.edgeLo,MSAMixture.edgeHi,symbol,s,
      mul_add,mul_div_assoc,Finset.sum_add_distrib]
    ring
  rw [hident]
  exact hbound

def factor (z : T → ℝ) (rho qp A : ℝ) (W C : T → ℝ) (k : ℝ) : ℂ :=
  fourierFactor z (fun _ : Fin 1 => rho) (fun _ => 1) (fun _ => A)
    (fun _ _ => qp) (fun u _ _ => W u) (fun u _ _ => C u) k 0 0

private theorem factor_eq (z : T → ℝ) (rho qp A : ℝ) (hrho : 0 ≤ rho)
    (W C : T → ℝ) (k : ℝ) :
    factor z rho qp A W C k = 1-(rho : ℂ)*
      fourierQ z (fun _ : Fin 1 => 1) (fun _ => A) (fun _ _ => qp)
        (fun u _ _ => W u) (fun u _ _ => C u) k 0 0 := by
  unfold factor fourierFactor
  simp only [Matrix.sub_apply,Matrix.one_apply,ite_true,Matrix.of_apply]
  rw [← Complex.ofReal_mul,Real.mul_self_sqrt hrho]

private theorem budget_nonneg (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (qp A : ℝ) (W C : T → ℝ) : 0 ≤ secondBudget z qp A W C := by
  unfold secondBudget
  apply add_nonneg (by positivity)
  exact Finset.sum_nonneg (fun u _ => mul_nonneg (hz u).le (by positivity))

/-- The density-weighted physical Fourier factor has the explicit three-term
tail estimate at both positive and negative wave numbers. -/
theorem factor_norm_sub_one_le (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho qp A : ℝ) (hrho : 0 ≤ rho) (W C : T → ℝ) (k : ℝ) (hk : k ≠ 0) :
    ‖factor z rho qp A W C k-1‖ ≤
      rho*(|origin qp A W C|/|k|+secondBudget z qp A W C/|k|^2+2*|A|/|k|^3) := by
  rw [factor_eq z rho qp A hrho W C k]
  rw [show (1-(rho : ℂ)*fourierQ z (fun _ : Fin 1 => 1) (fun _ => A) (fun _ _ => qp)
      (fun u _ _ => W u) (fun u _ _ => C u) k 0 0)-1 =
      -((rho : ℂ)*fourierQ z (fun _ : Fin 1 => 1) (fun _ => A) (fun _ _ => qp)
        (fun u _ _ => W u) (fun u _ _ => C u) k 0 0) by ring]
  rw [norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrho]
  exact mul_le_mul_of_nonneg_left (fourierQ_norm_le z hz qp A W C k hk) hrho

/-- Any positive cutoff satisfying the computed actual coefficient budget
excludes ALL larger absolute wave numbers, not just a finite grid. -/
theorem factor_ne_zero_of_cutoff (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho qp A : ℝ) (hrho : 0 ≤ rho) (W C : T → ℝ) (K : ℝ) (hK : 0 < K)
    (hbudget : rho*(|origin qp A W C|/K+secondBudget z qp A W C/K^2+2*|A|/K^3) < 1)
    (k : ℝ) (hk : K ≤ |k|) : factor z rho qp A W C k ≠ 0 := by
  have hkpos : 0 < |k| := hK.trans_le hk
  have hk0 : k ≠ 0 := abs_pos.mp hkpos
  have hB := budget_nonneg z hz qp A W C
  have hmon : |origin qp A W C|/|k|+secondBudget z qp A W C/|k|^2+2*|A|/|k|^3 ≤
      |origin qp A W C|/K+secondBudget z qp A W C/K^2+2*|A|/K^3 := by
    gcongr
  have hsmall : ‖factor z rho qp A W C k-1‖ < 1 :=
    lt_of_le_of_lt ((factor_norm_sub_one_le z hz rho qp A hrho W C k hk0).trans
      (mul_le_mul_of_nonneg_left hmon hrho)) hbudget
  intro hzero
  simp only [hzero,zero_sub,norm_neg,norm_one,lt_self_iff_false] at hsmall

def explicitCutoff (z : T → ℝ) (rho qp A : ℝ) (W C : T → ℝ) : ℝ :=
  1+4*rho*(|origin qp A W C|+secondBudget z qp A W C+2*|A|)

/-- A cutoff is CONSTRUCTED from arbitrary actual coefficients, without a
supplied inequality or enclosure. Beyond it the physical factor stays
strictly within1/4 of1. No root or canonical-prefix hypothesis is needed. -/
theorem factor_norm_lt_quarter_of_explicit_cutoff (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho qp A : ℝ) (hrho : 0 ≤ rho) (W C : T → ℝ) (k : ℝ)
    (hk : explicitCutoff z rho qp A W C ≤ |k|) : ‖factor z rho qp A W C k-1‖ < 1/4 := by
  let S := |origin qp A W C|+secondBudget z qp A W C+2*|A|
  let K := explicitCutoff z rho qp A W C
  have hB := budget_nonneg z hz qp A W C
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hformula : K = 1+4*(rho*S) := by dsimp [K,explicitCutoff,S]; ring
  have hK1 : 1 ≤ K := by rw [hformula]; nlinarith [mul_nonneg hrho hS]
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hx : 0 < |k| := hK.trans_le hk
  have hpow2 : |k| ≤ |k|^2 := by nlinarith [show 1 ≤ |k| from hK1.trans hk]
  have hpow3 : |k| ≤ |k|^3 := by
    have hstep : |k|^2 ≤ |k|^3 := by
      nlinarith [mul_nonneg (sq_nonneg |k|) (sub_nonneg.mpr (hK1.trans hk))]
    exact hpow2.trans hstep
  have htail : |origin qp A W C|/|k|+secondBudget z qp A W C/|k|^2+2*|A|/|k|^3 ≤ S/|k| := by
    dsimp only [S]
    rw [add_div,add_div]
    exact add_le_add (add_le_add le_rfl (div_le_div_of_nonneg_left hB hx hpow2))
      (div_le_div_of_nonneg_left (by positivity) hx hpow3)
  have hratio : rho*S/|k| < 1/4 := by
    apply (div_lt_iff₀ hx).mpr
    nlinarith
  exact lt_of_le_of_lt ((factor_norm_sub_one_le z hz rho qp A hrho W C k (abs_pos.mp hx)).trans
    (mul_le_mul_of_nonneg_left htail hrho)) (by simpa only [mul_div_assoc] using hratio)

/-- The actual original BH amplitudes themselves determine an explicit
all-wave tail of MATRIX units. Arbitrary signs/repeated rates and arbitrary
amplitudes are allowed; no BH root, inverse, external bound or seed is given. -/
theorem actual_tail_units_outside_explicit_cutoff (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho : ℝ) (hrho : 0 ≤ rho) (Dt G : TailMatrix T 1) (k : ℝ)
    (hk : explicitCutoff z rho
      (amplitudeQp z (fun _ => rho) (fun _ => 1) Dt G 0 0)
      (amplitudeA z (fun _ => rho) (fun _ => 1) Dt G 0)
      (fun u => W z (fun _ => rho) Dt G u 0 0)
      (fun u => C z (fun _ => rho) (fun _ => 1) Dt G u 0 0) ≤ |k|) :
    IsUnit (fourierFactor z (fun _ => rho) (fun _ => 1)
      (amplitudeA z (fun _ => rho) (fun _ => 1) Dt G)
      (amplitudeQp z (fun _ => rho) (fun _ => 1) Dt G)
      (W z (fun _ => rho) Dt G) (C z (fun _ => rho) (fun _ => 1) Dt G) k) := by
  let a := amplitudeA z (fun _ => rho) (fun _ => 1) Dt G
  let p := amplitudeQp z (fun _ => rho) (fun _ => 1) Dt G
  let w := W z (fun _ => rho) Dt G
  let c := C z (fun _ => rho) (fun _ => 1) Dt G
  have hsmall := factor_norm_lt_quarter_of_explicit_cutoff z hz rho (p 0 0) (a 0) hrho
    (fun u => w u 0 0) (fun u => c u 0 0) k hk
  have hzero : factor z rho (p 0 0) (a 0) (fun u => w u 0 0) (fun u => c u 0 0) k ≠ 0 := by
    intro h
    simp only [h,zero_sub,norm_neg,norm_one] at hsmall
    norm_num at hsmall
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_fin_one]
  have ha : a = fun _ : Fin 1 => a 0 := by funext i; fin_cases i; rfl
  have hp : p = fun _ _ : Fin 1 => p 0 0 := by funext i j; fin_cases i; fin_cases j; rfl
  have hw : w = fun u (_ _) => w u 0 0 := by funext u i j; fin_cases i; fin_cases j; rfl
  have hc : c = fun u (_ _) => c u 0 0 := by funext u i j; fin_cases i; fin_cases j; rfl
  change fourierFactor z (fun _ => rho) (fun _ => 1) a p w c k 0 0 ≠ 0
  rw [ha,hp,hw,hc]
  exact hzero

/-- info: 'FMSA.Convergence.ScalarFourierTail.fourierQ_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierTail.fourierQ_norm_le
/-- info: 'FMSA.Convergence.ScalarFourierTail.factor_norm_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierTail.factor_norm_sub_one_le
/-- info: 'FMSA.Convergence.ScalarFourierTail.factor_ne_zero_of_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierTail.factor_ne_zero_of_cutoff
/-- info: 'FMSA.Convergence.ScalarFourierTail.factor_norm_lt_quarter_of_explicit_cutoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierTail.factor_norm_lt_quarter_of_explicit_cutoff
/-- info: 'FMSA.Convergence.ScalarFourierTail.actual_tail_units_outside_explicit_cutoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierTail.actual_tail_units_outside_explicit_cutoff
end FMSA.Convergence.ScalarFourierTail
