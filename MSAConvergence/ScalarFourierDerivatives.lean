import MSAConvergence.ScalarFourierMoments
import MSAConvergence.QuadraticFrequencyStep

/-! Genuine derivatives of the actual Fourier integral at ALL real
frequencies, including zero. Polynomial moments discharge differentiation
under the integral; no quotient-at-zero or supplied differentiability. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.ScalarFourierDerivatives
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.ScalarFourierMoments
open FMSA.Convergence.QuadraticFrequencyStep
variable {T : Type*} [Fintype T]

def phase (k r : ℝ) : ℂ := Complex.exp (-(Complex.I*(k : ℂ))*(r : ℂ))

def weightedFourier (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (n : ℕ) (k : ℝ) : ℂ :=
  ∫ r : ℝ, ((r^n*scalarQ z qp A W C r : ℝ) : ℂ)*phase k r

def absoluteMoment (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (n : ℕ) : ℝ :=
  ∫ r : ℝ, |r^n*scalarQ z qp A W C r|

private theorem phase_norm (k r : ℝ) : ‖phase k r‖ = 1 := by
  rw [phase,Complex.norm_exp]
  simp

private theorem phase_hasDerivAt (k r : ℝ) :
    HasDerivAt (fun x : ℝ => phase x r) (phase k r*(-Complex.I*(r : ℂ))) k := by
  have hreal : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) k := by
    change HasDerivAt Complex.ofRealCLM (Complex.ofRealCLM 1) k
    exact Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  have hlin : HasDerivAt (fun x : ℝ => -(Complex.I*(x : ℂ))*(r : ℂ))
      (-Complex.I*(r : ℂ)) k := by
    have he : (fun x : ℝ => -(Complex.I*(x : ℂ))*(r : ℂ)) =
        fun x : ℝ => (-Complex.I*(r : ℂ))*(x : ℂ) := by funext x; ring
    rw [he]
    simpa only [mul_one] using hreal.const_mul (-Complex.I*(r : ℂ))
  exact hlin.cexp

/-- Every weighted actual Fourier integrand is L1, uniformly in the real
phase parameter; all moment integrability is discharged internally. -/
theorem weighted_fourier_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (qp A : ℝ) (W C : T → ℝ) (n : ℕ) (k : ℝ) :
    Integrable (fun r : ℝ => ((r^n*scalarQ z qp A W C r : ℝ) : ℂ)*phase k r) := by
  have hi : Integrable (fun r : ℝ => ((r^n*scalarQ z qp A W C r : ℝ) : ℂ)) :=
    (weighted_q_integrable z hz qp A W C n).ofReal
  apply hi.mul_bdd (c := 1)
  · unfold phase
    fun_prop
  · exact Eventually.of_forall (fun r => (phase_norm k r).le)

/-- Differentiating the HONEST integral adds one actual moment. The proof
works at zero as well as every other real frequency. -/
theorem weightedFourier_hasDerivAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (qp A : ℝ) (W C : T → ℝ) (n : ℕ) (k : ℝ) :
    HasDerivAt (weightedFourier z qp A W C n)
      (-Complex.I*weightedFourier z qp A W C (n+1) k) k := by
  let F : ℝ → ℝ → ℂ := fun x r => ((r^n*scalarQ z qp A W C r : ℝ) : ℂ)*phase x r
  let DF : ℝ → ℝ → ℂ := fun x r =>
    -Complex.I*(((r^(n+1)*scalarQ z qp A W C r : ℝ) : ℂ)*phase x r)
  have hF (x : ℝ) : Integrable (F x) := weighted_fourier_integrable z hz qp A W C n x
  have hDF (x : ℝ) : Integrable (DF x) :=
    (weighted_fourier_integrable z hz qp A W C (n+1) x).const_mul (-Complex.I)
  have hnorm (x r : ℝ) : ‖DF x r‖ = |r^(n+1)*scalarQ z qp A W C r| := by
    simp only [DF,norm_mul,norm_neg,Complex.norm_I,one_mul,phase_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_mul]
  have hbound : Integrable (fun r : ℝ => |r^(n+1)*scalarQ z qp A W C r|) := by
    simpa only [Real.norm_eq_abs] using (weighted_q_integrable z hz qp A W C (n+1)).norm
  have hdiff (x r : ℝ) : HasDerivAt (fun y => F y r) (DF x r) x := by
    apply ((phase_hasDerivAt x r).const_mul ((r^n*scalarQ z qp A W C r : ℝ) : ℂ)).congr_deriv
    dsimp only [DF]
    push_cast
    rw [pow_succ]
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := DF) (x₀ := k) (s := univ)
    (bound := fun r : ℝ => |r^(n+1)*scalarQ z qp A W C r|)
    (by simp) (Eventually.of_forall (fun x => (hF x).aestronglyMeasurable)) (hF k)
    (hDF k).aestronglyMeasurable
    (Eventually.of_forall (fun r x _ => (hnorm x r).le)) hbound
    (Eventually.of_forall (fun r x _ => hdiff x r))
  convert! h.2 using 1
  first | rfl | simp only [DF,weightedFourier,integral_const_mul]

/-- Order zero is the actual whole-line Fourier integral, without any
frequency restriction or removable-denominator convention. -/
theorem weightedFourier_zero_order (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (k : ℝ) :
    weightedFourier z qp A W C 0 k = fourierQ z (fun _ : Fin 1 => 1) (fun _ => A)
      (fun _ _ => qp) (fun u _ _ => W u) (fun u _ _ => C u) k 0 0 := by
  simp only [weightedFourier,scalarQ,phase,fourierQ,pow_zero,one_mul]

/-- An actual integral moment gives a uniform bound for every real Fourier
phase. The moment is finite by weighted_q_integrable, not assumed. -/
theorem weightedFourier_norm_le (z : T → ℝ) (hz : ∀ u, 0 < z u) (qp A : ℝ) (W C : T → ℝ)
    (n : ℕ) (k : ℝ) :
    ‖weightedFourier z qp A W C n k‖ ≤ absoluteMoment z qp A W C n := by
  unfold weightedFourier absoluteMoment
  apply MeasureTheory.norm_integral_le_of_norm_le
    (by simpa only [Real.norm_eq_abs] using (weighted_q_integrable z hz qp A W C n).norm)
  exact Eventually.of_forall (fun r => by
    simp only [norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_mul,le_refl])

def firstDerivative (z : T → ℝ) (rho qp A : ℝ) (W C : T → ℝ) (k : ℝ) : ℂ :=
  (rho : ℂ)*Complex.I*weightedFourier z qp A W C 1 k

def secondDerivative (z : T → ℝ) (rho qp A : ℝ) (W C : T → ℝ) (k : ℝ) : ℂ :=
  (rho : ℂ)*weightedFourier z qp A W C 2 k

/-- Physical sqrt-density weighting is exactly rho times the honest
zeroth-order integral, including frequency zero and vacuum. -/
theorem factor_eq_integral (z : T → ℝ) (rho qp A : ℝ) (hrho : 0 ≤ rho)
    (W C : T → ℝ) (k : ℝ) :
    ScalarFourierTail.factor z rho qp A W C k = 1-(rho : ℂ)*weightedFourier z qp A W C 0 k := by
  rw [weightedFourier_zero_order]
  unfold ScalarFourierTail.factor fourierFactor
  simp only [Matrix.sub_apply,Matrix.one_apply,ite_true,Matrix.of_apply]
  rw [← Complex.ofReal_mul,Real.mul_self_sqrt hrho]

/-- The first displayed weighted integral is the TRUE physical frequency
derivative of the existing Fourier factor, at every real k. -/
theorem factor_hasDerivAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho qp A : ℝ) (hrho : 0 ≤ rho) (W C : T → ℝ) (k : ℝ) :
    HasDerivAt (ScalarFourierTail.factor z rho qp A W C)
      (firstDerivative z rho qp A W C k) k := by
  have he : ScalarFourierTail.factor z rho qp A W C =
      fun x => 1-(rho : ℂ)*weightedFourier z qp A W C 0 x := by
    funext x
    exact factor_eq_integral z rho qp A hrho W C x
  rw [he]
  have h := (hasDerivAt_const k (1 : ℂ)).fun_sub
    ((weightedFourier_hasDerivAt z hz qp A W C 0 k).const_mul (rho : ℂ))
  exact h.congr_deriv (by dsimp [firstDerivative]; ring)

/-- The second displayed weighted integral is the true derivative of the
first one. No Hessian, differentiability or interchange is supplied. -/
theorem firstDerivative_hasDerivAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho qp A : ℝ) (W C : T → ℝ) (k : ℝ) :
    HasDerivAt (firstDerivative z rho qp A W C) (secondDerivative z rho qp A W C k) k := by
  have h := (weightedFourier_hasDerivAt z hz qp A W C 1 k).const_mul ((rho : ℂ)*Complex.I)
  apply h.congr_deriv
  dsimp [secondDerivative]
  calc
    _ = -(rho : ℂ)*(Complex.I*Complex.I)*weightedFourier z qp A W C 2 k := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

/-- Genuine second derivative of the ACTUAL physical Fourier factor. -/
theorem factor_hasSecondDerivAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho qp A : ℝ) (hrho : 0 ≤ rho) (W C : T → ℝ) (k : ℝ) :
    HasDerivAt (deriv (ScalarFourierTail.factor z rho qp A W C))
      (secondDerivative z rho qp A W C k) k := by
  have he : deriv (ScalarFourierTail.factor z rho qp A W C) =
      firstDerivative z rho qp A W C := by
    funext x
    exact (factor_hasDerivAt z hz rho qp A hrho W C x).deriv
  rw [he]
  exact firstDerivative_hasDerivAt z hz rho qp A W C k

/-- The true second derivative has a data-defined uniform absolute-moment
bound; moment integrability is discharged from the positive rates. -/
theorem secondDerivative_norm_le (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho qp A : ℝ) (hrho : 0 ≤ rho) (W C : T → ℝ) (k : ℝ) :
    ‖secondDerivative z rho qp A W C k‖ ≤ rho*absoluteMoment z qp A W C 2 := by
  dsimp only [secondDerivative]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrho]
  exact mul_le_mul_of_nonneg_left (weightedFourier_norm_le z hz qp A W C 2 k) hrho

/-- A whole closed frequency step is zero-free when its actual point
budgets beat the internally proved absolute-moment remainder. This is the
actual physical factor; it does not assume derivative identities or L1. -/
theorem factor_interval_ne_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho qp A : ℝ) (hrho : 0 ≤ rho) (W C : T → ℝ) (a h m d : ℝ)
    (hh : 0 ≤ h) (hm : m ≤ ‖ScalarFourierTail.factor z rho qp A W C a‖)
    (hd : ‖firstDerivative z rho qp A W C a‖ ≤ d)
    (hbudget : 0 < m-d*h-(rho*absoluteMoment z qp A W C 2)*h^2/2) :
    ∀ k ∈ Icc a (a+h), ScalarFourierTail.factor z rho qp A W C k ≠ 0 := by
  apply interval_nonzero (ScalarFourierTail.factor z rho qp A W C)
    (firstDerivative z rho qp A W C) (secondDerivative z rho qp A W C)
    a h (rho*absoluteMoment z qp A W C 2) m d hh
    (fun k _ => factor_hasDerivAt z hz rho qp A hrho W C k)
    (fun k _ => firstDerivative_hasDerivAt z hz rho qp A W C k) _ hm hd hbudget
  intro k _
  exact secondDerivative_norm_le z hz rho qp A hrho W C k

/-- The same proved point/remainder criterion returns units of the ORIGINAL
physical Fourier matrix at EVERY frequency in the closed step. -/
theorem fourierFactor_interval_isUnit (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho qp A : ℝ) (hrho : 0 ≤ rho) (W C : T → ℝ) (a h m d : ℝ)
    (hh : 0 ≤ h) (hm : m ≤ ‖ScalarFourierTail.factor z rho qp A W C a‖)
    (hd : ‖firstDerivative z rho qp A W C a‖ ≤ d)
    (hbudget : 0 < m-d*h-(rho*absoluteMoment z qp A W C 2)*h^2/2) :
    ∀ k ∈ Icc a (a+h), IsUnit (fourierFactor z (fun _ : Fin 1 => rho) (fun _ => 1)
      (fun _ => A) (fun _ _ => qp) (fun u _ _ => W u) (fun u _ _ => C u) k) := by
  intro k hk
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_fin_one]
  exact factor_interval_ne_zero z hz rho qp A hrho W C a h m d hh hm hd hbudget k hk

/-- info: 'FMSA.Convergence.ScalarFourierDerivatives.weighted_fourier_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierDerivatives.weighted_fourier_integrable
/-- info: 'FMSA.Convergence.ScalarFourierDerivatives.weightedFourier_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierDerivatives.weightedFourier_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFourierDerivatives.weightedFourier_zero_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierDerivatives.weightedFourier_zero_order
/-- info: 'FMSA.Convergence.ScalarFourierDerivatives.weightedFourier_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierDerivatives.weightedFourier_norm_le
/-- info: 'FMSA.Convergence.ScalarFourierDerivatives.factor_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierDerivatives.factor_eq_integral
/-- info: 'FMSA.Convergence.ScalarFourierDerivatives.factor_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierDerivatives.factor_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFourierDerivatives.firstDerivative_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierDerivatives.firstDerivative_hasDerivAt
/-- info: 'FMSA.Convergence.ScalarFourierDerivatives.factor_hasSecondDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierDerivatives.factor_hasSecondDerivAt
/-- info: 'FMSA.Convergence.ScalarFourierDerivatives.secondDerivative_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierDerivatives.secondDerivative_norm_le
/-- info: 'FMSA.Convergence.ScalarFourierDerivatives.factor_interval_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierDerivatives.factor_interval_ne_zero
/-- info: 'FMSA.Convergence.ScalarFourierDerivatives.fourierFactor_interval_isUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierDerivatives.fourierFactor_interval_isUnit
end FMSA.Convergence.ScalarFourierDerivatives
