import MSAConvergence.ScalarFourierDerivatives

/-! Explicit coefficient triangle bounds for the honest absolute moments
of the actual scalar Baxter kernel. Whole closed frequency steps give
original BH physical matrix units from verified coefficient/point budgets. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators
namespace FMSA.Convergence.ScalarAbsoluteMoments
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.ScalarFourierMoments
open FMSA.Convergence.ScalarFourierDerivatives
variable {T : Type*} [Fintype T]

private def coreEnvelope (qp A : ℝ) (C : T → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  |qp| *(r^n*(1-r))+|A| *(r^n*(r-1)^2/2)+∑ u, |C u| *r^n
private def wEnvelope (z : T → ℝ) (W : T → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  ∑ u, |W u| *(r^n*exp (-z u*r))
private def cEnvelope (z : T → ℝ) (C : T → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  ∑ u, |C u| *(r^n*exp (-z u*(r-1)))
private def envelope (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  (Icc (0 : ℝ) 1).indicator (coreEnvelope qp A C n) r+
  (Ici (0 : ℝ)).indicator (wEnvelope z W n) r+
  (Ioi (1 : ℝ)).indicator (cEnvelope z C n) r

private theorem q_negative (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (r : ℝ) (hr : r < 0) : scalarQ z qp A W C r = 0 := by
  norm_num [scalarQ,q,MSAMixture.edgeLo,MSAMixture.edgeHi,hr]
private theorem q_core (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    scalarQ z qp A W C r = qp*(r-1)+A/2*(r-1)^2+∑ u, (W u*exp (-z u*r)+C u) := by
  norm_num [scalarQ,q,MSAMixture.edgeLo,MSAMixture.edgeHi,not_lt.mpr hr0,hr1]
private theorem q_tail (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (r : ℝ) (hr : 1 < r) :
    scalarQ z qp A W C r = ∑ u, (W u*exp (-z u*r)+C u*exp (-z u*(r-1))) := by
  have hr0 : 0 ≤ r := by linarith
  norm_num [scalarQ,q,MSAMixture.edgeLo,MSAMixture.edgeHi,not_lt.mpr hr0,not_le.mpr hr]

private theorem core_point_bound (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (n : ℕ)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |r^n*scalarQ z qp A W C r| ≤ coreEnvelope qp A C n r+wEnvelope z W n r := by
  have hp : 0 ≤ r^n := pow_nonneg hr0 n
  have hsum : |∑ u, (W u*exp (-z u*r)+C u)| ≤ ∑ u, (|W u| *exp (-z u*r)+|C u|) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro u _
    simpa only [abs_mul,abs_of_pos (exp_pos _)] using abs_add_le (W u*exp (-z u*r)) (C u)
  have hqp : |qp*(r-1)| = |qp| *(1-r) := by
    rw [abs_mul,abs_of_nonpos (sub_nonpos.mpr hr1)]
    ring
  have hA : |A/2*(r-1)^2| = |A| *(r-1)^2/2 := by
    rw [abs_mul,abs_div,abs_of_nonneg (sq_nonneg (r-1))]
    norm_num
    ring
  have hq : |scalarQ z qp A W C r| ≤
      |qp| *(1-r)+|A| *(r-1)^2/2+∑ u, (|W u| *exp (-z u*r)+|C u|) := by
    rw [q_core z qp A W C r hr0 hr1]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (by rw [hqp,hA])) hsum)
  rw [abs_mul,abs_of_nonneg hp]
  apply (mul_le_mul_of_nonneg_left hq hp).trans_eq
  dsimp only [coreEnvelope,wEnvelope]
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
  have hW : (∑ u, r^n*(|W u| *exp (-z u*r))) =
      ∑ u, |W u| *(r^n*exp (-z u*r)) := by
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hC : (∑ u, r^n*|C u|) = ∑ u, |C u| *r^n := by
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hW,hC]
  ring

private theorem tail_point_bound (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (n : ℕ)
    (r : ℝ) (hr : 1 < r) :
    |r^n*scalarQ z qp A W C r| ≤ wEnvelope z W n r+cEnvelope z C n r := by
  have hp : 0 ≤ r^n := pow_nonneg (by linarith) n
  rw [q_tail z qp A W C r hr,abs_mul,abs_of_nonneg hp]
  have hsum : |∑ u, (W u*exp (-z u*r)+C u*exp (-z u*(r-1)))| ≤
      ∑ u, (|W u| *exp (-z u*r)+|C u| *exp (-z u*(r-1))) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro u _
    simpa only [abs_mul,abs_of_pos (exp_pos _)] using
      abs_add_le (W u*exp (-z u*r)) (C u*exp (-z u*(r-1)))
  apply (mul_le_mul_of_nonneg_left hsum hp).trans_eq
  dsimp only [wEnvelope,cEnvelope]
  simp only [Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

private theorem envelope_bound (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (n : ℕ) (r : ℝ) :
    |r^n*scalarQ z qp A W C r| ≤ envelope z qp A W C n r := by
  by_cases hneg : r < 0
  · have hc : r ∉ Icc (0 : ℝ) 1 := fun h => (not_le_of_gt hneg) h.1
    have hi : r ∉ Ici (0 : ℝ) := not_le_of_gt hneg
    have ht : r ∉ Ioi (1 : ℝ) := by show ¬(1 : ℝ)<r; linarith
    simp [envelope,q_negative z qp A W C r hneg,hc,hi,ht]
  · have hr0 := le_of_not_gt hneg
    by_cases hr1 : r ≤ 1
    · simpa only [envelope,indicator_of_mem (show r ∈ Icc (0 : ℝ) 1 from ⟨hr0,hr1⟩),
        indicator_of_mem (show r ∈ Ici (0 : ℝ) from hr0),
        indicator_of_notMem (show r ∉ Ioi (1 : ℝ) from not_lt.mpr hr1),add_zero] using
        core_point_bound z qp A W C n r hr0 hr1
    · have hrt := lt_of_not_ge hr1
      simpa only [envelope,indicator_of_notMem (show r ∉ Icc (0 : ℝ) 1 from fun h => hr1 h.2),
        indicator_of_mem (show r ∈ Ici (0 : ℝ) from hr0),
        indicator_of_mem (show r ∈ Ioi (1 : ℝ) from hrt),zero_add] using
        tail_point_bound z qp A W C n r hrt

private theorem core_integrable (qp A : ℝ) (C : T → ℝ) (n : ℕ) :
    IntegrableOn (coreEnvelope qp A C n) (Icc 0 1) := by
  apply ContinuousOn.integrableOn_Icc
  unfold coreEnvelope
  fun_prop

private theorem exp_Ici_integrable (z : ℝ) (hz : 0 < z) (n : ℕ) :
    IntegrableOn (fun r : ℝ => r^n*exp (-z*r)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact exponential_moment_integrable z hz n

private theorem w_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u) (W : T → ℝ) (n : ℕ) :
    IntegrableOn (wEnvelope z W n) (Ici 0) := by
  apply integrable_finsetSum
  intro u _
  exact (exp_Ici_integrable (z u) (hz u) n).const_mul |W u|

private theorem c_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u) (C : T → ℝ) (n : ℕ) :
    IntegrableOn (cEnvelope z C n) (Ioi 1) := by
  apply integrable_finsetSum
  intro u _
  exact (shifted_moment_integrable (z u) (hz u) n).const_mul |C u|

private theorem envelope_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (qp A : ℝ) (W C : T → ℝ) (n : ℕ) : Integrable (envelope z qp A W C n) := by
  exact (((core_integrable qp A C n).integrable_indicator measurableSet_Icc).fun_add
    ((w_integrable z hz W n).integrable_indicator measurableSet_Ici)).fun_add
      ((c_integrable z hz C n).integrable_indicator measurableSet_Ioi)

def momentBudget (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (n : ℕ) : ℝ :=
  |qp|/(((n : ℝ)+1)*((n : ℝ)+2))+
  |A|/(((n : ℝ)+1)*((n : ℝ)+2)*((n : ℝ)+3))+
  ∑ u, (|W u| *(n.factorial : ℝ)/z u^(n+1)+|C u| *(1/((n : ℝ)+1)+
    ∫ r in Ioi (1 : ℝ), r^n*exp (-z u*(r-1))))

private theorem core_integral (qp A : ℝ) (C : T → ℝ) (n : ℕ) :
    (∫ r in Icc (0 : ℝ) 1, coreEnvelope qp A C n r) =
      |qp|/(((n : ℝ)+1)*((n : ℝ)+2))+
      |A|/(((n : ℝ)+1)*((n : ℝ)+2)*((n : ℝ)+3))+
      ∑ u, |C u| /((n : ℝ)+1) := by
  have hl : IntegrableOn (fun r : ℝ => r^n*(1-r)) (Icc 0 1) := by
    apply ContinuousOn.integrableOn_Icc
    fun_prop
  have hq : IntegrableOn (fun r : ℝ => r^n*(r-1)^2/2) (Icc 0 1) := by
    apply ContinuousOn.integrableOn_Icc
    fun_prop
  have hp : IntegrableOn (fun r : ℝ => r^n) (Icc 0 1) := by
    apply ContinuousOn.integrableOn_Icc
    fun_prop
  dsimp only [coreEnvelope]
  rw [integral_add ((hl.const_mul |qp|).fun_add (hq.const_mul |A|))
      (integrable_finsetSum _ (fun u _ => hp.const_mul |C u|)),
    integral_add (hl.const_mul |qp|) (hq.const_mul |A|),
    integral_finsetSum _ (fun u _ => hp.const_mul |C u|)]
  simp only [integral_const_mul]
  rw [core_linear_moment,core_quadratic_moment]
  simp_rw [core_power_moment]
  simp [div_eq_mul_inv]

private theorem w_integral (z : T → ℝ) (hz : ∀ u, 0 < z u) (W : T → ℝ) (n : ℕ) :
    (∫ r in Ici (0 : ℝ), wEnvelope z W n r) = ∑ u, |W u| *(n.factorial : ℝ)/z u^(n+1) := by
  dsimp only [wEnvelope]
  rw [integral_finsetSum _ (fun u _ => (exp_Ici_integrable (z u) (hz u) n).const_mul |W u|)]
  apply Finset.sum_congr rfl
  intro u _
  rw [integral_const_mul,integral_Ici_eq_integral_Ioi,exponential_moment (z u) (hz u) n]
  ring

private theorem c_integral (z : T → ℝ) (hz : ∀ u, 0 < z u) (C : T → ℝ) (n : ℕ) :
    (∫ r in Ioi (1 : ℝ), cEnvelope z C n r) =
      ∑ u, |C u| *(∫ r in Ioi (1 : ℝ), r^n*exp (-z u*(r-1))) := by
  dsimp only [cEnvelope]
  rw [integral_finsetSum _ (fun u _ => (shifted_moment_integrable (z u) (hz u) n).const_mul |C u|)]
  simp only [integral_const_mul]

private theorem envelope_integral (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (qp A : ℝ) (W C : T → ℝ) (n : ℕ) :
    (∫ r : ℝ, envelope z qp A W C n r) = momentBudget z qp A W C n := by
  have hc := (core_integrable qp A C n).integrable_indicator measurableSet_Icc
  have hw := (w_integrable z hz W n).integrable_indicator measurableSet_Ici
  have ht := (c_integrable z hz C n).integrable_indicator measurableSet_Ioi
  dsimp only [envelope]
  rw [integral_add (hc.fun_add hw) ht,integral_add hc hw,
    integral_indicator measurableSet_Icc,integral_indicator measurableSet_Ici,
    integral_indicator measurableSet_Ioi,core_integral,w_integral z hz,c_integral z hz]
  unfold momentBudget
  simp only [div_eq_mul_inv,mul_add,Finset.sum_add_distrib,one_mul,mul_one,
    mul_comm,mul_assoc]
  ring

/-- A proved triangle budget for every honest absolute moment. All support,
majorant integrability and exponential tails are discharged internally. -/
theorem absoluteMoment_le_budget (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (qp A : ℝ) (W C : T → ℝ) (n : ℕ) :
    absoluteMoment z qp A W C n ≤ momentBudget z qp A W C n := by
  have ha : Integrable (fun r : ℝ => |r^n*scalarQ z qp A W C r|) := by
    simpa only [Real.norm_eq_abs] using (weighted_q_integrable z hz qp A W C n).norm
  exact (integral_mono ha (envelope_integrable z hz qp A W C n)
    (fun r => envelope_bound z qp A W C n r)).trans_eq (envelope_integral z hz qp A W C n)

def secondMomentBudget (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) : ℝ :=
  |qp|/12+|A|/60+∑ u, (2*|W u|/z u^3+|C u| *(1/3+1/z u+2/z u^2+2/z u^3))

def thirdMomentBudget (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) : ℝ :=
  |qp|/20+|A|/120+∑ u, (6*|W u|/z u^4+|C u| *(1/4+1/z u+3/z u^2+6/z u^3+6/z u^4))

def upperSecondMomentBudget (z : T → ℝ) (qpU AU : ℝ) (WU CU : T → ℝ) : ℝ :=
  qpU/12+AU/60+∑ u, (2*WU u/z u^3+CU u*(1/3+1/z u+2/z u^2+2/z u^3))

/-- The actual absolute second moment has exactly the coefficient triangle
upper bound used by the finite-frequency certificates. -/
theorem absoluteMoment_two_le (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (qp A : ℝ) (W C : T → ℝ) :
    absoluteMoment z qp A W C 2 ≤ secondMomentBudget z qp A W C := by
  apply (absoluteMoment_le_budget z hz qp A W C 2).trans_eq
  unfold momentBudget secondMomentBudget
  norm_num
  congr 1
  funext u
  have hs := shifted_moment_two (z u) (hz u)
  simp only [neg_mul] at hs
  rw [hs]
  ring

/-- A closed absolute third-moment bound for genuine small-frequency
remainders, with all moment integrability internally discharged. -/
theorem absoluteMoment_three_le (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (qp A : ℝ) (W C : T → ℝ) :
    absoluteMoment z qp A W C 3 ≤ thirdMomentBudget z qp A W C := by
  apply (absoluteMoment_le_budget z hz qp A W C 3).trans_eq
  unfold momentBudget thirdMomentBudget
  norm_num
  congr 1
  funext u
  have hs := shifted_moment_three (z u) (hz u)
  simp only [neg_mul] at hs
  rw [hs]
  ring

/-- Replacing actual absolute coefficients by verified upper bounds is
monotone in every entry; the rates remain the actual positive rates. -/
theorem secondMomentBudget_le_of_bounds (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (qp A qpU AU : ℝ) (W C WU CU : T → ℝ)
    (hqp : |qp| ≤ qpU) (hA : |A| ≤ AU)
    (hW : ∀ u, |W u| ≤ WU u) (hC : ∀ u, |C u| ≤ CU u) :
    secondMomentBudget z qp A W C ≤ upperSecondMomentBudget z qpU AU WU CU := by
  unfold secondMomentBudget upperSecondMomentBudget
  apply add_le_add
  · gcongr
  · apply Finset.sum_le_sum
    intro u _
    have hu := hz u
    gcongr
    · exact hW u
    · exact hC u

/-- The TRUE frequency second derivative is bounded by the explicit data
budget, with no supplied Hessian, moment or interchange premise. -/
theorem secondDerivative_norm_le_of_budget (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho qp A : ℝ) (hrho : 0 ≤ rho) (W C : T → ℝ) (k : ℝ) :
    ‖secondDerivative z rho qp A W C k‖ ≤ rho*secondMomentBudget z qp A W C :=
  (secondDerivative_norm_le z hz rho qp A hrho W C k).trans
    (mul_le_mul_of_nonneg_left (absoluteMoment_two_le z hz qp A W C) hrho)

/-- Actual pointwise coefficient and density bounds discharge the true
uniform second-derivative budget for every real frequency, including zero. -/
theorem secondDerivative_norm_le_of_bounds (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho rhoU qp A qpU AU : ℝ) (hrho : 0 ≤ rho) (hrhoU : rho ≤ rhoU)
    (W C WU CU : T → ℝ) (hqp : |qp| ≤ qpU) (hA : |A| ≤ AU)
    (hW : ∀ u, |W u| ≤ WU u) (hC : ∀ u, |C u| ≤ CU u) (k : ℝ) :
    ‖secondDerivative z rho qp A W C k‖ ≤ rhoU*upperSecondMomentBudget z qpU AU WU CU := by
  have hB := secondMomentBudget_le_of_bounds z hz qp A qpU AU W C WU CU hqp hA hW hC
  have hB0 : 0 ≤ secondMomentBudget z qp A W C :=
    (show 0 ≤ absoluteMoment z qp A W C 2 from integral_nonneg (fun _ => abs_nonneg _)).trans
      (absoluteMoment_two_le z hz qp A W C)
  exact (secondDerivative_norm_le_of_budget z hz rho qp A hrho W C k).trans
    (mul_le_mul hrhoU hB hB0 (hrho.trans hrhoU))

/-- A computed explicit second-moment budget and actual point bounds imply
units of the ORIGINAL physical Fourier matrix on the whole closed step. -/
theorem fourierFactor_interval_isUnit_of_budget (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho qp A : ℝ) (hrho : 0 ≤ rho) (W C : T → ℝ) (a h m d L : ℝ)
    (hh : 0 ≤ h) (hL : rho*secondMomentBudget z qp A W C ≤ L)
    (hm : m ≤ ‖ScalarFourierTail.factor z rho qp A W C a‖)
    (hd : ‖firstDerivative z rho qp A W C a‖ ≤ d)
    (hstep : 0 < m-d*h-L*h^2/2) :
    ∀ k ∈ Icc a (a+h), IsUnit (fourierFactor z (fun _ : Fin 1 => rho) (fun _ => 1)
      (fun _ => A) (fun _ _ => qp) (fun u _ _ => W u) (fun u _ _ => C u) k) := by
  apply fourierFactor_interval_isUnit z hz rho qp A hrho W C a h m d hh hm hd
  have hb := (mul_le_mul_of_nonneg_left (absoluteMoment_two_le z hz qp A W C) hrho).trans hL
  have hmul := mul_le_mul_of_nonneg_right hb (sq_nonneg h)
  linarith

/-- The same closed-step physical matrix conclusion from coefficient upper
bounds, density upper bound, and the saved numerical quadratic margin. -/
theorem fourierFactor_interval_isUnit_of_bounds (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho rhoU qp A qpU AU : ℝ) (hrho : 0 ≤ rho) (hrhoU : rho ≤ rhoU)
    (W C WU CU : T → ℝ) (hqp : |qp| ≤ qpU) (hA : |A| ≤ AU)
    (hW : ∀ u, |W u| ≤ WU u) (hC : ∀ u, |C u| ≤ CU u)
    (a h m d L : ℝ) (hh : 0 ≤ h) (hL : rhoU*upperSecondMomentBudget z qpU AU WU CU ≤ L)
    (hm : m ≤ ‖ScalarFourierTail.factor z rho qp A W C a‖)
    (hd : ‖firstDerivative z rho qp A W C a‖ ≤ d)
    (hstep : 0 < m-d*h-L*h^2/2) :
    ∀ k ∈ Icc a (a+h), IsUnit (fourierFactor z (fun _ : Fin 1 => rho) (fun _ => 1)
      (fun _ => A) (fun _ _ => qp) (fun u _ _ => W u) (fun u _ _ => C u) k) := by
  apply fourierFactor_interval_isUnit_of_budget z hz rho qp A hrho W C a h m d L hh _ hm hd hstep
  have hB := secondMomentBudget_le_of_bounds z hz qp A qpU AU W C WU CU hqp hA hW hC
  have hB0 : 0 ≤ secondMomentBudget z qp A W C :=
    (show 0 ≤ absoluteMoment z qp A W C 2 from integral_nonneg (fun _ => abs_nonneg _)).trans
      (absoluteMoment_two_le z hz qp A W C)
  exact (mul_le_mul hrhoU hB hB0 (hrho.trans hrhoU)).trans hL

/-- The original BH amplitudes satisfy the same closed-step matrix
criterion. The point derivative bound concerns deriv of the actual original
Fourier entry, not a supplied derivative dictionary or formal substitute. -/
theorem actual_interval_units_of_bounds (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho rhoU qpU AU : ℝ) (hrho : 0 ≤ rho) (hrhoU : rho ≤ rhoU)
    (Dt G : TailMatrix T 1) (WU CU : T → ℝ)
    (hqp : |amplitudeQp z (fun _ => rho) (fun _ => 1) Dt G 0 0| ≤ qpU)
    (hA : |amplitudeA z (fun _ => rho) (fun _ => 1) Dt G 0| ≤ AU)
    (hW : ∀ u, |W z (fun _ => rho) Dt G u 0 0| ≤ WU u)
    (hC : ∀ u, |C z (fun _ => rho) (fun _ => 1) Dt G u 0 0| ≤ CU u)
    (k0 h m d L : ℝ) (hh : 0 ≤ h)
    (hL : rhoU*upperSecondMomentBudget z qpU AU WU CU ≤ L)
    (hm : m ≤ ‖fourierFactor z (fun _ => rho) (fun _ => 1)
      (amplitudeA z (fun _ => rho) (fun _ => 1) Dt G)
      (amplitudeQp z (fun _ => rho) (fun _ => 1) Dt G)
      (W z (fun _ => rho) Dt G) (C z (fun _ => rho) (fun _ => 1) Dt G) k0 0 0‖)
    (hd : ‖deriv (fun k => fourierFactor z (fun _ => rho) (fun _ => 1)
      (amplitudeA z (fun _ => rho) (fun _ => 1) Dt G)
      (amplitudeQp z (fun _ => rho) (fun _ => 1) Dt G)
      (W z (fun _ => rho) Dt G) (C z (fun _ => rho) (fun _ => 1) Dt G) k 0 0) k0‖ ≤ d)
    (hstep : 0 < m-d*h-L*h^2/2) :
    ∀ k ∈ Icc k0 (k0+h), IsUnit (fourierFactor z (fun _ => rho) (fun _ => 1)
      (amplitudeA z (fun _ => rho) (fun _ => 1) Dt G)
      (amplitudeQp z (fun _ => rho) (fun _ => 1) Dt G)
      (W z (fun _ => rho) Dt G) (C z (fun _ => rho) (fun _ => 1) Dt G) k) := by
  let aa := amplitudeA z (fun _ => rho) (fun _ => 1) Dt G
  let qq := amplitudeQp z (fun _ => rho) (fun _ => 1) Dt G
  let ww := W z (fun _ => rho) Dt G
  let cc := C z (fun _ => rho) (fun _ => 1) Dt G
  have ha : aa = fun _ : Fin 1 => aa 0 := by funext i; fin_cases i; rfl
  have hq : qq = fun _ _ : Fin 1 => qq 0 0 := by funext i j; fin_cases i; fin_cases j; rfl
  have hw : ww = fun u (_ _) => ww u 0 0 := by funext u i j; fin_cases i; fin_cases j; rfl
  have hc : cc = fun u (_ _) => cc u 0 0 := by funext u i j; fin_cases i; fin_cases j; rfl
  have heq : (fun k => fourierFactor z (fun _ => rho) (fun _ => 1) aa qq ww cc k 0 0) =
      ScalarFourierTail.factor z rho (qq 0 0) (aa 0) (fun u => ww u 0 0) (fun u => cc u 0 0) := by
    funext k
    unfold ScalarFourierTail.factor
    rw [ha,hq,hw,hc]
  have hm' : m ≤ ‖ScalarFourierTail.factor z rho (qq 0 0) (aa 0)
      (fun u => ww u 0 0) (fun u => cc u 0 0) k0‖ := by
    rw [← heq]
    exact hm
  have hd' : ‖firstDerivative z rho (qq 0 0) (aa 0)
      (fun u => ww u 0 0) (fun u => cc u 0 0) k0‖ ≤ d := by
    rw [← (factor_hasDerivAt z hz rho (qq 0 0) (aa 0) hrho
      (fun u => ww u 0 0) (fun u => cc u 0 0) k0).deriv,← heq]
    exact hd
  have hall := fourierFactor_interval_isUnit_of_bounds z hz rho rhoU (qq 0 0) (aa 0) qpU AU hrho hrhoU
    (fun u => ww u 0 0) (fun u => cc u 0 0) WU CU hqp hA hW hC k0 h m d L hh hL hm' hd' hstep
  intro k hk
  change IsUnit (fourierFactor z (fun _ => rho) (fun _ => 1) aa qq ww cc k)
  rw [ha,hq,hw,hc]
  exact hall k hk

/-- info: 'FMSA.Convergence.ScalarAbsoluteMoments.absoluteMoment_le_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarAbsoluteMoments.absoluteMoment_le_budget
/-- info: 'FMSA.Convergence.ScalarAbsoluteMoments.absoluteMoment_two_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarAbsoluteMoments.absoluteMoment_two_le
/-- info: 'FMSA.Convergence.ScalarAbsoluteMoments.absoluteMoment_three_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarAbsoluteMoments.absoluteMoment_three_le
/-- info: 'FMSA.Convergence.ScalarAbsoluteMoments.secondMomentBudget_le_of_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarAbsoluteMoments.secondMomentBudget_le_of_bounds
/-- info: 'FMSA.Convergence.ScalarAbsoluteMoments.secondDerivative_norm_le_of_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarAbsoluteMoments.secondDerivative_norm_le_of_budget
/-- info: 'FMSA.Convergence.ScalarAbsoluteMoments.secondDerivative_norm_le_of_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarAbsoluteMoments.secondDerivative_norm_le_of_bounds
/-- info: 'FMSA.Convergence.ScalarAbsoluteMoments.fourierFactor_interval_isUnit_of_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarAbsoluteMoments.fourierFactor_interval_isUnit_of_budget
/-- info: 'FMSA.Convergence.ScalarAbsoluteMoments.fourierFactor_interval_isUnit_of_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarAbsoluteMoments.fourierFactor_interval_isUnit_of_bounds
/-- info: 'FMSA.Convergence.ScalarAbsoluteMoments.actual_interval_units_of_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarAbsoluteMoments.actual_interval_units_of_bounds
end FMSA.Convergence.ScalarAbsoluteMoments
