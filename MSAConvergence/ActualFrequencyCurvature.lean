import MSAConvergence.ScalarFrequencyCurvature
import MSAConvergence.ScalarAbsoluteMoments

/-! Exact compressed frequency-curvature budget for the ORIGINAL physical
Fourier factor. The closed transform is identified with the honest integral;
genuine first/second derivatives and the global moment bound are reused.
No differentiation identity, root, canonicity or numerical enclosure is assumed. -/
noncomputable section
open Set Real
open scoped BigOperators
namespace FMSA.Convergence.ActualFrequencyCurvature
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.ScalarFrequencyCurvature
open FMSA.Convergence.ScalarFourierDerivatives
open FMSA.Convergence.ScalarAbsoluteMoments
open FMSA.Convergence.QuadraticFrequencyStep
variable {T : Type*} [Fintype T]

/-- The closed kernel is the honest ORIGINAL Fourier integral. Only
positive frequency is used; no quotient convention is evaluated at zero. -/
theorem fourierQ_eq_closedSymbol (z : T → ℝ) (hz : ∀ u, 0< z u)
    (qp A : ℝ) (W C : T → ℝ) (k : ℝ) (hk : 0< k) :
    fourierQ z (fun _ : Fin 1 => 1) (fun _ => A) (fun _ _ => qp)
      (fun u _ _ => W u) (fun u _ _ => C u) k 0 0 =
      closedSymbol z qp A W C (Complex.I*(k : ℂ)) := by
  rw [fourierQ_eq_QhatComplex z hz _ _ _ _ _ (by intro i; norm_num) k hk.ne' 0 0]
  have hw (u : T) : w (z u) (Complex.I*(k : ℂ))*(W u : ℂ)=
      (W u : ℂ)/(Complex.I*(k : ℂ)+(z u : ℂ)) := by
    unfold w
    ring
  have hc (u : T) : c (z u) (Complex.I*(k : ℂ))*(C u : ℂ)=
      (C u : ℂ)*(1-Complex.exp (-(Complex.I*(k : ℂ))))/(Complex.I*(k : ℂ))+
        (C u : ℂ)*Complex.exp (-(Complex.I*(k : ℂ)))/(Complex.I*(k : ℂ)+(z u : ℂ)) := by
    unfold c
    ring
  dsimp only [closedSymbol]
  simp_rw [hw,hc]
  simp [QhatComplex,MSAMixture.edgeLo,MSAMixture.edgeHi,e1,e2,
    mul_add,mul_div_assoc,Finset.sum_add_distrib]
  ring

/-- The ORIGINAL sqrt-density physical factor has exactly this closed form. -/
theorem factor_eq_closedSymbol (z : T → ℝ) (hz : ∀ u, 0< z u)
    (rho qp A : ℝ) (hrho : 0≤ rho) (W C : T → ℝ) (k : ℝ) (hk : 0< k) :
    ScalarFourierTail.factor z rho qp A W C k =
      1-(rho : ℂ)*closedSymbol z qp A W C (Complex.I*(k : ℂ)) := by
  rw [factor_eq_integral z rho qp A hrho W C k,
    weightedFourier_zero_order,fourierQ_eq_closedSymbol z hz qp A W C k hk]

/-- The genuine first integral derivative equals the closed first derivative. -/
theorem firstDerivative_eq_closed (z : T → ℝ) (hz : ∀ u, 0< z u)
    (rho qp A : ℝ) (hrho : 0≤ rho) (W C : T → ℝ) (k : ℝ) (hk : 0< k) :
    firstDerivative z rho qp A W C k=
      -(rho : ℂ)*Complex.I*firstSymbol z qp A W C (Complex.I*(k : ℂ)) :=
  firstDerivative_eq_of_closedFactor z qp A W C rho _ _
    (factor_hasDerivAt z hz rho qp A hrho W C)
    (factor_eq_closedSymbol z hz rho qp A hrho W C) k hk

/-- The second weighted integral is the closed second derivative of the
ORIGINAL factor, obtained by uniqueness, not a differentiation premise. -/
theorem secondDerivative_eq_closed (z : T → ℝ) (hz : ∀ u, 0< z u)
    (rho qp A : ℝ) (hrho : 0≤ rho) (W C : T → ℝ) (k : ℝ) (hk : 0< k) :
    secondDerivative z rho qp A W C k=
      (rho : ℂ)*secondSymbol z qp A W C (Complex.I*(k : ℂ)) :=
  secondDerivative_eq_of_closedFactor z qp A W C rho _ _ _
    (factor_hasDerivAt z hz rho qp A hrho W C)
    (firstDerivative_hasDerivAt z hz rho qp A W C)
    (factor_eq_closedSymbol z hz rho qp A hrho W C) k hk

/-- Exact H2, including the actual density factor, bounds the true second
derivative at every positive real frequency. -/
theorem secondDerivative_norm_le_curvature (z : T → ℝ) (hz : ∀ u, 0< z u)
    (rho qp A : ℝ) (hrho : 0≤ rho) (W C : T → ℝ) (k : ℝ) (hk : 0< k) :
    ‖secondDerivative z rho qp A W C k‖≤ rho*groupedBudget z qp A W C k :=
  secondDerivative_norm_le_of_closedFactor z hz rho qp A hrho W C _ _ _
    (factor_hasDerivAt z hz rho qp A hrho W C)
    (firstDerivative_hasDerivAt z hz rho qp A W C)
    (factor_eq_closedSymbol z hz rho qp A hrho W C) k hk

/-- Density and coefficient upper bounds at a> 0 control EVERY real k≥ a. -/
theorem secondDerivative_norm_le_curvature_bounds (z : T → ℝ) (hz : ∀ u, 0< z u)
    (rho rhoU qp A qpU AU : ℝ) (hrho : 0≤ rho) (hrhoU : rho≤ rhoU)
    (W C WU CU : T → ℝ) (hqp : |qp|≤ qpU) (hA : |A|≤ AU)
    (hW : ∀ u, |W u|≤ WU u) (hC : ∀ u, |C u|≤ CU u)
    (a k : ℝ) (ha : 0< a) (hak : a≤ k) :
    ‖secondDerivative z rho qp A W C k‖≤ rhoU*upperGroupedBudget z qpU AU WU CU a :=
  secondDerivative_norm_le_of_closedFactor_bounds z hz rho rhoU qp A qpU AU hrho hrhoU
    W C WU CU hqp hA hW hC _ _ _
    (factor_hasDerivAt z hz rho qp A hrho W C)
    (firstDerivative_hasDerivAt z hz rho qp A W C)
    (factor_eq_closedSymbol z hz rho qp A hrho W C) a k ha hak

/-- Taking the smaller of the proved global S2 and high-frequency H2 is
valid on the WHOLE positive-frequency step. -/
theorem secondDerivative_norm_le_min_bounds (z : T → ℝ) (hz : ∀ u, 0< z u)
    (rho rhoU qp A qpU AU : ℝ) (hrho : 0≤ rho) (hrhoU : rho≤ rhoU)
    (W C WU CU : T → ℝ) (hqp : |qp|≤ qpU) (hA : |A|≤ AU)
    (hW : ∀ u, |W u|≤ WU u) (hC : ∀ u, |C u|≤ CU u)
    (a k : ℝ) (ha : 0< a) (hak : a≤ k) :
    ‖secondDerivative z rho qp A W C k‖≤
      min (rhoU*upperSecondMomentBudget z qpU AU WU CU)
        (rhoU*upperGroupedBudget z qpU AU WU CU a) :=
  le_min (secondDerivative_norm_le_of_bounds z hz rho rhoU qp A qpU AU hrho hrhoU
    W C WU CU hqp hA hW hC k)
    (secondDerivative_norm_le_curvature_bounds z hz rho rhoU qp A qpU AU hrho hrhoU
      W C WU CU hqp hA hW hC a k ha hak)

/-- The literal compressed march rule. At zero (or any nonpositive origin)
only the globally proved S2 is used, so no inverse power is evaluated there. -/
def stepBudget (z : T → ℝ) (rhoU qpU AU : ℝ) (WU CU : T → ℝ) (a : ℝ) : ℝ :=
  if 0< a then min (rhoU*upperSecondMomentBudget z qpU AU WU CU)
    (rhoU*upperGroupedBudget z qpU AU WU CU a)
  else rhoU*upperSecondMomentBudget z qpU AU WU CU

/-- The compressed saved L budget controls the true curvature on every
frequency at or to the right of the step's origin, including origin zero. -/
theorem secondDerivative_norm_le_stepBudget (z : T → ℝ) (hz : ∀ u, 0< z u)
    (rho rhoU qp A qpU AU : ℝ) (hrho : 0≤ rho) (hrhoU : rho≤ rhoU)
    (W C WU CU : T → ℝ) (hqp : |qp|≤ qpU) (hA : |A|≤ AU)
    (hW : ∀ u, |W u|≤ WU u) (hC : ∀ u, |C u|≤ CU u)
    (a k : ℝ) (hak : a≤ k) :
    ‖secondDerivative z rho qp A W C k‖≤ stepBudget z rhoU qpU AU WU CU a := by
  unfold stepBudget
  split_ifs with ha
  · exact secondDerivative_norm_le_min_bounds z hz rho rhoU qp A qpU AU hrho hrhoU
      W C WU CU hqp hA hW hC a k ha hak
  · exact secondDerivative_norm_le_of_bounds z hz rho rhoU qp A qpU AU hrho hrhoU
      W C WU CU hqp hA hW hC k

/-- Every saved compressed quadratic step is zero-free for the ORIGINAL
physical Fourier matrix once its actual point/coefficient bounds are proved. -/
theorem fourierFactor_interval_isUnit_of_stepBudget (z : T → ℝ) (hz : ∀ u, 0< z u)
    (rho rhoU qp A qpU AU : ℝ) (hrho : 0≤ rho) (hrhoU : rho≤ rhoU)
    (W C WU CU : T → ℝ) (hqp : |qp|≤ qpU) (hA : |A|≤ AU)
    (hW : ∀ u, |W u|≤ WU u) (hC : ∀ u, |C u|≤ CU u)
    (a h m d L : ℝ) (hh : 0≤ h) (hL : stepBudget z rhoU qpU AU WU CU a≤ L)
    (hm : m≤‖ScalarFourierTail.factor z rho qp A W C a‖)
    (hd : ‖firstDerivative z rho qp A W C a‖≤ d)
    (hstep : 0< m-d*h-L*h^2/2) :
    ∀ k ∈ Icc a (a+h), IsUnit (fourierFactor z (fun _ : Fin 1 => rho) (fun _ => 1)
      (fun _ => A) (fun _ _ => qp) (fun u _ _ => W u) (fun u _ _ => C u) k) := by
  have hzero := interval_nonzero (ScalarFourierTail.factor z rho qp A W C)
    (firstDerivative z rho qp A W C) (secondDerivative z rho qp A W C) a h L m d hh
    (fun k _ => factor_hasDerivAt z hz rho qp A hrho W C k)
    (fun k _ => firstDerivative_hasDerivAt z hz rho qp A W C k)
    (fun k hk => (secondDerivative_norm_le_stepBudget z hz rho rhoU qp A qpU AU hrho hrhoU
      W C WU CU hqp hA hW hC a k hk.1).trans hL) hm hd hstep
  intro k hk
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_fin_one]
  exact hzero k hk

/-- The original BH amplitudes satisfy the same closed-step matrix
criterion. The point derivative bound concerns deriv of the actual original
Fourier entry, not a supplied derivative dictionary or formal substitute. -/
theorem actual_interval_units_of_stepBudget (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho rhoU qpU AU : ℝ) (hrho : 0 ≤ rho) (hrhoU : rho ≤ rhoU)
    (Dt G : TailMatrix T 1) (WU CU : T → ℝ)
    (hqp : |amplitudeQp z (fun _ => rho) (fun _ => 1) Dt G 0 0| ≤ qpU)
    (hA : |amplitudeA z (fun _ => rho) (fun _ => 1) Dt G 0| ≤ AU)
    (hW : ∀ u, |W z (fun _ => rho) Dt G u 0 0| ≤ WU u)
    (hC : ∀ u, |C z (fun _ => rho) (fun _ => 1) Dt G u 0 0| ≤ CU u)
    (k0 h m d L : ℝ) (hh : 0 ≤ h)
    (hL : stepBudget z rhoU qpU AU WU CU k0 ≤ L)
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
  have hall := fourierFactor_interval_isUnit_of_stepBudget z hz rho rhoU (qq 0 0) (aa 0) qpU AU hrho hrhoU
    (fun u => ww u 0 0) (fun u => cc u 0 0) WU CU hqp hA hW hC k0 h m d L hh hL hm' hd' hstep
  intro k hk
  change IsUnit (fourierFactor z (fun _ => rho) (fun _ => 1) aa qq ww cc k)
  rw [ha,hq,hw,hc]
  exact hall k hk


/-- info: 'FMSA.Convergence.ActualFrequencyCurvature.fourierQ_eq_closedSymbol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualFrequencyCurvature.fourierQ_eq_closedSymbol
/-- info: 'FMSA.Convergence.ActualFrequencyCurvature.factor_eq_closedSymbol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualFrequencyCurvature.factor_eq_closedSymbol
/-- info: 'FMSA.Convergence.ActualFrequencyCurvature.firstDerivative_eq_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualFrequencyCurvature.firstDerivative_eq_closed
/-- info: 'FMSA.Convergence.ActualFrequencyCurvature.secondDerivative_eq_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualFrequencyCurvature.secondDerivative_eq_closed
/-- info: 'FMSA.Convergence.ActualFrequencyCurvature.secondDerivative_norm_le_curvature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualFrequencyCurvature.secondDerivative_norm_le_curvature
/-- info: 'FMSA.Convergence.ActualFrequencyCurvature.secondDerivative_norm_le_curvature_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualFrequencyCurvature.secondDerivative_norm_le_curvature_bounds
/-- info: 'FMSA.Convergence.ActualFrequencyCurvature.secondDerivative_norm_le_min_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualFrequencyCurvature.secondDerivative_norm_le_min_bounds
/-- info: 'FMSA.Convergence.ActualFrequencyCurvature.secondDerivative_norm_le_stepBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualFrequencyCurvature.secondDerivative_norm_le_stepBudget
/-- info: 'FMSA.Convergence.ActualFrequencyCurvature.fourierFactor_interval_isUnit_of_stepBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualFrequencyCurvature.fourierFactor_interval_isUnit_of_stepBudget
/-- info: 'FMSA.Convergence.ActualFrequencyCurvature.actual_interval_units_of_stepBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActualFrequencyCurvature.actual_interval_units_of_stepBudget
end FMSA.Convergence.ActualFrequencyCurvature
