import MSAConvergence.PureFluidActualDressingPoles

set_option linter.style.header false

/-! Positive-infinity normalization of the inverse dressing coordinates
recovered from the actual finite-tail BH factor. The raw rational and
exponential pieces, including the scaled exponential coefficient, have
limits determined without any root equation. This is one necessary step
toward global finite-sum dressing identification. -/

noncomputable section
open Real Filter Topology Set
namespace FMSA.Convergence.PureFluidActualInfinity
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidCandidateOriginConstraint
open FMSA.Convergence.PureFluidActualDressingCoordinates
variable {T : Type*} [Fintype T]

theorem inv_shift_tendsto_zero (a : ℝ) :
    Tendsto (fun s : ℝ => (s+a)⁻¹) atTop (𝓝 (0 : ℝ)) := by
  have hden : Tendsto (fun s : ℝ => s+a) atTop atTop :=
    tendsto_atTop_add_const_right atTop a tendsto_id
  simpa only [Function.comp_def] using (tendsto_inv_atTop_zero.comp hden)

theorem inv_sq_tendsto_zero :
    Tendsto (fun s : ℝ => (s^2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
  have h : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  simpa only [inv_pow, zero_pow (by norm_num : 2 ≠ 0)] using h.pow 2

theorem inv_cube_tendsto_zero :
    Tendsto (fun s : ℝ => (s^3)⁻¹) atTop (𝓝 (0 : ℝ)) := by
  have h : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  simpa only [inv_pow, zero_pow (by norm_num : 3 ≠ 0)] using h.pow 3

theorem actual_rational_tendsto_one_atTop
    (xi : ℝ) (z D G : T → ℝ) :
    Tendsto (rationalPart xi z D G) atTop (𝓝 (1 : ℝ)) := by
  let rho := rhoOf xi
  let A := MultiTail.amplitudeA xi z D G
  let q := MultiTail.amplitudeQp xi z D G
  have h1 : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have h2 := inv_sq_tendsto_zero
  have h3 := inv_cube_tendsto_zero
  have htail (t : T) : Tendsto
      (fun s : ℝ => rho*(MultiTail.W xi z D G t/(s+z t)+
        MultiTail.C xi z D G t/s)) atTop (𝓝 (0 : ℝ)) := by
    have hW := (tendsto_const_nhds (x := MultiTail.W xi z D G t)).mul
      (inv_shift_tendsto_zero (z t))
    have hC := (tendsto_const_nhds (x := MultiTail.C xi z D G t)).mul h1
    have h := (tendsto_const_nhds (x := rho)).mul (hW.add hC)
    convert h using 1
    · funext s
      simp only [div_eq_mul_inv]
    · ring_nf
  have hsum : Tendsto
      (fun s : ℝ => ∑ t, rho*(MultiTail.W xi z D G t/(s+z t)+
        MultiTail.C xi z D G t/s)) atTop (𝓝 (0 : ℝ)) := by
    convert tendsto_finsetSum Finset.univ (fun t _ => htail t) using 1
    simp
  have hA := (tendsto_const_nhds (x := rho*A)).mul h3
  have hB := (tendsto_const_nhds (x := rho*(A-q))).mul h2
  have hC := (tendsto_const_nhds (x := rho*(q-A/2))).mul h1
  have h := ((((tendsto_const_nhds (x := (1 : ℝ))).sub hA).add hB).add hC).sub hsum
  convert h using 1
  · funext s
    simp only [rationalPart,rho,A,q,div_eq_mul_inv]
  · ring_nf

theorem scaled_exponential_identity (xi : ℝ) (z D G : T → ℝ)
    (s : ℝ) (hs : s ≠ 0) (hzs : ∀ t, s+z t ≠ 0) :
    s*exponentialPart xi z D G s =
      rhoOf xi*MultiTail.amplitudeA xi z D G/s^2 +
      rhoOf xi*MultiTail.amplitudeQp xi z D G/s +
      ∑ t, rhoOf xi*MultiTail.C xi z D G t*z t/(s+z t) := by
  have hterm (t : T) :
      s*(rhoOf xi*MultiTail.C xi z D G t*(1/s-1/(s+z t))) =
        rhoOf xi*MultiTail.C xi z D G t*z t/(s+z t) := by
    field_simp [hs,hzs t]
    ring
  unfold exponentialPart
  dsimp
  rw [mul_add,mul_add,Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun t _ => hterm t)]
  field_simp [hs]

theorem actual_scaled_exponential_tendsto_zero_atTop
    (xi : ℝ) (z D G : T → ℝ) (hz : ∀ t, 0 ≤ z t) :
    Tendsto (fun s : ℝ => s*exponentialPart xi z D G s)
      atTop (𝓝 (0 : ℝ)) := by
  let rho := rhoOf xi
  let A := MultiTail.amplitudeA xi z D G
  let q := MultiTail.amplitudeQp xi z D G
  have h1 : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have h2 := inv_sq_tendsto_zero
  have htail (t : T) : Tendsto
      (fun s : ℝ => rho*MultiTail.C xi z D G t*z t/(s+z t))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds (x := rho*MultiTail.C xi z D G t*z t)).mul
        (inv_shift_tendsto_zero (z t))
  have hsum : Tendsto
      (fun s : ℝ => ∑ t, rho*MultiTail.C xi z D G t*z t/(s+z t))
      atTop (𝓝 (0 : ℝ)) := by
    convert tendsto_finsetSum Finset.univ (fun t _ => htail t) using 1
    simp
  have hA := (tendsto_const_nhds (x := rho*A)).mul h2
  have hq := (tendsto_const_nhds (x := rho*q)).mul h1
  have hlim : Tendsto
      (fun s : ℝ => rho*A/s^2+rho*q/s+
        ∑ t, rho*MultiTail.C xi z D G t*z t/(s+z t))
      atTop (𝓝 (0 : ℝ)) := by
    convert (hA.add hq).add hsum using 1
    · funext s
      simp only [div_eq_mul_inv]
    · ring_nf
  have heq : (fun s : ℝ => s*exponentialPart xi z D G s) =ᶠ[atTop]
      (fun s : ℝ => rho*A/s^2+rho*q/s+
        ∑ t, rho*MultiTail.C xi z D G t*z t/(s+z t)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    apply scaled_exponential_identity xi z D G s hs.ne'
    intro t
    exact (add_pos_of_pos_of_nonneg hs (hz t)).ne'
  exact hlim.congr' heq.symm

theorem actual_exponential_tendsto_zero_atTop
    (xi : ℝ) (z D G : T → ℝ) (hz : ∀ t, 0 ≤ z t) :
    Tendsto (exponentialPart xi z D G) atTop (𝓝 (0 : ℝ)) := by
  have h1 : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hlim := (actual_scaled_exponential_tendsto_zero_atTop xi z D G hz).mul h1
  have heq : exponentialPart xi z D G =ᶠ[atTop]
      (fun s : ℝ => (s*exponentialPart xi z D G s)*s⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    field_simp [hs.ne']
  simpa only [mul_zero] using hlim.congr' heq.symm

theorem actualU_tendsto_one_atTop
    (xi : ℝ) (z D G : T → ℝ) (hz : ∀ t, 0 ≤ z t) :
    Tendsto (actualU xi z D G) atTop (𝓝 (1 : ℝ)) := by
  have hinv : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hinvneg : Tendsto (fun s : ℝ => (-s)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [inv_neg,neg_zero] using hinv.neg
  have hP := actual_rational_tendsto_one_atTop xi z D G
  have hS := actual_exponential_tendsto_zero_atTop xi z D G hz
  have hp := hardP_tendsto_of_inv xi (fun s : ℝ => -s) hinvneg
  have hq := hardShat_tendsto_of_inv xi (fun s : ℝ => -s) hinvneg
  have hp0 := hardP_tendsto_of_inv xi (fun s : ℝ => s) hinv
  have hq0 := hardShat_tendsto_of_inv xi (fun s : ℝ => s) hinv
  have hlim := ((hp.mul hP).sub (hq.mul hS)).add
    ((hp0.mul hS).sub (hq0.mul hP))
  convert hlim using 1
  · funext s
    simp only [actualU,dressingU,dressingD]
  · norm_num

theorem actualG_tendsto_zero_atTop
    (xi : ℝ) (z D G : T → ℝ) (hz : ∀ t, 0 ≤ z t) :
    Tendsto (actualG xi z D G) atTop (𝓝 (0 : ℝ)) := by
  have hS := actual_scaled_exponential_tendsto_zero_atTop xi z D G hz
  have hSh : Tendsto (fun s : ℝ => s*hardShat xi s)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [exponentialPart_zero] using
      (actual_scaled_exponential_tendsto_zero_atTop
        xi z (fun _ => 0) G hz)
  have hP := actual_rational_tendsto_one_atTop xi z D G
  have hHP := hardP_tendsto_of_inv xi (fun s : ℝ => s)
    (show Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 (0 : ℝ)) from
      tendsto_inv_atTop_zero)
  have hlim := (hHP.mul hS).sub (hSh.mul hP)
  convert hlim using 1
  · funext s
    simp only [actualG,dressingG,dressingD]
    ring
  · norm_num

end FMSA.Convergence.PureFluidActualInfinity

/-- info: 'FMSA.Convergence.PureFluidActualInfinity.inv_shift_tendsto_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualInfinity.inv_shift_tendsto_zero
/-- info: 'FMSA.Convergence.PureFluidActualInfinity.inv_sq_tendsto_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualInfinity.inv_sq_tendsto_zero
/-- info: 'FMSA.Convergence.PureFluidActualInfinity.inv_cube_tendsto_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualInfinity.inv_cube_tendsto_zero
/-- info: 'FMSA.Convergence.PureFluidActualInfinity.actual_rational_tendsto_one_atTop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualInfinity.actual_rational_tendsto_one_atTop
/-- info: 'FMSA.Convergence.PureFluidActualInfinity.scaled_exponential_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualInfinity.scaled_exponential_identity
/-- info: 'FMSA.Convergence.PureFluidActualInfinity.actual_scaled_exponential_tendsto_zero_atTop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualInfinity.actual_scaled_exponential_tendsto_zero_atTop
/-- info: 'FMSA.Convergence.PureFluidActualInfinity.actual_exponential_tendsto_zero_atTop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualInfinity.actual_exponential_tendsto_zero_atTop
/-- info: 'FMSA.Convergence.PureFluidActualInfinity.actualU_tendsto_one_atTop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualInfinity.actualU_tendsto_one_atTop
/-- info: 'FMSA.Convergence.PureFluidActualInfinity.actualG_tendsto_zero_atTop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualInfinity.actualG_tendsto_zero_atTop
