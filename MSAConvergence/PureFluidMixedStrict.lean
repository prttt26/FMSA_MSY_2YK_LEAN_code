import MSAConvergence.PureFluidMixedTheorem

set_option linter.style.header false

/-! Every mixed coefficient of the pure-fluid amplitudes in the tail strengths is strictly positive,
except the monomials of `D_t` without `K_t`, which vanish. -/

noncomputable section
open Filter Topology
namespace FMSA.Convergence.PureFluidMixedStrict
open FMSA.Convergence.PureFluidMixedPicard FMSA.Convergence.PureFluidMixedRay
open FMSA.Convergence.PureFluidMixedAmplitude FMSA.Convergence.PureFluidMixedTheorem
open FMSA.Convergence.PureFluidFoldPath FMSA.Convergence.PureFluidFoldBridge
open FMSA.Convergence.PureFluidRFormalSolution FMSA.Convergence.PureFluidRLabelSubstitution
open FMSA.Convergence.PureFluidHFormalSolution FMSA.Convergence.PureFluidHPathFormalSubstitution
open FMSA.Convergence.PureFluidThetaCouplingTaylor
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.PureFluidNodeClosedForm
open FMSA.Convergence.PureFluidExponentialSplit FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.ExactMSA
open MvPowerSeries

variable {T : Type*} [Fintype T] [DecidableEq T]

theorem nn_sub_mul {A A' B B' : MvPowerSeries T ℝ} (hA : NN (A - A')) (hB : NN (B - B'))
    (hA' : NN A') (hB0 : NN B) : NN (A * B - A' * B') := by
  have h : A * B - A' * B' = (A - A') * B + A' * (B - B') := by ring
  rw [h]
  exact nn_add (nn_mul hA hB0) (nn_mul hA' hB)

theorem nn_sub_pow {A B : MvPowerSeries T ℝ} (hd : NN (A - B)) (hA : NN A) (hB : NN B) (k : ℕ) :
    NN (A ^ k - B ^ k) := by
  induction k with
  | zero =>
    intro m
    simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact nn_sub_mul ih hd (nn_pow hB k) hA

/-- Coefficientwise comparison passes to monomials in the entries. -/
theorem nn_sub_prod {a b : T → MvPowerSeries T ℝ} (hd : ∀ t, NN (a t - b t)) (ha : ∀ t, NN (a t))
    (hb : ∀ t, NN (b t)) (m : T →₀ ℕ) :
    NN ((m.prod fun t k => a t ^ k) - m.prod fun t k => b t ^ k) := by
  change NN ((∏ t ∈ m.support, a t ^ m t) - ∏ t ∈ m.support, b t ^ m t)
  induction m.support using Finset.induction_on with
  | empty =>
    intro n
    simp
  | insert t s ht ih =>
    rw [Finset.prod_insert ht, Finset.prod_insert ht]
    refine nn_sub_mul (nn_sub_pow (hd t) (ha t) (hb t) _) ih (nn_pow (hb t) _) ?_
    exact Finset.prod_induction _ NN (fun _ _ => nn_mul) nn_one fun u _ => nn_pow (ha u) _

/-- The monomial built from `c_t X_t`. -/
theorem coeff_prod_C_mul_X (c : T → ℝ) (m : T →₀ ℕ) :
    coeff m (m.prod fun t k => (C (c t) * X t : MvPowerSeries T ℝ) ^ k) =
      m.prod fun t k => c t ^ k := by
  have hX : (m.prod fun s n => (X s : MvPowerSeries T ℝ) ^ n) = monomial m (1 : ℝ) := by
    have h := subst_monomial (HasSubst.X (σ := T) (S := ℝ)) m (1 : ℝ)
    rw [subst_self] at h
    simpa using h.symm
  have hp : (m.prod fun t k => (C (c t) * X t : MvPowerSeries T ℝ) ^ k) =
      C (m.prod fun t k => c t ^ k) * m.prod fun s n => (X s : MvPowerSeries T ℝ) ^ n := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  rw [hp, hX, coeff_C_mul, coeff_monomial_same, mul_one]

/-- A term of the substitution bounds its coefficient from below. -/
theorem coeff_subst_ge {a : T → MvPowerSeries T ℝ} (h0 : ∀ t, constantCoeff (a t) = 0)
    (ha : ∀ t, NN (a t)) {f : MvPowerSeries T ℝ} (hf : NN f) (m e : T →₀ ℕ) :
    coeff m f * coeff e (m.prod fun t k => a t ^ k) ≤ coeff e (subst a f) := by
  classical
  have hs := hasSubst_of_constantCoeff_zero h0
  rw [coeff_subst hs]
  have hfin := coeff_subst_finite hs f e
  have hnn : ∀ d : T →₀ ℕ, 0 ≤ coeff d f • coeff e (d.prod fun t k => a t ^ k) := fun d => by
    simpa only [smul_eq_mul] using mul_nonneg (hf d) (nn_finsupp_prod ha d e)
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by simp)]
  by_cases hm : coeff m f * coeff e (m.prod fun t k => a t ^ k) = 0
  · rw [hm]
    exact Finset.sum_nonneg fun d _ => hnn d
  · have hmem : m ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hm
    exact Finset.single_le_sum (f := fun d => coeff d f • coeff e (d.prod fun t k => a t ^ k))
      (fun d _ => hnn d) hmem

/-- `1/(1 - κ r) = 1 + κ r q`. -/
theorem qK_expand (xi : ℝ) (z : T → ℝ) (t : T) :
    qK xi z t = 1 + C (kappaOf xi z t) * (rK xi z t * qK xi z t) := by
  have hm := MvPowerSeries.mul_inv_cancel (1 - C (kappaOf xi z t) * rK xi z t)
    (by simp [rK_constantCoeff])
  change (1 - C (kappaOf xi z t) * rK xi z t) * qK xi z t = 1 at hm
  linear_combination hm

variable {xi : ℝ} {z : T → ℝ}

theorem qK_sub_one_nn (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) :
    NN (qK xi z t - 1) := by
  have h : qK xi z t - 1 = C (kappaOf xi z t) * (rK xi z t * qK xi z t) := by
    linear_combination qK_expand xi z t
  rw [h]
  exact nn_mul (nn_C (kappaOf_pos hxi0 hxi1 hz t).le)
    (nn_mul (rK_nn hxi0 hxi1 hz t) (qK_nn hxi0 hxi1 hz t))

/-- `θ_t` dominates its leading term `a_t K_t`. -/
theorem thetaK_sub_leading_nn (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) :
    NN (thetaK xi z t - C (alphaUnit xi z t) * X t) := by
  have hfix : thetaK xi z t = C (alphaUnit xi z t) * (X t * qK xi z t ^ 2) :=
    thetaM_fixed (z := z) (a := alphaUnit xi z) (κ := kappaOf xi z) t
  have hE := qK_sub_one_nn hxi0 hxi1 hz t
  have heq : thetaK xi z t - C (alphaUnit xi z t) * X t =
      C (alphaUnit xi z t) * (X t * ((qK xi z t - 1) * (qK xi z t - 1) + (qK xi z t - 1) +
        (qK xi z t - 1))) := by
    rw [hfix]
    ring
  rw [heq]
  exact nn_mul (nn_C (alphaUnit_pos hxi0 hxi1 hz t).le) (nn_mul (nn_X t)
    (nn_add (nn_add (nn_mul hE hE) hE) hE))

/-- Every nonconstant mixed coefficient of `r_t` in the tail strengths is strictly positive. -/
theorem rK_coeff_pos (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) {m : T →₀ ℕ}
    (hm : m ≠ 0) : 0 < coeff m (rK xi z t) := by
  have hb : ∀ u, NN (C (alphaUnit xi z u) * X u : MvPowerSeries T ℝ) := fun u =>
    nn_mul (nn_C (alphaUnit_pos hxi0 hxi1 hz u).le) (nn_X u)
  have hd := nn_sub_prod (thetaK_sub_leading_nn hxi0 hxi1 hz) (thetaK_nn hxi0 hxi1 hz) hb m m
  rw [map_sub, coeff_prod_C_mul_X] at hd
  have hprod : 0 < m.prod fun u k => alphaUnit xi z u ^ k :=
    Finset.prod_pos fun u _ => pow_pos (alphaUnit_pos hxi0 hxi1 hz u) _
  have hge := coeff_subst_ge (thetaK_constantCoeff xi z) (thetaK_nn hxi0 hxi1 hz)
    (RSeries_nn z hz t) m m
  exact lt_of_lt_of_le (mul_pos (RSeries_coeff_pos_all m hm z hz t) (by linarith)) hge

theorem rK_mul_qK_coeff_pos (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T)
    {m : T →₀ ℕ} (hm : m ≠ 0) : 0 < coeff m (rK xi z t * qK xi z t) := by
  have heq : rK xi z t * qK xi z t = rK xi z t + rK xi z t * (qK xi z t - 1) := by ring
  rw [heq, map_add]
  exact add_pos_of_pos_of_nonneg (rK_coeff_pos hxi0 hxi1 hz t hm)
    (nn_mul (rK_nn hxi0 hxi1 hz t) (qK_sub_one_nn hxi0 hxi1 hz t) m)

/-- Every coefficient of `q_t` is strictly positive. -/
theorem qK_coeff_pos (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) (m : T →₀ ℕ) :
    0 < coeff m (qK xi z t) := by
  by_cases hm : m = 0
  · subst hm
    have h := qK_sub_one_nn hxi0 hxi1 hz t 0
    rw [map_sub, coeff_one, if_pos rfl] at h
    linarith
  · rw [qK_expand, map_add, coeff_one, if_neg hm, zero_add, coeff_C_mul]
    exact mul_pos (kappaOf_pos hxi0 hxi1 hz t) (rK_mul_qK_coeff_pos hxi0 hxi1 hz t hm)

/-- `H_t` starts at one. -/
theorem hK_coeff_zero (t : T) : coeff 0 (hK xi z t) = 1 := by
  have hθ0 : ∀ u, PowerSeries.constantCoeff (res 0 (thetaK xi z u)) = 0 := fun u =>
    constantCoeff_subst_eq_zero (ray_hasSubst 0) (ray_constantCoeff 0)
      (thetaK_constantCoeff xi z u)
  have hsys := eqH_of_path_system
    (HSeries_subst_path_system (fun s u => (z s + z u)⁻¹) _ hθ0) t
  have hH : PowerSeries.constantCoeff (MvPowerSeries.subst (fun u => res 0 (thetaK xi z u))
      (HSeries (fun s u => (z s + z u)⁻¹) t)) = 1 := by
    have h := congrArg PowerSeries.constantCoeff hsys
    simpa [map_sum, hθ0] using h
  have hHe : res 0 (hK xi z t) = MvPowerSeries.subst (fun u => res 0 (thetaK xi z u))
      (HSeries (fun s u => (z s + z u)⁻¹) t) := res_H xi z 0 t
  rw [← hHe, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_res] at hH
  simpa [Finset.finsuppAntidiag_zero] using hH

/-- Every coefficient of `H_t q_t` is strictly positive. -/
theorem hK_mul_qK_coeff_pos (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T)
    (m : T →₀ ℕ) : 0 < coeff m (hK xi z t * qK xi z t) := by
  rw [coeff_mul]
  have hmem : ((0, m) : (T →₀ ℕ) × (T →₀ ℕ)) ∈ Finset.antidiagonal m := by simp
  have hle := Finset.single_le_sum (f := fun p : (T →₀ ℕ) × (T →₀ ℕ) =>
    coeff p.1 (hK xi z t) * coeff p.2 (qK xi z t))
    (fun p _ => mul_nonneg (hK_nn hxi0 hxi1 hz t p.1) (qK_nn hxi0 hxi1 hz t p.2)) hmem
  refine lt_of_lt_of_le ?_ hle
  simpa [hK_coeff_zero] using qK_coeff_pos hxi0 hxi1 hz t m

/-- A coefficient of `D_t` at a monomial containing `K_t` is strictly positive. -/
theorem dK_coeff_pos (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) {m : T →₀ ℕ}
    (hm : m t ≠ 0) : 0 < coeff m (dK xi z t) := by
  have hF0 : 0 < F0 xi (z t) := lt_trans one_pos (actual_F0_gt_one xi (z t) hxi0 hxi1 (hz t))
  have hle : Finsupp.single t 1 ≤ m := by
    rw [Finsupp.single_le_iff]
    omega
  obtain ⟨m', rfl⟩ : ∃ m', m = Finsupp.single t 1 + m' :=
    ⟨m - Finsupp.single t 1, (add_tsub_cancel_of_le hle).symm⟩
  unfold dK
  rw [coeff_C_mul, X_def, coeff_add_monomial_mul, one_mul]
  exact mul_pos (mul_pos (div_pos hF0 (rhoOf_pos hxi0)) (alphaUnit_pos hxi0 hxi1 hz t))
    (hK_mul_qK_coeff_pos hxi0 hxi1 hz t m')

/-- A coefficient of `G_t` at a nonconstant monomial is strictly positive. -/
theorem gK_coeff_pos (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ t, 0 < z t) (t : T) {m : T →₀ ℕ}
    (hm : m ≠ 0) : 0 < coeff m (gK xi z t) := by
  have hF0 : 0 < F0 xi (z t) := lt_trans one_pos (actual_F0_gt_one xi (z t) hxi0 hxi1 (hz t))
  have hρ := rhoOf_pos hxi0
  unfold gK
  rw [map_add, coeff_C, if_neg hm, zero_add, coeff_C_mul]
  exact mul_pos (inv_pos.mpr (by positivity)) (rK_mul_qK_coeff_pos hxi0 hxi1 hz t hm)

/-- **Exact sign of every mixed coefficient.** The Taylor series of the hard-sphere root in the tail
strengths has a strictly positive coefficient at every monomial, apart from the constant term of
`G_t` and the monomials of `D_t` without `K_t`, which vanish. -/
theorem mixed_coefficients_exact (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1) (z : T → ℝ)
    (hz : ∀ t, 0 < z t) :
    ∃ (Φ : (T → ℝ) → Pairs T) (P : FormalMultilinearSeries ℝ (T → ℝ) (Pairs T)),
      Φ 0 = ((fun _ => 0), fun u => G0 xi (z u)) ∧ HasFPowerSeriesAt Φ P 0 ∧
      (∀ᶠ K : T → ℝ in 𝓝 0, MultiTail.IsRoot xi z K (Φ K).1 (Φ K).2) ∧
      (∀ t (m : T →₀ ℕ), m t = 0 → coeff m (dK xi z t) = 0) ∧
      (∀ t (m : T →₀ ℕ), m t ≠ 0 → 0 < coeff m (dK xi z t)) ∧
      (∀ t (m : T →₀ ℕ), m ≠ 0 → 0 < coeff m (gK xi z t)) ∧
      ∀ (K : T → ℝ) (n : ℕ) (t : T),
        (P n fun _ => K).1 t = (∑ m ∈ Finset.univ.finsuppAntidiag n,
          coeff m (dK xi z t) * m.prod fun u k => K u ^ k) ∧
        (P n fun _ => K).2 t = ∑ m ∈ Finset.univ.finsuppAntidiag n,
          coeff m (gK xi z t) * m.prod fun u k => K u ^ k := by
  obtain ⟨Φ, P, h0, hP, hr, -, hd, -, hsum⟩ := mixed_coefficients_nonneg xi hxi0 hxi1 z hz
  exact ⟨Φ, P, h0, hP, hr, hd, fun t m hm => dK_coeff_pos hxi0 hxi1 hz t hm,
    fun t m hm => gK_coeff_pos hxi0 hxi1 hz t hm, hsum⟩


end FMSA.Convergence.PureFluidMixedStrict

/-- info: 'FMSA.Convergence.PureFluidMixedStrict.nn_sub_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.nn_sub_mul
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.nn_sub_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.nn_sub_pow
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.nn_sub_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.nn_sub_prod
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.coeff_prod_C_mul_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.coeff_prod_C_mul_X
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.coeff_subst_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.coeff_subst_ge
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.qK_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.qK_expand
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.qK_sub_one_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.qK_sub_one_nn
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.thetaK_sub_leading_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.thetaK_sub_leading_nn
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.rK_coeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.rK_coeff_pos
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.rK_mul_qK_coeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.rK_mul_qK_coeff_pos
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.qK_coeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.qK_coeff_pos
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.hK_coeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.hK_coeff_zero
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.hK_mul_qK_coeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.hK_mul_qK_coeff_pos
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.dK_coeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.dK_coeff_pos
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.gK_coeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.gK_coeff_pos
/-- info: 'FMSA.Convergence.PureFluidMixedStrict.mixed_coefficients_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedStrict.mixed_coefficients_exact
