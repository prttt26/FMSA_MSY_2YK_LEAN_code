import MSAConvergence.PureFluidPositiveSubstitution

set_option linter.style.header false

/-! Coefficientwise uniqueness of the zero-seeded physical theta
Picard fixed point. -/
noncomputable section
open MvPowerSeries
namespace FMSA.Convergence.PureFluidThetaFixedPointUniqueness
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidPositiveSubstitution
open FMSA.Convergence.PureFluidThetaCouplingTaylor
open FMSA.Convergence.PureFluidHActualNodeBridge
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.ExactMSA

/-- Equality of one-variable coefficients strictly below a cutoff. -/
def CoeffEqBelow (N : ℕ) (f g : PowerSeries ℝ) : Prop :=
  ∀ n < N, PowerSeries.coeff n f = PowerSeries.coeff n g

theorem coeffEqBelow_mul (N : ℕ) (f g f' g' : PowerSeries ℝ)
    (hf : CoeffEqBelow N f f') (hg : CoeffEqBelow N g g') :
    CoeffEqBelow N (f * g) (f' * g') := by
  intro n hn
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hsum := Finset.mem_antidiagonal.mp hp
  rw [hf p.1 (by omega), hg p.2 (by omega)]

theorem coeffEqBelow_pow (N : ℕ) (f g : PowerSeries ℝ)
    (hfg : CoeffEqBelow N f g) (k : ℕ) :
    CoeffEqBelow N (f ^ k) (g ^ k) := by
  induction k with
  | zero => intro n hn; simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact coeffEqBelow_mul N _ _ _ _ ih hfg

theorem coeffEqBelow_prod {T : Type*} (N : ℕ)
    (s : Finset T) (f g : T → PowerSeries ℝ)
    (hfg : ∀ t ∈ s, CoeffEqBelow N (f t) (g t)) :
    CoeffEqBelow N (∏ t ∈ s, f t) (∏ t ∈ s, g t) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n hn; simp
  | @insert t s ht ih =>
    simp only [Finset.prod_insert ht]
    apply coeffEqBelow_mul
    · exact hfg t (Finset.mem_insert_self _ _)
    · apply ih
      intro u hu
      exact hfg u (Finset.mem_insert_of_mem hu)

theorem coeffEqBelow_finsupp_prod {T : Type*} (N : ℕ)
    (a b : T → PowerSeries ℝ)
    (hab : ∀ t, CoeffEqBelow N (a t) (b t))
    (m : T →₀ ℕ) :
    CoeffEqBelow N
      (m.prod fun t k => (a t) ^ k)
      (m.prod fun t k => (b t) ^ k) := by
  classical
  change CoeffEqBelow N
    (∏ t ∈ m.support, (a t) ^ m t)
    (∏ t ∈ m.support, (b t) ^ m t)
  apply coeffEqBelow_prod
  intro t _
  exact coeffEqBelow_pow N (a t) (b t) (hab t) (m t)

theorem coeffEqBelow_subst {T : Type*} [Finite T] (N : ℕ)
    (a b : T → PowerSeries ℝ)
    (ha0 : ∀ t, PowerSeries.constantCoeff (a t) = 0)
    (hb0 : ∀ t, PowerSeries.constantCoeff (b t) = 0)
    (hab : ∀ t, CoeffEqBelow N (a t) (b t))
    (f : MvPowerSeries T ℝ) :
    CoeffEqBelow N (MvPowerSeries.subst a f)
      (MvPowerSeries.subst b f) := by
  let hsA : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  let hsB : MvPowerSeries.HasSubst b :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
  intro n hn
  change MvPowerSeries.coeff (Finsupp.single () n)
      (MvPowerSeries.subst a f) =
    MvPowerSeries.coeff (Finsupp.single () n)
      (MvPowerSeries.subst b f)
  rw [MvPowerSeries.coeff_subst hsA,
    MvPowerSeries.coeff_subst hsB]
  apply finsum_congr
  intro m
  congr 1
  exact coeffEqBelow_finsupp_prod N a b hab m n hn

/-- Geometric inversion preserves equality through every fixed
finite degree when both inputs start at zero. -/
theorem coeffEqBelow_geometric (N : ℕ) (g g' : PowerSeries ℝ)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hg0' : PowerSeries.constantCoeff g' = 0)
    (hgg' : CoeffEqBelow N g g') :
    CoeffEqBelow N (1 - g)⁻¹ (1 - g')⁻¹ := by
  let q : PowerSeries ℝ := (1 - g)⁻¹
  let q' : PowerSeries ℝ := (1 - g')⁻¹
  have hconst : PowerSeries.constantCoeff (1 - g) ≠ 0 := by
    simp [hg0]
  have hconst' : PowerSeries.constantCoeff (1 - g') ≠ 0 := by
    simp [hg0']
  have hmul : (1 - g) * q = 1 :=
    PowerSeries.mul_inv_cancel (1 - g) hconst
  have hmul' : (1 - g') * q' = 1 :=
    PowerSeries.mul_inv_cancel (1 - g') hconst'
  have hfix : q = 1 + g * q := by
    linear_combination hmul
  have hfix' : q' = 1 + g' * q' := by
    linear_combination hmul'
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    change PowerSeries.coeff n q = PowerSeries.coeff n q'
    rw [hfix, hfix', map_add, map_add]
    congr 1
    simp only [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    by_cases hp0 : p.1 = 0
    · simp [hp0, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        hg0, hg0']
    · rw [hgg' p.1 (by omega), ih p.2 (by omega) (by omega)]

/-- The explicit X factor shifts the coefficient of the dressed
Picard update down by one. -/
theorem coeff_C_X_mul_succ (a : ℝ) (f : PowerSeries ℝ) (k : ℕ) :
    PowerSeries.coeff (k + 1) (PowerSeries.C a * PowerSeries.X * f) =
      a * PowerSeries.coeff k f := by
  rw [mul_assoc, PowerSeries.coeff_C_mul]
  congr 1
  simpa only [pow_one, Nat.add_comm] using
    PowerSeries.coeff_X_pow_mul f 1 k

/-- The zero-seeded formal physical theta Picard equation has at
most one solution. No sign or rate assumptions are needed for this
purely degree-lowering uniqueness statement. -/
theorem theta_fixed_point_unique {T : Type*} [Fintype T] [DecidableEq T]
    (z alpha kappa : T → ℝ)
    (theta theta' : T → PowerSeries ℝ)
    (hzero : ∀ t, PowerSeries.constantCoeff (theta t) = 0)
    (hzero' : ∀ t, PowerSeries.constantCoeff (theta' t) = 0)
    (hfix : ∀ t, theta t =
      PowerSeries.C (alpha t) * PowerSeries.X *
        (1 - PowerSeries.C (kappa t) *
          MvPowerSeries.subst theta (RSeries z t))⁻¹ ^ 2)
    (hfix' : ∀ t, theta' t =
      PowerSeries.C (alpha t) * PowerSeries.X *
        (1 - PowerSeries.C (kappa t) *
          MvPowerSeries.subst theta' (RSeries z t))⁻¹ ^ 2) :
    theta = theta' := by
  classical
  have hcoeff : ∀ n : ℕ, ∀ t : T,
      PowerSeries.coeff n (theta t) =
        PowerSeries.coeff n (theta' t) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hthetaBelow : ∀ t,
          CoeffEqBelow n (theta t) (theta' t) := by
        intro t k hk
        exact ih k hk t
      have hRBelow (t : T) : CoeffEqBelow n
          (MvPowerSeries.subst theta (RSeries z t))
          (MvPowerSeries.subst theta' (RSeries z t)) :=
        coeffEqBelow_subst n theta theta' hzero hzero'
          hthetaBelow (RSeries z t)
      have hqBelow (t : T) : CoeffEqBelow n
          (1 - PowerSeries.C (kappa t) *
            MvPowerSeries.subst theta (RSeries z t))⁻¹
          (1 - PowerSeries.C (kappa t) *
            MvPowerSeries.subst theta' (RSeries z t))⁻¹ := by
        apply coeffEqBelow_geometric n
        · simp [RSeries_subst_constantCoeff_zero z theta hzero t]
        · simp [RSeries_subst_constantCoeff_zero z theta' hzero' t]
        · apply coeffEqBelow_mul
          · intro k hk
            rfl
          · exact hRBelow t
      intro t
      by_cases hn : n = 0
      · subst n
        simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
          hzero t, hzero' t]
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        have hpow : PowerSeries.coeff k
            ((1 - PowerSeries.C (kappa t) *
              MvPowerSeries.subst theta (RSeries z t))⁻¹ ^ 2) =
            PowerSeries.coeff k
              ((1 - PowerSeries.C (kappa t) *
                MvPowerSeries.subst theta' (RSeries z t))⁻¹ ^ 2) :=
          (coeffEqBelow_pow (k + 1)
            (1 - PowerSeries.C (kappa t) *
              MvPowerSeries.subst theta (RSeries z t))⁻¹
            (1 - PowerSeries.C (kappa t) *
              MvPowerSeries.subst theta' (RSeries z t))⁻¹
            (hqBelow t) 2) k (by omega)
        rw [hfix t, hfix' t,
          coeff_C_X_mul_succ, coeff_C_X_mul_succ]
        exact congrArg (fun x : ℝ => alpha t * x) hpow
  funext t
  ext n
  exact hcoeff n t

/-- For physical pure-fluid data, the actual HS-seeded MSA germ
constructs the unique zero-seeded formal theta solution of the
physical-coupling Picard equation. -/
theorem exists_unique_physical_theta_fixed_point
    {T : Type*} [Fintype T] [DecidableEq T]
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t) :
    ∃! theta : T → PowerSeries ℝ,
      (∀ t, PowerSeries.constantCoeff (theta t) = 0) ∧
      ∀ t, theta t =
        PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X *
          (1 - PowerSeries.C (hardKappa xi (z t)) *
            MvPowerSeries.subst theta (RSeries z t))⁻¹ ^ 2 := by
  obtain ⟨p, theta, RS, hp0, _hpa, htheta, _hRS,
    hRident, _heq, hfixed, _hroot, _hsum⟩ :=
    exists_actual_hs_root_germ_with_theta_coupling_taylor
      xi hxi0 hxi1 z K hz
  have hzero : ∀ t, PowerSeries.constantCoeff (theta t) = 0 := by
    intro t
    rw [(htheta t).constantCoeff, hp0]
    exact (actual_hs_seed_nodes xi z
      (fun u => G0 xi (z u)) hxi1.ne hz).1 t
  have hfix : ∀ t, theta t =
      PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X *
        (1 - PowerSeries.C (hardKappa xi (z t)) *
          MvPowerSeries.subst theta (RSeries z t))⁻¹ ^ 2 := by
    intro t
    simpa only [hRident] using hfixed t
  refine ⟨theta, ⟨hzero, hfix⟩, ?_⟩
  intro theta' htheta'
  exact theta_fixed_point_unique z
    (physicalAlpha xi z K) (fun t => hardKappa xi (z t))
    theta' theta htheta'.1 hzero htheta'.2 hfix

end FMSA.Convergence.PureFluidThetaFixedPointUniqueness

/-- info: 'FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_mul

/-- info: 'FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_pow

/-- info: 'FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_prod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_prod

/-- info: 'FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_finsupp_prod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_finsupp_prod

/-- info: 'FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_subst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_subst

/-- info: 'FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_geometric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeffEqBelow_geometric

/-- info: 'FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeff_C_X_mul_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaFixedPointUniqueness.coeff_C_X_mul_succ

/-- info: 'FMSA.Convergence.PureFluidThetaFixedPointUniqueness.theta_fixed_point_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaFixedPointUniqueness.theta_fixed_point_unique

/-- info: 'FMSA.Convergence.PureFluidThetaFixedPointUniqueness.exists_unique_physical_theta_fixed_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidThetaFixedPointUniqueness.exists_unique_physical_theta_fixed_point
