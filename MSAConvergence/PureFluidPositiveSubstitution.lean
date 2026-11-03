import MSAConvergence.PureFluidThetaCouplingTaylor
import Mathlib.RingTheory.MvPowerSeries.Substitution

set_option linter.style.header false

/-! Coefficientwise nonnegativity through finite multivariate
substitution into one-variable power series. -/
noncomputable section
open MvPowerSeries Filter Topology
namespace FMSA.Convergence.PureFluidPositiveSubstitution
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidRLabelSubstitution
open FMSA.Convergence.PureFluidRPathFormalSubstitution
open FMSA.Convergence.PureFluidThetaCouplingTaylor
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.PureFluidHActualNodeBridge
open FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.PureFluidActualAnalyticGerm
open FMSA.Convergence.PureFluidRActualNodeBridge
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries
open FMSA.ExactMSA

/-- Coefficientwise order on real one-variable formal series. -/
def CoeffNonneg (f : PowerSeries ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤ PowerSeries.coeff n f

/-- Products preserve coefficientwise nonnegativity. -/
theorem coeffNonneg_mul (f g : PowerSeries ℝ)
    (hf : CoeffNonneg f) (hg : CoeffNonneg g) :
    CoeffNonneg (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (hf p.1) (hg p.2)

/-- A nonnegative series multiplied by a constant source. -/
theorem coeffNonneg_C_mul (c : ℝ) (hc : 0 ≤ c)
    (f : PowerSeries ℝ) (hf : CoeffNonneg f) :
    CoeffNonneg (PowerSeries.C c * f) := by
  intro n
  rw [PowerSeries.coeff_C_mul]
  exact mul_nonneg hc (hf n)

/-- The one-variable generator has nonnegative coefficients. -/
theorem coeffNonneg_X : CoeffNonneg (PowerSeries.X : PowerSeries ℝ) := by
  intro n
  simp only [PowerSeries.coeff_X]
  split_ifs <;> norm_num

/-- Nonnegative powers preserve coefficientwise nonnegativity. -/
theorem coeffNonneg_pow (f : PowerSeries ℝ)
    (hf : CoeffNonneg f) (k : ℕ) :
    CoeffNonneg (f ^ k) := by
  induction k with
  | zero =>
    intro n
    simp only [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ]
    exact coeffNonneg_mul _ _ ih hf

/-- The geometric inverse of a zero-seeded nonnegative series
has nonnegative coefficients. -/
theorem coeffNonneg_geometric (g : PowerSeries ℝ)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hg : CoeffNonneg g) :
    CoeffNonneg (1 - g)⁻¹ := by
  let q : PowerSeries ℝ := (1 - g)⁻¹
  have hconst : PowerSeries.constantCoeff (1 - g) ≠ 0 := by
    simp [hg0]
  have hmul : (1 - g) * q = 1 :=
    PowerSeries.mul_inv_cancel (1 - g) hconst
  have hfix : q = 1 + g * q := by
    linear_combination hmul
  have hmain : ∀ n : ℕ, 0 ≤ PowerSeries.coeff n q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rw [hfix, map_add]
      apply add_nonneg
      · rw [PowerSeries.coeff_one]
        split_ifs <;> norm_num
      · rw [PowerSeries.coeff_mul]
        apply Finset.sum_nonneg
        intro p hp
        have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
        by_cases hp0 : p.1 = 0
        · simp [hp0, PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0]
        · exact mul_nonneg (hg p.1) (ih p.2 (by omega))
  exact hmain

/-- The inverse-square dressing factor is coefficientwise
nonnegative whenever its zero-seeded input is. -/
theorem coeffNonneg_inverse_square (g : PowerSeries ℝ)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hg : CoeffNonneg g) :
    CoeffNonneg ((1 - g)⁻¹ ^ 2) :=
  coeffNonneg_pow _ (coeffNonneg_geometric g hg0 hg) 2

/-- A finite product of coefficientwise nonnegative series is
coefficientwise nonnegative. -/
theorem coeffNonneg_prod {T : Type*} (s : Finset T)
    (f : T → PowerSeries ℝ) (hf : ∀ t ∈ s, CoeffNonneg (f t)) :
    CoeffNonneg (∏ t ∈ s, f t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n
    simp only [Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs <;> norm_num
  | @insert t s ht ih =>
    simp only [Finset.prod_insert ht]
    apply coeffNonneg_mul
    · exact hf t (Finset.mem_insert_self _ _)
    · apply ih
      intro u hu
      exact hf u (Finset.mem_insert_of_mem hu)

/-- The monomial product in the substitution formula has
nonnegative coefficients. -/
theorem coeffNonneg_finsupp_prod {T : Type*}
    (a : T → PowerSeries ℝ) (ha : ∀ t, CoeffNonneg (a t))
    (m : T →₀ ℕ) :
    CoeffNonneg (m.prod fun t k => (a t) ^ k) := by
  classical
  change CoeffNonneg (∏ t ∈ m.support, (a t) ^ m t)
  apply coeffNonneg_prod
  intro t _
  exact coeffNonneg_pow (a t) (ha t) (m t)

/-- Substitution preserves coefficientwise nonnegativity when
all substituted series start at zero. -/
theorem coeffNonneg_subst {T : Type*} [Finite T]
    (a : T → PowerSeries ℝ)
    (ha0 : ∀ t, PowerSeries.constantCoeff (a t) = 0)
    (ha : ∀ t, CoeffNonneg (a t))
    (f : MvPowerSeries T ℝ)
    (hf : ∀ m : T →₀ ℕ, 0 ≤ MvPowerSeries.coeff m f) :
    CoeffNonneg (MvPowerSeries.subst a f) := by
  let hs : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  intro n
  change 0 ≤ MvPowerSeries.coeff (Finsupp.single () n)
    (MvPowerSeries.subst a f)
  rw [MvPowerSeries.coeff_subst hs]
  apply finsum_nonneg
  intro m
  simpa only [smul_eq_mul, PowerSeries.coeff] using
    mul_nonneg (hf m) (coeffNonneg_finsupp_prod a ha m n)

/-- The actual formal r-node solution preserves coefficientwise
nonnegativity under any zero-seeded nonnegative theta path. This
includes repeated indices and coincident positive tail rates. -/
theorem RSeries_subst_coeffNonneg {T : Type*}
    [Fintype T] [DecidableEq T]
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (theta : T → PowerSeries ℝ)
    (hzero : ∀ t, PowerSeries.constantCoeff (theta t) = 0)
    (htheta : ∀ t, CoeffNonneg (theta t)) (s : T) :
    CoeffNonneg (MvPowerSeries.subst theta (RSeries z s)) := by
  apply coeffNonneg_subst theta hzero htheta
  intro m
  by_cases hm : m = 0
  · subst m
    change 0 ≤ rCoeff z 0 s
    simp [rCoeff]
  · exact le_of_lt (RSeries_coeff_pos_all m hm z hz s)

/-- The substituted r-node path starts at zero for every zero-seeded
theta path. -/
theorem RSeries_subst_constantCoeff_zero {T : Type*}
    [Fintype T] [DecidableEq T]
    (z : T → ℝ) (theta : T → PowerSeries ℝ)
    (hzero : ∀ t, PowerSeries.constantCoeff (theta t) = 0) (s : T) :
    PowerSeries.constantCoeff
      (MvPowerSeries.subst theta (RSeries z s)) = 0 := by
  have hsys := RSeries_subst_path_system z theta hzero s
  have h := congrArg PowerSeries.constantCoeff hsys
  simpa [map_sum, map_mul, hzero] using h

/-- A positive theta source and a coefficientwise nonnegative r path
give a coefficientwise nonnegative Picard update. -/
theorem thetaPicard_coeffNonneg {T : Type*}
    (alpha kappa : T → ℝ) (theta R : T → PowerSeries ℝ)
    (halpha : ∀ t, 0 ≤ alpha t) (hkappa : ∀ t, 0 ≤ kappa t)
    (hR0 : ∀ t, PowerSeries.constantCoeff (R t) = 0)
    (hR : ∀ t, CoeffNonneg (R t))
    (hfix : ∀ t, theta t =
      PowerSeries.C (alpha t) * PowerSeries.X *
        (1 - PowerSeries.C (kappa t) * R t)⁻¹ ^ 2) :
    ∀ t, CoeffNonneg (theta t) := by
  intro t
  rw [hfix t]
  apply coeffNonneg_mul
  · exact coeffNonneg_C_mul (alpha t) (halpha t)
      PowerSeries.X coeffNonneg_X
  · apply coeffNonneg_inverse_square
    · simp [hR0 t]
    · exact coeffNonneg_C_mul (kappa t) (hkappa t) (R t) (hR t)

/-- Nonnegativity of coefficients strictly below a cutoff. -/
def CoeffNonnegBelow (N : ℕ) (f : PowerSeries ℝ) : Prop :=
  ∀ n < N, 0 ≤ PowerSeries.coeff n f

theorem coeffNonnegBelow_mul (N : ℕ) (f g : PowerSeries ℝ)
    (hf : CoeffNonnegBelow N f) (hg : CoeffNonnegBelow N g) :
    CoeffNonnegBelow N (f * g) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_nonneg
  intro p hp
  have hsum := Finset.mem_antidiagonal.mp hp
  exact mul_nonneg (hf p.1 (by omega)) (hg p.2 (by omega))

theorem coeffNonnegBelow_pow (N : ℕ) (f : PowerSeries ℝ)
    (hf : CoeffNonnegBelow N f) (k : ℕ) :
    CoeffNonnegBelow N (f ^ k) := by
  induction k with
  | zero =>
    intro n hn
    simp only [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ]
    exact coeffNonnegBelow_mul N _ _ ih hf

theorem coeffNonnegBelow_prod {T : Type*}
    (N : ℕ) (s : Finset T) (f : T → PowerSeries ℝ)
    (hf : ∀ t ∈ s, CoeffNonnegBelow N (f t)) :
    CoeffNonnegBelow N (∏ t ∈ s, f t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n hn
    simp only [Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs <;> norm_num
  | @insert t s ht ih =>
    simp only [Finset.prod_insert ht]
    apply coeffNonnegBelow_mul
    · exact hf t (Finset.mem_insert_self _ _)
    · apply ih
      intro u hu
      exact hf u (Finset.mem_insert_of_mem hu)

theorem coeffNonnegBelow_finsupp_prod {T : Type*}
    (N : ℕ) (a : T → PowerSeries ℝ)
    (ha : ∀ t, CoeffNonnegBelow N (a t)) (m : T →₀ ℕ) :
    CoeffNonnegBelow N (m.prod fun t k => (a t) ^ k) := by
  classical
  change CoeffNonnegBelow N (∏ t ∈ m.support, (a t) ^ m t)
  apply coeffNonnegBelow_prod
  intro t _
  exact coeffNonnegBelow_pow N (a t) (ha t) (m t)

theorem coeffNonnegBelow_subst {T : Type*} [Finite T]
    (N : ℕ) (a : T → PowerSeries ℝ)
    (ha0 : ∀ t, PowerSeries.constantCoeff (a t) = 0)
    (ha : ∀ t, CoeffNonnegBelow N (a t))
    (f : MvPowerSeries T ℝ)
    (hf : ∀ m : T →₀ ℕ, 0 ≤ MvPowerSeries.coeff m f) :
    CoeffNonnegBelow N (MvPowerSeries.subst a f) := by
  let hs : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  intro n hn
  change 0 ≤ MvPowerSeries.coeff (Finsupp.single () n)
    (MvPowerSeries.subst a f)
  rw [MvPowerSeries.coeff_subst hs]
  apply finsum_nonneg
  intro m
  simpa only [smul_eq_mul, PowerSeries.coeff] using
    mul_nonneg (hf m) (coeffNonnegBelow_finsupp_prod N a ha m n hn)

theorem coeffNonnegBelow_geometric (N : ℕ) (g : PowerSeries ℝ)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hg : CoeffNonnegBelow N g) :
    CoeffNonnegBelow N (1 - g)⁻¹ := by
  let q : PowerSeries ℝ := (1 - g)⁻¹
  have hconst : PowerSeries.constantCoeff (1 - g) ≠ 0 := by
    simp [hg0]
  have hmul : (1 - g) * q = 1 :=
    PowerSeries.mul_inv_cancel (1 - g) hconst
  have hfix : q = 1 + g * q := by
    linear_combination hmul
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    change 0 ≤ PowerSeries.coeff n q
    rw [hfix, map_add]
    apply add_nonneg
    · rw [PowerSeries.coeff_one]
      split_ifs <;> norm_num
    · rw [PowerSeries.coeff_mul]
      apply Finset.sum_nonneg
      intro p hp
      have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
      by_cases hp0 : p.1 = 0
      · simp [hp0, PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0]
      · exact mul_nonneg (hg p.1 (by omega)) (ih p.2 (by omega) (by omega))

/-- The zero-seeded physical Picard fixed point has nonnegative
one-variable Taylor coefficients. The proof is a simultaneous strong
induction over all tail labels: the explicit X factor makes degree n
depend only on theta coefficients below n. -/
theorem theta_fixed_point_coeffNonneg {T : Type*}
    [Fintype T] [DecidableEq T]
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (alpha kappa : T → ℝ)
    (halpha : ∀ t, 0 ≤ alpha t)
    (hkappa : ∀ t, 0 ≤ kappa t)
    (theta : T → PowerSeries ℝ)
    (hzero : ∀ t, PowerSeries.constantCoeff (theta t) = 0)
    (hfix : ∀ t, theta t =
      PowerSeries.C (alpha t) * PowerSeries.X *
        (1 - PowerSeries.C (kappa t) *
          MvPowerSeries.subst theta (RSeries z t))⁻¹ ^ 2) :
    ∀ t, CoeffNonneg (theta t) := by
  have hmain : ∀ n : ℕ, ∀ t : T,
      0 ≤ PowerSeries.coeff n (theta t) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hthetaBelow : ∀ t, CoeffNonnegBelow n (theta t) := by
        intro t k hk
        exact ih k hk t
      have hRBelow (t : T) : CoeffNonnegBelow n
          (MvPowerSeries.subst theta (RSeries z t)) := by
        apply coeffNonnegBelow_subst n theta hzero hthetaBelow
        intro m
        by_cases hm : m = 0
        · subst m
          change 0 ≤ rCoeff z 0 t
          simp [rCoeff]
        · exact le_of_lt (RSeries_coeff_pos_all m hm z hz t)
      have hqBelow (t : T) : CoeffNonnegBelow n
          (1 - PowerSeries.C (kappa t) *
            MvPowerSeries.subst theta (RSeries z t))⁻¹ := by
        apply coeffNonnegBelow_geometric n
        · simp [RSeries_subst_constantCoeff_zero z theta hzero t]
        · intro k hk
          rw [PowerSeries.coeff_C_mul]
          exact mul_nonneg (hkappa t) (hRBelow t k hk)
      intro t
      rw [hfix t, mul_assoc, PowerSeries.coeff_C_mul]
      by_cases hn : n = 0
      · subst n
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        have hsq : CoeffNonnegBelow (k + 1)
            ((1 - PowerSeries.C (kappa t) *
              MvPowerSeries.subst theta (RSeries z t))⁻¹ ^ 2) := by
          simpa only [pow_two] using coeffNonnegBelow_mul (k + 1)
            _ _ (hqBelow t) (hqBelow t)
        have hX : PowerSeries.coeff (k + 1)
            (PowerSeries.X *
              (1 - PowerSeries.C (kappa t) *
                MvPowerSeries.subst theta (RSeries z t))⁻¹ ^ 2) =
            PowerSeries.coeff k
              ((1 - PowerSeries.C (kappa t) *
                MvPowerSeries.subst theta (RSeries z t))⁻¹ ^ 2) := by
          simpa only [pow_one, Nat.add_comm] using
            PowerSeries.coeff_X_pow_mul
              ((1 - PowerSeries.C (kappa t) *
                MvPowerSeries.subst theta (RSeries z t))⁻¹ ^ 2) 1 k
        rw [hX]
        exact mul_nonneg (halpha t) (hsq k (by omega))
  intro t n
  exact hmain n t

/-- Along the genuine positive-coupling HS-seeded MSA root, the
physical one-variable Taylor series of every actual theta and r
node has nonnegative coefficients. This includes repeated tail
indices and coincident positive rates. -/
theorem exists_actual_hs_root_germ_with_nonnegative_theta_r_taylor
    {T : Type*} [Fintype T]
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t)
    (hK : ∀ t, 0 < K t) :
    ∃ (p : ℝ → (T → ℝ) × (T → ℝ))
      (thetaS RS : T → PowerSeries ℝ),
      p 0 = ((fun _ => 0), fun t => G0 xi (z t)) ∧
      AnalyticAt ℝ p 0 ∧
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualTheta xi z (p tau).1 (p tau).2 t) (thetaS t)) ∧
      (∀ t, HasTaylorPowerSeriesAt
        (fun tau => actualNodeR xi z (p tau).1 (p tau).2 t) (RS t)) ∧
      (∀ t, CoeffNonneg (thetaS t)) ∧
      (∀ t, CoeffNonneg (RS t)) ∧
      (∀ᶠ tau : ℝ in 𝓝 0,
        MultiTail.IsRoot xi z (fun t => tau * K t)
          (p tau).1 (p tau).2) ∧
      (∀ s, ∀ᶠ tau : ℝ in 𝓝 0,
        HasSum (fun n => PowerSeries.coeff n (thetaS s) * tau ^ n)
          (actualTheta xi z (p tau).1 (p tau).2 s)) ∧
      ∀ s, ∀ᶠ tau : ℝ in 𝓝 0,
        HasSum (fun n => PowerSeries.coeff n (RS s) * tau ^ n)
          (actualNodeR xi z (p tau).1 (p tau).2 s) := by
  classical
  obtain ⟨p, thetaS, RS, hp0, hpa, htheta, hRS,
    hRident, _heq, hfixed, hroot, hsum⟩ :=
    exists_actual_hs_root_germ_with_theta_coupling_taylor
      xi hxi0 hxi1 z K hz
  have htheta0 : ∀ t, PowerSeries.constantCoeff (thetaS t) = 0 := by
    intro t
    rw [(htheta t).constantCoeff, hp0]
    exact (actual_hs_seed_nodes xi z
      (fun u => G0 xi (z u)) hxi1.ne hz).1 t
  have halpha : ∀ t, 0 ≤ physicalAlpha xi z K t := by
    intro t
    exact le_of_lt (physicalAlpha_pos xi hxi0 hxi1 z K hz hK t)
  have hkappa : ∀ t, 0 ≤ hardKappa xi (z t) := by
    intro t
    exact le_of_lt (hardKappa_pos xi (z t) hxi0 hxi1 (hz t))
  have hfixed' : ∀ t, thetaS t =
      PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X *
        (1 - PowerSeries.C (hardKappa xi (z t)) *
          MvPowerSeries.subst thetaS (RSeries z t))⁻¹ ^ 2 := by
    intro t
    simpa only [hRident] using hfixed t
  have hthetaPos := theta_fixed_point_coeffNonneg
    z hz (physicalAlpha xi z K)
    (fun t => hardKappa xi (z t)) halpha hkappa
    thetaS htheta0 hfixed'
  have hRPos : ∀ t, CoeffNonneg (RS t) := by
    intro t
    rw [hRident]
    exact RSeries_subst_coeffNonneg z hz thetaS htheta0 hthetaPos t
  exact ⟨p, thetaS, RS, hp0, hpa, htheta, hRS,
    hthetaPos, hRPos, hroot,
    (fun s => (htheta s).eventually_hasSum), hsum⟩

end FMSA.Convergence.PureFluidPositiveSubstitution

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_mul

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_C_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_C_mul

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_X' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_X

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_pow

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_geometric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_geometric

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_inverse_square' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_inverse_square

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_prod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_prod

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_finsupp_prod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_finsupp_prod

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_subst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonneg_subst

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.RSeries_subst_coeffNonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.RSeries_subst_coeffNonneg

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.RSeries_subst_constantCoeff_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.RSeries_subst_constantCoeff_zero

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.thetaPicard_coeffNonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.thetaPicard_coeffNonneg

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_mul

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_pow

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_prod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_prod

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_finsupp_prod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_finsupp_prod

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_subst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_subst

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_geometric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.coeffNonnegBelow_geometric

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.theta_fixed_point_coeffNonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.theta_fixed_point_coeffNonneg

/-- info: 'FMSA.Convergence.PureFluidPositiveSubstitution.exists_actual_hs_root_germ_with_nonnegative_theta_r_taylor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidPositiveSubstitution.exists_actual_hs_root_germ_with_nonnegative_theta_r_taylor
