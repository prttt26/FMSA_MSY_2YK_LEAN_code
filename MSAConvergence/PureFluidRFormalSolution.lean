import MSAConvergence.PureFluidHFormalSolution

set_option linter.style.header false

/-! Construct the independent multivariate pure-fluid r-node formal
series after the finite H-node formal solution is fixed. -/
noncomputable section
open MvPowerSeries Finsupp
namespace FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidHFormalSolution
variable {T : Type*} [Fintype T] [DecidableEq T]

def physicalH (z : T → ℝ) (s : T) : MvPowerSeries T ℝ :=
  HSeries (fun s t => (z s + z t)⁻¹) s

def RNodeSystem (z : T → ℝ) (R : T → MvPowerSeries T ℝ) : Prop :=
  ∀ s, R s = ∑ t, MvPowerSeries.C ((z s + z t)⁻¹) *
    (MvPowerSeries.X t *
      ((physicalH z s * physicalH z t) *
        (MvPowerSeries.C (z t) - R t)))

/-- Coefficients of the finite r system are determined recursively by
lower total degree, because every term contains one theta variable. -/
noncomputable def rCoeff (z : T → ℝ) (m : T →₀ ℕ) (s : T) : ℝ :=
  if m = 0 then 0 else
    ∑ t, (z s + z t)⁻¹ *
      (if hle : Finsupp.single t 1 ≤ m then
        ∑ p ∈ (Finset.antidiagonal (m - Finsupp.single t 1)).attach,
          MvPowerSeries.coeff p.1.1
            (physicalH z s * physicalH z t) *
            ((if p.1.2 = 0 then z t else 0) - rCoeff z p.1.2 t)
      else 0)
termination_by m.degree
decreasing_by
  exact (antidiagonal_degree_lt_of_single_le m t hle p.1 p.2).2

def RSeries (z : T → ℝ) (s : T) : MvPowerSeries T ℝ :=
  fun m => rCoeff z m s

/-- The total-degree recursion satisfies the finite multivariate
theta/H/r node equation. -/
theorem RSeries_system (z : T → ℝ) : RNodeSystem z (RSeries z) := by
  classical
  intro s
  ext m
  change rCoeff z m s = MvPowerSeries.coeff m
    (∑ t, MvPowerSeries.C ((z s + z t)⁻¹) *
      (MvPowerSeries.X t *
        ((physicalH z s * physicalH z t) *
          (MvPowerSeries.C (z t) - RSeries z t))))
  rw [rCoeff.eq_1]
  simp only [map_sum, MvPowerSeries.coeff_C_mul]
  simp_rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases hm : m = 0
  · subst m
    simp
  · simp only [if_neg hm]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs with hle
    · congr 1
      have hRcoeff (d : T →₀ ℕ) :
          MvPowerSeries.coeff d (RSeries z t) = rCoeff z d t := rfl
      conv_rhs => rw [MvPowerSeries.coeff_mul]
      simp only [map_sub, MvPowerSeries.coeff_C, one_mul]
      simp_rw [hRcoeff]
      exact Finset.sum_attach (Finset.antidiagonal (m - Finsupp.single t 1))
        (fun p => MvPowerSeries.coeff p.1
          (physicalH z s * physicalH z t) *
          ((if p.2 = 0 then z t else 0) - rCoeff z p.2 t))
    · rfl

/-- The coefficient of an X-weighted r term uses only r coefficients of
strictly smaller total degree. -/
theorem coeff_X_mul_R_eq_of_lower_degree
    (z : T → ℝ) (R Q : T → MvPowerSeries T ℝ)
    (s t : T) (m : T →₀ ℕ)
    (hprev : ∀ u d, d.degree < m.degree →
      MvPowerSeries.coeff d (R u) = MvPowerSeries.coeff d (Q u)) :
    MvPowerSeries.coeff m
      (MvPowerSeries.X t *
        ((physicalH z s * physicalH z t) *
          (MvPowerSeries.C (z t) - R t))) =
    MvPowerSeries.coeff m
      (MvPowerSeries.X t *
        ((physicalH z s * physicalH z t) *
          (MvPowerSeries.C (z t) - Q t))) := by
  classical
  simp only [MvPowerSeries.X_def]
  rw [MvPowerSeries.coeff_monomial_mul,
    MvPowerSeries.coeff_monomial_mul]
  split_ifs with hle
  · simp only [one_mul, MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hpr := (antidiagonal_degree_lt_of_single_le m t hle p hp).2
    simp only [map_sub]
    rw [hprev t p.2 hpr]
  · rfl

/-- The finite multivariate theta/H/r node system has at most one
solution after the H series is fixed. -/
theorem RNodeSystem_unique (z : T → ℝ)
    (R Q : T → MvPowerSeries T ℝ)
    (hR : RNodeSystem z R) (hQ : RNodeSystem z Q) : R = Q := by
  classical
  have hmain : ∀ n : ℕ, ∀ m : T →₀ ℕ, m.degree = n →
      ∀ s, MvPowerSeries.coeff m (R s) =
        MvPowerSeries.coeff m (Q s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm s
      have hprev : ∀ u d, d.degree < m.degree →
          MvPowerSeries.coeff d (R u) =
            MvPowerSeries.coeff d (Q u) := by
        intro u d hd
        exact ih d.degree (by omega) d rfl u
      rw [hR s, hQ s]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro t _
      simp only [MvPowerSeries.coeff_C_mul]
      exact congrArg (fun q : ℝ => (z s + z t)⁻¹ * q)
        (coeff_X_mul_R_eq_of_lower_degree z R Q s t m hprev)
  funext s
  ext m
  exact hmain m.degree m rfl s

/-- The recursive coefficients construct the unique multivariate
formal r-node solution. -/
theorem RSeries_unique (z : T → ℝ) :
    ∃! R : T → MvPowerSeries T ℝ, RNodeSystem z R := by
  exact ⟨RSeries z, RSeries_system z,
    fun Q hQ => RNodeSystem_unique z Q (RSeries z) hQ (RSeries_system z)⟩

end FMSA.Convergence.PureFluidRFormalSolution

/-- info: 'FMSA.Convergence.PureFluidRFormalSolution.RSeries_system' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalSolution.RSeries_system
/-- info: 'FMSA.Convergence.PureFluidRFormalSolution.coeff_X_mul_R_eq_of_lower_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalSolution.coeff_X_mul_R_eq_of_lower_degree
/-- info: 'FMSA.Convergence.PureFluidRFormalSolution.RNodeSystem_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalSolution.RNodeSystem_unique
/-- info: 'FMSA.Convergence.PureFluidRFormalSolution.RSeries_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRFormalSolution.RSeries_unique
