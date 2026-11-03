import MSAConvergence.PureFluidRKernelContinuity
import MSAConvergence.PureFluidHFormalSolution
import MSAConvergence.PureFluidRFormalSolution

set_option linter.style.header false

/-! Continuity in positive tail rates of the finite-degree formal
H, R and off-node r coefficients. -/
noncomputable section
open MvPowerSeries Finsupp Filter Topology
namespace FMSA.Convergence.PureFluidRCoeffRateContinuity
open FMSA.Convergence.PureFluidHFormalSolution
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidRFormalDispersion
variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Every recursively defined H coefficient is continuous in the
finitely many entries of its abstract node kernel. -/
theorem hCoeff_continuous (m : T →₀ ℕ) (s : T) :
    Continuous (fun c : T → T → ℝ => hCoeff c m s) := by
  classical
  have hmain : ∀ n : ℕ, ∀ m : T →₀ ℕ, m.degree = n →
      ∀ s : T, Continuous (fun c : T → T → ℝ => hCoeff c m s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm s
      have hformula : (fun c : T → T → ℝ => hCoeff c m s) =
          (fun c => if m = 0 then 1 else
            ∑ t, c s t *
              (if hle : Finsupp.single t 1 ≤ m then
                ∑ p ∈ (Finset.antidiagonal (m - Finsupp.single t 1)).attach,
                  hCoeff c p.1.1 s * hCoeff c p.1.2 t
              else 0)) := by
        funext c
        rw [hCoeff.eq_1]
      rw [hformula]
      by_cases hm0 : m = 0
      · simp only [if_pos hm0]
        exact continuous_const
      · simp only [if_neg hm0]
        apply continuous_finsetSum
        intro t _
        apply Continuous.mul (continuous_apply_apply s t)
        split_ifs with hle
        · apply continuous_finsetSum
          intro p hp
          obtain ⟨hpl, hpr⟩ :=
            antidiagonal_degree_lt_of_single_le m t hle p.1 p.2
          exact (ih p.1.1.degree (by omega) p.1.1 rfl s).mul
            (ih p.1.2.degree (by omega) p.1.2 rfl t)
        · exact continuous_const
  exact hmain m.degree m rfl s

omit [Fintype T] [DecidableEq T] in
/-- The finite positive-rate kernel matrix depends continuously on
all rates, even at coincident rates. -/
theorem physicalNodeKernel_continuousAt
    (z : T → ℝ) (hz : ∀ t, 0 < z t) :
    ContinuousAt
      (fun z' : T → ℝ => fun s t => (z' s + z' t)⁻¹) z := by
  classical
  apply continuousAt_pi.mpr
  intro s
  apply continuousAt_pi.mpr
  intro t
  have hsum : ContinuousAt (fun z' : T → ℝ => z' s + z' t) z :=
    (continuousAt_apply s z).add (continuousAt_apply t z)
  exact hsum.inv₀ (add_pos (hz s) (hz t)).ne'

/-- Every H-node formal coefficient is continuous in all positive
rates, with no rate-distinctness condition. -/
theorem physicalH_coeff_continuousAt
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (m : T →₀ ℕ) (s : T) :
    ContinuousAt
      (fun z' : T → ℝ => MvPowerSeries.coeff m (physicalH z' s)) z := by
  have hc := physicalNodeKernel_continuousAt z hz
  have hh := (hCoeff_continuous m s).continuousAt.comp hc
  simpa only [Function.comp_def, physicalH, HSeries,
    MvPowerSeries.coeff_apply] using hh

/-- Every finite Cauchy-product coefficient of two physical H series
is continuous in positive rates. -/
theorem physicalH_mul_coeff_continuousAt
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (m : T →₀ ℕ) (s t : T) :
    ContinuousAt
      (fun z' : T → ℝ => MvPowerSeries.coeff m
        (physicalH z' s * physicalH z' t)) z := by
  have hformula : (fun z' : T → ℝ => MvPowerSeries.coeff m
      (physicalH z' s * physicalH z' t)) =
      (fun z' => ∑ p ∈ Finset.antidiagonal m,
        MvPowerSeries.coeff p.1 (physicalH z' s) *
          MvPowerSeries.coeff p.2 (physicalH z' t)) := by
    funext z'
    exact MvPowerSeries.coeff_mul _ _ _
  rw [hformula]
  apply tendsto_finsetSum
  intro p hp
  exact (physicalH_coeff_continuousAt z hz p.1 s).mul
    (physicalH_coeff_continuousAt z hz p.2 t)

/-- Every recursively defined R-node coefficient is continuous in
positive rates, including at rate coincidences. -/
theorem rCoeff_continuousAt
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (m : T →₀ ℕ) (s : T) :
    ContinuousAt (fun z' : T → ℝ => rCoeff z' m s) z := by
  classical
  have hmain : ∀ n : ℕ, ∀ m : T →₀ ℕ, m.degree = n →
      ∀ s : T, ContinuousAt (fun z' : T → ℝ => rCoeff z' m s) z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm s
      have hformula : (fun z' : T → ℝ => rCoeff z' m s) =
          (fun z' => if m = 0 then 0 else
            ∑ t, (z' s + z' t)⁻¹ *
              (if hle : Finsupp.single t 1 ≤ m then
                ∑ p ∈ (Finset.antidiagonal (m - Finsupp.single t 1)).attach,
                  MvPowerSeries.coeff p.1.1
                    (physicalH z' s * physicalH z' t) *
                    ((if p.1.2 = 0 then z' t else 0) - rCoeff z' p.1.2 t)
              else 0)) := by
        funext z'
        rw [rCoeff.eq_1]
      rw [hformula]
      by_cases hm0 : m = 0
      · simp only [if_pos hm0]
        exact continuousAt_const
      · simp only [if_neg hm0]
        apply tendsto_finsetSum
        intro t ht
        have hden : z s + z t ≠ 0 := (add_pos (hz s) (hz t)).ne'
        have hkernel : ContinuousAt
            (fun z' : T → ℝ => (z' s + z' t)⁻¹) z :=
          ((continuousAt_apply s z).add (continuousAt_apply t z)).inv₀ hden
        apply ContinuousAt.mul hkernel
        split_ifs with hle
        · apply tendsto_finsetSum
          intro p hp
          have hdeg :=
            (antidiagonal_degree_lt_of_single_le m t hle p.1 p.2).2
          have hR : ContinuousAt
              (fun z' : T → ℝ => rCoeff z' p.1.2 t) z :=
            ih p.1.2.degree (by omega) p.1.2 rfl t
          have hzt : ContinuousAt
              (fun z' : T → ℝ => if p.1.2 = 0 then z' t else 0) z := by
            split_ifs
            · exact continuousAt_apply t z
            · exact continuousAt_const
          exact (physicalH_mul_coeff_continuousAt z hz p.1.1 s t).mul
            (hzt.sub hR)
        · exact continuousAt_const
  exact hmain m.degree m rfl s

/-- The independently recursive physical R-node formal coefficient
is continuous at every strictly positive rate vector. -/
theorem RSeries_coeff_continuousAt
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (m : T →₀ ℕ) (s : T) :
    ContinuousAt (fun z' : T → ℝ => MvPowerSeries.coeff m (RSeries z' s)) z := by
  simpa only [RSeries, MvPowerSeries.coeff_apply] using
    rCoeff_continuousAt z hz m s

/-- The off-node r coefficient depends on lower-degree r coefficients,
with H and R coefficients already defined by finite recursions. -/
theorem physicalFormalR_coeff_recursion
    (z : T → ℝ) (x : ℝ) (m : T →₀ ℕ) :
    MvPowerSeries.coeff m (physicalFormalR z x) =
      ∑ t, (x + z t)⁻¹ *
        (if Finsupp.single t 1 ≤ m then
          ∑ p ∈ Finset.antidiagonal (m - Finsupp.single t 1),
            MvPowerSeries.coeff p.1 (physicalH z t) *
              ((if p.2 = 0 then z t else 0) -
                MvPowerSeries.coeff p.2 (RSeries z t) +
                MvPowerSeries.coeff p.2 (physicalFormalR z x))
        else 0) := by
  classical
  conv_lhs => rw [physicalFormalR_series_recursion z x]
  simp only [map_sum, MvPowerSeries.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  rw [show MvPowerSeries.X t * physicalH z t *
      (C (z t) - RSeries z t + physicalFormalR z x) =
      MvPowerSeries.X t *
        (physicalH z t * (C (z t) - RSeries z t + physicalFormalR z x)) by ring]
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  split_ifs with hle
  · rw [one_mul, MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [map_add, map_sub, MvPowerSeries.coeff_C]
  · rfl

/-- Every off-node formal r coefficient is continuous in the positive
rate vector at fixed positive evaluation frequency, even when rates
coincide. -/
theorem physicalFormalR_coeff_continuousAt_rate
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (x : ℝ) (hx : 0 < x) (m : T →₀ ℕ) :
    ContinuousAt
      (fun z' : T → ℝ => MvPowerSeries.coeff m (physicalFormalR z' x)) z := by
  classical
  have hmain : ∀ n : ℕ, ∀ m : T →₀ ℕ, m.degree = n →
      ContinuousAt
        (fun z' : T → ℝ => MvPowerSeries.coeff m (physicalFormalR z' x)) z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm
      have hformula : (fun z' : T → ℝ =>
          MvPowerSeries.coeff m (physicalFormalR z' x)) =
          (fun z' => ∑ t, (x + z' t)⁻¹ *
            (if Finsupp.single t 1 ≤ m then
              ∑ p ∈ Finset.antidiagonal (m - Finsupp.single t 1),
                MvPowerSeries.coeff p.1 (physicalH z' t) *
                  ((if p.2 = 0 then z' t else 0) -
                    MvPowerSeries.coeff p.2 (RSeries z' t) +
                    MvPowerSeries.coeff p.2 (physicalFormalR z' x))
            else 0)) := by
        funext z'
        exact physicalFormalR_coeff_recursion z' x m
      rw [hformula]
      apply tendsto_finsetSum
      intro t ht
      have hden : x + z t ≠ 0 := (add_pos hx (hz t)).ne'
      have hkernel : ContinuousAt
          (fun z' : T → ℝ => (x + z' t)⁻¹) z :=
        (continuousAt_const.add (continuousAt_apply t z)).inv₀ hden
      apply ContinuousAt.mul hkernel
      split_ifs with hle
      · apply tendsto_finsetSum
        intro p hp
        have hdeg :=
          (antidiagonal_degree_lt_of_single_le m t hle p hp).2
        have hr : ContinuousAt
            (fun z' : T → ℝ => MvPowerSeries.coeff p.2
              (physicalFormalR z' x)) z :=
          ih p.2.degree (by omega) p.2 rfl
        have hzt : ContinuousAt
            (fun z' : T → ℝ => if p.2 = 0 then z' t else 0) z := by
          split_ifs
          · exact continuousAt_apply t z
          · exact continuousAt_const
        exact (physicalH_coeff_continuousAt z hz p.1 t).mul
          ((hzt.sub (RSeries_coeff_continuousAt z hz p.2 t)).add hr)
      · exact continuousAt_const
  exact hmain m.degree m rfl

end FMSA.Convergence.PureFluidRCoeffRateContinuity

/-- info: 'FMSA.Convergence.PureFluidRCoeffRateContinuity.hCoeff_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRCoeffRateContinuity.hCoeff_continuous
/-- info: 'FMSA.Convergence.PureFluidRCoeffRateContinuity.physicalNodeKernel_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRCoeffRateContinuity.physicalNodeKernel_continuousAt
/-- info: 'FMSA.Convergence.PureFluidRCoeffRateContinuity.physicalH_coeff_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRCoeffRateContinuity.physicalH_coeff_continuousAt
/-- info: 'FMSA.Convergence.PureFluidRCoeffRateContinuity.physicalH_mul_coeff_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRCoeffRateContinuity.physicalH_mul_coeff_continuousAt
/-- info: 'FMSA.Convergence.PureFluidRCoeffRateContinuity.rCoeff_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRCoeffRateContinuity.rCoeff_continuousAt
/-- info: 'FMSA.Convergence.PureFluidRCoeffRateContinuity.RSeries_coeff_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRCoeffRateContinuity.RSeries_coeff_continuousAt
/-- info: 'FMSA.Convergence.PureFluidRCoeffRateContinuity.physicalFormalR_coeff_recursion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRCoeffRateContinuity.physicalFormalR_coeff_recursion
/-- info: 'FMSA.Convergence.PureFluidRCoeffRateContinuity.physicalFormalR_coeff_continuousAt_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRCoeffRateContinuity.physicalFormalR_coeff_continuousAt_rate
