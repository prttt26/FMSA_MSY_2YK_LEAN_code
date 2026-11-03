import MSAConvergence.PureFluidRFormalSolution

set_option linter.style.header false

/-! Identify the linear coefficients of the independent multivariate
pure-fluid r series with the singleton rational weight. -/
noncomputable section
open MvPowerSeries Finsupp
namespace FMSA.Convergence.PureFluidRLowOrder
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidHFormalSolution
variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The first independent theta coefficient follows directly from the
finite r-node recurrence and the unit H constant terms. -/
theorem rCoeff_single (z : T → ℝ) (s t : T) :
    rCoeff z (Finsupp.single t 1) s = (z s + z t)⁻¹ * z t := by
  classical
  rw [rCoeff.eq_1]
  have hsingle (u : T) :
      (Finsupp.single u 1 ≤ Finsupp.single t 1) ↔ t = u := by
    by_cases h : u = t
    · subst u; simp
    · simp [Finsupp.single_le_iff, h, Ne.symm h]
  simp_rw [hsingle]
  have hnonzero : Finsupp.single t 1 ≠ (0 : T →₀ ℕ) := by simp
  have hH0 (u : T) : MvPowerSeries.coeff 0 (physicalH z u) = 1 := by
    change hCoeff (fun a b => (z a + z b)⁻¹) 0 u = 1
    rw [hCoeff.eq_1]
    simp
  have hr0 : rCoeff z 0 t = 0 := by
    rw [rCoeff.eq_1]
    simp
  have hsub : Finsupp.single t 1 - Finsupp.single t 1 = (0 : T →₀ ℕ) := by
    ext u
    simp
  simp only [if_neg hnonzero]
  rw [Finset.sum_eq_single t]
  · rw [hsub]
    congr 1
    split_ifs with ht
    · calc
        (∑ p ∈ (Finset.antidiagonal (0 : T →₀ ℕ)).attach,
          MvPowerSeries.coeff p.1.1 (physicalH z s * physicalH z t) *
            ((if p.1.2 = 0 then z t else 0) - rCoeff z p.1.2 t)) =
          ∑ p ∈ Finset.antidiagonal (0 : T →₀ ℕ),
            MvPowerSeries.coeff p.1 (physicalH z s * physicalH z t) *
              ((if p.2 = 0 then z t else 0) - rCoeff z p.2 t) := by
                exact Finset.sum_attach (Finset.antidiagonal (0 : T →₀ ℕ))
                  (fun p : (T →₀ ℕ) × (T →₀ ℕ) =>
                    MvPowerSeries.coeff p.1 (physicalH z s * physicalH z t) *
                      ((if p.2 = 0 then z t else 0) - rCoeff z p.2 t))
        _ = z t := by
          simp [Finset.antidiagonal_zero, MvPowerSeries.coeff_mul, hH0, hr0]
    · exact False.elim (ht rfl)
  · intro u _ hut
    simp [Ne.symm hut]
  · intro ht
    exact False.elim (ht (Finset.mem_univ t))

/-- The first coefficient is the singleton squarefree weight. -/
theorem RSeries_coeff_single (z : T → ℝ) (s t : T) :
    MvPowerSeries.coeff (Finsupp.single t 1) (RSeries z s) =
      z t / (z s + z t) := by
  change rCoeff z (Finsupp.single t 1) s = _
  rw [rCoeff_single]
  ring

/-- Positive rates give strict positivity of every first-order r-node
coefficient, including at a physical rate node. -/
theorem RSeries_coeff_single_pos (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (s t : T) :
    0 < MvPowerSeries.coeff (Finsupp.single t 1) (RSeries z s) := by
  rw [RSeries_coeff_single]
  exact div_pos (hz t) (add_pos (hz s) (hz t))

end FMSA.Convergence.PureFluidRLowOrder

/-- info: 'FMSA.Convergence.PureFluidRLowOrder.rCoeff_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLowOrder.rCoeff_single
/-- info: 'FMSA.Convergence.PureFluidRLowOrder.RSeries_coeff_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLowOrder.RSeries_coeff_single
/-- info: 'FMSA.Convergence.PureFluidRLowOrder.RSeries_coeff_single_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRLowOrder.RSeries_coeff_single_pos
