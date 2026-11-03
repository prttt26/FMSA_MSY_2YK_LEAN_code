import MSAConvergence.PureFluidRLowOrder

set_option linter.style.header false

/-! Coefficient algebra for the quadratic squarefree r identity. -/
noncomputable section
open MvPowerSeries Finsupp
namespace FMSA.Convergence.PureFluidRQuadraticBridge
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidHFormalSolution
open FMSA.Convergence.PureFluidRLowOrder
variable {T : Type*} [Fintype T] [DecidableEq T]

omit [Fintype T] in
theorem coeff_single_mul (A B : MvPowerSeries T ℝ) (i : T) :
    MvPowerSeries.coeff (Finsupp.single i 1) (A * B) =
      MvPowerSeries.coeff 0 A * MvPowerSeries.coeff (Finsupp.single i 1) B +
      MvPowerSeries.coeff (Finsupp.single i 1) A * MvPowerSeries.coeff 0 B := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
  have hnat : Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by decide
  rw [hnat]
  simp

theorem physicalH_coeff_zero (z : T → ℝ) (s : T) :
    MvPowerSeries.coeff 0 (physicalH z s) = 1 := by
  change hCoeff (fun a b => (z a + z b)⁻¹) 0 s = 1
  rw [hCoeff.eq_1]
  simp

theorem physicalH_coeff_single (z : T → ℝ) (s i : T) :
    MvPowerSeries.coeff (Finsupp.single i 1) (physicalH z s) =
      (z s + z i)⁻¹ := by
  classical
  change hCoeff (fun a b => (z a + z b)⁻¹) (Finsupp.single i 1) s = _
  rw [hCoeff.eq_1]
  have hsingle (u : T) :
      (Finsupp.single u 1 ≤ Finsupp.single i 1) ↔ i = u := by
    by_cases h : u = i
    · subst u; simp
    · simp [Finsupp.single_le_iff, h, Ne.symm h]
  simp_rw [hsingle]
  have hnonzero : Finsupp.single i 1 ≠ (0 : T →₀ ℕ) := by simp
  have hsub : Finsupp.single i 1 - Finsupp.single i 1 = (0 : T →₀ ℕ) := by
    ext u
    simp
  simp only [if_neg hnonzero]
  rw [Finset.sum_eq_single i]
  · rw [hsub]
    split_ifs with hi
    · have hc0 (u : T) : hCoeff (fun a b => (z a + z b)⁻¹) 0 u = 1 := by
        exact physicalH_coeff_zero z u
      have hsum :
          (∑ p ∈ (Finset.antidiagonal (0 : T →₀ ℕ)).attach,
            hCoeff (fun a b => (z a + z b)⁻¹) p.1.1 s *
              hCoeff (fun a b => (z a + z b)⁻¹) p.1.2 i) = 1 := by
        calc
          _ = ∑ p ∈ Finset.antidiagonal (0 : T →₀ ℕ),
              hCoeff (fun a b => (z a + z b)⁻¹) p.1 s *
                hCoeff (fun a b => (z a + z b)⁻¹) p.2 i := by
                  exact Finset.sum_attach (Finset.antidiagonal (0 : T →₀ ℕ))
                    (fun p : (T →₀ ℕ) × (T →₀ ℕ) =>
                      hCoeff (fun a b => (z a + z b)⁻¹) p.1 s *
                        hCoeff (fun a b => (z a + z b)⁻¹) p.2 i)
          _ = 1 := by simp [Finset.antidiagonal_zero, hc0]
      rw [hsum]
      ring
    · exact False.elim (hi rfl)
  · intro u _ hui
    simp [Ne.symm hui]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem physicalH_product_coeff_single (z : T → ℝ) (s t i : T) :
    MvPowerSeries.coeff (Finsupp.single i 1)
      (physicalH z s * physicalH z t) =
      (z s + z i)⁻¹ + (z t + z i)⁻¹ := by
  rw [coeff_single_mul, physicalH_coeff_zero, physicalH_coeff_zero,
    physicalH_coeff_single, physicalH_coeff_single]
  ring

omit [Fintype T] in
theorem single_le_two (i j t : T) :
    Finsupp.single t 1 ≤ Finsupp.single i 1 + Finsupp.single j 1 ↔
      t = i ∨ t = j := by
  rw [Finsupp.single_le_iff, Finsupp.add_apply]
  by_cases hti : t = i
  · subst t
    simp
  by_cases htj : t = j
  · subst t
    simp [hti]
  · simp [hti, htj]

omit [Fintype T] [DecidableEq T] in
theorem two_sub_left (i j : T) :
    (Finsupp.single i 1 + Finsupp.single j 1) - Finsupp.single i 1 =
      Finsupp.single j 1 := by
  ext t
  simp

omit [Fintype T] [DecidableEq T] in
theorem two_sub_right (i j : T) :
    (Finsupp.single i 1 + Finsupp.single j 1) - Finsupp.single j 1 =
      Finsupp.single i 1 := by
  rw [add_comm]
  exact two_sub_left j i

omit [Fintype T] in
theorem coeff_X_two (A : MvPowerSeries T ℝ) (i j t : T) :
    MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single j 1)
      (MvPowerSeries.X t * A) =
      if t = i then MvPowerSeries.coeff (Finsupp.single j 1) A
      else if t = j then MvPowerSeries.coeff (Finsupp.single i 1) A
      else 0 := by
  classical
  simp only [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul,
    one_mul]
  by_cases hti : t = i
  · subst t
    simp
  by_cases htj : t = j
  · subst t
    simp [hti]
  · have hnot : ¬ Finsupp.single t 1 ≤
        Finsupp.single i 1 + Finsupp.single j 1 := by
      intro h
      rcases (single_le_two i j t).mp h with h | h
      · exact hti h
      · exact htj h
    simp [hti, htj, hnot]

theorem RSeries_coeff_zero (z : T → ℝ) (s : T) :
    MvPowerSeries.coeff 0 (RSeries z s) = 0 := by
  change rCoeff z 0 s = 0
  rw [rCoeff.eq_1]
  simp

theorem physicalH_product_coeff_zero (z : T → ℝ) (s t : T) :
    MvPowerSeries.coeff 0 (physicalH z s * physicalH z t) = 1 := by
  rw [MvPowerSeries.coeff_mul]
  simp [Finset.antidiagonal_zero, physicalH_coeff_zero]

theorem r_core_coeff_single (z : T → ℝ) (s t i : T) :
    MvPowerSeries.coeff (Finsupp.single i 1)
      ((physicalH z s * physicalH z t) *
        (MvPowerSeries.C (z t) - RSeries z t)) =
      z t * ((z s + z i)⁻¹ + (z t + z i)⁻¹) -
        z i / (z t + z i) := by
  rw [coeff_single_mul]
  rw [physicalH_product_coeff_zero, physicalH_product_coeff_single]
  simp only [map_sub, MvPowerSeries.coeff_C,
    RSeries_coeff_zero, RSeries_coeff_single]
  have hne : Finsupp.single i 1 ≠ (0 : T →₀ ℕ) := by simp
  simp only [if_neg hne, if_pos trivial, zero_sub]
  ring

theorem RSeries_coeff_two_raw (z : T → ℝ) (s i j : T) (hij : i ≠ j) :
    MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single j 1)
      (RSeries z s) =
      (z s + z i)⁻¹ *
        (z i * ((z s + z j)⁻¹ + (z i + z j)⁻¹) -
          z j / (z i + z j)) +
      (z s + z j)⁻¹ *
        (z j * ((z s + z i)⁻¹ + (z j + z i)⁻¹) -
          z i / (z j + z i)) := by
  classical
  let core (t : T) : MvPowerSeries T ℝ :=
    (physicalH z s * physicalH z t) *
      (MvPowerSeries.C (z t) - RSeries z t)
  calc
    MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single j 1)
      (RSeries z s) =
        ∑ t, (z s + z t)⁻¹ *
          (if t = i then MvPowerSeries.coeff (Finsupp.single j 1) (core t)
          else if t = j then MvPowerSeries.coeff (Finsupp.single i 1) (core t)
          else 0) := by
            rw [RSeries_system z s]
            simp only [map_sum, MvPowerSeries.coeff_C_mul]
            apply Finset.sum_congr rfl
            intro t _
            exact congrArg (fun v : ℝ => (z s + z t)⁻¹ * v)
              (coeff_X_two (core t) i j t)
    _ = _ := by
      simp only [mul_ite, mul_zero]
      dsimp only [core]
      simp_rw [r_core_coeff_single]
      let A (t : T) : ℝ := (z s + z t)⁻¹ *
        (z t * ((z s + z j)⁻¹ + (z t + z j)⁻¹) - z j / (z t + z j))
      let B (t : T) : ℝ := (z s + z t)⁻¹ *
        (z t * ((z s + z i)⁻¹ + (z t + z i)⁻¹) - z i / (z t + z i))
      change (∑ t, if t = i then A t else if t = j then B t else 0) =
        A i + B j
      calc
        _ = (∑ t, if t = i then A t else 0) +
            (∑ t, if t = j then B t else 0) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro t _
              by_cases hti : t = i
              · subst t
                simp [hij]
              · simp [hti]
        _ = A i + B j := by simp [Finset.sum_ite_eq']

/-- The first genuinely mixed theta coefficient has an explicit positive
rational form, valid for every finite rate family. -/
theorem RSeries_coeff_two_pos_formula (z : T → ℝ)
    (hz : ∀ t, 0 < z t) (s i j : T) (hij : i ≠ j) :
    MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single j 1)
      (RSeries z s) =
      4 * z i * z j /
        ((z s + z i) * (z s + z j) * (z i + z j)) := by
  rw [RSeries_coeff_two_raw z s i j hij]
  have hsi : z s + z i ≠ 0 := (add_pos (hz s) (hz i)).ne'
  have hsj : z s + z j ≠ 0 := (add_pos (hz s) (hz j)).ne'
  have hijsum : z i + z j ≠ 0 := (add_pos (hz i) (hz j)).ne'
  have hjisum : z j + z i ≠ 0 := (add_pos (hz j) (hz i)).ne'
  field_simp [hsi, hsj, hijsum, hjisum]
  ring

theorem RSeries_coeff_two_pos (z : T → ℝ)
    (hz : ∀ t, 0 < z t) (s i j : T) (hij : i ≠ j) :
    0 < MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single j 1)
      (RSeries z s) := by
  rw [RSeries_coeff_two_pos_formula z hz s i j hij]
  exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) (hz i)) (hz j))
    (mul_pos (mul_pos (add_pos (hz s) (hz i))
      (add_pos (hz s) (hz j))) (add_pos (hz i) (hz j)))

/-- At two distinct rates, the actual multivariate r coefficient equals
twice the finite squarefree W weight. -/
theorem RSeries_coeff_two_eq_W (z : T → ℝ)
    (hz : ∀ t, 0 < z t) (s i j : T)
    (hij : i ≠ j) (hzij : z i ≠ z j) :
    MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single j 1)
      (RSeries z s) =
      2 * ∑ t ∈ ({i, j} : Finset T),
        (z t / (z s + z t)) *
          ∏ u ∈ ({i, j} : Finset T).erase t,
            (2 * z u) / (z u ^ 2 - z t ^ 2) := by
  rw [RSeries_coeff_two_pos_formula z hz s i j hij]
  have herasei : ({i, j} : Finset T).erase i = {j} := by
    simp [hij]
  have herasej : ({i, j} : Finset T).erase j = {i} := by
    ext t
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hi | hj⟩
      · exact hi
      · contradiction
    · intro hi
      exact ⟨fun hj => hij (hi.symm.trans hj), Or.inl hi⟩
  simp [herasei, herasej, hij]
  have hsi : z s + z i ≠ 0 := (add_pos (hz s) (hz i)).ne'
  have hsj : z s + z j ≠ 0 := (add_pos (hz s) (hz j)).ne'
  have hijsum : z i + z j ≠ 0 := (add_pos (hz i) (hz j)).ne'
  have hdiff : z j ^ 2 - z i ^ 2 ≠ 0 := by
    intro heq
    have hsq : z j ^ 2 = z i ^ 2 := sub_eq_zero.mp heq
    exact hzij ((sq_eq_sq₀ (hz i).le (hz j).le).mp hsq.symm)
  have hdiff' : z i ^ 2 - z j ^ 2 ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hdiff))
  field_simp [hsi, hsj, hijsum, hdiff, hdiff']
  ring

/-- The remaining degree-two monomial has a one-rate square formula. -/
theorem RSeries_coeff_square_raw (z : T → ℝ) (s i : T) :
    MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single i 1)
      (RSeries z s) =
      (z s + z i)⁻¹ *
        (z i * ((z s + z i)⁻¹ + (z i + z i)⁻¹) -
          z i / (z i + z i)) := by
  classical
  rw [RSeries_system z s]
  simp only [map_sum, MvPowerSeries.coeff_C_mul]
  rw [Finset.sum_eq_single i]
  · rw [coeff_X_two]
    simp [r_core_coeff_single]
  · intro t _ hti
    rw [coeff_X_two]
    simp [hti]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem RSeries_coeff_square_formula (z : T → ℝ)
    (hz : ∀ t, 0 < z t) (s i : T) :
    MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single i 1)
      (RSeries z s) = z i / (z s + z i) ^ 2 := by
  rw [RSeries_coeff_square_raw]
  have hsi : z s + z i ≠ 0 := (add_pos (hz s) (hz i)).ne'
  have hii : z i + z i ≠ 0 := (add_pos (hz i) (hz i)).ne'
  have hzi : z i ≠ 0 := (hz i).ne'
  field_simp [hsi, hii, hzi]
  ring

theorem RSeries_coeff_square_pos (z : T → ℝ)
    (hz : ∀ t, 0 < z t) (s i : T) :
    0 < MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single i 1)
      (RSeries z s) := by
  rw [RSeries_coeff_square_formula z hz]
  exact div_pos (hz i) (sq_pos_of_pos (add_pos (hz s) (hz i)))

end FMSA.Convergence.PureFluidRQuadraticBridge

/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.coeff_single_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.coeff_single_mul
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.physicalH_coeff_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.physicalH_coeff_zero
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.physicalH_coeff_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.physicalH_coeff_single
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.physicalH_product_coeff_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.physicalH_product_coeff_single
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.single_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.single_le_two
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.two_sub_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.two_sub_left
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.two_sub_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.two_sub_right
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.coeff_X_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.coeff_X_two
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_zero
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.physicalH_product_coeff_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.physicalH_product_coeff_zero
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.r_core_coeff_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.r_core_coeff_single
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_two_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_two_raw
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_two_pos_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_two_pos_formula
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_two_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_two_pos
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_two_eq_W' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_two_eq_W
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_square_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_square_raw
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_square_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_square_formula
/-- info: 'FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_square_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRQuadraticBridge.RSeries_coeff_square_pos
