import Mathlib

/-! # One tail, matrix positive system: coefficient signs

The system `p = X + p²`, `h = 1 + κ p h`, `X = τ h K hᵀ`, as formal series in `τ` with matrix
coefficients. If `κ` and `K` are entrywise nonnegative, every coefficient of every solution with
`p(0) = 0` is entrywise nonnegative. This is purely algebraic: nothing here says that the
physical MSA root solves this system. That link is not proved.
-/

noncomputable section
open PowerSeries Matrix Finset
namespace FMSA.Convergence.T1PositiveSystem

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- All entries of `A` have nonnegative coefficients in degrees up to `d`. -/
def NN (A : Matrix n n ℝ⟦X⟧) (d : ℕ) : Prop := ∀ l ≤ d, ∀ i j, 0 ≤ coeff l (A i j)

theorem coeff_mul_apply (A B : Matrix n n ℝ⟦X⟧) (m : ℕ) (i j : n) :
    coeff m ((A * B) i j) =
      ∑ k, ∑ p ∈ antidiagonal m, coeff p.1 (A i k) * coeff p.2 (B k j) := by
  simp only [Matrix.mul_apply, map_sum, PowerSeries.coeff_mul]

theorem NN.mul {A B : Matrix n n ℝ⟦X⟧} {d : ℕ} (hA : NN A d) (hB : NN B d) : NN (A * B) d := by
  intro l hl i j
  rw [coeff_mul_apply]
  refine sum_nonneg fun k _ => sum_nonneg fun p hp => ?_
  have hp' := mem_antidiagonal.mp hp
  exact mul_nonneg (hA _ (by omega) _ _) (hB _ (by omega) _ _)

theorem NN.transpose {A : Matrix n n ℝ⟦X⟧} {d : ℕ} (hA : NN A d) : NN Aᵀ d :=
  fun l hl i j => hA l hl j i

/-- A constant matrix with nonnegative entries, as a matrix of series. -/
theorem NN.const {K : Matrix n n ℝ} (hK : ∀ i j, 0 ≤ K i j) (d : ℕ) :
    NN (K.map (C (R := ℝ))) d := by
  intro l _ i j
  rw [Matrix.map_apply, PowerSeries.coeff_C]
  split_ifs
  · exact hK i j
  · exact le_rfl

/-- **Sign theorem.** Every solution of the positive system with `p(0) = 0` has entrywise
nonnegative coefficients in all three unknowns. -/
theorem coeff_nonneg_of_system
    {κ K : Matrix n n ℝ} (hκ : ∀ i j, 0 ≤ κ i j) (hK : ∀ i j, 0 ≤ K i j)
    {P H Y : Matrix n n ℝ⟦X⟧}
    (hP0 : ∀ i j, coeff 0 (P i j) = 0)
    (hY : Y = (X : ℝ⟦X⟧) • (H * K.map (C (R := ℝ)) * Hᵀ))
    (hP : P = Y + P * P)
    (hH : H = 1 + κ.map (C (R := ℝ)) * (P * H)) (m : ℕ) :
    NN P m ∧ NN H m ∧ NN Y m := by
  have hprev : ∀ m, (∀ l < m, ∀ i j, 0 ≤ coeff l (P i j) ∧ 0 ≤ coeff l (H i j) ∧ 0 ≤ coeff l (Y i j)) →
      ∀ i j, 0 ≤ coeff m (P i j) ∧ 0 ≤ coeff m (H i j) ∧ 0 ≤ coeff m (Y i j) := by
    intro m ih
    have hYm : ∀ i j, 0 ≤ coeff m (Y i j) := by
      intro i j
      rw [hY, Matrix.smul_apply, smul_eq_mul]
      cases m with
      | zero => simp
      | succ l =>
        rw [PowerSeries.coeff_succ_X_mul]
        have hHl : NN H l := fun a ha i j => (ih a (by omega) i j).2.1
        exact ((hHl.mul (NN.const hK l)).mul hHl.transpose) l le_rfl i j
    have hPm : ∀ i j, 0 ≤ coeff m (P i j) := by
      intro i j
      have h : coeff m (P i j) = coeff m (Y i j) + coeff m ((P * P) i j) := by
        conv_lhs => rw [hP]
        simp
      rw [h, coeff_mul_apply]
      refine add_nonneg (hYm i j) (sum_nonneg fun k _ => sum_nonneg fun p hp => ?_)
      have hp' := mem_antidiagonal.mp hp
      by_cases h1 : p.1 = 0
      · simp [h1, hP0]
      by_cases h2 : p.2 = 0
      · simp [h2, hP0]
      exact mul_nonneg (ih _ (by omega) _ _).1 (ih _ (by omega) _ _).1
    have hHm : ∀ i j, 0 ≤ coeff m (H i j) := by
      intro i j
      have h : coeff m (H i j) = coeff m ((1 : Matrix n n ℝ⟦X⟧) i j) +
          coeff m ((κ.map (C (R := ℝ)) * (P * H)) i j) := by
        conv_lhs => rw [hH]
        simp
      rw [h]
      refine add_nonneg ?_ ?_
      · rw [Matrix.one_apply]
        split_ifs
        · rw [PowerSeries.coeff_one]; split_ifs <;> norm_num
        · simp
      · simp only [Matrix.mul_apply, map_sum, Matrix.map_apply, PowerSeries.coeff_C_mul]
        refine sum_nonneg fun k _ => mul_nonneg (hκ _ _) ?_
        rw [← map_sum, ← Matrix.mul_apply, coeff_mul_apply]
        refine sum_nonneg fun l _ => sum_nonneg fun p hp => ?_
        have hp' := mem_antidiagonal.mp hp
        by_cases h1 : p.1 = 0
        · simp [h1, hP0]
        have hp1 : 0 ≤ coeff p.1 (P k l) := by
          by_cases h3 : p.1 = m
          · rw [h3]; exact hPm k l
          · exact (ih _ (by omega) _ _).1
        exact mul_nonneg hp1 (ih _ (by omega) _ _).2.1
    exact fun i j => ⟨hPm i j, hHm i j, hYm i j⟩
  have hall : ∀ m i j, 0 ≤ coeff m (P i j) ∧ 0 ≤ coeff m (H i j) ∧ 0 ≤ coeff m (Y i j) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih => exact hprev m ih
  exact ⟨fun l _ i j => (hall l i j).1, fun l _ i j => (hall l i j).2.1,
    fun l _ i j => (hall l i j).2.2⟩

/-- Conjugation by a diagonal sign matrix, as a matrix of series. -/
def flip (d : n → ℝ) : Matrix n n ℝ⟦X⟧ := Matrix.diagonal fun i => C (R := ℝ) (d i)

theorem flip_mul_flip {d : n → ℝ} (hd : ∀ i, d i * d i = 1) : flip d * flip d = 1 := by
  rw [flip, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i
  rw [← map_mul, hd, map_one]

theorem flip_transpose (d : n → ℝ) : (flip d)ᵀ = flip d := Matrix.diagonal_transpose _

theorem flip_apply_conj (d : n → ℝ) (A : Matrix n n ℝ⟦X⟧) (i j : n) :
    (flip d * A * flip d) i j = C (R := ℝ) (d i) * A i j * C (R := ℝ) (d j) := by
  simp [flip, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem coeff_flip_conj (d : n → ℝ) (A : Matrix n n ℝ⟦X⟧) (m : ℕ) (i j : n) :
    coeff m ((flip d * A * flip d) i j) = d i * d j * coeff m (A i j) := by
  rw [flip_apply_conj, mul_assoc, PowerSeries.coeff_C_mul, mul_comm (A i j), PowerSeries.coeff_C_mul]
  ring

theorem flip_conj_const (d : n → ℝ) (K : Matrix n n ℝ) :
    flip d * K.map (C (R := ℝ)) * flip d =
      (Matrix.of fun i j => d i * d j * K i j).map (C (R := ℝ)) := by
  ext1 i j
  rw [flip_apply_conj]
  simp only [Matrix.map_apply, Matrix.of_apply, map_mul]
  ring

/-- A diagonal `κ` commutes with sign flips. -/
theorem flip_conj_diagonal {d : n → ℝ} (hd : ∀ i, d i * d i = 1) (k : n → ℝ) :
    flip d * (Matrix.diagonal k).map (C (R := ℝ)) * flip d = (Matrix.diagonal k).map (C (R := ℝ)) := by
  rw [flip_conj_const]
  ext1 i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; rw [hd, one_mul]
  · simp

/-- **Flip theorem.** With `κ` diagonal and nonnegative, suppose some signs `d` make `K`
entrywise nonnegative, which is the absence of frustration. Then every solution of the system has
`d i * d j * coeff m (P i j) ≥ 0`, and likewise for `H` and `Y`. -/
theorem coeff_flip_nonneg_of_system
    {k : n → ℝ} (hk : ∀ i, 0 ≤ k i) {K : Matrix n n ℝ} {d : n → ℝ} (hd : ∀ i, d i * d i = 1)
    (hdK : ∀ i j, 0 ≤ d i * d j * K i j)
    {P H Y : Matrix n n ℝ⟦X⟧}
    (hP0 : ∀ i j, coeff 0 (P i j) = 0)
    (hY : Y = (X : ℝ⟦X⟧) • (H * K.map (C (R := ℝ)) * Hᵀ))
    (hP : P = Y + P * P)
    (hH : H = 1 + (Matrix.diagonal k).map (C (R := ℝ)) * (P * H)) (m : ℕ) (i j : n) :
    0 ≤ d i * d j * coeff m (P i j) ∧ 0 ≤ d i * d j * coeff m (H i j) ∧
      0 ≤ d i * d j * coeff m (Y i j) := by
  set D := flip d with hDdef
  have hDD : D * D = 1 := flip_mul_flip hd
  have hins : ∀ A B : Matrix n n ℝ⟦X⟧, D * (A * B) * D = (D * A * D) * (D * B * D) := by
    intro A B
    calc D * (A * B) * D = D * A * 1 * B * D := by simp [Matrix.mul_assoc]
      _ = D * A * (D * D) * B * D := by rw [hDD]
      _ = (D * A * D) * (D * B * D) := by simp only [Matrix.mul_assoc]
  have hκ' : ∀ a b, 0 ≤ (Matrix.diagonal k) a b := by
    intro a b; rw [Matrix.diagonal_apply]; split_ifs
    · exact hk a
    · exact le_rfl
  have hsys := coeff_nonneg_of_system (κ := Matrix.diagonal k)
    (K := Matrix.of fun a b => d a * d b * K a b) hκ' (fun a b => hdK a b)
    (P := D * P * D) (H := D * H * D) (Y := D * Y * D)
    (fun a b => by rw [coeff_flip_conj, hP0, mul_zero])
    (by
      have htr : (D * H * D)ᵀ = D * Hᵀ * D := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, flip_transpose, Matrix.mul_assoc]
      conv_lhs => rw [hY]
      rw [htr, ← flip_conj_const, ← hins, ← hins]
      rw [Matrix.mul_smul, Matrix.smul_mul])
    (by
      conv_lhs => rw [hP]
      rw [Matrix.mul_add, Matrix.add_mul, hins])
    (by
      conv_lhs => rw [hH]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hDD, hins, hins]
      conv_lhs => rw [show D * (Matrix.diagonal k).map (C (R := ℝ)) * D = (Matrix.diagonal k).map (C (R := ℝ)) from flip_conj_diagonal hd k])
    m
  have e := fun A => coeff_flip_conj (d := d) A m i j
  refine ⟨?_, ?_, ?_⟩
  · rw [← e]; exact hsys.1 m le_rfl i j
  · rw [← e]; exact hsys.2.1 m le_rfl i j
  · rw [← e]; exact hsys.2.2 m le_rfl i j

/-- **Two species.** A symmetric `2 × 2` matrix with nonnegative diagonal can always be sign
flipped to be nonnegative, so all coefficients have fixed signs. The diagonal of a PSD `K` is
nonnegative. -/
theorem two_species_signs
    {k : Fin 2 → ℝ} (hk : ∀ i, 0 ≤ k i) {K : Matrix (Fin 2) (Fin 2) ℝ} (hsym : K 0 1 = K 1 0)
    (h00 : 0 ≤ K 0 0) (h11 : 0 ≤ K 1 1)
    {P H Y : Matrix (Fin 2) (Fin 2) ℝ⟦X⟧}
    (hP0 : ∀ i j, coeff 0 (P i j) = 0)
    (hY : Y = (X : ℝ⟦X⟧) • (H * K.map (C (R := ℝ)) * Hᵀ))
    (hP : P = Y + P * P)
    (hH : H = 1 + (Matrix.diagonal k).map (C (R := ℝ)) * (P * H)) (m : ℕ) :
    ∃ s : ℝ, s * s = 1 ∧ 0 ≤ s * K 0 1 ∧
      0 ≤ coeff m (P 0 0) ∧ 0 ≤ coeff m (P 1 1) ∧ 0 ≤ s * coeff m (P 0 1) ∧
      0 ≤ coeff m (H 0 0) ∧ 0 ≤ coeff m (H 1 1) ∧ 0 ≤ s * coeff m (H 0 1) := by
  obtain ⟨s, hs, hsK⟩ : ∃ s : ℝ, s * s = 1 ∧ 0 ≤ s * K 0 1 := by
    rcases le_total 0 (K 0 1) with h | h
    · exact ⟨1, by norm_num, by simpa using h⟩
    · exact ⟨-1, by norm_num, by simpa using h⟩
  let d : Fin 2 → ℝ := ![1, s]
  have hd : ∀ i, d i * d i = 1 := by
    intro i; fin_cases i
    · simp [d]
    · simpa [d] using hs
  have hdK : ∀ i j, 0 ≤ d i * d j * K i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [d] using h00
    · simpa [d] using hsK
    · simpa [d, hsym] using (hsym ▸ hsK)
    · simpa [d, hs] using h11
  have h := fun i j => coeff_flip_nonneg_of_system hk hd hdK hP0 hY hP hH m i j
  refine ⟨s, hs, hsK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [d] using (h 0 0).1
  · simpa [d, hs] using (h 1 1).1
  · simpa [d] using (h 0 1).1
  · simpa [d] using (h 0 0).2.1
  · simpa [d, hs] using (h 1 1).2.1
  · simpa [d] using (h 0 1).2.1

/-- The system implies the polynomial form `(1 - κ p) (p - p²) (1 - κ p)ᵀ = τ K`. -/
theorem polynomial_form_of_system
    {κ K : Matrix n n ℝ} {P H Y : Matrix n n ℝ⟦X⟧}
    (hY : Y = (X : ℝ⟦X⟧) • (H * K.map (C (R := ℝ)) * Hᵀ))
    (hP : P = Y + P * P)
    (hH : H = 1 + κ.map (C (R := ℝ)) * (P * H)) :
    (1 - κ.map (C (R := ℝ)) * P) * (P - P * P) * (1 - κ.map (C (R := ℝ)) * P)ᵀ =
      (X : ℝ⟦X⟧) • K.map (C (R := ℝ)) := by
  set F := 1 - κ.map (C (R := ℝ)) * P with hF
  have hFH : F * H = 1 := by
    have : H - κ.map (C (R := ℝ)) * (P * H) = 1 := by
      nth_rewrite 1 [hH]; simp
    rw [hF, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]; exact this
  have hHT : Hᵀ * Fᵀ = 1 := by
    rw [← Matrix.transpose_mul, hFH, Matrix.transpose_one]
  have hPP : P - P * P = Y := by
    nth_rewrite 1 [hP]; simp
  rw [hPP, hY, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc F * (H * K.map (C (R := ℝ)) * Hᵀ) * Fᵀ
      = (F * H) * K.map (C (R := ℝ)) * (Hᵀ * Fᵀ) := by simp only [Matrix.mul_assoc]
    _ = K.map (C (R := ℝ)) := by rw [hFH, hHT, Matrix.one_mul, Matrix.mul_one]


end FMSA.Convergence.T1PositiveSystem

/-- info: 'FMSA.Convergence.T1PositiveSystem.coeff_mul_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.coeff_mul_apply
/-- info: 'FMSA.Convergence.T1PositiveSystem.NN.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.NN.mul
/-- info: 'FMSA.Convergence.T1PositiveSystem.NN.transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.NN.transpose
/-- info: 'FMSA.Convergence.T1PositiveSystem.NN.const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.NN.const
/-- info: 'FMSA.Convergence.T1PositiveSystem.coeff_nonneg_of_system' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.coeff_nonneg_of_system
/-- info: 'FMSA.Convergence.T1PositiveSystem.flip_mul_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.flip_mul_flip
/-- info: 'FMSA.Convergence.T1PositiveSystem.flip_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.flip_transpose
/-- info: 'FMSA.Convergence.T1PositiveSystem.flip_apply_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.flip_apply_conj
/-- info: 'FMSA.Convergence.T1PositiveSystem.coeff_flip_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.coeff_flip_conj
/-- info: 'FMSA.Convergence.T1PositiveSystem.flip_conj_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.flip_conj_const
/-- info: 'FMSA.Convergence.T1PositiveSystem.flip_conj_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.flip_conj_diagonal
/-- info: 'FMSA.Convergence.T1PositiveSystem.coeff_flip_nonneg_of_system' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.coeff_flip_nonneg_of_system
/-- info: 'FMSA.Convergence.T1PositiveSystem.two_species_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.two_species_signs
/-- info: 'FMSA.Convergence.T1PositiveSystem.polynomial_form_of_system' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1PositiveSystem.polynomial_form_of_system
