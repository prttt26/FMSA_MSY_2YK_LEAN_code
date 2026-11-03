import MSAConvergence.PureFluidFoldTheorem

set_option linter.style.header false

/-! The physical `θ` Picard equation in several tail strengths: a solution in formal series,
obtained from stabilizing iterates, with nonnegative mixed coefficients. -/

noncomputable section
open MvPowerSeries
namespace FMSA.Convergence.PureFluidMixedPicard
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidRLabelSubstitution

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Nonnegative mixed coefficients. -/
def NN {U : Type*} (f : MvPowerSeries U ℝ) : Prop := ∀ m, 0 ≤ coeff m f

/-- Agreement below a total degree. -/
def EqBelow {U : Type*} (N : ℕ) (f g : MvPowerSeries U ℝ) : Prop :=
  ∀ m : U →₀ ℕ, m.degree < N → coeff m f = coeff m g

section General

variable {U : Type*} [DecidableEq U]

theorem nn_add {f g : MvPowerSeries U ℝ} (hf : NN f) (hg : NN g) : NN (f + g) := fun m => by
  rw [map_add]; exact add_nonneg (hf m) (hg m)

theorem nn_mul {f g : MvPowerSeries U ℝ} (hf : NN f) (hg : NN g) : NN (f * g) := fun m => by
  rw [coeff_mul]; exact Finset.sum_nonneg fun _ _ => mul_nonneg (hf _) (hg _)

theorem nn_C {a : ℝ} (h : 0 ≤ a) : NN (C a : MvPowerSeries U ℝ) := fun m => by
  rw [coeff_C]; split_ifs <;> simp [h]

theorem nn_one : NN (1 : MvPowerSeries U ℝ) := by
  simpa using nn_C (U := U) (a := 1) zero_le_one

theorem nn_X (t : U) : NN (X t : MvPowerSeries U ℝ) := fun m => by
  rw [coeff_X]; split_ifs <;> simp

theorem nn_pow {f : MvPowerSeries U ℝ} (hf : NN f) (k : ℕ) : NN (f ^ k) := by
  induction k with
  | zero => simpa using nn_one
  | succ k ih => rw [pow_succ]; exact nn_mul ih hf

theorem degree_lt_of_mem {m : U →₀ ℕ} {p : (U →₀ ℕ) × (U →₀ ℕ)}
    (hp : p ∈ Finset.antidiagonal m) : p.1.degree ≤ m.degree ∧ p.2.degree ≤ m.degree ∧
      (p.1 ≠ 0 → p.2.degree < m.degree) := by
  have h := Finset.mem_antidiagonal.mp hp
  have hd : p.1.degree + p.2.degree = m.degree := by rw [← h, map_add]
  refine ⟨by omega, by omega, fun h1 => ?_⟩
  have : p.1.degree ≠ 0 := fun h0 => h1 ((Finsupp.degree_eq_zero_iff _).mp h0)
  omega

theorem eqBelow_mul {N : ℕ} {f f' g g' : MvPowerSeries U ℝ} (hf : EqBelow N f f')
    (hg : EqBelow N g g') : EqBelow N (f * g) (f' * g') := fun m hm => by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, -⟩ := degree_lt_of_mem hp
  rw [hf p.1 (by omega), hg p.2 (by omega)]

theorem eqBelow_refl (N : ℕ) (f : MvPowerSeries U ℝ) : EqBelow N f f := fun _ _ => rfl

theorem eqBelow_pow {N : ℕ} {f f' : MvPowerSeries U ℝ} (hf : EqBelow N f f') (k : ℕ) :
    EqBelow N (f ^ k) (f' ^ k) := by
  induction k with
  | zero => simpa using eqBelow_refl N 1
  | succ k ih => rw [pow_succ, pow_succ]; exact eqBelow_mul ih hf

/-- Multiplying by a variable raises the agreement degree by one. -/
theorem eqBelow_X_mul {N : ℕ} {f g : MvPowerSeries U ℝ} (t : U) (h : EqBelow N f g) :
    EqBelow (N + 1) (X t * f) (X t * g) := fun m hm => by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [coeff_X]
  split_ifs with h1
  · have hdeg : p.1.degree + p.2.degree = m.degree := by
      rw [← Finset.mem_antidiagonal.mp hp, map_add]
    have h11 : p.1.degree = 1 := by rw [h1]; simp
    rw [h p.2 (by omega)]
  · simp

/-- The geometric inverse is determined by the coefficients of its argument. -/
theorem eqBelow_inv {N : ℕ} {g g' : MvPowerSeries U ℝ} (h0 : constantCoeff g = 0)
    (h0' : constantCoeff g' = 0) (h : EqBelow N g g') :
    EqBelow N (1 - g)⁻¹ (1 - g')⁻¹ := by
  have hc : constantCoeff (1 - g) ≠ 0 := by simp [h0]
  have hc' : constantCoeff (1 - g') ≠ 0 := by simp [h0']
  have hq : (1 - g)⁻¹ = 1 + g * (1 - g)⁻¹ := by
    linear_combination MvPowerSeries.mul_inv_cancel (1 - g) hc
  have hq' : (1 - g')⁻¹ = 1 + g' * (1 - g')⁻¹ := by
    linear_combination MvPowerSeries.mul_inv_cancel (1 - g') hc'
  intro m hm
  induction hd : m.degree using Nat.strong_induction_on generalizing m with
  | _ d ih =>
    rw [hq, hq', map_add, map_add, coeff_mul, coeff_mul]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, -, h3⟩ := degree_lt_of_mem hp
    by_cases hp0 : p.1 = 0
    · have hg0 : coeff p.1 g = 0 := by rw [hp0]; simpa using h0
      have hg0' : coeff p.1 g' = 0 := by rw [hp0]; simpa using h0'
      rw [hg0, hg0', zero_mul, zero_mul]
    · have hlt := h3 hp0
      rw [h p.1 (by omega), ih p.2.degree (by omega) p.2 (by omega) rfl]

/-- The geometric inverse keeps nonnegative coefficients. -/
theorem nn_inv {g : MvPowerSeries U ℝ} (h0 : constantCoeff g = 0) (hg : NN g) :
    NN (1 - g)⁻¹ := by
  have hc : constantCoeff (1 - g) ≠ 0 := by simp [h0]
  have hq : (1 - g)⁻¹ = 1 + g * (1 - g)⁻¹ := by
    linear_combination MvPowerSeries.mul_inv_cancel (1 - g) hc
  intro m
  induction hd : m.degree using Nat.strong_induction_on generalizing m with
  | _ d ih =>
    rw [hq, map_add, coeff_mul]
    refine add_nonneg (nn_one m) (Finset.sum_nonneg fun p hp => ?_)
    obtain ⟨-, -, h3⟩ := degree_lt_of_mem hp
    by_cases hp0 : p.1 = 0
    · have hg0 : coeff p.1 g = 0 := by rw [hp0]; simpa using h0
      rw [hg0, zero_mul]
    · exact mul_nonneg (hg _) (ih p.2.degree (by have := h3 hp0; omega) p.2 rfl)

end General

section Subst

variable {σ U : Type*} [Finite σ] [DecidableEq U]

theorem eqBelow_finsupp_prod {N : ℕ} {a b : σ → MvPowerSeries U ℝ} (h : ∀ t, EqBelow N (a t) (b t))
    (m : σ →₀ ℕ) :
    EqBelow N (m.prod fun t k => a t ^ k) (m.prod fun t k => b t ^ k) := by
  classical
  change EqBelow N (∏ t ∈ m.support, a t ^ m t) (∏ t ∈ m.support, b t ^ m t)
  induction m.support using Finset.induction_on with
  | empty => simpa using eqBelow_refl N 1
  | insert t s ht ih =>
    rw [Finset.prod_insert ht, Finset.prod_insert ht]
    exact eqBelow_mul (eqBelow_pow (h t) _) ih

theorem nn_finsupp_prod {a : σ → MvPowerSeries U ℝ} (h : ∀ t, NN (a t)) (m : σ →₀ ℕ) :
    NN (m.prod fun t k => a t ^ k) := by
  classical
  change NN (∏ t ∈ m.support, a t ^ m t)
  induction m.support using Finset.induction_on with
  | empty => simpa using nn_one
  | insert t s ht ih =>
    rw [Finset.prod_insert ht]
    exact nn_mul (nn_pow (h t) _) ih

theorem eqBelow_subst {N : ℕ} {a b : σ → MvPowerSeries U ℝ} (ha : ∀ t, constantCoeff (a t) = 0)
    (hb : ∀ t, constantCoeff (b t) = 0) (h : ∀ t, EqBelow N (a t) (b t))
    (f : MvPowerSeries σ ℝ) : EqBelow N (subst a f) (subst b f) := fun m hm => by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero hb)]
  exact finsum_congr fun e => by rw [eqBelow_finsupp_prod h e m hm]

theorem nn_subst {a : σ → MvPowerSeries U ℝ} (h0 : ∀ t, constantCoeff (a t) = 0)
    (ha : ∀ t, NN (a t)) {f : MvPowerSeries σ ℝ} (hf : NN f) : NN (subst a f) := fun m => by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero h0)]
  exact finsum_nonneg fun e => by
    simpa only [smul_eq_mul] using mul_nonneg (hf e) (nn_finsupp_prod ha e m)

end Subst

theorem RSeries_constantCoeff (z : T → ℝ) (s : T) : constantCoeff (RSeries z s) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  change rCoeff z 0 s = 0
  simp [rCoeff]

theorem RSeries_nn (z : T → ℝ) (hz : ∀ t, 0 < z t) (s : T) : NN (RSeries z s) := fun m => by
  by_cases hm : m = 0
  · subst m
    change 0 ≤ rCoeff z 0 s
    simp [rCoeff]
  · exact (RSeries_coeff_pos_all m hm z hz s).le

theorem subst_constantCoeff_zero {a : T → MvPowerSeries T ℝ} (h0 : ∀ t, constantCoeff (a t) = 0)
    {f : MvPowerSeries T ℝ} (hf : constantCoeff f = 0) : constantCoeff (subst a f) = 0 := by
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hf

/-- The Picard update. -/
def pic (z a κ : T → ℝ) (θ : T → MvPowerSeries T ℝ) (t : T) : MvPowerSeries T ℝ :=
  C (a t) * (X t * (1 - C (κ t) * subst θ (RSeries z t))⁻¹ ^ 2)

/-- The Picard iterates from zero. -/
def iter (z a κ : T → ℝ) : ℕ → T → MvPowerSeries T ℝ
  | 0 => fun _ => 0
  | k + 1 => pic z a κ (iter z a κ k)

/-- The limit of the iterates, read off degree by degree. -/
def thetaM (z a κ : T → ℝ) (t : T) : MvPowerSeries T ℝ :=
  fun m => coeff m (iter z a κ (m.degree + 1) t)

variable {z a κ : T → ℝ}

theorem pic_constantCoeff (θ : T → MvPowerSeries T ℝ) (t : T) :
    constantCoeff (pic z a κ θ t) = 0 := by
  simp [pic]

theorem iter_constantCoeff (k : ℕ) (t : T) : constantCoeff (iter z a κ k t) = 0 := by
  cases k with
  | zero => simp [iter]
  | succ k => exact pic_constantCoeff _ t

/-- The update raises the order of agreement. -/
theorem pic_eqBelow {N : ℕ} {θ θ' : T → MvPowerSeries T ℝ} (h0 : ∀ t, constantCoeff (θ t) = 0)
    (h0' : ∀ t, constantCoeff (θ' t) = 0) (h : ∀ t, EqBelow N (θ t) (θ' t)) (t : T) :
    EqBelow (N + 1) (pic z a κ θ t) (pic z a κ θ' t) := by
  have hR := eqBelow_subst h0 h0' h (RSeries z t)
  have hg : EqBelow N (C (κ t) * subst θ (RSeries z t)) (C (κ t) * subst θ' (RSeries z t)) :=
    eqBelow_mul (eqBelow_refl N _) hR
  have hc : constantCoeff (C (κ t) * subst θ (RSeries z t)) = 0 := by
    simp [subst_constantCoeff_zero h0 (RSeries_constantCoeff z t)]
  have hc' : constantCoeff (C (κ t) * subst θ' (RSeries z t)) = 0 := by
    simp [subst_constantCoeff_zero h0' (RSeries_constantCoeff z t)]
  have hX := eqBelow_X_mul t (eqBelow_pow (eqBelow_inv hc hc' hg) 2)
  exact eqBelow_mul (eqBelow_refl _ _) hX

theorem iter_step (k : ℕ) (t : T) :
    EqBelow k (iter z a κ k t) (iter z a κ (k + 1) t) := by
  induction k generalizing t with
  | zero => exact fun m hm => absurd hm (Nat.not_lt_zero _)
  | succ k ih =>
    exact pic_eqBelow (iter_constantCoeff k) (iter_constantCoeff (k + 1)) ih t

theorem iter_stable {k j : ℕ} (h : k ≤ j) (t : T) :
    EqBelow k (iter z a κ k t) (iter z a κ j t) := by
  induction j, h using Nat.le_induction with
  | base => exact eqBelow_refl _ _
  | succ j hj ih => exact fun m hm => (ih m hm).trans (iter_step j t m (by omega))

theorem coeff_thetaM (m : T →₀ ℕ) (t : T) :
    coeff m (thetaM z a κ t) = coeff m (iter z a κ (m.degree + 1) t) := by
  rw [coeff_apply]
  simp only [thetaM]

theorem thetaM_eqBelow (k : ℕ) (t : T) : EqBelow k (thetaM z a κ t) (iter z a κ k t) := by
  intro m hm
  rw [coeff_thetaM]
  exact iter_stable (k := m.degree + 1) (j := k) (by omega) t m (by omega)

theorem thetaM_constantCoeff (t : T) : constantCoeff (thetaM z a κ t) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, thetaM_eqBelow 1 t 0 (by simp),
    coeff_zero_eq_constantCoeff_apply]
  exact iter_constantCoeff 1 t

/-- `θ` solves the Picard equation in the tail strengths. -/
theorem thetaM_fixed (t : T) :
    thetaM z a κ t = C (a t) * (X t * (1 - C (κ t) *
      subst (thetaM z a κ) (RSeries z t))⁻¹ ^ 2) := by
  ext m
  set N := m.degree + 1
  have h1 := pic_eqBelow (z := z) (a := a) (κ := κ) (thetaM_constantCoeff (z := z) (a := a) (κ := κ))
    (iter_constantCoeff N) (fun u => thetaM_eqBelow N u) t m (by omega)
  have h2 := thetaM_eqBelow (z := z) (a := a) (κ := κ) (N + 1) t m (by omega)
  exact h2.trans h1.symm

theorem pic_nn (hz : ∀ t, 0 < z t) (ha : ∀ t, 0 ≤ a t) (hκ : ∀ t, 0 ≤ κ t)
    {θ : T → MvPowerSeries T ℝ} (h0 : ∀ t, constantCoeff (θ t) = 0) (hθ : ∀ t, NN (θ t)) (t : T) :
    NN (pic z a κ θ t) := by
  have hR := nn_subst h0 hθ (RSeries_nn z hz t)
  have hc : constantCoeff (C (κ t) * subst θ (RSeries z t)) = 0 := by
    simp [subst_constantCoeff_zero h0 (RSeries_constantCoeff z t)]
  exact nn_mul (nn_C (ha t)) (nn_mul (nn_X t)
    (nn_pow (nn_inv hc (nn_mul (nn_C (hκ t)) hR)) 2))

theorem iter_nn (hz : ∀ t, 0 < z t) (ha : ∀ t, 0 ≤ a t) (hκ : ∀ t, 0 ≤ κ t) (k : ℕ) (t : T) :
    NN (iter z a κ k t) := by
  induction k generalizing t with
  | zero => intro m; simp [iter]
  | succ k ih => exact pic_nn hz ha hκ (iter_constantCoeff k) ih t

/-- All mixed coefficients of `θ` are nonnegative. -/
theorem thetaM_nn (hz : ∀ t, 0 < z t) (ha : ∀ t, 0 ≤ a t) (hκ : ∀ t, 0 ≤ κ t) (t : T) :
    NN (thetaM z a κ t) := fun m => by
  rw [coeff_thetaM]
  exact iter_nn hz ha hκ _ t m


end FMSA.Convergence.PureFluidMixedPicard

/-- info: 'FMSA.Convergence.PureFluidMixedPicard.nn_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.nn_add
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.nn_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.nn_mul
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.nn_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.nn_C
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.nn_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.nn_one
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.nn_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.nn_X
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.nn_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.nn_pow
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.degree_lt_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.degree_lt_of_mem
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.eqBelow_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.eqBelow_mul
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.eqBelow_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.eqBelow_refl
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.eqBelow_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.eqBelow_pow
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.eqBelow_X_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.eqBelow_X_mul
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.eqBelow_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.eqBelow_inv
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.nn_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.nn_inv
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.eqBelow_finsupp_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.eqBelow_finsupp_prod
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.nn_finsupp_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.nn_finsupp_prod
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.eqBelow_subst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.eqBelow_subst
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.nn_subst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.nn_subst
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.RSeries_constantCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.RSeries_constantCoeff
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.RSeries_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.RSeries_nn
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.subst_constantCoeff_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.subst_constantCoeff_zero
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.pic_constantCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.pic_constantCoeff
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.iter_constantCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.iter_constantCoeff
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.pic_eqBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.pic_eqBelow
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.iter_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.iter_step
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.iter_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.iter_stable
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.coeff_thetaM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.coeff_thetaM
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.thetaM_eqBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.thetaM_eqBelow
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.thetaM_constantCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.thetaM_constantCoeff
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.thetaM_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.thetaM_fixed
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.pic_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.pic_nn
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.iter_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.iter_nn
/-- info: 'FMSA.Convergence.PureFluidMixedPicard.thetaM_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedPicard.thetaM_nn
