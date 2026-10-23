import Mathlib

/-! Absolutely monotone functions on open real sets: all iterated derivatives
are nonnegative. Reciprocals `(d - u)⁻¹` on `u < d` are absolutely monotone, the
class is closed under products and nonnegative scalars, and Faà di Bruno's
formula transports it through an autonomous ODE `v' = h (v)` and through
composition. These give all-order Taylor-coefficient signs without any series
inversion theorem. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace FMSA.Paper.AbsolutelyMonotone

/-- Smooth on an open set with every iterated derivative nonnegative there. -/
def AbsMonoOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ContDiffOn ℝ ∞ f S ∧ ∀ n : ℕ, ∀ x ∈ S, 0 ≤ iteratedDeriv n f x

theorem contDiffAt_of_contDiffOn {f : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) {x : ℝ} (hx : x ∈ S) (n : ℕ) : ContDiffAt ℝ n f x :=
  ((hf.contDiffAt (hS.mem_nhds hx)).of_le (by exact_mod_cast le_top))

theorem prod_range_neg_one_sub (k : ℕ) :
    (-1 : ℝ) ^ k * ∏ i ∈ Finset.range k, ((-1 : ℝ) - i) = k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, pow_succ, Nat.factorial_succ]
    push_cast
    calc (-1 : ℝ) ^ k * (-1) * ((∏ i ∈ Finset.range k, ((-1 : ℝ) - i)) * (-1 - k))
        = ((-1 : ℝ) ^ k * ∏ i ∈ Finset.range k, ((-1 : ℝ) - i)) * (k + 1) := by ring
      _ = _ := by rw [ih]; ring

theorem iteratedDeriv_inv_sub (d : ℝ) (k : ℕ) (u : ℝ) :
    iteratedDeriv k (fun x => (d - x)⁻¹) u = k.factorial * (d - u) ^ (-1 - (k : ℤ)) := by
  have h1 : (fun x : ℝ => (d - x)⁻¹) = fun x => (fun y : ℝ => y ^ (-1 : ℤ)) (d - x) := by
    funext x; simp
  have h2 := congrFun (iteratedDeriv_comp_const_sub (n := k)
    (f := fun y : ℝ => y ^ (-1 : ℤ)) (s := d)) u
  rw [h1, h2]
  simp only [smul_eq_mul]
  rw [iteratedDeriv_eq_iterate, iter_deriv_zpow]
  push_cast
  rw [← mul_assoc, prod_range_neg_one_sub]

theorem inv_sub_absMono (d : ℝ) : AbsMonoOn (fun x => (d - x)⁻¹) (Iio d) := by
  constructor
  · intro x hx
    apply ContDiffAt.contDiffWithinAt
    apply ContDiffAt.inv (contDiffAt_const.sub contDiffAt_id)
    exact sub_ne_zero.mpr (ne_of_gt hx)
  · intro n x hx
    rw [iteratedDeriv_inv_sub]
    have : 0 < d - x := sub_pos.mpr hx
    positivity

theorem AbsMonoOn.mono {f : ℝ → ℝ} {S T : Set ℝ} (hf : AbsMonoOn f S) (hTS : T ⊆ S) :
    AbsMonoOn f T :=
  ⟨hf.1.mono hTS, fun n x hx => hf.2 n x (hTS hx)⟩

theorem AbsMonoOn.mul {f g : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hf : AbsMonoOn f S) (hg : AbsMonoOn g S) : AbsMonoOn (fun x => f x * g x) S := by
  refine ⟨hf.1.mul hg.1, fun n x hx => ?_⟩
  rw [iteratedDeriv_fun_mul (contDiffAt_of_contDiffOn hS hf.1 hx n)
    (contDiffAt_of_contDiffOn hS hg.1 hx n)]
  apply Finset.sum_nonneg
  intro i _
  have := hf.2 i x hx
  have := hg.2 (n - i) x hx
  positivity

theorem AbsMonoOn.const_mul {f : ℝ → ℝ} {S : Set ℝ} (hf : AbsMonoOn f S) (c : ℝ)
    (hc : 0 ≤ c) : AbsMonoOn (fun x => c * f x) S := by
  refine ⟨contDiffOn_const.mul hf.1, fun n x hx => ?_⟩
  rw [iteratedDeriv_const_mul_field]
  exact mul_nonneg hc (hf.2 n x hx)

/-- Faà di Bruno with signs: if every derivative of order at least one of `v`
is nonnegative at `t`, and every derivative of `g` of order at least one has
the sign of `s` at `v t`, then so does every derivative of `g ∘ v` of order at
least one at `t`. -/
theorem comp_signed (g v : ℝ → ℝ) (t : ℝ) (s : ℝ)
    (hg : ∀ n : ℕ, ContDiffAt ℝ n g (v t)) (hv : ∀ n : ℕ, ContDiffAt ℝ n v t)
    (hgs : ∀ k : ℕ, 0 < k → 0 ≤ s * iteratedDeriv k g (v t))
    (hvs : ∀ k : ℕ, 0 < k → 0 ≤ iteratedDeriv k v t)
    (n : ℕ) (hn : 0 < n) : 0 ≤ s * iteratedDeriv n (g ∘ v) t := by
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition (hg n) (hv n) le_rfl, Finset.mul_sum]
  apply Finset.sum_nonneg
  intro c _
  rw [← mul_assoc]
  apply mul_nonneg (hgs _ (c.length_pos hn))
  exact Finset.prod_nonneg (fun j _ => hvs _ (c.partSize_pos j))

/-- An autonomous ODE `v' = h ∘ v` with absolutely monotone `h` makes every
derivative of `v` of order at least one nonnegative. -/
theorem iteratedDeriv_nonneg_of_ode (v h : ℝ → ℝ) (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (hv : ContDiffOn ℝ ∞ v I) (hh : AbsMonoOn h J) (hmaps : MapsTo v I J)
    (hode : ∀ t ∈ I, deriv v t = h (v t)) :
    ∀ n : ℕ, ∀ t ∈ I, 0 ≤ iteratedDeriv (n + 1) v t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t ht
    have heq : deriv v =ᶠ[𝓝 t] h ∘ v := by
      filter_upwards [hI.mem_nhds ht] with y hy
      exact hode y hy
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq]
    rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
      (contDiffAt_of_contDiffOn hJ hh.1 (hmaps ht) n)
      (contDiffAt_of_contDiffOn hI hv ht n) le_rfl]
    apply Finset.sum_nonneg
    intro c _
    apply mul_nonneg (hh.2 _ _ (hmaps ht))
    apply Finset.prod_nonneg
    intro j _
    have hpos := c.partSize_pos j
    have hle := c.partSize_le j
    obtain ⟨m, hm⟩ : ∃ m, c.partSize j = m + 1 := ⟨c.partSize j - 1, by omega⟩
    rw [hm]
    exact ih m (by omega) t ht

end FMSA.Paper.AbsolutelyMonotone

/-- info: 'FMSA.Paper.AbsolutelyMonotone.contDiffAt_of_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AbsolutelyMonotone.contDiffAt_of_contDiffOn

/-- info: 'FMSA.Paper.AbsolutelyMonotone.prod_range_neg_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AbsolutelyMonotone.prod_range_neg_one_sub

/-- info: 'FMSA.Paper.AbsolutelyMonotone.iteratedDeriv_inv_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AbsolutelyMonotone.iteratedDeriv_inv_sub

/-- info: 'FMSA.Paper.AbsolutelyMonotone.inv_sub_absMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AbsolutelyMonotone.inv_sub_absMono

/-- info: 'FMSA.Paper.AbsolutelyMonotone.AbsMonoOn.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AbsolutelyMonotone.AbsMonoOn.mono

/-- info: 'FMSA.Paper.AbsolutelyMonotone.AbsMonoOn.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AbsolutelyMonotone.AbsMonoOn.mul

/-- info: 'FMSA.Paper.AbsolutelyMonotone.AbsMonoOn.const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AbsolutelyMonotone.AbsMonoOn.const_mul

/-- info: 'FMSA.Paper.AbsolutelyMonotone.comp_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AbsolutelyMonotone.comp_signed

/-- info: 'FMSA.Paper.AbsolutelyMonotone.iteratedDeriv_nonneg_of_ode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.AbsolutelyMonotone.iteratedDeriv_nonneg_of_ode
