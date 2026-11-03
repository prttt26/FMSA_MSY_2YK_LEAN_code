import MSAConvergence.PureFluidRPartialFraction
import MSAConvergence.PureFluidRKernelIntegral
import Mathlib.Topology.Algebra.Module.Cardinality

set_option linter.style.header false

/-! Add the external positive node x to a finite rate family, then
transfer divided-difference positivity to the rational W weight. -/
noncomputable section
namespace FMSA.Convergence.PureFluidRWeightPositivity
open FMSA.Convergence.PureFluidRPartialFraction
open FMSA.Convergence.PureFluidRKernelIntegral
variable {ι : Type*} [DecidableEq ι]

def extendedNodes (s : Finset ι) : Finset (Option ι) :=
  insert none (s.image some)

def extendedRate (x : ℝ) (z : ι → ℝ) : Option ι → ℝ
  | none => x
  | some i => z i

/-- A positive rate x distinct from all old nodes produces a positive,
distinct family with at least two nodes. -/
theorem extendedNodes_admissible
    (s : Finset ι) (z : ι → ℝ) (x : ℝ)
    (hs : s.Nonempty) (hx : 0 < x)
    (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s)
    (hxn : ∀ i ∈ s, x ≠ z i) :
    2 ≤ (extendedNodes s).card ∧
    (∀ o ∈ extendedNodes s, 0 < extendedRate x z o) ∧
    Set.InjOn (extendedRate x z) (extendedNodes s) := by
  classical
  have hnone : (none : Option ι) ∉ s.image some := by simp
  constructor
  · rw [extendedNodes, Finset.card_insert_of_notMem hnone,
      Finset.card_image_of_injective _ (Option.some_injective ι)]
    exact Nat.succ_le_succ (Finset.Nonempty.card_pos hs)
  constructor
  · intro o ho
    rcases Finset.mem_insert.mp ho with (h0 | hi)
    · subst o
      exact hx
    · obtain ⟨i, his, rfl⟩ := Finset.mem_image.mp hi
      exact hz i his
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with (ha0 | ha1) <;>
      rcases Finset.mem_insert.mp hb with (hb0 | hb1)
    · exact ha0.trans hb0.symm
    · subst a
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb1
      exact False.elim (hxn j hj hab)
    · subst b
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha1
      exact False.elim (hxn i hi hab.symm)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha1
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb1
      exact congrArg some (hzinj hi hj hab)

/-- Expanding the symmetric divided difference at the new node gives
the expression obtained independently from the rational W weight. -/
theorem extended_A_eq_expanded
    (s : Finset ι) (z : ι → ℝ) (x : ℝ) :
    -(∑ o ∈ extendedNodes s, extendedRate x z o *
      ∏ p ∈ (extendedNodes s).erase o,
        (extendedRate x z p ^ 2 - extendedRate x z o ^ 2)⁻¹) =
      -x * (∏ i ∈ s, (z i ^ 2 - x ^ 2))⁻¹ -
        ∑ i ∈ s, z i * (x ^ 2 - z i ^ 2)⁻¹ *
          ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹ := by
  classical
  have hnone : (none : Option ι) ∉ s.image some := by simp
  have hprodNone :
      (∏ p ∈ (extendedNodes s).erase none,
        (extendedRate x z p ^ 2 - x ^ 2)⁻¹) =
        (∏ i ∈ s, (z i ^ 2 - x ^ 2)⁻¹) := by
    rw [extendedNodes, Finset.erase_insert hnone]
    rw [Finset.prod_image]
    · rfl
    · intro a ha b hb hab
      exact Option.some_injective ι hab
  have hprodSome (i : ι) :
      (∏ p ∈ (extendedNodes s).erase (some i),
        (extendedRate x z p ^ 2 - z i ^ 2)⁻¹) =
        (x ^ 2 - z i ^ 2)⁻¹ *
          ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹ := by
    rw [extendedNodes, Finset.erase_insert_of_ne (by simp : (none : Option ι) ≠ some i)]
    rw [← Finset.image_erase (Option.some_injective ι)]
    rw [Finset.prod_insert (by simp)]
    rw [Finset.prod_image]
    · rfl
    · intro a ha b hb hab
      exact Option.some_injective ι hab
  rw [extendedNodes, Finset.sum_insert hnone]
  rw [Finset.sum_image]
  · rw [show insert none (s.image some) = extendedNodes s from rfl]
    change -(x * (∏ p ∈ (extendedNodes s).erase none,
      (extendedRate x z p ^ 2 - x ^ 2)⁻¹) +
      ∑ i ∈ s, z i * (∏ p ∈ (extendedNodes s).erase (some i),
        (extendedRate x z p ^ 2 - z i ^ 2)⁻¹)) = _
    rw [hprodNone]
    simp_rw [hprodSome]
    simp only [← Finset.prod_inv_distrib]
    ring_nf
  · intro a ha b hb hab
    exact Option.some_injective ι hab

/-- The rational core of every squarefree multilinear W weight is
strictly positive for positive pairwise distinct rates. -/
theorem rational_W_core_pos
    (s : Finset ι) (z : ι → ℝ) (x : ℝ)
    (hs : s.Nonempty) (hx : 0 < x)
    (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s)
    (hxn : ∀ i ∈ s, x ≠ z i) :
    0 < ∑ i ∈ s, (x + z i)⁻¹ *
      ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹ := by
  obtain ⟨hcard, hpositive, hinj⟩ :=
    extendedNodes_admissible s z x hs hx hz hzinj hxn
  have hA := divided_difference_A_pos
    (extendedNodes s) (extendedRate x z) hcard hpositive hinj
  rw [extended_A_eq_expanded s z x] at hA
  rw [← rational_W_core_eq_A_expanded s z x hs hx hz hzinj hxn] at hA
  exact hA

/-- Claude's complete squarefree multilinear weight, including every
positive rate and factor of two, is strictly positive. -/
theorem multilinear_W_pos
    (s : Finset ι) (z : ι → ℝ) (x : ℝ)
    (hs : s.Nonempty) (hx : 0 < x)
    (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s)
    (hxn : ∀ i ∈ s, x ≠ z i) :
    0 < ∑ i ∈ s, (z i / (x + z i)) *
      ∏ j ∈ s.erase i, (2 * z j) / (z j ^ 2 - z i ^ 2) := by
  let c : ℝ := 2 ^ (s.card - 1) * ∏ i ∈ s, z i
  have hc : 0 < c := by
    dsimp [c]
    apply mul_pos
    · positivity
    · exact Finset.prod_pos (fun i hi => hz i hi)
  have hterm (i : ι) (hi : i ∈ s) :
      (z i / (x + z i)) *
        (∏ j ∈ s.erase i, (2 * z j) / (z j ^ 2 - z i ^ 2)) =
      c * ((x + z i)⁻¹ *
        ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) := by
    dsimp [c]
    simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem hi]
    rw [← Finset.mul_prod_erase s z hi]
    ring
  rw [show (∑ i ∈ s, (z i / (x + z i)) *
      ∏ j ∈ s.erase i, (2 * z j) / (z j ^ 2 - z i ^ 2)) =
      c * ∑ i ∈ s, (x + z i)⁻¹ *
        ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹ from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hterm]
  exact mul_pos hc (rational_W_core_pos s z x hs hx hz hzinj hxn)

/-- At an evaluation node that coincides with a rate, continuity retains
the nonnegative sign needed for the r-coefficient induction. -/
theorem multilinear_W_nonneg
    (s : Finset ι) (z : ι → ℝ) (x : ℝ)
    (hs : s.Nonempty) (hx : 0 < x)
    (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s) :
    0 ≤ ∑ i ∈ s, (z i / (x + z i)) *
      ∏ j ∈ s.erase i, (2 * z j) / (z j ^ 2 - z i ^ 2) := by
  classical
  let f : ℝ → ℝ := fun y => ∑ i ∈ s,
    (z i / (max y 0 + z i)) *
      ∏ j ∈ s.erase i, (2 * z j) / (z j ^ 2 - z i ^ 2)
  have hf : Continuous f := by
    dsimp [f]
    apply continuous_finsetSum s
    intro i hi
    apply Continuous.mul
    · apply Continuous.div continuous_const
      · exact (continuous_id.max continuous_const).add continuous_const
      · intro y
        exact (add_pos_of_nonneg_of_pos (le_max_right y 0) (hz i hi)).ne'
    · exact continuous_const
  have hdense : Dense ((↑(s.image z) : Set ℝ)ᶜ) :=
    Set.Countable.dense_compl ℝ (s.image z).finite_toSet.countable
  have hclosed : IsClosed {y : ℝ | y ≤ 0 ∨ 0 ≤ f y} :=
    (isClosed_le continuous_id continuous_const).union
      (isClosed_le continuous_const hf)
  have hforall (y : ℝ) (hy : y ∈ (↑(s.image z) : Set ℝ)ᶜ) :
      y ≤ 0 ∨ 0 ≤ f y := by
    by_cases hy0 : y ≤ 0
    · exact Or.inl hy0
    · have hyp : 0 < y := lt_of_not_ge hy0
      right
      have hyn : ∀ i ∈ s, y ≠ z i := by
        intro i hi heq
        exact hy (Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨i, hi, heq.symm⟩))
      have hpos := multilinear_W_pos s z y hs hyp hz hzinj hyn
      simpa [f, max_eq_left hyp.le] using hpos.le
  have hgeneral : x ≤ 0 ∨ 0 ≤ f x :=
    Dense.induction hdense (P := fun y : ℝ => y ≤ 0 ∨ 0 ≤ f y)
      hforall hclosed x
  rcases hgeneral with hnonpos | hnonneg
  · exact False.elim ((not_le_of_gt hx) hnonpos)
  · simpa [f, max_eq_left hx.le] using hnonneg

end FMSA.Convergence.PureFluidRWeightPositivity

/-- info: 'FMSA.Convergence.PureFluidRWeightPositivity.extendedNodes_admissible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightPositivity.extendedNodes_admissible
/-- info: 'FMSA.Convergence.PureFluidRWeightPositivity.extended_A_eq_expanded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightPositivity.extended_A_eq_expanded
/-- info: 'FMSA.Convergence.PureFluidRWeightPositivity.rational_W_core_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightPositivity.rational_W_core_pos
/-- info: 'FMSA.Convergence.PureFluidRWeightPositivity.multilinear_W_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightPositivity.multilinear_W_pos
/-- info: 'FMSA.Convergence.PureFluidRWeightPositivity.multilinear_W_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightPositivity.multilinear_W_nonneg
