import MSAConvergence.PureFluidRLabelSubstitution

set_option linter.style.header false

/-! Exact positive integral for every repeated formal r coefficient. -/
noncomputable section
open MvPowerSeries Finsupp
namespace FMSA.Convergence.PureFluidRRepeatedKernel
open FMSA.Convergence.PureFluidRLabelSubstitution
open FMSA.Convergence.PureFluidRDistinctRateApprox
open FMSA.Convergence.PureFluidRKernelContinuity
open FMSA.Convergence.PureFluidRSquarefreeGeometric
open FMSA.Convergence.PureFluidRFormalDispersion
variable {T : Type*} [Fintype T] [DecidableEq T]

omit [DecidableEq T] in
theorem card_TailCopies (m : T →₀ ℕ) :
    Fintype.card (TailCopies m) = ∑ t : T, m t := by
  simp [TailCopies, Fintype.card_sigma]

omit [DecidableEq T] in
theorem prod_TailCopies (m : T →₀ ℕ) (g : T → ℝ) :
    (∏ a : TailCopies m, g a.1) =
      ∏ t : T, (g t) ^ (m t) := by
  rw [Fintype.prod_sigma]
  simp

omit [DecidableEq T] in
theorem kernelProduct_copies_eq_repeated
    (m : T →₀ ℕ) (z : T → ℝ) (x k : ℝ) :
    kernelProduct (Finset.univ : Finset (TailCopies m))
      (fun a : TailCopies m => z a.1) x k =
        k ^ 2 / ((k ^ 2 + x ^ 2) *
          ∏ t : T, (k ^ 2 + z t ^ 2) ^ (m t)) := by
  unfold kernelProduct
  rw [prod_TailCopies m (fun t => k ^ 2 + z t ^ 2)]

/-- Exact repeated-index kernel identity, retaining labelled copies
in the finite denominator product. The denominator on the left is
strictly positive, so this also determines the original coefficient. -/
theorem physicalFormalR_repeated_kernel_copy_identity
    (m : T →₀ ℕ) (hm : m ≠ 0)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (x : ℝ) (hx : 0 < x) :
    (∏ t : T, (Nat.factorial (m t) : ℝ)) *
      MvPowerSeries.coeff m (physicalFormalR z x) =
        (Nat.factorial (Fintype.card (TailCopies m)) : ℝ) *
          ((2 ^ (Fintype.card (TailCopies m) - 1) *
              ∏ a : TailCopies m, z a.1) *
            ((2 / Real.pi) *
              (∫ k in Set.Ioi (0 : ℝ),
                kernelProduct
                  (Finset.univ : Finset (TailCopies m))
                  (fun a : TailCopies m => z a.1) x k))) := by
  classical
  let zc : TailCopies m → ℝ := fun a => z a.1
  have hzc : ∀ a : TailCopies m, 0 < zc a := fun a => hz a.1
  obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr hm
  have hmt : 0 < m t := Nat.pos_of_ne_zero
    (Finsupp.mem_support_iff.mp ht)
  have hs : (Finset.univ : Finset (TailCopies m)).Nonempty := by
    exact ⟨⟨t, ⟨0, hmt⟩⟩, Finset.mem_univ _⟩
  have hsplit := congrArg
    (MvPowerSeries.coeff
      (squarefreeMonomial (Finset.univ : Finset (TailCopies m))))
    (split_physicalFormalR_eq_copy m z x)
  rw [coeff_splitTheta_full_squarefree] at hsplit
  have hkernel := physicalFormalR_squarefree_eq_kernel_any_rates
    (Finset.univ : Finset (TailCopies m)) hs zc hzc x hx
  rw [← hsplit] at hkernel
  simpa only [zc, Finset.card_univ] using hkernel

/-- The repeated-index positive-kernel identity in the original
tail labels. Its multinomial coefficient counts all label splittings. -/
theorem physicalFormalR_repeated_kernel_integral
    (m : T →₀ ℕ) (hm : m ≠ 0)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (x : ℝ) (hx : 0 < x) :
    MvPowerSeries.coeff m (physicalFormalR z x) =
      (m.multinomial : ℝ) *
        ((2 ^ ((∑ t : T, m t) - 1) *
            ∏ t : T, (z t) ^ (m t)) *
          ((2 / Real.pi) *
            (∫ k in Set.Ioi (0 : ℝ),
              k ^ 2 / ((k ^ 2 + x ^ 2) *
                ∏ t : T, (k ^ 2 + z t ^ 2) ^ (m t))))) := by
  classical
  have hcopy := physicalFormalR_repeated_kernel_copy_identity
    m hm z hz x hx
  rw [card_TailCopies m,
    prod_TailCopies m z] at hcopy
  simp_rw [kernelProduct_copies_eq_repeated m z x] at hcopy
  have hspecNat :
      (∏ t : T, Nat.factorial (m t)) * m.multinomial =
        Nat.factorial (∑ t : T, m t) := by
    rw [Finsupp.multinomial_eq_of_support_subset
      (Finset.subset_univ _)]
    exact Nat.multinomial_spec Finset.univ m
  have hspec :
      (∏ t : T, (Nat.factorial (m t) : ℝ)) *
        (m.multinomial : ℝ) =
          (Nat.factorial (∑ t : T, m t) : ℝ) := by
    exact_mod_cast hspecNat
  have hfactor : (0 : ℝ) <
      ∏ t : T, (Nat.factorial (m t) : ℝ) := by
    apply Finset.prod_pos
    intro t _
    exact_mod_cast Nat.factorial_pos (m t)
  apply (mul_left_cancel₀ (ne_of_gt hfactor))
  rw [← mul_assoc, hspec]
  exact hcopy

/-- Normalized form of the full repeated-index positive-kernel
formula, with coefficient `multinomial(m) * 2^|m| / π`. -/
theorem physicalFormalR_repeated_kernel_integral_normalized
    (m : T →₀ ℕ) (hm : m ≠ 0)
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (x : ℝ) (hx : 0 < x) :
    MvPowerSeries.coeff m (physicalFormalR z x) =
      (m.multinomial : ℝ) *
        ((2 ^ (∑ t : T, m t) / Real.pi) *
          (∏ t : T, (z t) ^ (m t)) *
            (∫ k in Set.Ioi (0 : ℝ),
              k ^ 2 / ((k ^ 2 + x ^ 2) *
                ∏ t : T, (k ^ 2 + z t ^ 2) ^ (m t)))) := by
  classical
  obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr hm
  have hmt : 0 < m t := Nat.pos_of_ne_zero
    (Finsupp.mem_support_iff.mp ht)
  have hN : 0 < ∑ u : T, m u := by
    exact lt_of_lt_of_le hmt
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
  have hpow : (2 : ℝ) ^ ((∑ u : T, m u) - 1) * 2 =
      2 ^ (∑ u : T, m u) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [physicalFormalR_repeated_kernel_integral m hm z hz x hx]
  calc
    (m.multinomial : ℝ) *
        ((2 ^ ((∑ t : T, m t) - 1) *
            ∏ t : T, (z t) ^ (m t)) *
          ((2 / Real.pi) *
            (∫ k in Set.Ioi (0 : ℝ),
              k ^ 2 / ((k ^ 2 + x ^ 2) *
                ∏ t : T, (k ^ 2 + z t ^ 2) ^ (m t))))) =
      (m.multinomial : ℝ) *
        ((((2 : ℝ) ^ ((∑ t : T, m t) - 1) * 2) / Real.pi) *
          (∏ t : T, (z t) ^ (m t)) *
            (∫ k in Set.Ioi (0 : ℝ),
              k ^ 2 / ((k ^ 2 + x ^ 2) *
                ∏ t : T, (k ^ 2 + z t ^ 2) ^ (m t)))) := by ring
    _ = _ := by rw [hpow]

/-- The independent R-node coefficients have the same repeated
kernel formula evaluated at the node's positive rate. -/
theorem RSeries_repeated_kernel_integral_normalized
    (m : T →₀ ℕ) (hm : m ≠ 0)
    (z : T → ℝ) (hz : ∀ t, 0 < z t) (t : T) :
    MvPowerSeries.coeff m
      (FMSA.Convergence.PureFluidRFormalSolution.RSeries z t) =
      (m.multinomial : ℝ) *
        ((2 ^ (∑ u : T, m u) / Real.pi) *
          (∏ u : T, (z u) ^ (m u)) *
            (∫ k in Set.Ioi (0 : ℝ),
              k ^ 2 / ((k ^ 2 + (z t) ^ 2) *
                ∏ u : T, (k ^ 2 + z u ^ 2) ^ (m u)))) := by
  rw [← physicalFormalR_at_node z t]
  exact physicalFormalR_repeated_kernel_integral_normalized
    m hm z hz (z t) (hz t)

end FMSA.Convergence.PureFluidRRepeatedKernel

/-- info: 'FMSA.Convergence.PureFluidRRepeatedKernel.card_TailCopies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRRepeatedKernel.card_TailCopies
/-- info: 'FMSA.Convergence.PureFluidRRepeatedKernel.prod_TailCopies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRRepeatedKernel.prod_TailCopies
/-- info: 'FMSA.Convergence.PureFluidRRepeatedKernel.kernelProduct_copies_eq_repeated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRRepeatedKernel.kernelProduct_copies_eq_repeated
/-- info: 'FMSA.Convergence.PureFluidRRepeatedKernel.physicalFormalR_repeated_kernel_copy_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRRepeatedKernel.physicalFormalR_repeated_kernel_copy_identity
/-- info: 'FMSA.Convergence.PureFluidRRepeatedKernel.physicalFormalR_repeated_kernel_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRRepeatedKernel.physicalFormalR_repeated_kernel_integral
/-- info: 'FMSA.Convergence.PureFluidRRepeatedKernel.physicalFormalR_repeated_kernel_integral_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRRepeatedKernel.physicalFormalR_repeated_kernel_integral_normalized
/-- info: 'FMSA.Convergence.PureFluidRRepeatedKernel.RSeries_repeated_kernel_integral_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRRepeatedKernel.RSeries_repeated_kernel_integral_normalized
