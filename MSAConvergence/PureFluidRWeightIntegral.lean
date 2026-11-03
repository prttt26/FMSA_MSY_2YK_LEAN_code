import MSAConvergence.PureFluidRWeightOddPart
import MSAConvergence.PureFluidRWeightPositivity
import MSAConvergence.PureFluidRSquarefreePoleSpan

set_option linter.style.header false

/-! The distinct-rate squarefree r weight as an actual positive
half-line kernel integral. -/
noncomputable section
open Real Set MeasureTheory
namespace FMSA.Convergence.PureFluidRWeightIntegral
open FMSA.Convergence.PureFluidRKernelIntegral
open FMSA.Convergence.PureFluidRPartialFraction
open FMSA.Convergence.PureFluidRWeightPositivity
open FMSA.Convergence.PureFluidRWeightOddPart
open FMSA.Convergence.PureFluidRSquarefreeGeometric
open FMSA.Convergence.PureFluidRSquarefreePoleSpan
open FMSA.Convergence.PureFluidRFormalDispersion
variable {T : Type*} [DecidableEq T]

theorem extendedNodes_kernel_prod
    (s : Finset T) (z : T → ℝ) (x k : ℝ) :
    (∏ o ∈ extendedNodes s,
      (k ^ 2 + extendedRate x z o ^ 2)) =
      (k ^ 2 + x ^ 2) * ∏ i ∈ s, (k ^ 2 + z i ^ 2) := by
  classical
  simp [extendedNodes, Finset.prod_image, extendedRate]

theorem rational_W_core_eq_extended_integral
    (s : Finset T) (z : T → ℝ) (x : ℝ)
    (hs : s.Nonempty) (hx : 0 < x)
    (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s)
    (hxn : ∀ i ∈ s, x ≠ z i) :
    (∑ i ∈ s, (x + z i)⁻¹ *
      ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) =
      (2 / Real.pi) *
        (∫ k in Set.Ioi (0 : ℝ),
          k ^ 2 /
            ∏ o ∈ extendedNodes s,
              (k ^ 2 + extendedRate x z o ^ 2)) := by
  obtain ⟨hcard, hpositive, hinj⟩ :=
    extendedNodes_admissible s z x hs hx hz hzinj hxn
  have hA := divided_difference_A_integral_identity
    (extendedNodes s) (extendedRate x z) hcard hpositive hinj
  rw [extended_A_eq_expanded s z x,
    ← rational_W_core_eq_A_expanded s z x hs hx hz hzinj hxn] at hA
  rw [hA]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]

theorem multilinearWeight_eq_extended_integral
    (s : Finset T) (z : T → ℝ) (x : ℝ)
    (hs : s.Nonempty) (hx : 0 < x)
    (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s)
    (hxn : ∀ i ∈ s, x ≠ z i) :
    multilinearWeight s z x =
      (2 ^ (s.card - 1) * ∏ i ∈ s, z i) *
        ((2 / Real.pi) *
          (∫ k in Set.Ioi (0 : ℝ),
            k ^ 2 /
              ∏ o ∈ extendedNodes s,
                (k ^ 2 + extendedRate x z o ^ 2))) := by
  classical
  let c : ℝ := 2 ^ (s.card - 1) * ∏ i ∈ s, z i
  have hterm (i : T) (hi : i ∈ s) :
      (z i / (x + z i)) *
        (∏ j ∈ s.erase i, (2 * z j) / (z j ^ 2 - z i ^ 2)) =
      c * ((x + z i)⁻¹ *
        ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) := by
    dsimp [c]
    simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem hi]
    rw [← Finset.mul_prod_erase s z hi]
    ring
  have hfactor : multilinearWeight s z x =
      c * (∑ i ∈ s, (x + z i)⁻¹ *
        ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) := by
    unfold multilinearWeight
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [hfactor, rational_W_core_eq_extended_integral s z x hs hx hz hzinj hxn]

/-- The actual squarefree formal r coefficient, rather than merely its
candidate weight, equals a positive half-line kernel integral. -/
theorem physicalFormalR_squarefree_eq_extended_integral
    [Fintype T] (s : Finset T) (z : T → ℝ)
    (hz : ∀ t, 0 < z t) (hinj : Set.InjOn z s)
    (hs : s.Nonempty) (x : ℝ) (hx : 0 < x)
    (hxn : ∀ i ∈ s, x ≠ z i) :
    MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x) =
      (Nat.factorial s.card : ℝ) *
        ((2 ^ (s.card - 1) * ∏ i ∈ s, z i) *
          ((2 / Real.pi) *
            (∫ k in Set.Ioi (0 : ℝ),
              k ^ 2 /
                ∏ o ∈ extendedNodes s,
                  (k ^ 2 + extendedRate x z o ^ 2)))) := by
  have hplus : ∀ t ∈ s, x + z t ≠ 0 := by
    intro t _
    exact (add_pos hx (hz t)).ne'
  rw [physicalFormalR_squarefree_eq_weight_all s z hz hinj x hplus]
  rw [multilinearWeight_eq_extended_integral s z x hs hx
    (fun i _ => hz i) hinj hxn]

/-- The same actual squarefree coefficient identity with the external
frequency factor and every selected rate factor displayed explicitly. -/
theorem physicalFormalR_squarefree_eq_kernel_product
    [Fintype T] (s : Finset T) (z : T → ℝ)
    (hz : ∀ t, 0 < z t) (hinj : Set.InjOn z s)
    (hs : s.Nonempty) (x : ℝ) (hx : 0 < x)
    (hxn : ∀ i ∈ s, x ≠ z i) :
    MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x) =
      (Nat.factorial s.card : ℝ) *
        ((2 ^ (s.card - 1) * ∏ i ∈ s, z i) *
          ((2 / Real.pi) *
            (∫ k in Set.Ioi (0 : ℝ),
              k ^ 2 / ((k ^ 2 + x ^ 2) *
                ∏ i ∈ s, (k ^ 2 + z i ^ 2))))) := by
  simpa only [extendedNodes_kernel_prod] using
    physicalFormalR_squarefree_eq_extended_integral
      s z hz hinj hs x hx hxn

end FMSA.Convergence.PureFluidRWeightIntegral

/-- info: 'FMSA.Convergence.PureFluidRWeightIntegral.extendedNodes_kernel_prod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightIntegral.extendedNodes_kernel_prod
/-- info: 'FMSA.Convergence.PureFluidRWeightIntegral.rational_W_core_eq_extended_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightIntegral.rational_W_core_eq_extended_integral
/-- info: 'FMSA.Convergence.PureFluidRWeightIntegral.multilinearWeight_eq_extended_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightIntegral.multilinearWeight_eq_extended_integral
/-- info: 'FMSA.Convergence.PureFluidRWeightIntegral.physicalFormalR_squarefree_eq_extended_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightIntegral.physicalFormalR_squarefree_eq_extended_integral
/-- info: 'FMSA.Convergence.PureFluidRWeightIntegral.physicalFormalR_squarefree_eq_kernel_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRWeightIntegral.physicalFormalR_squarefree_eq_kernel_product
