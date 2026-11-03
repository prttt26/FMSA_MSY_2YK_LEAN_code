import MSAConvergence.PureFluidRPartialFraction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option linter.style.header false

/-! Elementary positive Cauchy-kernel integrals needed for the
divided-difference representation of pure-fluid r coefficients. -/
noncomputable section
open Real Set MeasureTheory
namespace FMSA.Convergence.PureFluidRKernelIntegral

/-- Rescaling the arctangent integral evaluates the positive-rate
half-line Cauchy kernel. -/
theorem integral_Ioi_inv_sq_add_sq (a : ℝ) (ha : 0 < a) :
    ∫ k in Set.Ioi (0 : ℝ), (k ^ 2 + a ^ 2)⁻¹ = Real.pi / (2 * a) := by
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (fun y : ℝ => (y ^ 2 + a ^ 2)⁻¹) 0 ha
  have hpoint (x : ℝ) : ((a * x) ^ 2 + a ^ 2)⁻¹ =
      a⁻¹ ^ 2 * (1 + x ^ 2)⁻¹ := by
    field_simp [ha.ne']
    ring
  simp_rw [hpoint] at hscale
  rw [MeasureTheory.integral_const_mul] at hscale
  simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero,
    sub_zero, smul_eq_mul] at hscale
  field_simp [ha.ne'] at hscale ⊢
  nlinarith

/-- The scaled Cauchy kernel is integrable on the positive half-line. -/
theorem integrableOn_Ioi_inv_sq_add_sq (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun k : ℝ => (k ^ 2 + a ^ 2)⁻¹) (Set.Ioi 0) := by
  have hbase : IntegrableOn (fun x : ℝ => (1 + x ^ 2)⁻¹) (Set.Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  have hpoint (x : ℝ) : ((a * x) ^ 2 + a ^ 2)⁻¹ =
      a⁻¹ ^ 2 * (1 + x ^ 2)⁻¹ := by
    field_simp [ha.ne']
    ring
  have hscaled : IntegrableOn
      (fun x : ℝ => ((a * x) ^ 2 + a ^ 2)⁻¹) (Set.Ioi 0) := by
    simp_rw [hpoint]
    exact hbase.const_mul _
  simpa only [mul_zero] using
    (integrableOn_Ioi_comp_mul_left_iff
      (fun y : ℝ => (y ^ 2 + a ^ 2)⁻¹) 0 ha).mp hscaled

/-- For at least two distinct positive nodes, the rational kernel
`k² / prod_i (k²+z_i²)` is integrable on the positive half-line. -/
theorem integrableOn_Ioi_squared_rate_kernel
    {ι : Type*}
    (s : Finset ι) (z : ι → ℝ)
    (hs : 2 ≤ s.card) (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s) :
    IntegrableOn
      (fun k : ℝ => k ^ 2 / ∏ i ∈ s, (k ^ 2 + z i ^ 2))
      (Set.Ioi 0) := by
  classical
  have hfun : (fun k : ℝ => k ^ 2 / ∏ i ∈ s, (k ^ 2 + z i ^ 2)) =
      (fun k : ℝ => ∑ i ∈ s, (-z i ^ 2) *
        (∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) *
          (k ^ 2 + z i ^ 2)⁻¹) := by
    funext k
    exact FMSA.Convergence.PureFluidRPartialFraction.squared_rate_partial_fraction
      s z k hs hz hzinj
  rw [hfun]
  apply integrable_finsetSum s
  intro i hi
  exact (integrableOn_Ioi_inv_sq_add_sq (z i) (hz i hi)).const_mul _

/-- Integrating the Lagrange partial fractions gives an exact finite
formula for the rational kernel integral. -/
theorem integral_Ioi_squared_rate_kernel_eq_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℝ)
    (hs : 2 ≤ s.card) (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s) :
    (∫ k in Set.Ioi (0 : ℝ),
      k ^ 2 / ∏ i ∈ s, (k ^ 2 + z i ^ 2)) =
      ∑ i ∈ s, (-z i ^ 2) *
        (∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) *
          (Real.pi / (2 * z i)) := by
  let a (i : ι) : ℝ := (-z i ^ 2) *
    ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹
  have hterm (i : ι) (hi : i ∈ s) : IntegrableOn
      (fun k : ℝ => a i * (k ^ 2 + z i ^ 2)⁻¹) (Set.Ioi 0) :=
    (integrableOn_Ioi_inv_sq_add_sq (z i) (hz i hi)).const_mul _
  calc
    (∫ k in Set.Ioi (0 : ℝ),
      k ^ 2 / ∏ i ∈ s, (k ^ 2 + z i ^ 2)) =
        ∫ k in Set.Ioi (0 : ℝ),
          ∑ i ∈ s, a i * (k ^ 2 + z i ^ 2)⁻¹ := by
            congr 1
            funext k
            exact FMSA.Convergence.PureFluidRPartialFraction.squared_rate_partial_fraction
              s z k hs hz hzinj
    _ = ∑ i ∈ s, ∫ k in Set.Ioi (0 : ℝ),
        a i * (k ^ 2 + z i ^ 2)⁻¹ := by
          exact integral_finsetSum s hterm
    _ = ∑ i ∈ s, (-z i ^ 2) *
        (∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) *
          (Real.pi / (2 * z i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_const_mul, integral_Ioi_inv_sq_add_sq (z i) (hz i hi)]

/-- The rational kernel integral is strictly positive for any finite
family of at least two distinct positive rates. -/
theorem integral_Ioi_squared_rate_kernel_pos
    {ι : Type*}
    (s : Finset ι) (z : ι → ℝ)
    (hs : 2 ≤ s.card) (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s) :
    0 < ∫ k in Set.Ioi (0 : ℝ),
      k ^ 2 / ∏ i ∈ s, (k ^ 2 + z i ^ 2) := by
  classical
  let f : ℝ → ℝ := fun k => k ^ 2 / ∏ i ∈ s, (k ^ 2 + z i ^ 2)
  have hden (k : ℝ) : 0 < ∏ i ∈ s, (k ^ 2 + z i ^ 2) := by
    apply Finset.prod_pos
    intro i hi
    exact add_pos_of_nonneg_of_pos (sq_nonneg k) (sq_pos_of_pos (hz i hi))
  have hf_nonneg : 0 ≤ f := by
    intro k
    exact div_nonneg (sq_nonneg k) (hden k).le
  have hf_cont : Continuous f := by
    dsimp [f]
    apply Continuous.div
    · fun_prop
    · apply continuous_finsetProd s
      intro i hi
      fun_prop
    · intro k
      exact (hden k).ne'
  have hf_int : IntegrableOn f (Set.Ioi 0) :=
    integrableOn_Ioi_squared_rate_kernel s z hs hz hzinj
  have hf_one : f 1 ≠ 0 := ne_of_gt (div_pos (by norm_num) (hden 1))
  have hμ : 0 < volume (Function.support f ∩ Set.Ioi (0 : ℝ)) :=
    (hf_cont.isOpen_support.inter isOpen_Ioi).measure_pos volume
      ⟨1, hf_one, by norm_num⟩
  exact (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall hf_nonneg) hf_int).2 hμ

/-- The symmetric divided difference is exactly the positive rational
kernel integral, with its half-line normalization. -/
theorem divided_difference_A_integral_identity
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℝ)
    (hs : 2 ≤ s.card) (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s) :
    (∫ k in Set.Ioi (0 : ℝ),
      k ^ 2 / ∏ i ∈ s, (k ^ 2 + z i ^ 2)) =
      (Real.pi / 2) *
        (-(∑ i ∈ s, z i *
          ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹)) := by
  have hsum := integral_Ioi_squared_rate_kernel_eq_sum s z hs hz hzinj
  rw [hsum, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [(hz i hi).ne']

/-- The symmetric divided-difference expression from the r-coefficient
formula is strictly positive for distinct positive nodes. -/
theorem divided_difference_A_pos
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℝ)
    (hs : 2 ≤ s.card) (hz : ∀ i ∈ s, 0 < z i)
    (hzinj : Set.InjOn z s) :
    0 < -(∑ i ∈ s, z i *
      ∏ j ∈ s.erase i, (z j ^ 2 - z i ^ 2)⁻¹) := by
  have hpos := integral_Ioi_squared_rate_kernel_pos s z hs hz hzinj
  rw [divided_difference_A_integral_identity s z hs hz hzinj] at hpos
  have hpi : 0 < Real.pi / 2 := by positivity
  exact (mul_pos_iff_of_pos_left hpi).mp hpos

end FMSA.Convergence.PureFluidRKernelIntegral

/-- info: 'FMSA.Convergence.PureFluidRKernelIntegral.integral_Ioi_inv_sq_add_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelIntegral.integral_Ioi_inv_sq_add_sq
/-- info: 'FMSA.Convergence.PureFluidRKernelIntegral.integrableOn_Ioi_inv_sq_add_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelIntegral.integrableOn_Ioi_inv_sq_add_sq
/-- info: 'FMSA.Convergence.PureFluidRKernelIntegral.integrableOn_Ioi_squared_rate_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelIntegral.integrableOn_Ioi_squared_rate_kernel
/-- info: 'FMSA.Convergence.PureFluidRKernelIntegral.integral_Ioi_squared_rate_kernel_eq_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelIntegral.integral_Ioi_squared_rate_kernel_eq_sum
/-- info: 'FMSA.Convergence.PureFluidRKernelIntegral.integral_Ioi_squared_rate_kernel_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelIntegral.integral_Ioi_squared_rate_kernel_pos
/-- info: 'FMSA.Convergence.PureFluidRKernelIntegral.divided_difference_A_integral_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelIntegral.divided_difference_A_integral_identity
/-- info: 'FMSA.Convergence.PureFluidRKernelIntegral.divided_difference_A_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelIntegral.divided_difference_A_pos
