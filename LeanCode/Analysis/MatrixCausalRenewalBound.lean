import LeanCode.Analysis.CausalRenewalBound

/-! An explicit entry-sum majorant for actual matrix causal renewal. The
entry norm is unchanged by transposition, so one budget controls both sides. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators
namespace FMSA
variable {N : ℕ}

def matrixAbsSum (M : Matrix (Fin N) (Fin N) ℝ) : ℝ := ∑ i, ∑ j, |M i j|

theorem matrixAbsSum_nonneg (M : Matrix (Fin N) (Fin N) ℝ) : 0 ≤ matrixAbsSum M := by
  unfold matrixAbsSum
  positivity

theorem matrixAbsSum_transpose (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixAbsSum M.transpose=matrixAbsSum M := by
  unfold matrixAbsSum
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

theorem matrixAbsSum_entry_le (M : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    |M i j| ≤ matrixAbsSum M := by
  have hrow : |M i j| ≤ ∑ j, |M i j| := Finset.single_le_sum (f := fun j : Fin N => |M i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  exact hrow.trans (Finset.single_le_sum (f := fun i : Fin N => ∑ j, |M i j|) (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i))

theorem matrixAbsSum_continuous (M : ℝ → Matrix (Fin N) (Fin N) ℝ) (hM : Continuous M) :
    Continuous (fun r => matrixAbsSum (M r)) :=
  continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => (hM.matrix_elem i j).abs))

theorem matrixAbsSum_product_majorant (Q Y : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, ∑ m, |Q i m| *|Y m j|) ≤ matrixAbsSum Q*matrixAbsSum Y := by
  have hrow (m : Fin N) : (∑ j, |Y m j|) ≤ matrixAbsSum Y :=
    Finset.single_le_sum (f := fun m : Fin N => ∑ j, |Y m j|) (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ m)
  calc
    _ = ∑ i, ∑ m, |Q i m| *(∑ j, |Y m j|) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ i, ∑ m, |Q i m| *matrixAbsSum Y := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro m _
      exact mul_le_mul_of_nonneg_left (hrow m) (abs_nonneg _)
    _ = _ := by simp only [matrixAbsSum, Finset.sum_mul]

theorem matrixRenewal_absSum_norm_inequality (q f y : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hq : Continuous q) (hy : Continuous y)
    (heq : ∀ i j r, 0 ≤ r → y r i j=f r i j+∑ m, ∫ t in (0 : ℝ)..r, q (r-t) i m*y t m j)
    (r : ℝ) (hr : 0 ≤ r) :
    |matrixAbsSum (y r)| ≤ |matrixAbsSum (f r)|+
      |∫ t in (0 : ℝ)..r, matrixAbsSum (q (r-t))*matrixAbsSum (y t)| := by
  let v := fun (i j m : Fin N) (t : ℝ) => |q (r-t) i m| *|y t m j|
  have hc (i j m : Fin N) : Continuous (v i j m) :=
    (((hq.matrix_elem i m).comp (continuous_const.sub continuous_id)).abs).mul (hy.matrix_elem m j).abs
  have hab (i j : Fin N) : |y r i j| ≤ |f r i j|+∑ m, ∫ t in (0 : ℝ)..r, v i j m t := by
    rw [heq i j r hr]
    apply (abs_add_le _ _).trans
    apply add_le_add (le_refl _)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro m _
    simpa only [Real.norm_eq_abs, abs_mul] using
      (intervalIntegral.norm_integral_le_integral_norm (f := fun t => q (r-t) i m*y t m j) hr)
  have he : (∑ i, ∑ j, ∑ m, ∫ t in (0 : ℝ)..r, v i j m t) =
      ∫ t in (0 : ℝ)..r, ∑ i, ∑ j, ∑ m, v i j m t := by
    rw [intervalIntegral.integral_finsetSum (fun i _ =>
      (continuous_finsetSum _ (fun j _ => continuous_finsetSum _ (fun m _ => hc i j m))).intervalIntegrable (μ := volume) 0 r)]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
      (continuous_finsetSum _ (fun m _ => hc i j m)).intervalIntegrable (μ := volume) 0 r)]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_finsetSum (fun m _ => (hc i j m).intervalIntegrable (μ := volume) 0 r)]
  have hm : (∫ t in (0 : ℝ)..r, ∑ i, ∑ j, ∑ m, v i j m t) ≤
      ∫ t in (0 : ℝ)..r, matrixAbsSum (q (r-t))*matrixAbsSum (y t) := by
    apply intervalIntegral.integral_mono_on hr
      ((continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        continuous_finsetSum _ (fun m _ => hc i j m)))).intervalIntegrable (μ := volume) 0 r)
      ((((matrixAbsSum_continuous q hq).comp (continuous_const.sub continuous_id)).mul
        (matrixAbsSum_continuous y hy)).intervalIntegrable (μ := volume) 0 r)
    intro t _
    exact matrixAbsSum_product_majorant _ _
  calc
    _ = matrixAbsSum (y r) := abs_of_nonneg (matrixAbsSum_nonneg _)
    _ ≤ matrixAbsSum (f r)+(∑ i, ∑ j, ∑ m, ∫ t in (0 : ℝ)..r, v i j m t) := by
      unfold matrixAbsSum
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hab i j
    _ ≤ matrixAbsSum (f r)+∫ t in (0 : ℝ)..r, matrixAbsSum (q (r-t))*matrixAbsSum (y t) := by
      rw [he]
      exact add_le_add (le_refl _) hm
    _ ≤ _ := add_le_add (le_abs_self _) (le_abs_self _)

theorem matrixRenewal_weighted_absSum_bound (q f y : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hq : Continuous q) (hy : Continuous y) (δ A B : ℝ)
    (hkernel : IntegrableOn (fun t => exp (δ*t)*matrixAbsSum (q t)) (Ioi 0))
    (hmass : (∫ t in Ioi (0 : ℝ), exp (δ*t)*matrixAbsSum (q t)) ≤ A)
    (hA : A < 1) (hB : 0 ≤ B)
    (hf : ∀ r, 0 ≤ r → exp (δ*r)*matrixAbsSum (f r) ≤ B)
    (heq : ∀ i j r, 0 ≤ r → y r i j=f r i j+∑ m, ∫ t in (0 : ℝ)..r, q (r-t) i m*y t m j)
    (r : ℝ) (hr : 0 ≤ r) : exp (δ*r)*matrixAbsSum (y r) ≤ B/(1-A) := by
  have habs : ∀ t, |matrixAbsSum (q t)|=matrixAbsSum (q t) := fun _ => abs_of_nonneg (matrixAbsSum_nonneg _)
  have h := causal_renewal_weighted_bound_of_norm_inequality
    (matrixAbsSum_continuous q hq).continuousOn (matrixAbsSum_continuous y hy).continuousOn
    (by simpa only [habs] using hkernel) (by simpa only [habs] using hmass) hA hB
    (fun t ht => by simpa only [abs_of_nonneg (matrixAbsSum_nonneg _)] using hf t ht)
    (matrixRenewal_absSum_norm_inequality q f y hq hy heq) hr
  simpa only [abs_of_nonneg (matrixAbsSum_nonneg _)] using h

theorem matrixRenewal_entry_integrable_of_weighted_budget (q f y : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hq : Continuous q) (hy : Continuous y) (δ A B : ℝ) (hδ : 0 < δ)
    (hkernel : IntegrableOn (fun t => exp (δ*t)*matrixAbsSum (q t)) (Ioi 0))
    (hmass : (∫ t in Ioi (0 : ℝ), exp (δ*t)*matrixAbsSum (q t)) ≤ A)
    (hA : A < 1) (hB : 0 ≤ B)
    (hf : ∀ r, 0 ≤ r → exp (δ*r)*matrixAbsSum (f r) ≤ B)
    (heq : ∀ i j r, 0 ≤ r → y r i j=f r i j+∑ m, ∫ t in (0 : ℝ)..r, q (r-t) i m*y t m j)
    (i j : Fin N) : IntegrableOn (fun r => y r i j) (Ioi 0) := by
  have hi : IntegrableOn (fun t => (B/(1-A))*exp (-δ*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -δ < 0) 0).const_mul _
  apply hi.mono' (hy.matrix_elem i j).measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  have hb := matrixRenewal_weighted_absSum_bound q f y hq hy δ A B hkernel hmass hA hB hf heq t ht.le
  have he : exp (δ*t)*exp (-δ*t)=1 := by rw [← exp_add]; simp
  calc
    |y t i j| ≤ matrixAbsSum (y t) := matrixAbsSum_entry_le _ i j
    _ = (exp (δ*t)*matrixAbsSum (y t))*exp (-δ*t) := by linear_combination -matrixAbsSum (y t)*he
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (exp_pos _).le

end FMSA
