import MSAConvergence.M2WeightBranch
import MSAConvergence.M2CurvatureCertificate

/-! Proved uniform weight-response approximation bounds. No actual
velocity, inverse or external analytic enclosure is assumed. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2WeightCertificate
open FMSA.Convergence.M2WeightBranch FMSA.Convergence.M2BranchSecondDerivative
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.NewtonBoxExistence
open FMSA.Convergence.RealIntervalCertificates
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def approximateWeightVelocity (y : T) : Fin 4 → ℝ :=
  matrixCLM M2KernelCertificate.preconditioner ((y 4) • weightDerivative)

private theorem approx_bound_0 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |approximateWeightVelocity y 0| ≤ ((1000 : ℝ) / 1) := by
  let v0 : ℝ := ((2563290988475823 : ℝ) / 562949953421312)
  have h0 : ((2563290988475823 : ℝ) / 562949953421312) ≤ v0 ∧ v0 ≤ ((2563290988475823 : ℝ) / 562949953421312) := by constructor <;> norm_num [v0]
  let v1 : ℝ := Real.pi
  have h1 : ((157079632679489661923 : ℝ) / 50000000000000000000) ≤ v1 ∧ v1 ≤ ((314159265358979323847 : ℝ) / 100000000000000000000) := by
    dsimp only [v1]
    constructor <;> linarith [M2PhysicalBounds.pi_interval.1,M2PhysicalBounds.pi_interval.2]
  let v2 : ℝ := v0*v1
  have h2 : ((7152337511947384117171919 : ℝ) / 500000000000000000000000) ≤ v2 ∧ v2 ≤ ((3576168755973692058597343 : ℝ) / 250000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := y 4
  have h3 : ((56135716456019828353704387 : ℝ) / 10000000000000000000000000) ≤ v3 ∧ v3 ≤ ((56135716468569701646295613 : ℝ) / 10000000000000000000000000) := by simpa [v3,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 4
  let v4 : ℝ := v2*v3
  have h4 : ((40150159056843268627048077 : ℝ) / 500000000000000000000000) ≤ v4 ∧ v4 ≤ ((16060063626327744631701827 : ℝ) / 200000000000000000000000) := mul_interval h2 h3 (by norm_num) (by norm_num)
  have he : approximateWeightVelocity y 0 = v4 := by
    simp only [approximateWeightVelocity,matrixCLM_apply,Matrix.mulVec,dotProduct,weightDerivative,Pi.smul_apply,smul_eq_mul,M2KernelCertificate.preconditioner,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h4 (by norm_num) (by norm_num)

private theorem approx_bound_1 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |approximateWeightVelocity y 1| ≤ ((1000 : ℝ) / 1) := by
  let v0 : ℝ := ((-5402920345206155 : ℝ) / 13510798882111488)
  have h0 : ((-5402920345206155 : ℝ) / 13510798882111488) ≤ v0 ∧ v0 ≤ ((-5402920345206155 : ℝ) / 13510798882111488) := by constructor <;> norm_num [v0]
  let v1 : ℝ := Real.pi
  have h1 : ((157079632679489661923 : ℝ) / 50000000000000000000) ≤ v1 ∧ v1 ≤ ((314159265358979323847 : ℝ) / 100000000000000000000) := by
    dsimp only [v1]
    constructor <;> linarith [M2PhysicalBounds.pi_interval.1,M2PhysicalBounds.pi_interval.2]
  let v2 : ℝ := v0*v1
  have h2 : ((-1256311711286298053704233 : ℝ) / 1000000000000000000000000) ≤ v2 ∧ v2 ≤ ((-1256311711286298053700233 : ℝ) / 1000000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := y 4
  have h3 : ((56135716456019828353704387 : ℝ) / 10000000000000000000000000) ≤ v3 ∧ v3 ≤ ((56135716468569701646295613 : ℝ) / 10000000000000000000000000) := by simpa [v3,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 4
  let v4 : ℝ := v2*v3
  have h4 : ((-7052395802091122596626133 : ℝ) / 1000000000000000000000000) ≤ v4 ∧ v4 ≤ ((-881549475064308414667441 : ℝ) / 125000000000000000000000) := mul_interval h2 h3 (by norm_num) (by norm_num)
  have he : approximateWeightVelocity y 1 = v4 := by
    simp only [approximateWeightVelocity,matrixCLM_apply,Matrix.mulVec,dotProduct,weightDerivative,Pi.smul_apply,smul_eq_mul,M2KernelCertificate.preconditioner,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h4 (by norm_num) (by norm_num)

private theorem approx_bound_2 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |approximateWeightVelocity y 2| ≤ ((1000 : ℝ) / 1) := by
  let v0 : ℝ := ((5676625074002731 : ℝ) / 108086391056891904)
  have h0 : ((5676625074002731 : ℝ) / 108086391056891904) ≤ v0 ∧ v0 ≤ ((5676625074002731 : ℝ) / 108086391056891904) := by constructor <;> norm_num [v0]
  let v1 : ℝ := Real.pi
  have h1 : ((157079632679489661923 : ℝ) / 50000000000000000000) ≤ v1 ∧ v1 ≤ ((314159265358979323847 : ℝ) / 100000000000000000000) := by
    dsimp only [v1]
    constructor <;> linarith [M2PhysicalBounds.pi_interval.1,M2PhysicalBounds.pi_interval.2]
  let v2 : ℝ := v0*v1
  have h2 : ((82497174044250184491131 : ℝ) / 500000000000000000000000) ≤ v2 ∧ v2 ≤ ((41248587022125092245697 : ℝ) / 250000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := y 4
  have h3 : ((56135716456019828353704387 : ℝ) / 10000000000000000000000000) ≤ v3 ∧ v3 ≤ ((56135716468569701646295613 : ℝ) / 10000000000000000000000000) := by simpa [v3,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 4
  let v4 : ℝ := v2*v3
  have h4 : ((231551898528547346843319 : ℝ) / 250000000000000000000000) ≤ v4 ∧ v4 ≤ ((463103797160627601813333 : ℝ) / 500000000000000000000000) := mul_interval h2 h3 (by norm_num) (by norm_num)
  have he : approximateWeightVelocity y 2 = v4 := by
    simp only [approximateWeightVelocity,matrixCLM_apply,Matrix.mulVec,dotProduct,weightDerivative,Pi.smul_apply,smul_eq_mul,M2KernelCertificate.preconditioner,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h4 (by norm_num) (by norm_num)

private theorem approx_bound_3 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |approximateWeightVelocity y 3| ≤ ((1000 : ℝ) / 1) := by
  let v0 : ℝ := ((1828646140081387 : ℝ) / 108086391056891904)
  have h0 : ((1828646140081387 : ℝ) / 108086391056891904) ≤ v0 ∧ v0 ≤ ((1828646140081387 : ℝ) / 108086391056891904) := by constructor <;> norm_num [v0]
  let v1 : ℝ := Real.pi
  have h1 : ((157079632679489661923 : ℝ) / 50000000000000000000) ≤ v1 ∧ v1 ≤ ((314159265358979323847 : ℝ) / 100000000000000000000) := by
    dsimp only [v1]
    constructor <;> linarith [M2PhysicalBounds.pi_interval.1,M2PhysicalBounds.pi_interval.2]
  let v2 : ℝ := v0*v1
  have h2 : ((53150643883291246359213 : ℝ) / 1000000000000000000000000) ≤ v2 ∧ v2 ≤ ((53150643883291246359383 : ℝ) / 1000000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := y 4
  have h3 : ((56135716456019828353704387 : ℝ) / 10000000000000000000000000) ≤ v3 ∧ v3 ≤ ((56135716468569701646295613 : ℝ) / 10000000000000000000000000) := by simpa [v3,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 4
  let v4 : ℝ := v2*v3
  have h4 : ((59672989489746441029083 : ℝ) / 200000000000000000000000) ≤ v4 ∧ v4 ≤ ((59672989503087117952373 : ℝ) / 200000000000000000000000) := mul_interval h2 h3 (by norm_num) (by norm_num)
  have he : approximateWeightVelocity y 3 = v4 := by
    simp only [approximateWeightVelocity,matrixCLM_apply,Matrix.mulVec,dotProduct,weightDerivative,Pi.smul_apply,smul_eq_mul,M2KernelCertificate.preconditioner,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h4 (by norm_num) (by norm_num)

/-- Uniform negative bound on the exact preconditioned response.
The true branch derivative is identified and bounded separately. -/
theorem approximate_weight_slope_lt (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    (∑ i, curvatureGradient y i*approximateWeightVelocity y i) < (-20 : ℝ) := by
  let v0 : ℝ := ((-5402920345206155 : ℝ) / 13510798882111488)
  have h0 : ((-5402920345206155 : ℝ) / 13510798882111488) ≤ v0 ∧ v0 ≤ ((-5402920345206155 : ℝ) / 13510798882111488) := by constructor <;> norm_num [v0]
  let v1 : ℝ := Real.pi
  have h1 : ((157079632679489661923 : ℝ) / 50000000000000000000) ≤ v1 ∧ v1 ≤ ((314159265358979323847 : ℝ) / 100000000000000000000) := by
    dsimp only [v1]
    constructor <;> linarith [M2PhysicalBounds.pi_interval.1,M2PhysicalBounds.pi_interval.2]
  let v2 : ℝ := v0*v1
  have h2 : ((-1256311711286298053704233 : ℝ) / 1000000000000000000000000) ≤ v2 ∧ v2 ≤ ((-1256311711286298053700233 : ℝ) / 1000000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := jacobian y 9 7
  have h3 : ((-27740261258299526549517 : ℝ) / 125000000000000000000000) ≤ v3 ∧ v3 ≤ ((-887688360263508957861 : ℝ) / 4000000000000000000000) := by
    simpa [v3,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 7
  let v4 : ℝ := v2*v3
  have h4 : ((278803320742894199887493 : ℝ) / 1000000000000000000000000) ≤ v4 ∧ v4 ≤ ((139401660371773095829647 : ℝ) / 500000000000000000000000) := mul_interval h2 h3 (by norm_num) (by norm_num)
  let v5 : ℝ := y 4
  have h5 : ((56135716456019828353704387 : ℝ) / 10000000000000000000000000) ≤ v5 ∧ v5 ≤ ((56135716468569701646295613 : ℝ) / 10000000000000000000000000) := by simpa [v5,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 4
  let v6 : ℝ := v4*v5
  have h6 : ((782541208010993014627447 : ℝ) / 500000000000000000000000) ≤ v6 ∧ v6 ≤ ((39127060409388516666669 : ℝ) / 25000000000000000000000) := mul_interval h4 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((1828646140081387 : ℝ) / 108086391056891904)
  have h7 : ((1828646140081387 : ℝ) / 108086391056891904) ≤ v7 ∧ v7 ≤ ((1828646140081387 : ℝ) / 108086391056891904) := by constructor <;> norm_num [v7]
  let v8 : ℝ := v7*v1
  have h8 : ((53150643883291246359213 : ℝ) / 1000000000000000000000000) ≤ v8 ∧ v8 ≤ ((53150643883291246359383 : ℝ) / 1000000000000000000000000) := mul_interval h7 h1 (by norm_num) (by norm_num)
  let v9 : ℝ := jacobian y 9 9
  have h9 : ((183107489880450076869 : ℝ) / 6250000000000000000000) ≤ v9 ∧ v9 ≤ ((2929719838736338153881 : ℝ) / 100000000000000000000000) := by
    simpa [v9,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 9
  let v10 : ℝ := v8*v9
  have h10 : ((1557164957919865227071 : ℝ) / 1000000000000000000000000) ≤ v10 ∧ v10 ≤ ((311432991652977136371 : ℝ) / 200000000000000000000000) := mul_interval h8 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := v10*v5
  have h11 : ((1748251411060792039483 : ℝ) / 200000000000000000000000) ≤ v11 ∧ v11 ≤ ((8741257059194979531733 : ℝ) / 1000000000000000000000000) := mul_interval h10 h5 (by norm_num) (by norm_num)
  let v12 : ℝ := v6+v11
  have h12 : ((1573823673077289989452309 : ℝ) / 1000000000000000000000000) ≤ v12 ∧ v12 ≤ ((1573823673434735646198493 : ℝ) / 1000000000000000000000000) := add_interval h6 h11 (by norm_num) (by norm_num)
  let v13 : ℝ := ((2563290988475823 : ℝ) / 562949953421312)
  have h13 : ((2563290988475823 : ℝ) / 562949953421312) ≤ v13 ∧ v13 ≤ ((2563290988475823 : ℝ) / 562949953421312) := by constructor <;> norm_num [v13]
  let v14 : ℝ := v13*v1
  have h14 : ((7152337511947384117171919 : ℝ) / 500000000000000000000000) ≤ v14 ∧ v14 ≤ ((3576168755973692058597343 : ℝ) / 250000000000000000000000) := mul_interval h13 h1 (by norm_num) (by norm_num)
  let v15 : ℝ := jacobian y 9 6
  have h15 : ((-68481857285323689111453 : ℝ) / 250000000000000000000000) ≤ v15 ∧ v15 ≤ ((-273927429117514510828087 : ℝ) / 1000000000000000000000000) := by
    simpa [v15,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 6
  let v16 : ℝ := v14*v15
  have h16 : ((-979610713499295750633713 : ℝ) / 250000000000000000000000) ≤ v16 ∧ v16 ≤ ((-489805356707126789621553 : ℝ) / 125000000000000000000000) := mul_interval h14 h15 (by norm_num) (by norm_num)
  let v17 : ℝ := v16*v5
  have h17 : ((-10998229852513946442292143 : ℝ) / 500000000000000000000000) ≤ v17 ∧ v17 ≤ ((-5499114924550183866099231 : ℝ) / 250000000000000000000000) := mul_interval h16 h5 (by norm_num) (by norm_num)
  let v18 : ℝ := v12+v17
  have h18 : ((-20422636031950602895131977 : ℝ) / 1000000000000000000000000) ≤ v18 ∧ v18 ≤ ((-20422636024765999818198431 : ℝ) / 1000000000000000000000000) := add_interval h12 h17 (by norm_num) (by norm_num)
  let v19 : ℝ := ((5676625074002731 : ℝ) / 108086391056891904)
  have h19 : ((5676625074002731 : ℝ) / 108086391056891904) ≤ v19 ∧ v19 ≤ ((5676625074002731 : ℝ) / 108086391056891904) := by constructor <;> norm_num [v19]
  let v20 : ℝ := v19*v1
  have h20 : ((82497174044250184491131 : ℝ) / 500000000000000000000000) ≤ v20 ∧ v20 ≤ ((41248587022125092245697 : ℝ) / 250000000000000000000000) := mul_interval h19 h1 (by norm_num) (by norm_num)
  let v21 : ℝ := jacobian y 9 8
  have h21 : ((-770981222685690422294011 : ℝ) / 1000000000000000000000000) ≤ v21 ∧ v21 ≤ ((-385490611161663940667689 : ℝ) / 500000000000000000000000) := by
    simpa [v21,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 8
  let v22 : ℝ := v20*v21
  have h22 : ((-12720754422550042284273 : ℝ) / 100000000000000000000000) ≤ v22 ∧ v22 ≤ ((-127207544165712651625161 : ℝ) / 1000000000000000000000000) := mul_interval h20 h21 (by norm_num) (by norm_num)
  let v23 : ℝ := v22*v5
  have h23 : ((-71408866353057327394801 : ℝ) / 100000000000000000000000) ≤ v23 ∧ v23 ≤ ((-89261082879413310062269 : ℝ) / 125000000000000000000000) := mul_interval h22 h5 (by norm_num) (by norm_num)
  let v24 : ℝ := v18+v23
  have h24 : ((-21136724695481176169079987 : ℝ) / 1000000000000000000000000) ≤ v24 ∧ v24 ≤ ((-21136724687801306298696583 : ℝ) / 1000000000000000000000000) := add_interval h18 h23 (by norm_num) (by norm_num)
  have he : (∑ i, curvatureGradient y i*approximateWeightVelocity y i) = v24 := by
    simp only [curvatureGradient,velocityIndex,approximateWeightVelocity,matrixCLM_apply,Matrix.mulVec,dotProduct,weightDerivative,Pi.smul_apply,smul_eq_mul,M2KernelCertificate.preconditioner,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact lt_of_le_of_lt h24.2 (by norm_num)

/-- A genuine Pi-space bound on the preconditioned weight velocity. -/
theorem approximate_weight_velocity_norm (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    ‖approximateWeightVelocity y‖ ≤ (1000 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1000)).mpr
  intro i
  fin_cases i
  · change |approximateWeightVelocity y 0| ≤ (1000 : ℝ)
    simpa only [div_one] using approx_bound_0 y hx
  · change |approximateWeightVelocity y 1| ≤ (1000 : ℝ)
    simpa only [div_one] using approx_bound_1 y hx
  · change |approximateWeightVelocity y 2| ≤ (1000 : ℝ)
    simpa only [div_one] using approx_bound_2 y hx
  · change |approximateWeightVelocity y 3| ≤ (1000 : ℝ)
    simpa only [div_one] using approx_bound_3 y hx

end FMSA.Convergence.M2WeightCertificate

/-- info: 'FMSA.Convergence.M2WeightCertificate.approximate_weight_slope_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2WeightCertificate.approximate_weight_slope_lt

/-- info: 'FMSA.Convergence.M2WeightCertificate.approximate_weight_velocity_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2WeightCertificate.approximate_weight_velocity_norm

