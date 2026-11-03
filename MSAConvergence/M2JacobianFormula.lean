import MSAConvergence.BHPolynomialJacobian

/-! Literal M2 four-coordinate Jacobian formulas, PROVED from the original
polynomial residual. A symbolic generator supplies candidate expressions only.
No numeric interval, root existence, canonicity or Taylor radius is assumed. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2JacobianFormula
open FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.BHPolynomialJacobian
open FMSA.ExactMSA.Breakpoint MSAMixture
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def z : Fin 2 → ℝ := ![9/5,12]
def rho : Fin 1 → ℝ := fun _ => (3/5)/Real.pi
def sigma : Fin 1 → ℝ := fun _ => 1

/-- Ordered ORIGINAL coordinates: Dt1, Dt2, G1, G2. -/
def index : Fin 4 ≃ AmpIndex (Fin 2) 1 :=
  Equiv.ofBijective (fun i => ![(false,0,0,0),(false,1,0,0),(true,0,0,0),(true,1,0,0)] i)
    (by decide)

def point (x : Fin 4 → ℝ) : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1 :=
  (fun u _ _ => ![x 0,x 1] u, fun u _ _ => ![x 2,x 3] u)

/-- Exact forward four-coordinate encoding, with no float convention. -/
theorem point_coordinates (x : Fin 4 → ℝ) (i : Fin 4) :
    amplitudeValues (point x) (index i) = x i := by
  fin_cases i <;> rfl

/-- The ordered encoding recovers ALL original amplitudes, not just a root. -/
theorem point_coordinates_inverse (a : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1) :
    point (fun i => amplitudeValues a (index i)) = a := by
  apply Prod.ext
  · funext u i j
    fin_cases u <;> fin_cases i <;> fin_cases j <;> rfl
  · funext u i j
    fin_cases u <;> fin_cases i <;> fin_cases j <;> rfl

private lemma hv : vacMix rho sigma = 9/10 := by
  norm_num [vacMix,etaMix,rho,sigma,Fin.sum_univ_one]
private lemma hqp : Q0phys rho sigma 0 0 = 70*Real.pi/27 := by
  simp [Q0phys,hv,xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring
private lemma hqpp : Qppphys rho sigma 0 0 = 80*Real.pi/27 := by
  simp [Qppphys,hv,xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring
private lemma h18 : Real.exp (-(18/5 : ℝ)) = Real.exp (-(9/5 : ℝ))^2 := by
  rw [← Real.exp_nat_mul]
  norm_num
private lemma h69 : Real.exp (-(69/5 : ℝ)) = Real.exp (-(9/5 : ℝ))*Real.exp (-12) := by
  rw [← Real.exp_add]
  norm_num
private lemma h24 : Real.exp (-24) = Real.exp (-12)^2 := by
  rw [← Real.exp_nat_mul]
  norm_num

/-- Exact expanded expressions in the original four coordinates. -/
def formula (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(((7441 : ℝ) / 6561) + (((5150 : ℝ) / 6561) * (Real.exp ((-9 : ℝ) / 5))) + (((-71398 : ℝ) / 177147) * x 0 * (Real.pi ^ 1)⁻¹) + (((-24353 : ℝ) / 78732) * x 1 * (Real.pi ^ 1)⁻¹) + (((-108578 : ℝ) / 531441) * x 0 * x 2 * (Real.pi ^ 1)⁻¹) + (((-88507 : ℝ) / 18108360) * x 1 * x 3 * (Real.pi ^ 1)⁻¹) + (((2809 : ℝ) / 177147) * x 0 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((12655 : ℝ) / 452709) * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((-5618 : ℝ) / 531441) * x 0 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-18 : ℝ) / 5))) + (((-2531 : ℝ) / 905418) * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 39366) * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 787320) * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((49396 : ℝ) / 531441) * x 0 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5)))), ((((-24353 : ℝ) / 78732) * x 0 * (Real.pi ^ 1)⁻¹) + (((-88507 : ℝ) / 18108360) * x 0 * x 3 * (Real.pi ^ 1)⁻¹) + (((12655 : ℝ) / 452709) * x 0 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((-2531 : ℝ) / 905418) * x 0 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 39366) * x 0 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 787320) * x 0 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ)))), ((((-54289 : ℝ) / 531441) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2)) + (((-2809 : ℝ) / 531441) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp ((-18 : ℝ) / 5))) + (((24698 : ℝ) / 531441) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp ((-9 : ℝ) / 5)))), ((((-88507 : ℝ) / 18108360) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((-2531 : ℝ) / 905418) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 39366) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 787320) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))));
      ((((-8849 : ℝ) / 524880) * x 1 * (Real.pi ^ 1)⁻¹) + (((-25853 : ℝ) / 905418) * x 1 * x 2 * (Real.pi ^ 1)⁻¹) + (((72499 : ℝ) / 12072240) * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 18108360) * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 39366) * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 787320) * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5)))), (((2053 : ℝ) / 1944) + (((23 : ℝ) / 1944) * (Real.exp (-12 : ℝ))) + (((-23077 : ℝ) / 233280) * x 1 * (Real.pi ^ 1)⁻¹) + (((-8849 : ℝ) / 524880) * x 0 * (Real.pi ^ 1)⁻¹) + (((-25853 : ℝ) / 905418) * x 0 * x 2 * (Real.pi ^ 1)⁻¹) + (((-12769 : ℝ) / 2332800) * x 1 * x 3 * (Real.pi ^ 1)⁻¹) + (((10201 : ℝ) / 233280) * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((72499 : ℝ) / 12072240) * x 0 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 18108360) * x 0 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-10201 : ℝ) / 2332800) * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-24 : ℝ))) + (((-41 : ℝ) / 39366) * x 0 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 787320) * x 0 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((11413 : ℝ) / 1166400) * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ)))), ((((-25853 : ℝ) / 905418) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((-72499 : ℝ) / 18108360) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 39366) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 787320) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5)))), ((((-12769 : ℝ) / 4665600) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2)) + (((-10201 : ℝ) / 4665600) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-24 : ℝ))) + (((11413 : ℝ) / 2332800) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-12 : ℝ))));
      (((-2809 : ℝ) / 118098) + (((-108578 : ℝ) / 531441) * (x 2 ^ 2)) + (((-24698 : ℝ) / 177147) * x 2) + (((-5618 : ℝ) / 531441) * (x 2 ^ 2) * (Real.exp ((-18 : ℝ) / 5))) + (((5618 : ℝ) / 177147) * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((49396 : ℝ) / 531441) * (x 2 ^ 2) * (Real.exp ((-9 : ℝ) / 5)))), (((-12655 : ℝ) / 150903) + (((-24353 : ℝ) / 39366) * x 2) + (((143 : ℝ) / 13122) * x 3) + (((-88507 : ℝ) / 9054180) * x 2 * x 3) + (((2531 : ℝ) / 301806) * x 3 * (Real.exp (-12 : ℝ))) + (((25310 : ℝ) / 452709) * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((-2531 : ℝ) / 452709) * x 2 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 19683) * x 2 * x 3 * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 393660) * x 2 * x 3 * (Real.exp (-12 : ℝ)))), ((((-24698 : ℝ) / 177147) * x 0) + (((-24353 : ℝ) / 39366) * x 1) + (((14882 : ℝ) / 6561) * Real.pi) + (((-217156 : ℝ) / 531441) * x 0 * x 2) + (((-88507 : ℝ) / 9054180) * x 1 * x 3) + (((5618 : ℝ) / 177147) * x 0 * (Real.exp ((-9 : ℝ) / 5))) + (((10300 : ℝ) / 6561) * Real.pi * (Real.exp ((-9 : ℝ) / 5))) + (((25310 : ℝ) / 452709) * x 1 * (Real.exp ((-9 : ℝ) / 5))) + (((-11236 : ℝ) / 531441) * x 0 * x 2 * (Real.exp ((-18 : ℝ) / 5))) + (((-2531 : ℝ) / 452709) * x 1 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 19683) * x 1 * x 3 * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 393660) * x 1 * x 3 * (Real.exp (-12 : ℝ))) + (((98792 : ℝ) / 531441) * x 0 * x 2 * (Real.exp ((-9 : ℝ) / 5)))), ((((143 : ℝ) / 13122) * x 1) + (((-88507 : ℝ) / 9054180) * x 1 * x 2) + (((2531 : ℝ) / 301806) * x 1 * (Real.exp (-12 : ℝ))) + (((-2531 : ℝ) / 452709) * x 1 * x 2 * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 19683) * x 1 * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 393660) * x 1 * x 2 * (Real.exp (-12 : ℝ))));
      (((-72499 : ℝ) / 603612) + (((-8849 : ℝ) / 262440) * x 3) + (((410 : ℝ) / 19683) * x 2) + (((-25853 : ℝ) / 452709) * x 2 * x 3) + (((72499 : ℝ) / 905418) * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((72499 : ℝ) / 6036120) * x 3 * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 9054180) * x 2 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 19683) * x 2 * x 3 * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 393660) * x 2 * x 3 * (Real.exp ((-9 : ℝ) / 5)))), (((-10201 : ℝ) / 23328) + (((-12769 : ℝ) / 2332800) * (x 3 ^ 2)) + (((-11413 : ℝ) / 116640) * x 3) + (((-10201 : ℝ) / 2332800) * (x 3 ^ 2) * (Real.exp (-24 : ℝ))) + (((10201 : ℝ) / 116640) * x 3 * (Real.exp (-12 : ℝ))) + (((11413 : ℝ) / 1166400) * (x 3 ^ 2) * (Real.exp (-12 : ℝ)))), ((((410 : ℝ) / 19683) * x 0) + (((-25853 : ℝ) / 452709) * x 0 * x 3) + (((72499 : ℝ) / 905418) * x 0 * (Real.exp ((-9 : ℝ) / 5))) + (((-72499 : ℝ) / 9054180) * x 0 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 19683) * x 0 * x 3 * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 393660) * x 0 * x 3 * (Real.exp ((-9 : ℝ) / 5)))), ((((-11413 : ℝ) / 116640) * x 1) + (((-8849 : ℝ) / 262440) * x 0) + (((2053 : ℝ) / 972) * Real.pi) + (((-25853 : ℝ) / 452709) * x 0 * x 2) + (((-12769 : ℝ) / 1166400) * x 1 * x 3) + (((23 : ℝ) / 972) * Real.pi * (Real.exp (-12 : ℝ))) + (((10201 : ℝ) / 116640) * x 1 * (Real.exp (-12 : ℝ))) + (((72499 : ℝ) / 6036120) * x 0 * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 9054180) * x 0 * x 2 * (Real.exp ((-69 : ℝ) / 5))) + (((-10201 : ℝ) / 1166400) * x 1 * x 3 * (Real.exp (-24 : ℝ))) + (((-41 : ℝ) / 19683) * x 0 * x 2 * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 393660) * x 0 * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((11413 : ℝ) / 583200) * x 1 * x 3 * (Real.exp (-12 : ℝ))))]

private theorem entry_0_0 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (false,0,0,0) (false,0,0,0) = (((7441 : ℝ) / 6561) + (((5150 : ℝ) / 6561) * (Real.exp ((-9 : ℝ) / 5))) + (((-71398 : ℝ) / 177147) * x 0 * (Real.pi ^ 1)⁻¹) + (((-24353 : ℝ) / 78732) * x 1 * (Real.pi ^ 1)⁻¹) + (((-108578 : ℝ) / 531441) * x 0 * x 2 * (Real.pi ^ 1)⁻¹) + (((-88507 : ℝ) / 18108360) * x 1 * x 3 * (Real.pi ^ 1)⁻¹) + (((2809 : ℝ) / 177147) * x 0 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((12655 : ℝ) / 452709) * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((-5618 : ℝ) / 531441) * x 0 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-18 : ℝ) / 5))) + (((-2531 : ℝ) / 905418) * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 39366) * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 787320) * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((49396 : ℝ) / 531441) * x 0 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_0_1 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (false,0,0,0) (false,1,0,0) = ((((-24353 : ℝ) / 78732) * x 0 * (Real.pi ^ 1)⁻¹) + (((-88507 : ℝ) / 18108360) * x 0 * x 3 * (Real.pi ^ 1)⁻¹) + (((12655 : ℝ) / 452709) * x 0 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((-2531 : ℝ) / 905418) * x 0 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 39366) * x 0 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 787320) * x 0 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_0_2 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (false,0,0,0) (true,0,0,0) = ((((-54289 : ℝ) / 531441) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2)) + (((-2809 : ℝ) / 531441) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp ((-18 : ℝ) / 5))) + (((24698 : ℝ) / 531441) * (Real.pi ^ 1)⁻¹ * (x 0 ^ 2) * (Real.exp ((-9 : ℝ) / 5)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_0_3 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (false,0,0,0) (true,1,0,0) = ((((-88507 : ℝ) / 18108360) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((-2531 : ℝ) / 905418) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 39366) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 787320) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_1_0 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (false,1,0,0) (false,0,0,0) = ((((-8849 : ℝ) / 524880) * x 1 * (Real.pi ^ 1)⁻¹) + (((-25853 : ℝ) / 905418) * x 1 * x 2 * (Real.pi ^ 1)⁻¹) + (((72499 : ℝ) / 12072240) * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 18108360) * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 39366) * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 787320) * x 1 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_1_1 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (false,1,0,0) (false,1,0,0) = (((2053 : ℝ) / 1944) + (((23 : ℝ) / 1944) * (Real.exp (-12 : ℝ))) + (((-23077 : ℝ) / 233280) * x 1 * (Real.pi ^ 1)⁻¹) + (((-8849 : ℝ) / 524880) * x 0 * (Real.pi ^ 1)⁻¹) + (((-25853 : ℝ) / 905418) * x 0 * x 2 * (Real.pi ^ 1)⁻¹) + (((-12769 : ℝ) / 2332800) * x 1 * x 3 * (Real.pi ^ 1)⁻¹) + (((10201 : ℝ) / 233280) * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((72499 : ℝ) / 12072240) * x 0 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 18108360) * x 0 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-10201 : ℝ) / 2332800) * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-24 : ℝ))) + (((-41 : ℝ) / 39366) * x 0 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 787320) * x 0 * x 2 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5))) + (((11413 : ℝ) / 1166400) * x 1 * x 3 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_1_2 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (false,1,0,0) (true,0,0,0) = ((((-25853 : ℝ) / 905418) * x 0 * x 1 * (Real.pi ^ 1)⁻¹) + (((-72499 : ℝ) / 18108360) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 39366) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 787320) * x 0 * x 1 * (Real.pi ^ 1)⁻¹ * (Real.exp ((-9 : ℝ) / 5)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_1_3 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (false,1,0,0) (true,1,0,0) = ((((-12769 : ℝ) / 4665600) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2)) + (((-10201 : ℝ) / 4665600) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-24 : ℝ))) + (((11413 : ℝ) / 2332800) * (Real.pi ^ 1)⁻¹ * (x 1 ^ 2) * (Real.exp (-12 : ℝ)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_2_0 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (true,0,0,0) (false,0,0,0) = (((-2809 : ℝ) / 118098) + (((-108578 : ℝ) / 531441) * (x 2 ^ 2)) + (((-24698 : ℝ) / 177147) * x 2) + (((-5618 : ℝ) / 531441) * (x 2 ^ 2) * (Real.exp ((-18 : ℝ) / 5))) + (((5618 : ℝ) / 177147) * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((49396 : ℝ) / 531441) * (x 2 ^ 2) * (Real.exp ((-9 : ℝ) / 5)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_2_1 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (true,0,0,0) (false,1,0,0) = (((-12655 : ℝ) / 150903) + (((-24353 : ℝ) / 39366) * x 2) + (((143 : ℝ) / 13122) * x 3) + (((-88507 : ℝ) / 9054180) * x 2 * x 3) + (((2531 : ℝ) / 301806) * x 3 * (Real.exp (-12 : ℝ))) + (((25310 : ℝ) / 452709) * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((-2531 : ℝ) / 452709) * x 2 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 19683) * x 2 * x 3 * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 393660) * x 2 * x 3 * (Real.exp (-12 : ℝ)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_2_2 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (true,0,0,0) (true,0,0,0) = ((((-24698 : ℝ) / 177147) * x 0) + (((-24353 : ℝ) / 39366) * x 1) + (((14882 : ℝ) / 6561) * Real.pi) + (((-217156 : ℝ) / 531441) * x 0 * x 2) + (((-88507 : ℝ) / 9054180) * x 1 * x 3) + (((5618 : ℝ) / 177147) * x 0 * (Real.exp ((-9 : ℝ) / 5))) + (((10300 : ℝ) / 6561) * Real.pi * (Real.exp ((-9 : ℝ) / 5))) + (((25310 : ℝ) / 452709) * x 1 * (Real.exp ((-9 : ℝ) / 5))) + (((-11236 : ℝ) / 531441) * x 0 * x 2 * (Real.exp ((-18 : ℝ) / 5))) + (((-2531 : ℝ) / 452709) * x 1 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 19683) * x 1 * x 3 * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 393660) * x 1 * x 3 * (Real.exp (-12 : ℝ))) + (((98792 : ℝ) / 531441) * x 0 * x 2 * (Real.exp ((-9 : ℝ) / 5)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_2_3 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (true,0,0,0) (true,1,0,0) = ((((143 : ℝ) / 13122) * x 1) + (((-88507 : ℝ) / 9054180) * x 1 * x 2) + (((2531 : ℝ) / 301806) * x 1 * (Real.exp (-12 : ℝ))) + (((-2531 : ℝ) / 452709) * x 1 * x 2 * (Real.exp ((-69 : ℝ) / 5))) + (((-143 : ℝ) / 19683) * x 1 * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((24353 : ℝ) / 393660) * x 1 * x 2 * (Real.exp (-12 : ℝ)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_3_0 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (true,1,0,0) (false,0,0,0) = (((-72499 : ℝ) / 603612) + (((-8849 : ℝ) / 262440) * x 3) + (((410 : ℝ) / 19683) * x 2) + (((-25853 : ℝ) / 452709) * x 2 * x 3) + (((72499 : ℝ) / 905418) * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((72499 : ℝ) / 6036120) * x 3 * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 9054180) * x 2 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 19683) * x 2 * x 3 * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 393660) * x 2 * x 3 * (Real.exp ((-9 : ℝ) / 5)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_3_1 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (true,1,0,0) (false,1,0,0) = (((-10201 : ℝ) / 23328) + (((-12769 : ℝ) / 2332800) * (x 3 ^ 2)) + (((-11413 : ℝ) / 116640) * x 3) + (((-10201 : ℝ) / 2332800) * (x 3 ^ 2) * (Real.exp (-24 : ℝ))) + (((10201 : ℝ) / 116640) * x 3 * (Real.exp (-12 : ℝ))) + (((11413 : ℝ) / 1166400) * (x 3 ^ 2) * (Real.exp (-12 : ℝ)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_3_2 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (true,1,0,0) (true,0,0,0) = ((((410 : ℝ) / 19683) * x 0) + (((-25853 : ℝ) / 452709) * x 0 * x 3) + (((72499 : ℝ) / 905418) * x 0 * (Real.exp ((-9 : ℝ) / 5))) + (((-72499 : ℝ) / 9054180) * x 0 * x 3 * (Real.exp ((-69 : ℝ) / 5))) + (((-41 : ℝ) / 19683) * x 0 * x 3 * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 393660) * x 0 * x 3 * (Real.exp ((-9 : ℝ) / 5)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

private theorem entry_3_3 (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ) :
    jacobian z rho sigma K b (point x) (true,1,0,0) (true,1,0,0) = ((((-11413 : ℝ) / 116640) * x 1) + (((-8849 : ℝ) / 262440) * x 0) + (((2053 : ℝ) / 972) * Real.pi) + (((-25853 : ℝ) / 452709) * x 0 * x 2) + (((-12769 : ℝ) / 1166400) * x 1 * x 3) + (((23 : ℝ) / 972) * Real.pi * (Real.exp (-12 : ℝ))) + (((10201 : ℝ) / 116640) * x 1 * (Real.exp (-12 : ℝ))) + (((72499 : ℝ) / 6036120) * x 0 * (Real.exp (-12 : ℝ))) + (((-72499 : ℝ) / 9054180) * x 0 * x 2 * (Real.exp ((-69 : ℝ) / 5))) + (((-10201 : ℝ) / 1166400) * x 1 * x 3 * (Real.exp (-24 : ℝ))) + (((-41 : ℝ) / 19683) * x 0 * x 2 * (Real.exp (-12 : ℝ))) + (((8849 : ℝ) / 393660) * x 0 * x 2 * (Real.exp ((-9 : ℝ) / 5))) + (((11413 : ℝ) / 583200) * x 1 * x 3 * (Real.exp (-12 : ℝ)))) := by
  norm_num [jacobian,endpointPoly,specializeTime,residualPoly,firstPoly,secondPoly,
    qhatPoly,qpPoly,aPoly,mPoly,nPoly,cPoly,gammaPoly,wPoly,dVar,gVar,tauVar,
    point,amplitudeValues,z,sigMix,edgeLo,edgeHi,hqp,hqpp,hv,
    Fin.sum_univ_two,Fin.sum_univ_one,Pi.single_apply,MvPolynomial.pderiv_C]
  simp only [h18,h69,h24]
  simp [xi2,rho,sigma]
  field_simp [Real.pi_ne_zero]
  ring

/-- ALL 16 symbolic candidates are proved against the literal original
BH polynomial Jacobian. K and coupling are arbitrary; no root or physical
box premise is supplied to this identity. -/
theorem jacobian_formula (x : Fin 4 → ℝ) (K : TailMatrix (Fin 2) 1) (b : ℝ)
    (i j : Fin 4) :
    jacobian z rho sigma K b (point x) (index i) (index j) = formula x i j := by
  fin_cases i <;> fin_cases j
  · exact entry_0_0 x K b
  · exact entry_0_1 x K b
  · exact entry_0_2 x K b
  · exact entry_0_3 x K b
  · exact entry_1_0 x K b
  · exact entry_1_1 x K b
  · exact entry_1_2 x K b
  · exact entry_1_3 x K b
  · exact entry_2_0 x K b
  · exact entry_2_1 x K b
  · exact entry_2_2 x K b
  · exact entry_2_3 x K b
  · exact entry_3_0 x K b
  · exact entry_3_1 x K b
  · exact entry_3_2 x K b
  · exact entry_3_3 x K b

/-- The same formula for EVERY original amplitude point via a proved exact
coordinate inverse. -/
theorem jacobian_formula_actual (a : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1)
    (K : TailMatrix (Fin 2) 1) (b : ℝ) (i j : Fin 4) :
    jacobian z rho sigma K b a (index i) (index j) =
      formula (fun k => amplitudeValues a (index k)) i j := by
  simpa only [point_coordinates_inverse] using
    jacobian_formula (fun k => amplitudeValues a (index k)) K b i j

end FMSA.Convergence.M2JacobianFormula

/-- info: 'FMSA.Convergence.M2JacobianFormula.point_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JacobianFormula.point_coordinates

/-- info: 'FMSA.Convergence.M2JacobianFormula.point_coordinates_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JacobianFormula.point_coordinates_inverse

/-- info: 'FMSA.Convergence.M2JacobianFormula.jacobian_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JacobianFormula.jacobian_formula

/-- info: 'FMSA.Convergence.M2JacobianFormula.jacobian_formula_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JacobianFormula.jacobian_formula_actual
