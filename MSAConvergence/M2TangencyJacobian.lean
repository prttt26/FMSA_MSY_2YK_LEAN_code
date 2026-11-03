import MSAConvergence.M2TangencyPolynomials

/-! Every entry of the genuine ten-variable M2 contact Jacobian, proved
from the exact literal polynomials. Symbolic differentiation is not trusted. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2TangencyJacobian
open FMSA.Convergence.M2TangencyPolynomials FMSA.Convergence.NewtonBoxExistence
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def formula (y : Fin 10 → ℝ) : Matrix (Fin 10) (Fin 10) ℝ :=
  !![(((7441 : ℝ)/6561)+(((5150 : ℝ)/6561)*(Real.exp ((-9 : ℝ)/5)))+(((-71398 : ℝ)/177147)*y 0*(Real.pi^1)⁻¹)+(((-24353 : ℝ)/78732)*y 1*(Real.pi^1)⁻¹)+(((-108578 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 1*y 3*(Real.pi^1)⁻¹)+(((2809 : ℝ)/177147)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((12655 : ℝ)/452709)*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-5618 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((49396 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-24353 : ℝ)/78732)*y 0*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 0*y 3*(Real.pi^1)⁻¹)+(((12655 : ℝ)/452709)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),((((-54289 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2))+(((-2809 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2)*(Real.exp ((-18 : ℝ)/5)))+(((24698 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2)*(Real.exp ((-9 : ℝ)/5)))),((((-88507 : ℝ)/18108360)*y 0*y 1*(Real.pi^1)⁻¹)+(((-2531 : ℝ)/905418)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),(((-10 : ℝ)/9)*Real.pi),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ);
    ((((-8849 : ℝ)/524880)*y 1*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 1*y 2*(Real.pi^1)⁻¹)+(((72499 : ℝ)/12072240)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),(((2053 : ℝ)/1944)+(((23 : ℝ)/1944)*(Real.exp (-12 : ℝ)))+(((-23077 : ℝ)/233280)*y 1*(Real.pi^1)⁻¹)+(((-8849 : ℝ)/524880)*y 0*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 0*y 2*(Real.pi^1)⁻¹)+(((-12769 : ℝ)/2332800)*y 1*y 3*(Real.pi^1)⁻¹)+(((10201 : ℝ)/233280)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/12072240)*y 0*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/2332800)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/39366)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/1166400)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),((((-25853 : ℝ)/905418)*y 0*y 1*(Real.pi^1)⁻¹)+(((-72499 : ℝ)/18108360)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-12769 : ℝ)/4665600)*(Real.pi^1)⁻¹*(y 1^2))+(((-10201 : ℝ)/4665600)*(Real.pi^1)⁻¹*(y 1^2)*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/2332800)*(Real.pi^1)⁻¹*(y 1^2)*(Real.exp (-12 : ℝ)))),(((-1 : ℝ)/6)*Real.pi*y 5),(((-1 : ℝ)/6)*Real.pi*y 4),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ);
    (((-2809 : ℝ)/118098)+(((-108578 : ℝ)/531441)*(y 2^2))+(((-24698 : ℝ)/177147)*y 2)+(((-5618 : ℝ)/531441)*(y 2^2)*(Real.exp ((-18 : ℝ)/5)))+(((5618 : ℝ)/177147)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((49396 : ℝ)/531441)*(y 2^2)*(Real.exp ((-9 : ℝ)/5)))),(((-12655 : ℝ)/150903)+(((-24353 : ℝ)/39366)*y 2)+(((143 : ℝ)/13122)*y 3)+(((-88507 : ℝ)/9054180)*y 2*y 3)+(((2531 : ℝ)/301806)*y 3*(Real.exp (-12 : ℝ)))+(((25310 : ℝ)/452709)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 2*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 2*y 3*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 2*y 3*(Real.exp (-12 : ℝ)))),((((-24698 : ℝ)/177147)*y 0)+(((-24353 : ℝ)/39366)*y 1)+(((14882 : ℝ)/6561)*Real.pi)+(((-217156 : ℝ)/531441)*y 0*y 2)+(((-88507 : ℝ)/9054180)*y 1*y 3)+(((5618 : ℝ)/177147)*y 0*(Real.exp ((-9 : ℝ)/5)))+(((10300 : ℝ)/6561)*Real.pi*(Real.exp ((-9 : ℝ)/5)))+(((25310 : ℝ)/452709)*y 1*(Real.exp ((-9 : ℝ)/5)))+(((-11236 : ℝ)/531441)*y 0*y 2*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 1*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 3*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 3*(Real.exp (-12 : ℝ)))+(((98792 : ℝ)/531441)*y 0*y 2*(Real.exp ((-9 : ℝ)/5)))),((((143 : ℝ)/13122)*y 1)+(((-88507 : ℝ)/9054180)*y 1*y 2)+(((2531 : ℝ)/301806)*y 1*(Real.exp (-12 : ℝ)))+(((-2531 : ℝ)/452709)*y 1*y 2*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 2*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 2*(Real.exp (-12 : ℝ)))),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ);
    (((-72499 : ℝ)/603612)+(((-8849 : ℝ)/262440)*y 3)+(((410 : ℝ)/19683)*y 2)+(((-25853 : ℝ)/452709)*y 2*y 3)+(((72499 : ℝ)/905418)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((72499 : ℝ)/6036120)*y 3*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 2*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 2*y 3*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 2*y 3*(Real.exp ((-9 : ℝ)/5)))),(((-10201 : ℝ)/23328)+(((-12769 : ℝ)/2332800)*(y 3^2))+(((-11413 : ℝ)/116640)*y 3)+(((-10201 : ℝ)/2332800)*(y 3^2)*(Real.exp (-24 : ℝ)))+(((10201 : ℝ)/116640)*y 3*(Real.exp (-12 : ℝ)))+(((11413 : ℝ)/1166400)*(y 3^2)*(Real.exp (-12 : ℝ)))),((((410 : ℝ)/19683)*y 0)+(((-25853 : ℝ)/452709)*y 0*y 3)+(((72499 : ℝ)/905418)*y 0*(Real.exp ((-9 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 0*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 0*y 3*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 3*(Real.exp ((-9 : ℝ)/5)))),((((-11413 : ℝ)/116640)*y 1)+(((-8849 : ℝ)/262440)*y 0)+(((2053 : ℝ)/972)*Real.pi)+(((-25853 : ℝ)/452709)*y 0*y 2)+(((-12769 : ℝ)/1166400)*y 1*y 3)+(((23 : ℝ)/972)*Real.pi*(Real.exp (-12 : ℝ)))+(((10201 : ℝ)/116640)*y 1*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/6036120)*y 0*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 0*y 2*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/1166400)*y 1*y 3*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/19683)*y 0*y 2*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 2*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/583200)*y 1*y 3*(Real.exp (-12 : ℝ)))),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ);
    ((((-71398 : ℝ)/177147)*y 6*(Real.pi^1)⁻¹)+(((-24353 : ℝ)/78732)*y 7*(Real.pi^1)⁻¹)+(((-108578 : ℝ)/531441)*y 0*y 8*(Real.pi^1)⁻¹)+(((-108578 : ℝ)/531441)*y 2*y 6*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 1*y 9*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 3*y 7*(Real.pi^1)⁻¹)+(((2809 : ℝ)/177147)*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((12655 : ℝ)/452709)*y 7*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-5618 : ℝ)/531441)*y 0*y 8*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((-5618 : ℝ)/531441)*y 2*y 6*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 1*y 9*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 3*y 7*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 1*y 9*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 3*y 7*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 1*y 9*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/787320)*y 3*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((49396 : ℝ)/531441)*y 0*y 8*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((49396 : ℝ)/531441)*y 2*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-24353 : ℝ)/78732)*y 6*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 0*y 9*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 3*y 6*(Real.pi^1)⁻¹)+(((12655 : ℝ)/452709)*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 0*y 9*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 3*y 6*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 9*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 3*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 9*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/787320)*y 3*y 6*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),((((-108578 : ℝ)/531441)*y 0*y 6*(Real.pi^1)⁻¹)+(((-5618 : ℝ)/531441)*y 0*y 6*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((49396 : ℝ)/531441)*y 0*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-88507 : ℝ)/18108360)*y 0*y 7*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 1*y 6*(Real.pi^1)⁻¹)+(((-2531 : ℝ)/905418)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/787320)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),(0 : ℝ),(0 : ℝ),(((7441 : ℝ)/6561)+(((5150 : ℝ)/6561)*(Real.exp ((-9 : ℝ)/5)))+(((-71398 : ℝ)/177147)*y 0*(Real.pi^1)⁻¹)+(((-24353 : ℝ)/78732)*y 1*(Real.pi^1)⁻¹)+(((-108578 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 1*y 3*(Real.pi^1)⁻¹)+(((2809 : ℝ)/177147)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((12655 : ℝ)/452709)*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-5618 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((49396 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-24353 : ℝ)/78732)*y 0*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 0*y 3*(Real.pi^1)⁻¹)+(((12655 : ℝ)/452709)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),((((-54289 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2))+(((-2809 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2)*(Real.exp ((-18 : ℝ)/5)))+(((24698 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2)*(Real.exp ((-9 : ℝ)/5)))),((((-88507 : ℝ)/18108360)*y 0*y 1*(Real.pi^1)⁻¹)+(((-2531 : ℝ)/905418)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))));
    ((((-8849 : ℝ)/524880)*y 7*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 1*y 8*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 2*y 7*(Real.pi^1)⁻¹)+(((72499 : ℝ)/12072240)*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 1*y 8*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/18108360)*y 2*y 7*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 1*y 8*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/39366)*y 2*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 1*y 8*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/787320)*y 2*y 7*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-23077 : ℝ)/233280)*y 7*(Real.pi^1)⁻¹)+(((-8849 : ℝ)/524880)*y 6*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 0*y 8*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 2*y 6*(Real.pi^1)⁻¹)+(((-12769 : ℝ)/2332800)*y 1*y 9*(Real.pi^1)⁻¹)+(((-12769 : ℝ)/2332800)*y 3*y 7*(Real.pi^1)⁻¹)+(((10201 : ℝ)/233280)*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/12072240)*y 6*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 0*y 8*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/18108360)*y 2*y 6*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/2332800)*y 1*y 9*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((-10201 : ℝ)/2332800)*y 3*y 7*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/39366)*y 0*y 8*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/39366)*y 2*y 6*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 8*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/787320)*y 2*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/1166400)*y 1*y 9*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((11413 : ℝ)/1166400)*y 3*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),((((-25853 : ℝ)/905418)*y 0*y 7*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 1*y 6*(Real.pi^1)⁻¹)+(((-72499 : ℝ)/18108360)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/18108360)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/39366)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/787320)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-12769 : ℝ)/2332800)*y 1*y 7*(Real.pi^1)⁻¹)+(((-10201 : ℝ)/2332800)*y 1*y 7*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/1166400)*y 1*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),(0 : ℝ),(((-1 : ℝ)/6)*Real.pi),((((-8849 : ℝ)/524880)*y 1*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 1*y 2*(Real.pi^1)⁻¹)+(((72499 : ℝ)/12072240)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),(((2053 : ℝ)/1944)+(((23 : ℝ)/1944)*(Real.exp (-12 : ℝ)))+(((-23077 : ℝ)/233280)*y 1*(Real.pi^1)⁻¹)+(((-8849 : ℝ)/524880)*y 0*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 0*y 2*(Real.pi^1)⁻¹)+(((-12769 : ℝ)/2332800)*y 1*y 3*(Real.pi^1)⁻¹)+(((10201 : ℝ)/233280)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/12072240)*y 0*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/2332800)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/39366)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/1166400)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),((((-25853 : ℝ)/905418)*y 0*y 1*(Real.pi^1)⁻¹)+(((-72499 : ℝ)/18108360)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-12769 : ℝ)/4665600)*(Real.pi^1)⁻¹*(y 1^2))+(((-10201 : ℝ)/4665600)*(Real.pi^1)⁻¹*(y 1^2)*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/2332800)*(Real.pi^1)⁻¹*(y 1^2)*(Real.exp (-12 : ℝ))));
    ((((-24698 : ℝ)/177147)*y 8)+(((-217156 : ℝ)/531441)*y 2*y 8)+(((5618 : ℝ)/177147)*y 8*(Real.exp ((-9 : ℝ)/5)))+(((-11236 : ℝ)/531441)*y 2*y 8*(Real.exp ((-18 : ℝ)/5)))+(((98792 : ℝ)/531441)*y 2*y 8*(Real.exp ((-9 : ℝ)/5)))),((((-24353 : ℝ)/39366)*y 8)+(((143 : ℝ)/13122)*y 9)+(((-88507 : ℝ)/9054180)*y 2*y 9)+(((-88507 : ℝ)/9054180)*y 3*y 8)+(((2531 : ℝ)/301806)*y 9*(Real.exp (-12 : ℝ)))+(((25310 : ℝ)/452709)*y 8*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 2*y 9*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 3*y 8*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 2*y 9*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 3*y 8*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 2*y 9*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/393660)*y 3*y 8*(Real.exp (-12 : ℝ)))),((((-24698 : ℝ)/177147)*y 6)+(((-24353 : ℝ)/39366)*y 7)+(((-217156 : ℝ)/531441)*y 0*y 8)+(((-217156 : ℝ)/531441)*y 2*y 6)+(((-88507 : ℝ)/9054180)*y 1*y 9)+(((-88507 : ℝ)/9054180)*y 3*y 7)+(((5618 : ℝ)/177147)*y 6*(Real.exp ((-9 : ℝ)/5)))+(((25310 : ℝ)/452709)*y 7*(Real.exp ((-9 : ℝ)/5)))+(((-11236 : ℝ)/531441)*y 0*y 8*(Real.exp ((-18 : ℝ)/5)))+(((-11236 : ℝ)/531441)*y 2*y 6*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 1*y 9*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 3*y 7*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 9*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 3*y 7*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 9*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/393660)*y 3*y 7*(Real.exp (-12 : ℝ)))+(((98792 : ℝ)/531441)*y 0*y 8*(Real.exp ((-9 : ℝ)/5)))+(((98792 : ℝ)/531441)*y 2*y 6*(Real.exp ((-9 : ℝ)/5)))),((((143 : ℝ)/13122)*y 7)+(((-88507 : ℝ)/9054180)*y 1*y 8)+(((-88507 : ℝ)/9054180)*y 2*y 7)+(((2531 : ℝ)/301806)*y 7*(Real.exp (-12 : ℝ)))+(((-2531 : ℝ)/452709)*y 1*y 8*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 2*y 7*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 8*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 2*y 7*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 8*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/393660)*y 2*y 7*(Real.exp (-12 : ℝ)))),(0 : ℝ),(0 : ℝ),(((-2809 : ℝ)/118098)+(((-108578 : ℝ)/531441)*(y 2^2))+(((-24698 : ℝ)/177147)*y 2)+(((-5618 : ℝ)/531441)*(y 2^2)*(Real.exp ((-18 : ℝ)/5)))+(((5618 : ℝ)/177147)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((49396 : ℝ)/531441)*(y 2^2)*(Real.exp ((-9 : ℝ)/5)))),(((-12655 : ℝ)/150903)+(((-24353 : ℝ)/39366)*y 2)+(((143 : ℝ)/13122)*y 3)+(((-88507 : ℝ)/9054180)*y 2*y 3)+(((2531 : ℝ)/301806)*y 3*(Real.exp (-12 : ℝ)))+(((25310 : ℝ)/452709)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 2*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 2*y 3*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 2*y 3*(Real.exp (-12 : ℝ)))),((((-24698 : ℝ)/177147)*y 0)+(((-24353 : ℝ)/39366)*y 1)+(((14882 : ℝ)/6561)*Real.pi)+(((-217156 : ℝ)/531441)*y 0*y 2)+(((-88507 : ℝ)/9054180)*y 1*y 3)+(((5618 : ℝ)/177147)*y 0*(Real.exp ((-9 : ℝ)/5)))+(((10300 : ℝ)/6561)*Real.pi*(Real.exp ((-9 : ℝ)/5)))+(((25310 : ℝ)/452709)*y 1*(Real.exp ((-9 : ℝ)/5)))+(((-11236 : ℝ)/531441)*y 0*y 2*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 1*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 3*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 3*(Real.exp (-12 : ℝ)))+(((98792 : ℝ)/531441)*y 0*y 2*(Real.exp ((-9 : ℝ)/5)))),((((143 : ℝ)/13122)*y 1)+(((-88507 : ℝ)/9054180)*y 1*y 2)+(((2531 : ℝ)/301806)*y 1*(Real.exp (-12 : ℝ)))+(((-2531 : ℝ)/452709)*y 1*y 2*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 2*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 2*(Real.exp (-12 : ℝ))));
    ((((-8849 : ℝ)/262440)*y 9)+(((410 : ℝ)/19683)*y 8)+(((-25853 : ℝ)/452709)*y 2*y 9)+(((-25853 : ℝ)/452709)*y 3*y 8)+(((72499 : ℝ)/905418)*y 8*(Real.exp ((-9 : ℝ)/5)))+(((72499 : ℝ)/6036120)*y 9*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 2*y 9*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 3*y 8*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 2*y 9*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/19683)*y 3*y 8*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 2*y 9*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/393660)*y 3*y 8*(Real.exp ((-9 : ℝ)/5)))),((((-11413 : ℝ)/116640)*y 9)+(((-12769 : ℝ)/1166400)*y 3*y 9)+(((10201 : ℝ)/116640)*y 9*(Real.exp (-12 : ℝ)))+(((-10201 : ℝ)/1166400)*y 3*y 9*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/583200)*y 3*y 9*(Real.exp (-12 : ℝ)))),((((410 : ℝ)/19683)*y 6)+(((-25853 : ℝ)/452709)*y 0*y 9)+(((-25853 : ℝ)/452709)*y 3*y 6)+(((72499 : ℝ)/905418)*y 6*(Real.exp ((-9 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 0*y 9*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 3*y 6*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 0*y 9*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/19683)*y 3*y 6*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 9*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/393660)*y 3*y 6*(Real.exp ((-9 : ℝ)/5)))),((((-11413 : ℝ)/116640)*y 7)+(((-8849 : ℝ)/262440)*y 6)+(((-25853 : ℝ)/452709)*y 0*y 8)+(((-25853 : ℝ)/452709)*y 2*y 6)+(((-12769 : ℝ)/1166400)*y 1*y 9)+(((-12769 : ℝ)/1166400)*y 3*y 7)+(((10201 : ℝ)/116640)*y 7*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/6036120)*y 6*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 0*y 8*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 2*y 6*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/1166400)*y 1*y 9*(Real.exp (-24 : ℝ)))+(((-10201 : ℝ)/1166400)*y 3*y 7*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/19683)*y 0*y 8*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/19683)*y 2*y 6*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 8*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/393660)*y 2*y 6*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/583200)*y 1*y 9*(Real.exp (-12 : ℝ)))+(((11413 : ℝ)/583200)*y 3*y 7*(Real.exp (-12 : ℝ)))),(0 : ℝ),(0 : ℝ),(((-72499 : ℝ)/603612)+(((-8849 : ℝ)/262440)*y 3)+(((410 : ℝ)/19683)*y 2)+(((-25853 : ℝ)/452709)*y 2*y 3)+(((72499 : ℝ)/905418)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((72499 : ℝ)/6036120)*y 3*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 2*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 2*y 3*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 2*y 3*(Real.exp ((-9 : ℝ)/5)))),(((-10201 : ℝ)/23328)+(((-12769 : ℝ)/2332800)*(y 3^2))+(((-11413 : ℝ)/116640)*y 3)+(((-10201 : ℝ)/2332800)*(y 3^2)*(Real.exp (-24 : ℝ)))+(((10201 : ℝ)/116640)*y 3*(Real.exp (-12 : ℝ)))+(((11413 : ℝ)/1166400)*(y 3^2)*(Real.exp (-12 : ℝ)))),((((410 : ℝ)/19683)*y 0)+(((-25853 : ℝ)/452709)*y 0*y 3)+(((72499 : ℝ)/905418)*y 0*(Real.exp ((-9 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 0*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 0*y 3*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 3*(Real.exp ((-9 : ℝ)/5)))),((((-11413 : ℝ)/116640)*y 1)+(((-8849 : ℝ)/262440)*y 0)+(((2053 : ℝ)/972)*Real.pi)+(((-25853 : ℝ)/452709)*y 0*y 2)+(((-12769 : ℝ)/1166400)*y 1*y 3)+(((23 : ℝ)/972)*Real.pi*(Real.exp (-12 : ℝ)))+(((10201 : ℝ)/116640)*y 1*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/6036120)*y 0*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 0*y 2*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/1166400)*y 1*y 3*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/19683)*y 0*y 2*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 2*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/583200)*y 1*y 3*(Real.exp (-12 : ℝ))));
    ((((-566 : ℝ)/729)*(Real.pi^1)⁻¹)+(((-520 : ℝ)/2187)*y 2*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-227 : ℝ)/324)*(Real.pi^1)⁻¹)+(((-23 : ℝ)/3240)*y 3*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),((((-520 : ℝ)/2187)*y 0*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-23 : ℝ)/3240)*y 1*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ),(0 : ℝ);
    ((((-520 : ℝ)/2187)*y 8*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 8*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-23 : ℝ)/3240)*y 9*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 9*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),((((-520 : ℝ)/2187)*y 6*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-23 : ℝ)/3240)*y 7*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),(0 : ℝ),(0 : ℝ),((((-566 : ℝ)/729)*(Real.pi^1)⁻¹)+(((-520 : ℝ)/2187)*y 2*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-227 : ℝ)/324)*(Real.pi^1)⁻¹)+(((-23 : ℝ)/3240)*y 3*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))),((((-520 : ℝ)/2187)*y 0*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))),((((-23 : ℝ)/3240)*y 1*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))]

private theorem entry_0_0 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 0 0 = (((7441 : ℝ)/6561)+(((5150 : ℝ)/6561)*(Real.exp ((-9 : ℝ)/5)))+(((-71398 : ℝ)/177147)*y 0*(Real.pi^1)⁻¹)+(((-24353 : ℝ)/78732)*y 1*(Real.pi^1)⁻¹)+(((-108578 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 1*y 3*(Real.pi^1)⁻¹)+(((2809 : ℝ)/177147)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((12655 : ℝ)/452709)*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-5618 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((49396 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 0 equation_0) = _
  norm_num [equation_0,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_0_1 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 0 1 = ((((-24353 : ℝ)/78732)*y 0*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 0*y 3*(Real.pi^1)⁻¹)+(((12655 : ℝ)/452709)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 1 equation_0) = _
  norm_num [equation_0,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_0_2 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 0 2 = ((((-54289 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2))+(((-2809 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2)*(Real.exp ((-18 : ℝ)/5)))+(((24698 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2)*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 2 equation_0) = _
  norm_num [equation_0,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_0_3 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 0 3 = ((((-88507 : ℝ)/18108360)*y 0*y 1*(Real.pi^1)⁻¹)+(((-2531 : ℝ)/905418)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 3 equation_0) = _
  norm_num [equation_0,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_0_4 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 0 4 = (((-10 : ℝ)/9)*Real.pi) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 4 equation_0) = _
  norm_num [equation_0,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_0_5 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 0 5 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 5 equation_0) = _
  norm_num [equation_0,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_0_6 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 0 6 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 6 equation_0) = _
  norm_num [equation_0,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_0_7 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 0 7 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 7 equation_0) = _
  norm_num [equation_0,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_0_8 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 0 8 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 8 equation_0) = _
  norm_num [equation_0,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_0_9 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 0 9 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 9 equation_0) = _
  norm_num [equation_0,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_1_0 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 1 0 = ((((-8849 : ℝ)/524880)*y 1*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 1*y 2*(Real.pi^1)⁻¹)+(((72499 : ℝ)/12072240)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 0 equation_1) = _
  norm_num [equation_1,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_1_1 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 1 1 = (((2053 : ℝ)/1944)+(((23 : ℝ)/1944)*(Real.exp (-12 : ℝ)))+(((-23077 : ℝ)/233280)*y 1*(Real.pi^1)⁻¹)+(((-8849 : ℝ)/524880)*y 0*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 0*y 2*(Real.pi^1)⁻¹)+(((-12769 : ℝ)/2332800)*y 1*y 3*(Real.pi^1)⁻¹)+(((10201 : ℝ)/233280)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/12072240)*y 0*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/2332800)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/39366)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/1166400)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 1 equation_1) = _
  norm_num [equation_1,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_1_2 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 1 2 = ((((-25853 : ℝ)/905418)*y 0*y 1*(Real.pi^1)⁻¹)+(((-72499 : ℝ)/18108360)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 2 equation_1) = _
  norm_num [equation_1,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_1_3 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 1 3 = ((((-12769 : ℝ)/4665600)*(Real.pi^1)⁻¹*(y 1^2))+(((-10201 : ℝ)/4665600)*(Real.pi^1)⁻¹*(y 1^2)*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/2332800)*(Real.pi^1)⁻¹*(y 1^2)*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 3 equation_1) = _
  norm_num [equation_1,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_1_4 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 1 4 = (((-1 : ℝ)/6)*Real.pi*y 5) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 4 equation_1) = _
  norm_num [equation_1,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_1_5 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 1 5 = (((-1 : ℝ)/6)*Real.pi*y 4) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 5 equation_1) = _
  norm_num [equation_1,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_1_6 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 1 6 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 6 equation_1) = _
  norm_num [equation_1,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_1_7 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 1 7 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 7 equation_1) = _
  norm_num [equation_1,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_1_8 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 1 8 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 8 equation_1) = _
  norm_num [equation_1,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_1_9 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 1 9 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 9 equation_1) = _
  norm_num [equation_1,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_2_0 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 2 0 = (((-2809 : ℝ)/118098)+(((-108578 : ℝ)/531441)*(y 2^2))+(((-24698 : ℝ)/177147)*y 2)+(((-5618 : ℝ)/531441)*(y 2^2)*(Real.exp ((-18 : ℝ)/5)))+(((5618 : ℝ)/177147)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((49396 : ℝ)/531441)*(y 2^2)*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 0 equation_2) = _
  norm_num [equation_2,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_2_1 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 2 1 = (((-12655 : ℝ)/150903)+(((-24353 : ℝ)/39366)*y 2)+(((143 : ℝ)/13122)*y 3)+(((-88507 : ℝ)/9054180)*y 2*y 3)+(((2531 : ℝ)/301806)*y 3*(Real.exp (-12 : ℝ)))+(((25310 : ℝ)/452709)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 2*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 2*y 3*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 2*y 3*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 1 equation_2) = _
  norm_num [equation_2,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_2_2 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 2 2 = ((((-24698 : ℝ)/177147)*y 0)+(((-24353 : ℝ)/39366)*y 1)+(((14882 : ℝ)/6561)*Real.pi)+(((-217156 : ℝ)/531441)*y 0*y 2)+(((-88507 : ℝ)/9054180)*y 1*y 3)+(((5618 : ℝ)/177147)*y 0*(Real.exp ((-9 : ℝ)/5)))+(((10300 : ℝ)/6561)*Real.pi*(Real.exp ((-9 : ℝ)/5)))+(((25310 : ℝ)/452709)*y 1*(Real.exp ((-9 : ℝ)/5)))+(((-11236 : ℝ)/531441)*y 0*y 2*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 1*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 3*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 3*(Real.exp (-12 : ℝ)))+(((98792 : ℝ)/531441)*y 0*y 2*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 2 equation_2) = _
  norm_num [equation_2,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_2_3 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 2 3 = ((((143 : ℝ)/13122)*y 1)+(((-88507 : ℝ)/9054180)*y 1*y 2)+(((2531 : ℝ)/301806)*y 1*(Real.exp (-12 : ℝ)))+(((-2531 : ℝ)/452709)*y 1*y 2*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 2*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 2*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 3 equation_2) = _
  norm_num [equation_2,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_2_4 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 2 4 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 4 equation_2) = _
  norm_num [equation_2,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_2_5 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 2 5 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 5 equation_2) = _
  norm_num [equation_2,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_2_6 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 2 6 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 6 equation_2) = _
  norm_num [equation_2,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_2_7 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 2 7 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 7 equation_2) = _
  norm_num [equation_2,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_2_8 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 2 8 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 8 equation_2) = _
  norm_num [equation_2,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_2_9 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 2 9 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 9 equation_2) = _
  norm_num [equation_2,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_3_0 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 3 0 = (((-72499 : ℝ)/603612)+(((-8849 : ℝ)/262440)*y 3)+(((410 : ℝ)/19683)*y 2)+(((-25853 : ℝ)/452709)*y 2*y 3)+(((72499 : ℝ)/905418)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((72499 : ℝ)/6036120)*y 3*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 2*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 2*y 3*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 2*y 3*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 0 equation_3) = _
  norm_num [equation_3,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_3_1 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 3 1 = (((-10201 : ℝ)/23328)+(((-12769 : ℝ)/2332800)*(y 3^2))+(((-11413 : ℝ)/116640)*y 3)+(((-10201 : ℝ)/2332800)*(y 3^2)*(Real.exp (-24 : ℝ)))+(((10201 : ℝ)/116640)*y 3*(Real.exp (-12 : ℝ)))+(((11413 : ℝ)/1166400)*(y 3^2)*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 1 equation_3) = _
  norm_num [equation_3,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_3_2 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 3 2 = ((((410 : ℝ)/19683)*y 0)+(((-25853 : ℝ)/452709)*y 0*y 3)+(((72499 : ℝ)/905418)*y 0*(Real.exp ((-9 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 0*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 0*y 3*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 3*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 2 equation_3) = _
  norm_num [equation_3,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_3_3 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 3 3 = ((((-11413 : ℝ)/116640)*y 1)+(((-8849 : ℝ)/262440)*y 0)+(((2053 : ℝ)/972)*Real.pi)+(((-25853 : ℝ)/452709)*y 0*y 2)+(((-12769 : ℝ)/1166400)*y 1*y 3)+(((23 : ℝ)/972)*Real.pi*(Real.exp (-12 : ℝ)))+(((10201 : ℝ)/116640)*y 1*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/6036120)*y 0*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 0*y 2*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/1166400)*y 1*y 3*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/19683)*y 0*y 2*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 2*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/583200)*y 1*y 3*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 3 equation_3) = _
  norm_num [equation_3,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_3_4 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 3 4 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 4 equation_3) = _
  norm_num [equation_3,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_3_5 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 3 5 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 5 equation_3) = _
  norm_num [equation_3,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_3_6 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 3 6 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 6 equation_3) = _
  norm_num [equation_3,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_3_7 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 3 7 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 7 equation_3) = _
  norm_num [equation_3,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_3_8 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 3 8 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 8 equation_3) = _
  norm_num [equation_3,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_3_9 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 3 9 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 9 equation_3) = _
  norm_num [equation_3,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_4_0 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 4 0 = ((((-71398 : ℝ)/177147)*y 6*(Real.pi^1)⁻¹)+(((-24353 : ℝ)/78732)*y 7*(Real.pi^1)⁻¹)+(((-108578 : ℝ)/531441)*y 0*y 8*(Real.pi^1)⁻¹)+(((-108578 : ℝ)/531441)*y 2*y 6*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 1*y 9*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 3*y 7*(Real.pi^1)⁻¹)+(((2809 : ℝ)/177147)*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((12655 : ℝ)/452709)*y 7*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-5618 : ℝ)/531441)*y 0*y 8*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((-5618 : ℝ)/531441)*y 2*y 6*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 1*y 9*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 3*y 7*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 1*y 9*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 3*y 7*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 1*y 9*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/787320)*y 3*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((49396 : ℝ)/531441)*y 0*y 8*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((49396 : ℝ)/531441)*y 2*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 0 equation_4) = _
  norm_num [equation_4,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_4_1 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 4 1 = ((((-24353 : ℝ)/78732)*y 6*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 0*y 9*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 3*y 6*(Real.pi^1)⁻¹)+(((12655 : ℝ)/452709)*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 0*y 9*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 3*y 6*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 9*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 3*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 9*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/787320)*y 3*y 6*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 1 equation_4) = _
  norm_num [equation_4,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_4_2 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 4 2 = ((((-108578 : ℝ)/531441)*y 0*y 6*(Real.pi^1)⁻¹)+(((-5618 : ℝ)/531441)*y 0*y 6*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((49396 : ℝ)/531441)*y 0*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 2 equation_4) = _
  norm_num [equation_4,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_4_3 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 4 3 = ((((-88507 : ℝ)/18108360)*y 0*y 7*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 1*y 6*(Real.pi^1)⁻¹)+(((-2531 : ℝ)/905418)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/787320)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 3 equation_4) = _
  norm_num [equation_4,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_4_4 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 4 4 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 4 equation_4) = _
  norm_num [equation_4,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_4_5 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 4 5 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 5 equation_4) = _
  norm_num [equation_4,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_4_6 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 4 6 = (((7441 : ℝ)/6561)+(((5150 : ℝ)/6561)*(Real.exp ((-9 : ℝ)/5)))+(((-71398 : ℝ)/177147)*y 0*(Real.pi^1)⁻¹)+(((-24353 : ℝ)/78732)*y 1*(Real.pi^1)⁻¹)+(((-108578 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 1*y 3*(Real.pi^1)⁻¹)+(((2809 : ℝ)/177147)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((12655 : ℝ)/452709)*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-5618 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((49396 : ℝ)/531441)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 6 equation_4) = _
  norm_num [equation_4,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_4_7 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 4 7 = ((((-24353 : ℝ)/78732)*y 0*(Real.pi^1)⁻¹)+(((-88507 : ℝ)/18108360)*y 0*y 3*(Real.pi^1)⁻¹)+(((12655 : ℝ)/452709)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/905418)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 7 equation_4) = _
  norm_num [equation_4,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_4_8 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 4 8 = ((((-54289 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2))+(((-2809 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2)*(Real.exp ((-18 : ℝ)/5)))+(((24698 : ℝ)/531441)*(Real.pi^1)⁻¹*(y 0^2)*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 8 equation_4) = _
  norm_num [equation_4,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_4_9 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 4 9 = ((((-88507 : ℝ)/18108360)*y 0*y 1*(Real.pi^1)⁻¹)+(((-2531 : ℝ)/905418)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 9 equation_4) = _
  norm_num [equation_4,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_5_0 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 5 0 = ((((-8849 : ℝ)/524880)*y 7*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 1*y 8*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 2*y 7*(Real.pi^1)⁻¹)+(((72499 : ℝ)/12072240)*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 1*y 8*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/18108360)*y 2*y 7*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 1*y 8*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/39366)*y 2*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 1*y 8*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/787320)*y 2*y 7*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 0 equation_5) = _
  norm_num [equation_5,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_5_1 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 5 1 = ((((-23077 : ℝ)/233280)*y 7*(Real.pi^1)⁻¹)+(((-8849 : ℝ)/524880)*y 6*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 0*y 8*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 2*y 6*(Real.pi^1)⁻¹)+(((-12769 : ℝ)/2332800)*y 1*y 9*(Real.pi^1)⁻¹)+(((-12769 : ℝ)/2332800)*y 3*y 7*(Real.pi^1)⁻¹)+(((10201 : ℝ)/233280)*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/12072240)*y 6*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 0*y 8*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/18108360)*y 2*y 6*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/2332800)*y 1*y 9*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((-10201 : ℝ)/2332800)*y 3*y 7*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/39366)*y 0*y 8*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/39366)*y 2*y 6*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 8*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/787320)*y 2*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/1166400)*y 1*y 9*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((11413 : ℝ)/1166400)*y 3*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 1 equation_5) = _
  norm_num [equation_5,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_5_2 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 5 2 = ((((-25853 : ℝ)/905418)*y 0*y 7*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 1*y 6*(Real.pi^1)⁻¹)+(((-72499 : ℝ)/18108360)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/18108360)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/39366)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 7*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/787320)*y 1*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 2 equation_5) = _
  norm_num [equation_5,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_5_3 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 5 3 = ((((-12769 : ℝ)/2332800)*y 1*y 7*(Real.pi^1)⁻¹)+(((-10201 : ℝ)/2332800)*y 1*y 7*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/1166400)*y 1*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 3 equation_5) = _
  norm_num [equation_5,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_5_4 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 5 4 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 4 equation_5) = _
  norm_num [equation_5,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_5_5 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 5 5 = (((-1 : ℝ)/6)*Real.pi) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 5 equation_5) = _
  norm_num [equation_5,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_5_6 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 5 6 = ((((-8849 : ℝ)/524880)*y 1*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 1*y 2*(Real.pi^1)⁻¹)+(((72499 : ℝ)/12072240)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 1*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 6 equation_5) = _
  norm_num [equation_5,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_5_7 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 5 7 = (((2053 : ℝ)/1944)+(((23 : ℝ)/1944)*(Real.exp (-12 : ℝ)))+(((-23077 : ℝ)/233280)*y 1*(Real.pi^1)⁻¹)+(((-8849 : ℝ)/524880)*y 0*(Real.pi^1)⁻¹)+(((-25853 : ℝ)/905418)*y 0*y 2*(Real.pi^1)⁻¹)+(((-12769 : ℝ)/2332800)*y 1*y 3*(Real.pi^1)⁻¹)+(((10201 : ℝ)/233280)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/12072240)*y 0*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/18108360)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/2332800)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/39366)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/1166400)*y 1*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 7 equation_5) = _
  norm_num [equation_5,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_5_8 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 5 8 = ((((-25853 : ℝ)/905418)*y 0*y 1*(Real.pi^1)⁻¹)+(((-72499 : ℝ)/18108360)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*y 0*y 1*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 8 equation_5) = _
  norm_num [equation_5,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_5_9 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 5 9 = ((((-12769 : ℝ)/4665600)*(Real.pi^1)⁻¹*(y 1^2))+(((-10201 : ℝ)/4665600)*(Real.pi^1)⁻¹*(y 1^2)*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/2332800)*(Real.pi^1)⁻¹*(y 1^2)*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 9 equation_5) = _
  norm_num [equation_5,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_6_0 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 6 0 = ((((-24698 : ℝ)/177147)*y 8)+(((-217156 : ℝ)/531441)*y 2*y 8)+(((5618 : ℝ)/177147)*y 8*(Real.exp ((-9 : ℝ)/5)))+(((-11236 : ℝ)/531441)*y 2*y 8*(Real.exp ((-18 : ℝ)/5)))+(((98792 : ℝ)/531441)*y 2*y 8*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 0 equation_6) = _
  norm_num [equation_6,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_6_1 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 6 1 = ((((-24353 : ℝ)/39366)*y 8)+(((143 : ℝ)/13122)*y 9)+(((-88507 : ℝ)/9054180)*y 2*y 9)+(((-88507 : ℝ)/9054180)*y 3*y 8)+(((2531 : ℝ)/301806)*y 9*(Real.exp (-12 : ℝ)))+(((25310 : ℝ)/452709)*y 8*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 2*y 9*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 3*y 8*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 2*y 9*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 3*y 8*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 2*y 9*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/393660)*y 3*y 8*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 1 equation_6) = _
  norm_num [equation_6,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_6_2 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 6 2 = ((((-24698 : ℝ)/177147)*y 6)+(((-24353 : ℝ)/39366)*y 7)+(((-217156 : ℝ)/531441)*y 0*y 8)+(((-217156 : ℝ)/531441)*y 2*y 6)+(((-88507 : ℝ)/9054180)*y 1*y 9)+(((-88507 : ℝ)/9054180)*y 3*y 7)+(((5618 : ℝ)/177147)*y 6*(Real.exp ((-9 : ℝ)/5)))+(((25310 : ℝ)/452709)*y 7*(Real.exp ((-9 : ℝ)/5)))+(((-11236 : ℝ)/531441)*y 0*y 8*(Real.exp ((-18 : ℝ)/5)))+(((-11236 : ℝ)/531441)*y 2*y 6*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 1*y 9*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 3*y 7*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 9*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 3*y 7*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 9*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/393660)*y 3*y 7*(Real.exp (-12 : ℝ)))+(((98792 : ℝ)/531441)*y 0*y 8*(Real.exp ((-9 : ℝ)/5)))+(((98792 : ℝ)/531441)*y 2*y 6*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 2 equation_6) = _
  norm_num [equation_6,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_6_3 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 6 3 = ((((143 : ℝ)/13122)*y 7)+(((-88507 : ℝ)/9054180)*y 1*y 8)+(((-88507 : ℝ)/9054180)*y 2*y 7)+(((2531 : ℝ)/301806)*y 7*(Real.exp (-12 : ℝ)))+(((-2531 : ℝ)/452709)*y 1*y 8*(Real.exp ((-69 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 2*y 7*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 8*(Real.exp ((-9 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 2*y 7*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 8*(Real.exp (-12 : ℝ)))+(((24353 : ℝ)/393660)*y 2*y 7*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 3 equation_6) = _
  norm_num [equation_6,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_6_4 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 6 4 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 4 equation_6) = _
  norm_num [equation_6,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_6_5 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 6 5 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 5 equation_6) = _
  norm_num [equation_6,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_6_6 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 6 6 = (((-2809 : ℝ)/118098)+(((-108578 : ℝ)/531441)*(y 2^2))+(((-24698 : ℝ)/177147)*y 2)+(((-5618 : ℝ)/531441)*(y 2^2)*(Real.exp ((-18 : ℝ)/5)))+(((5618 : ℝ)/177147)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((49396 : ℝ)/531441)*(y 2^2)*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 6 equation_6) = _
  norm_num [equation_6,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_6_7 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 6 7 = (((-12655 : ℝ)/150903)+(((-24353 : ℝ)/39366)*y 2)+(((143 : ℝ)/13122)*y 3)+(((-88507 : ℝ)/9054180)*y 2*y 3)+(((2531 : ℝ)/301806)*y 3*(Real.exp (-12 : ℝ)))+(((25310 : ℝ)/452709)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 2*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 2*y 3*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 2*y 3*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 7 equation_6) = _
  norm_num [equation_6,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_6_8 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 6 8 = ((((-24698 : ℝ)/177147)*y 0)+(((-24353 : ℝ)/39366)*y 1)+(((14882 : ℝ)/6561)*Real.pi)+(((-217156 : ℝ)/531441)*y 0*y 2)+(((-88507 : ℝ)/9054180)*y 1*y 3)+(((5618 : ℝ)/177147)*y 0*(Real.exp ((-9 : ℝ)/5)))+(((10300 : ℝ)/6561)*Real.pi*(Real.exp ((-9 : ℝ)/5)))+(((25310 : ℝ)/452709)*y 1*(Real.exp ((-9 : ℝ)/5)))+(((-11236 : ℝ)/531441)*y 0*y 2*(Real.exp ((-18 : ℝ)/5)))+(((-2531 : ℝ)/452709)*y 1*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 3*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 3*(Real.exp (-12 : ℝ)))+(((98792 : ℝ)/531441)*y 0*y 2*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 8 equation_6) = _
  norm_num [equation_6,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_6_9 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 6 9 = ((((143 : ℝ)/13122)*y 1)+(((-88507 : ℝ)/9054180)*y 1*y 2)+(((2531 : ℝ)/301806)*y 1*(Real.exp (-12 : ℝ)))+(((-2531 : ℝ)/452709)*y 1*y 2*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*y 1*y 2*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*y 1*y 2*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 9 equation_6) = _
  norm_num [equation_6,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_7_0 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 7 0 = ((((-8849 : ℝ)/262440)*y 9)+(((410 : ℝ)/19683)*y 8)+(((-25853 : ℝ)/452709)*y 2*y 9)+(((-25853 : ℝ)/452709)*y 3*y 8)+(((72499 : ℝ)/905418)*y 8*(Real.exp ((-9 : ℝ)/5)))+(((72499 : ℝ)/6036120)*y 9*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 2*y 9*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 3*y 8*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 2*y 9*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/19683)*y 3*y 8*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 2*y 9*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/393660)*y 3*y 8*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 0 equation_7) = _
  norm_num [equation_7,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_7_1 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 7 1 = ((((-11413 : ℝ)/116640)*y 9)+(((-12769 : ℝ)/1166400)*y 3*y 9)+(((10201 : ℝ)/116640)*y 9*(Real.exp (-12 : ℝ)))+(((-10201 : ℝ)/1166400)*y 3*y 9*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/583200)*y 3*y 9*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 1 equation_7) = _
  norm_num [equation_7,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_7_2 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 7 2 = ((((410 : ℝ)/19683)*y 6)+(((-25853 : ℝ)/452709)*y 0*y 9)+(((-25853 : ℝ)/452709)*y 3*y 6)+(((72499 : ℝ)/905418)*y 6*(Real.exp ((-9 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 0*y 9*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 3*y 6*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 0*y 9*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/19683)*y 3*y 6*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 9*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/393660)*y 3*y 6*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 2 equation_7) = _
  norm_num [equation_7,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_7_3 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 7 3 = ((((-11413 : ℝ)/116640)*y 7)+(((-8849 : ℝ)/262440)*y 6)+(((-25853 : ℝ)/452709)*y 0*y 8)+(((-25853 : ℝ)/452709)*y 2*y 6)+(((-12769 : ℝ)/1166400)*y 1*y 9)+(((-12769 : ℝ)/1166400)*y 3*y 7)+(((10201 : ℝ)/116640)*y 7*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/6036120)*y 6*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 0*y 8*(Real.exp ((-69 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 2*y 6*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/1166400)*y 1*y 9*(Real.exp (-24 : ℝ)))+(((-10201 : ℝ)/1166400)*y 3*y 7*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/19683)*y 0*y 8*(Real.exp (-12 : ℝ)))+(((-41 : ℝ)/19683)*y 2*y 6*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 8*(Real.exp ((-9 : ℝ)/5)))+(((8849 : ℝ)/393660)*y 2*y 6*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/583200)*y 1*y 9*(Real.exp (-12 : ℝ)))+(((11413 : ℝ)/583200)*y 3*y 7*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 3 equation_7) = _
  norm_num [equation_7,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_7_4 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 7 4 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 4 equation_7) = _
  norm_num [equation_7,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_7_5 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 7 5 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 5 equation_7) = _
  norm_num [equation_7,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_7_6 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 7 6 = (((-72499 : ℝ)/603612)+(((-8849 : ℝ)/262440)*y 3)+(((410 : ℝ)/19683)*y 2)+(((-25853 : ℝ)/452709)*y 2*y 3)+(((72499 : ℝ)/905418)*y 2*(Real.exp ((-9 : ℝ)/5)))+(((72499 : ℝ)/6036120)*y 3*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 2*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 2*y 3*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 2*y 3*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 6 equation_7) = _
  norm_num [equation_7,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_7_7 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 7 7 = (((-10201 : ℝ)/23328)+(((-12769 : ℝ)/2332800)*(y 3^2))+(((-11413 : ℝ)/116640)*y 3)+(((-10201 : ℝ)/2332800)*(y 3^2)*(Real.exp (-24 : ℝ)))+(((10201 : ℝ)/116640)*y 3*(Real.exp (-12 : ℝ)))+(((11413 : ℝ)/1166400)*(y 3^2)*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 7 equation_7) = _
  norm_num [equation_7,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_7_8 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 7 8 = ((((410 : ℝ)/19683)*y 0)+(((-25853 : ℝ)/452709)*y 0*y 3)+(((72499 : ℝ)/905418)*y 0*(Real.exp ((-9 : ℝ)/5)))+(((-72499 : ℝ)/9054180)*y 0*y 3*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*y 0*y 3*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 3*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 8 equation_7) = _
  norm_num [equation_7,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_7_9 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 7 9 = ((((-11413 : ℝ)/116640)*y 1)+(((-8849 : ℝ)/262440)*y 0)+(((2053 : ℝ)/972)*Real.pi)+(((-25853 : ℝ)/452709)*y 0*y 2)+(((-12769 : ℝ)/1166400)*y 1*y 3)+(((23 : ℝ)/972)*Real.pi*(Real.exp (-12 : ℝ)))+(((10201 : ℝ)/116640)*y 1*(Real.exp (-12 : ℝ)))+(((72499 : ℝ)/6036120)*y 0*(Real.exp (-12 : ℝ)))+(((-72499 : ℝ)/9054180)*y 0*y 2*(Real.exp ((-69 : ℝ)/5)))+(((-10201 : ℝ)/1166400)*y 1*y 3*(Real.exp (-24 : ℝ)))+(((-41 : ℝ)/19683)*y 0*y 2*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*y 0*y 2*(Real.exp ((-9 : ℝ)/5)))+(((11413 : ℝ)/583200)*y 1*y 3*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 9 equation_7) = _
  norm_num [equation_7,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_8_0 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 8 0 = ((((-566 : ℝ)/729)*(Real.pi^1)⁻¹)+(((-520 : ℝ)/2187)*y 2*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 0 equation_8) = _
  norm_num [equation_8,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_8_1 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 8 1 = ((((-227 : ℝ)/324)*(Real.pi^1)⁻¹)+(((-23 : ℝ)/3240)*y 3*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 1 equation_8) = _
  norm_num [equation_8,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_8_2 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 8 2 = ((((-520 : ℝ)/2187)*y 0*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 2 equation_8) = _
  norm_num [equation_8,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_8_3 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 8 3 = ((((-23 : ℝ)/3240)*y 1*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 3 equation_8) = _
  norm_num [equation_8,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_8_4 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 8 4 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 4 equation_8) = _
  norm_num [equation_8,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_8_5 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 8 5 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 5 equation_8) = _
  norm_num [equation_8,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_8_6 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 8 6 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 6 equation_8) = _
  norm_num [equation_8,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_8_7 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 8 7 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 7 equation_8) = _
  norm_num [equation_8,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_8_8 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 8 8 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 8 equation_8) = _
  norm_num [equation_8,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_8_9 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 8 9 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 9 equation_8) = _
  norm_num [equation_8,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_9_0 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 9 0 = ((((-520 : ℝ)/2187)*y 8*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 8*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 0 equation_9) = _
  norm_num [equation_9,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_9_1 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 9 1 = ((((-23 : ℝ)/3240)*y 9*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 9*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 1 equation_9) = _
  norm_num [equation_9,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_9_2 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 9 2 = ((((-520 : ℝ)/2187)*y 6*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 6*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 2 equation_9) = _
  norm_num [equation_9,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_9_3 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 9 3 = ((((-23 : ℝ)/3240)*y 7*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 7*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 3 equation_9) = _
  norm_num [equation_9,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_9_4 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 9 4 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 4 equation_9) = _
  norm_num [equation_9,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_9_5 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 9 5 = (0 : ℝ) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 5 equation_9) = _
  norm_num [equation_9,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_9_6 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 9 6 = ((((-566 : ℝ)/729)*(Real.pi^1)⁻¹)+(((-520 : ℝ)/2187)*y 2*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 2*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 6 equation_9) = _
  norm_num [equation_9,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_9_7 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 9 7 = ((((-227 : ℝ)/324)*(Real.pi^1)⁻¹)+(((-23 : ℝ)/3240)*y 3*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 3*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 7 equation_9) = _
  norm_num [equation_9,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_9_8 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 9 8 = ((((-520 : ℝ)/2187)*y 0*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*y 0*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 8 equation_9) = _
  norm_num [equation_9,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

private theorem entry_9_9 (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y 9 9 = ((((-23 : ℝ)/3240)*y 1*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*y 1*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))) := by
  change MvPolynomial.eval y (MvPolynomial.pderiv 9 equation_9) = _
  norm_num [equation_9,Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring

/-- All 100 entries agree with the ORIGINAL full system derivative. -/
theorem jacobian_formula (y : Fin 10 → ℝ) (i j : Fin 10) :
    PolynomialNewtonMap.jacobian polynomial y i j = formula y i j := by
  fin_cases i <;> fin_cases j
  · exact entry_0_0 y
  · exact entry_0_1 y
  · exact entry_0_2 y
  · exact entry_0_3 y
  · exact entry_0_4 y
  · exact entry_0_5 y
  · exact entry_0_6 y
  · exact entry_0_7 y
  · exact entry_0_8 y
  · exact entry_0_9 y
  · exact entry_1_0 y
  · exact entry_1_1 y
  · exact entry_1_2 y
  · exact entry_1_3 y
  · exact entry_1_4 y
  · exact entry_1_5 y
  · exact entry_1_6 y
  · exact entry_1_7 y
  · exact entry_1_8 y
  · exact entry_1_9 y
  · exact entry_2_0 y
  · exact entry_2_1 y
  · exact entry_2_2 y
  · exact entry_2_3 y
  · exact entry_2_4 y
  · exact entry_2_5 y
  · exact entry_2_6 y
  · exact entry_2_7 y
  · exact entry_2_8 y
  · exact entry_2_9 y
  · exact entry_3_0 y
  · exact entry_3_1 y
  · exact entry_3_2 y
  · exact entry_3_3 y
  · exact entry_3_4 y
  · exact entry_3_5 y
  · exact entry_3_6 y
  · exact entry_3_7 y
  · exact entry_3_8 y
  · exact entry_3_9 y
  · exact entry_4_0 y
  · exact entry_4_1 y
  · exact entry_4_2 y
  · exact entry_4_3 y
  · exact entry_4_4 y
  · exact entry_4_5 y
  · exact entry_4_6 y
  · exact entry_4_7 y
  · exact entry_4_8 y
  · exact entry_4_9 y
  · exact entry_5_0 y
  · exact entry_5_1 y
  · exact entry_5_2 y
  · exact entry_5_3 y
  · exact entry_5_4 y
  · exact entry_5_5 y
  · exact entry_5_6 y
  · exact entry_5_7 y
  · exact entry_5_8 y
  · exact entry_5_9 y
  · exact entry_6_0 y
  · exact entry_6_1 y
  · exact entry_6_2 y
  · exact entry_6_3 y
  · exact entry_6_4 y
  · exact entry_6_5 y
  · exact entry_6_6 y
  · exact entry_6_7 y
  · exact entry_6_8 y
  · exact entry_6_9 y
  · exact entry_7_0 y
  · exact entry_7_1 y
  · exact entry_7_2 y
  · exact entry_7_3 y
  · exact entry_7_4 y
  · exact entry_7_5 y
  · exact entry_7_6 y
  · exact entry_7_7 y
  · exact entry_7_8 y
  · exact entry_7_9 y
  · exact entry_8_0 y
  · exact entry_8_1 y
  · exact entry_8_2 y
  · exact entry_8_3 y
  · exact entry_8_4 y
  · exact entry_8_5 y
  · exact entry_8_6 y
  · exact entry_8_7 y
  · exact entry_8_8 y
  · exact entry_8_9 y
  · exact entry_9_0 y
  · exact entry_9_1 y
  · exact entry_9_2 y
  · exact entry_9_3 y
  · exact entry_9_4 y
  · exact entry_9_5 y
  · exact entry_9_6 y
  · exact entry_9_7 y
  · exact entry_9_8 y
  · exact entry_9_9 y

/-- The expanded full Jacobian is exactly the Frechet derivative, EVERYWHERE. -/
theorem system_hasFDerivAt (y : Fin 10 → ℝ) :
    HasFDerivAt M2TangencySystem.system (matrixCLM (formula y)) y := by
  have he : PolynomialNewtonMap.jacobian polynomial y = formula y := by
    ext i j
    exact jacobian_formula y i j
  rw [← he]
  exact M2TangencyPolynomials.system_hasFDerivAt y

end FMSA.Convergence.M2TangencyJacobian

/-- info: 'FMSA.Convergence.M2TangencyJacobian.jacobian_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencyJacobian.jacobian_formula

/-- info: 'FMSA.Convergence.M2TangencyJacobian.system_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencyJacobian.system_hasFDerivAt

