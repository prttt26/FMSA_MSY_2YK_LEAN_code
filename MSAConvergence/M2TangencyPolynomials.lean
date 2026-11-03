import MSAConvergence.M2TangencySystem
import MSAConvergence.PolynomialNewtonMap

/-! Literal polynomials for the FULL ten-equation M2 contact system.
Every expression candidate is proved against the actual ten-coordinate
system. No root, tangency witness or numerical interval is a premise. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2TangencyPolynomials
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.M2ZeroMode
open FMSA.Convergence.M2ResidualFormula FMSA.Convergence.M2JacobianFormula
open FMSA.Convergence.PolynomialNewtonMap FMSA.Convergence.NewtonBoxExistence
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def equation_0 : MvPolynomial (Fin 10) ℝ :=
  ((MvPolynomial.C ((((-54289 : ℝ)/531441)*(Real.pi^1)⁻¹)+(((-2809 : ℝ)/531441)*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((24698 : ℝ)/531441)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^2*(MvPolynomial.X 2)^1)+(MvPolynomial.C ((((-35699 : ℝ)/177147)*(Real.pi^1)⁻¹)+(((2809 : ℝ)/354294)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^2)+(MvPolynomial.C ((((-88507 : ℝ)/18108360)*(Real.pi^1)⁻¹)+(((-2531 : ℝ)/905418)*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 1)^1*(MvPolynomial.X 3)^1)+(MvPolynomial.C ((((-24353 : ℝ)/78732)*(Real.pi^1)⁻¹)+(((12655 : ℝ)/452709)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 1)^1)+(MvPolynomial.C (((7441 : ℝ)/6561)+(((5150 : ℝ)/6561)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1)+(MvPolynomial.C (((-10 : ℝ)/9)*Real.pi)*(MvPolynomial.X 4)^1))

def equation_1 : MvPolynomial (Fin 10) ℝ :=
  ((MvPolynomial.C ((((-25853 : ℝ)/905418)*(Real.pi^1)⁻¹)+(((-72499 : ℝ)/18108360)*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 1)^1*(MvPolynomial.X 2)^1)+(MvPolynomial.C ((((-8849 : ℝ)/524880)*(Real.pi^1)⁻¹)+(((72499 : ℝ)/12072240)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 1)^1)+(MvPolynomial.C ((((-12769 : ℝ)/4665600)*(Real.pi^1)⁻¹)+(((-10201 : ℝ)/4665600)*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/2332800)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^2*(MvPolynomial.X 3)^1)+(MvPolynomial.C ((((-23077 : ℝ)/466560)*(Real.pi^1)⁻¹)+(((10201 : ℝ)/466560)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^2)+(MvPolynomial.C (((2053 : ℝ)/1944)+(((23 : ℝ)/1944)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1)+(MvPolynomial.C (((-1 : ℝ)/6)*Real.pi)*(MvPolynomial.X 4)^1*(MvPolynomial.X 5)^1))

def equation_2 : MvPolynomial (Fin 10) ℝ :=
  ((MvPolynomial.C (((-108578 : ℝ)/531441)+(((-5618 : ℝ)/531441)*(Real.exp ((-18 : ℝ)/5)))+(((49396 : ℝ)/531441)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 2)^2)+(MvPolynomial.C (((-24698 : ℝ)/177147)+(((5618 : ℝ)/177147)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 2)^1)+(MvPolynomial.C ((-2809 : ℝ)/118098)*(MvPolynomial.X 0)^1)+(MvPolynomial.C (((-88507 : ℝ)/9054180)+(((-2531 : ℝ)/452709)*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 2)^1*(MvPolynomial.X 3)^1)+(MvPolynomial.C (((-24353 : ℝ)/39366)+(((25310 : ℝ)/452709)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 2)^1)+(MvPolynomial.C (((143 : ℝ)/13122)+(((2531 : ℝ)/301806)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 3)^1)+(MvPolynomial.C ((-12655 : ℝ)/150903)*(MvPolynomial.X 1)^1)+(MvPolynomial.C ((((14882 : ℝ)/6561)*Real.pi)+(((10300 : ℝ)/6561)*Real.pi*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 2)^1)+(MvPolynomial.C (((-5150 : ℝ)/2187)*Real.pi)))

def equation_3 : MvPolynomial (Fin 10) ℝ :=
  ((MvPolynomial.C (((-25853 : ℝ)/452709)+(((-72499 : ℝ)/9054180)*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 2)^1*(MvPolynomial.X 3)^1)+(MvPolynomial.C (((410 : ℝ)/19683)+(((72499 : ℝ)/905418)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 2)^1)+(MvPolynomial.C (((-8849 : ℝ)/262440)+(((72499 : ℝ)/6036120)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 3)^1)+(MvPolynomial.C ((-72499 : ℝ)/603612)*(MvPolynomial.X 0)^1)+(MvPolynomial.C (((-12769 : ℝ)/2332800)+(((-10201 : ℝ)/2332800)*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/1166400)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 3)^2)+(MvPolynomial.C (((-11413 : ℝ)/116640)+(((10201 : ℝ)/116640)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 3)^1)+(MvPolynomial.C ((-10201 : ℝ)/23328)*(MvPolynomial.X 1)^1)+(MvPolynomial.C ((((2053 : ℝ)/972)*Real.pi)+(((23 : ℝ)/972)*Real.pi*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 3)^1)+(MvPolynomial.C (((-115 : ℝ)/486)*Real.pi)))

def equation_4 : MvPolynomial (Fin 10) ℝ :=
  ((MvPolynomial.C ((((-54289 : ℝ)/531441)*(Real.pi^1)⁻¹)+(((-2809 : ℝ)/531441)*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((24698 : ℝ)/531441)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^2*(MvPolynomial.X 8)^1)+(MvPolynomial.C ((((-88507 : ℝ)/18108360)*(Real.pi^1)⁻¹)+(((-2531 : ℝ)/905418)*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 1)^1*(MvPolynomial.X 9)^1)+(MvPolynomial.C ((((-108578 : ℝ)/531441)*(Real.pi^1)⁻¹)+(((-5618 : ℝ)/531441)*(Real.pi^1)⁻¹*(Real.exp ((-18 : ℝ)/5)))+(((49396 : ℝ)/531441)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 2)^1*(MvPolynomial.X 6)^1)+(MvPolynomial.C ((((-88507 : ℝ)/18108360)*(Real.pi^1)⁻¹)+(((-2531 : ℝ)/905418)*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 3)^1*(MvPolynomial.X 7)^1)+(MvPolynomial.C ((((-71398 : ℝ)/177147)*(Real.pi^1)⁻¹)+(((2809 : ℝ)/177147)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 6)^1)+(MvPolynomial.C ((((-24353 : ℝ)/78732)*(Real.pi^1)⁻¹)+(((12655 : ℝ)/452709)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 7)^1)+(MvPolynomial.C ((((-88507 : ℝ)/18108360)*(Real.pi^1)⁻¹)+(((-2531 : ℝ)/905418)*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/39366)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/787320)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 3)^1*(MvPolynomial.X 6)^1)+(MvPolynomial.C ((((-24353 : ℝ)/78732)*(Real.pi^1)⁻¹)+(((12655 : ℝ)/452709)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 6)^1)+(MvPolynomial.C (((7441 : ℝ)/6561)+(((5150 : ℝ)/6561)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 6)^1)+(MvPolynomial.C (((-10 : ℝ)/9)*Real.pi)))

def equation_5 : MvPolynomial (Fin 10) ℝ :=
  ((MvPolynomial.C ((((-25853 : ℝ)/905418)*(Real.pi^1)⁻¹)+(((-72499 : ℝ)/18108360)*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 1)^1*(MvPolynomial.X 8)^1)+(MvPolynomial.C ((((-25853 : ℝ)/905418)*(Real.pi^1)⁻¹)+(((-72499 : ℝ)/18108360)*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 2)^1*(MvPolynomial.X 7)^1)+(MvPolynomial.C ((((-8849 : ℝ)/524880)*(Real.pi^1)⁻¹)+(((72499 : ℝ)/12072240)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 7)^1)+(MvPolynomial.C ((((-12769 : ℝ)/4665600)*(Real.pi^1)⁻¹)+(((-10201 : ℝ)/4665600)*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/2332800)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^2*(MvPolynomial.X 9)^1)+(MvPolynomial.C ((((-25853 : ℝ)/905418)*(Real.pi^1)⁻¹)+(((-72499 : ℝ)/18108360)*(Real.pi^1)⁻¹*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/39366)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/787320)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 2)^1*(MvPolynomial.X 6)^1)+(MvPolynomial.C ((((-12769 : ℝ)/2332800)*(Real.pi^1)⁻¹)+(((-10201 : ℝ)/2332800)*(Real.pi^1)⁻¹*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/1166400)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 3)^1*(MvPolynomial.X 7)^1)+(MvPolynomial.C ((((-8849 : ℝ)/524880)*(Real.pi^1)⁻¹)+(((72499 : ℝ)/12072240)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 6)^1)+(MvPolynomial.C ((((-23077 : ℝ)/233280)*(Real.pi^1)⁻¹)+(((10201 : ℝ)/233280)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 7)^1)+(MvPolynomial.C (((-1 : ℝ)/6)*Real.pi)*(MvPolynomial.X 5)^1)+(MvPolynomial.C (((2053 : ℝ)/1944)+(((23 : ℝ)/1944)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 7)^1))

def equation_6 : MvPolynomial (Fin 10) ℝ :=
  ((MvPolynomial.C (((-217156 : ℝ)/531441)+(((-11236 : ℝ)/531441)*(Real.exp ((-18 : ℝ)/5)))+(((98792 : ℝ)/531441)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 2)^1*(MvPolynomial.X 8)^1)+(MvPolynomial.C (((-24698 : ℝ)/177147)+(((5618 : ℝ)/177147)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 8)^1)+(MvPolynomial.C (((-88507 : ℝ)/9054180)+(((-2531 : ℝ)/452709)*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 2)^1*(MvPolynomial.X 9)^1)+(MvPolynomial.C (((-88507 : ℝ)/9054180)+(((-2531 : ℝ)/452709)*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 3)^1*(MvPolynomial.X 8)^1)+(MvPolynomial.C (((-24353 : ℝ)/39366)+(((25310 : ℝ)/452709)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 8)^1)+(MvPolynomial.C (((143 : ℝ)/13122)+(((2531 : ℝ)/301806)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 9)^1)+(MvPolynomial.C (((-108578 : ℝ)/531441)+(((-5618 : ℝ)/531441)*(Real.exp ((-18 : ℝ)/5)))+(((49396 : ℝ)/531441)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 2)^2*(MvPolynomial.X 6)^1)+(MvPolynomial.C (((-88507 : ℝ)/9054180)+(((-2531 : ℝ)/452709)*(Real.exp ((-69 : ℝ)/5)))+(((-143 : ℝ)/19683)*(Real.exp ((-9 : ℝ)/5)))+(((24353 : ℝ)/393660)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 2)^1*(MvPolynomial.X 3)^1*(MvPolynomial.X 7)^1)+(MvPolynomial.C (((-24698 : ℝ)/177147)+(((5618 : ℝ)/177147)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 2)^1*(MvPolynomial.X 6)^1)+(MvPolynomial.C (((-24353 : ℝ)/39366)+(((25310 : ℝ)/452709)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 2)^1*(MvPolynomial.X 7)^1)+(MvPolynomial.C (((143 : ℝ)/13122)+(((2531 : ℝ)/301806)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 3)^1*(MvPolynomial.X 7)^1)+(MvPolynomial.C ((-2809 : ℝ)/118098)*(MvPolynomial.X 6)^1)+(MvPolynomial.C ((-12655 : ℝ)/150903)*(MvPolynomial.X 7)^1)+(MvPolynomial.C ((((14882 : ℝ)/6561)*Real.pi)+(((10300 : ℝ)/6561)*Real.pi*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 8)^1))

def equation_7 : MvPolynomial (Fin 10) ℝ :=
  ((MvPolynomial.C (((-25853 : ℝ)/452709)+(((-72499 : ℝ)/9054180)*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 2)^1*(MvPolynomial.X 9)^1)+(MvPolynomial.C (((-25853 : ℝ)/452709)+(((-72499 : ℝ)/9054180)*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 3)^1*(MvPolynomial.X 8)^1)+(MvPolynomial.C (((410 : ℝ)/19683)+(((72499 : ℝ)/905418)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 8)^1)+(MvPolynomial.C (((-8849 : ℝ)/262440)+(((72499 : ℝ)/6036120)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 9)^1)+(MvPolynomial.C (((-12769 : ℝ)/1166400)+(((-10201 : ℝ)/1166400)*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/583200)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 3)^1*(MvPolynomial.X 9)^1)+(MvPolynomial.C (((-11413 : ℝ)/116640)+(((10201 : ℝ)/116640)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 9)^1)+(MvPolynomial.C (((-25853 : ℝ)/452709)+(((-72499 : ℝ)/9054180)*(Real.exp ((-69 : ℝ)/5)))+(((-41 : ℝ)/19683)*(Real.exp (-12 : ℝ)))+(((8849 : ℝ)/393660)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 2)^1*(MvPolynomial.X 3)^1*(MvPolynomial.X 6)^1)+(MvPolynomial.C (((410 : ℝ)/19683)+(((72499 : ℝ)/905418)*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 2)^1*(MvPolynomial.X 6)^1)+(MvPolynomial.C (((-12769 : ℝ)/2332800)+(((-10201 : ℝ)/2332800)*(Real.exp (-24 : ℝ)))+(((11413 : ℝ)/1166400)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 3)^2*(MvPolynomial.X 7)^1)+(MvPolynomial.C (((-8849 : ℝ)/262440)+(((72499 : ℝ)/6036120)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 3)^1*(MvPolynomial.X 6)^1)+(MvPolynomial.C (((-11413 : ℝ)/116640)+(((10201 : ℝ)/116640)*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 3)^1*(MvPolynomial.X 7)^1)+(MvPolynomial.C ((-72499 : ℝ)/603612)*(MvPolynomial.X 6)^1)+(MvPolynomial.C ((-10201 : ℝ)/23328)*(MvPolynomial.X 7)^1)+(MvPolynomial.C ((((2053 : ℝ)/972)*Real.pi)+(((23 : ℝ)/972)*Real.pi*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 9)^1))

def equation_8 : MvPolynomial (Fin 10) ℝ :=
  ((MvPolynomial.C ((((-520 : ℝ)/2187)*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 2)^1)+(MvPolynomial.C (((-566 : ℝ)/729)*(Real.pi^1)⁻¹)*(MvPolynomial.X 0)^1)+(MvPolynomial.C ((((-23 : ℝ)/3240)*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 3)^1)+(MvPolynomial.C (((-227 : ℝ)/324)*(Real.pi^1)⁻¹)*(MvPolynomial.X 1)^1)+(MvPolynomial.C ((40 : ℝ)/27)))

def equation_9 : MvPolynomial (Fin 10) ℝ :=
  ((MvPolynomial.C ((((-520 : ℝ)/2187)*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 0)^1*(MvPolynomial.X 8)^1)+(MvPolynomial.C ((((-23 : ℝ)/3240)*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 1)^1*(MvPolynomial.X 9)^1)+(MvPolynomial.C ((((-520 : ℝ)/2187)*(Real.pi^1)⁻¹)+(((1132 : ℝ)/2187)*(Real.pi^1)⁻¹*(Real.exp ((-9 : ℝ)/5))))*(MvPolynomial.X 2)^1*(MvPolynomial.X 6)^1)+(MvPolynomial.C ((((-23 : ℝ)/3240)*(Real.pi^1)⁻¹)+(((227 : ℝ)/3240)*(Real.pi^1)⁻¹*(Real.exp (-12 : ℝ))))*(MvPolynomial.X 3)^1*(MvPolynomial.X 7)^1)+(MvPolynomial.C (((-566 : ℝ)/729)*(Real.pi^1)⁻¹)*(MvPolynomial.X 6)^1)+(MvPolynomial.C (((-227 : ℝ)/324)*(Real.pi^1)⁻¹)*(MvPolynomial.X 7)^1))

def polynomial : Fin 10 → MvPolynomial (Fin 10) ℝ :=
  ![equation_0,equation_1,equation_2,equation_3,equation_4,equation_5,equation_6,equation_7,equation_8,equation_9]

private theorem entry_0 (y : Fin 10 → ℝ) :
    MvPolynomial.eval y equation_0 = system y 0 := by
  change MvPolynomial.eval y equation_0 = residualFormula (strength (y 5)) (y 4) (amplitudes y) 0
  norm_num [equation_0,amplitudes,velocity,residualFormula,formula,
    strength,forcing,M2ZeroMode.zeroMode,M2ZeroMode.gradient,M2ZeroMode.alpha,M2ZeroMode.beta,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four,Fin.castAdd,Fin.castLE,Fin.natAdd,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

private theorem entry_1 (y : Fin 10 → ℝ) :
    MvPolynomial.eval y equation_1 = system y 1 := by
  change MvPolynomial.eval y equation_1 = residualFormula (strength (y 5)) (y 4) (amplitudes y) 1
  norm_num [equation_1,amplitudes,velocity,residualFormula,formula,
    strength,forcing,M2ZeroMode.zeroMode,M2ZeroMode.gradient,M2ZeroMode.alpha,M2ZeroMode.beta,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four,Fin.castAdd,Fin.castLE,Fin.natAdd,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

private theorem entry_2 (y : Fin 10 → ℝ) :
    MvPolynomial.eval y equation_2 = system y 2 := by
  change MvPolynomial.eval y equation_2 = residualFormula (strength (y 5)) (y 4) (amplitudes y) 2
  norm_num [equation_2,amplitudes,velocity,residualFormula,formula,
    strength,forcing,M2ZeroMode.zeroMode,M2ZeroMode.gradient,M2ZeroMode.alpha,M2ZeroMode.beta,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four,Fin.castAdd,Fin.castLE,Fin.natAdd,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

private theorem entry_3 (y : Fin 10 → ℝ) :
    MvPolynomial.eval y equation_3 = system y 3 := by
  change MvPolynomial.eval y equation_3 = residualFormula (strength (y 5)) (y 4) (amplitudes y) 3
  norm_num [equation_3,amplitudes,velocity,residualFormula,formula,
    strength,forcing,M2ZeroMode.zeroMode,M2ZeroMode.gradient,M2ZeroMode.alpha,M2ZeroMode.beta,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four,Fin.castAdd,Fin.castLE,Fin.natAdd,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

private theorem entry_4 (y : Fin 10 → ℝ) :
    MvPolynomial.eval y equation_4 = system y 4 := by
  change MvPolynomial.eval y equation_4 = (formula (amplitudes y)).mulVec (velocity y) 0-forcing (y 5) 0
  norm_num [equation_4,amplitudes,velocity,residualFormula,formula,
    strength,forcing,M2ZeroMode.zeroMode,M2ZeroMode.gradient,M2ZeroMode.alpha,M2ZeroMode.beta,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four,Fin.castAdd,Fin.castLE,Fin.natAdd,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

private theorem entry_5 (y : Fin 10 → ℝ) :
    MvPolynomial.eval y equation_5 = system y 5 := by
  change MvPolynomial.eval y equation_5 = (formula (amplitudes y)).mulVec (velocity y) 1-forcing (y 5) 1
  norm_num [equation_5,amplitudes,velocity,residualFormula,formula,
    strength,forcing,M2ZeroMode.zeroMode,M2ZeroMode.gradient,M2ZeroMode.alpha,M2ZeroMode.beta,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four,Fin.castAdd,Fin.castLE,Fin.natAdd,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

private theorem entry_6 (y : Fin 10 → ℝ) :
    MvPolynomial.eval y equation_6 = system y 6 := by
  change MvPolynomial.eval y equation_6 = (formula (amplitudes y)).mulVec (velocity y) 2-forcing (y 5) 2
  norm_num [equation_6,amplitudes,velocity,residualFormula,formula,
    strength,forcing,M2ZeroMode.zeroMode,M2ZeroMode.gradient,M2ZeroMode.alpha,M2ZeroMode.beta,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four,Fin.castAdd,Fin.castLE,Fin.natAdd,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

private theorem entry_7 (y : Fin 10 → ℝ) :
    MvPolynomial.eval y equation_7 = system y 7 := by
  change MvPolynomial.eval y equation_7 = (formula (amplitudes y)).mulVec (velocity y) 3-forcing (y 5) 3
  norm_num [equation_7,amplitudes,velocity,residualFormula,formula,
    strength,forcing,M2ZeroMode.zeroMode,M2ZeroMode.gradient,M2ZeroMode.alpha,M2ZeroMode.beta,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four,Fin.castAdd,Fin.castLE,Fin.natAdd,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

private theorem entry_8 (y : Fin 10 → ℝ) :
    MvPolynomial.eval y equation_8 = system y 8 := by
  change MvPolynomial.eval y equation_8 = M2ZeroMode.zeroMode (amplitudes y)
  norm_num [equation_8,amplitudes,velocity,residualFormula,formula,
    strength,forcing,M2ZeroMode.zeroMode,M2ZeroMode.gradient,M2ZeroMode.alpha,M2ZeroMode.beta,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four,Fin.castAdd,Fin.castLE,Fin.natAdd,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

private theorem entry_9 (y : Fin 10 → ℝ) :
    MvPolynomial.eval y equation_9 = system y 9 := by
  change MvPolynomial.eval y equation_9 = ∑ k, M2ZeroMode.gradient (amplitudes y) k*velocity y k
  norm_num [equation_9,amplitudes,velocity,residualFormula,formula,
    strength,forcing,M2ZeroMode.zeroMode,M2ZeroMode.gradient,M2ZeroMode.alpha,M2ZeroMode.beta,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four,Fin.castAdd,Fin.castLE,Fin.natAdd,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

/-- Literal polynomial evaluation equals ALL ten actual equations. -/
theorem system_eq_polynomialMap : system = polynomialMap polynomial := by
  funext y i
  fin_cases i
  · exact (entry_0 y).symm
  · exact (entry_1 y).symm
  · exact (entry_2 y).symm
  · exact (entry_3 y).symm
  · exact (entry_4 y).symm
  · exact (entry_5 y).symm
  · exact (entry_6 y).symm
  · exact (entry_7 y).symm
  · exact (entry_8 y).symm
  · exact (entry_9 y).symm

/-- The formal polynomial partials are the actual full system derivative. -/
theorem system_hasFDerivAt (y : Fin 10 → ℝ) :
    HasFDerivAt system (matrixCLM (jacobian polynomial y)) y := by
  rw [system_eq_polynomialMap]
  exact polynomialMap_hasFDerivAt polynomial y

end FMSA.Convergence.M2TangencyPolynomials

/-- info: 'FMSA.Convergence.M2TangencyPolynomials.system_eq_polynomialMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencyPolynomials.system_eq_polynomialMap

/-- info: 'FMSA.Convergence.M2TangencyPolynomials.system_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencyPolynomials.system_hasFDerivAt

