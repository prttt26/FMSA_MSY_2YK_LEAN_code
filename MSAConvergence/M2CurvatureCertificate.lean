import MSAConvergence.M2BranchSecondDerivative
import MSAConvergence.M2TangencyJacobianBounds

/-! Kernel-checked local curvature bounds from actual full-Jacobian entries.
No external Hessian, inverse, acceleration or analytic enclosure is assumed. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2CurvatureCertificate
open FMSA.Convergence.M2BranchSecondDerivative
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.NewtonBoxExistence
open FMSA.Convergence.RealIntervalCertificates
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

abbrev preconditioner := M2KernelCertificate.preconditioner
def approximateAcceleration (y : T) : E := matrixCLM preconditioner (accelerationForcing y)

def radius : Matrix (Fin 4) (Fin 4) ℝ :=
  !![((515960894976933 : ℝ) / 40000000000000000000000), ((1699145935416127 : ℝ) / 250000000000000000000000), ((308771927652181 : ℝ) / 4000000000000000000000), ((3086980868191403 : ℝ) / 1000000000000000000000000);
    ((183044250735509 : ℝ) / 125000000000000000000000), ((726657207045771 : ℝ) / 1000000000000000000000000), ((2210852973118251 : ℝ) / 250000000000000000000000), ((1333424713739 : ℝ) / 3906250000000000000000);
    ((27880119630483 : ℝ) / 200000000000000000000000), ((40147880246573 : ℝ) / 500000000000000000000000), ((519554695846491 : ℝ) / 500000000000000000000000), ((726115608071 : ℝ) / 20000000000000000000000);
    ((16219768504629 : ℝ) / 500000000000000000000000), ((24102139729 : ℝ) / 1250000000000000000000), ((180321409771479 : ℝ) / 1000000000000000000000000), ((32469928011973 : ℝ) / 500000000000000000000000)]

private theorem e_bound_0_0 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 0 0| ≤ ((515960894976933 : ℝ) / 40000000000000000000000) := by
  let v0 : ℝ := ((1 : ℝ) / 1)
  have h0 : ((1 : ℝ) / 1) ≤ v0 ∧ v0 ≤ ((1 : ℝ) / 1) := by constructor <;> norm_num [v0]
  let v1 : ℝ := ((-7689872965427469 : ℝ) / 281474976710656)
  have h1 : ((-7689872965427469 : ℝ) / 281474976710656) ≤ v1 ∧ v1 ≤ ((-7689872965427469 : ℝ) / 281474976710656) := by constructor <;> norm_num [v1]
  let v2 : ℝ := jacobian y 5 6
  have h2 : ((652535574979217430457 : ℝ) / 5000000000000000000000) ≤ v2 ∧ v2 ≤ ((130507115055637303510633 : ℝ) / 1000000000000000000000000) := by
    simpa [v2,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 6
  let v3 : ℝ := v1*v2
  have h3 : ((-3565443534591414892096973 : ℝ) / 1000000000000000000000000) ≤ v3 ∧ v3 ≤ ((-1782721766478926385356673 : ℝ) / 500000000000000000000000) := mul_interval h1 h2 (by norm_num) (by norm_num)
  let v4 : ℝ := v0+v3
  have h4 : ((-2565443534591414892096973 : ℝ) / 1000000000000000000000000) ≤ v4 ∧ v4 ≤ ((-1282721766478926385356673 : ℝ) / 500000000000000000000000) := add_interval h0 h3 (by norm_num) (by norm_num)
  let v5 : ℝ := ((-5864275639152445 : ℝ) / 562949953421312)
  have h5 : ((-5864275639152445 : ℝ) / 562949953421312) ≤ v5 ∧ v5 ≤ ((-5864275639152445 : ℝ) / 562949953421312) := by constructor <;> norm_num [v5]
  let v6 : ℝ := jacobian y 6 6
  have h6 : ((-155834307137490777530731 : ℝ) / 1000000000000000000000000) ≤ v6 ∧ v6 ≤ ((-31166861409571967260273 : ℝ) / 200000000000000000000000) := by
    simpa [v6,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 6
  let v7 : ℝ := v5*v6
  have h7 : ((16233331666714551851643 : ℝ) / 10000000000000000000000) ≤ v7 ∧ v7 ≤ ((1623333167605144835498637 : ℝ) / 1000000000000000000000000) := mul_interval h5 h6 (by norm_num) (by norm_num)
  let v8 : ℝ := v4+v7
  have h8 : ((-942110367919959706932673 : ℝ) / 1000000000000000000000000) ≤ v8 ∧ v8 ≤ ((-942110365352707935214709 : ℝ) / 1000000000000000000000000) := add_interval h4 h7 (by norm_num) (by norm_num)
  let v9 : ℝ := ((-5717564422701105 : ℝ) / 281474976710656)
  have h9 : ((-5717564422701105 : ℝ) / 281474976710656) ≤ v9 ∧ v9 ≤ ((-5717564422701105 : ℝ) / 281474976710656) := by constructor <;> norm_num [v9]
  let v10 : ℝ := jacobian y 4 6
  have h10 : ((-23870084181672384861613 : ℝ) / 500000000000000000000000) ≤ v10 ∧ v10 ≤ ((-1909606688811010103167 : ℝ) / 40000000000000000000000) := by
    simpa [v10,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 6
  let v11 : ℝ := v9*v10
  have h11 : ((969739778726531977542627 : ℝ) / 1000000000000000000000000) ≤ v11 ∧ v11 ≤ ((969739801945553718914833 : ℝ) / 1000000000000000000000000) := mul_interval h9 h10 (by norm_num) (by norm_num)
  let v12 : ℝ := v8+v11
  have h12 : ((13814705403286135304977 : ℝ) / 500000000000000000000000) ≤ v12 ∧ v12 ≤ ((6907359148211445925031 : ℝ) / 250000000000000000000000) := add_interval h8 h11 (by norm_num) (by norm_num)
  let v13 : ℝ := ((1759319900783941 : ℝ) / 4503599627370496)
  have h13 : ((1759319900783941 : ℝ) / 4503599627370496) ≤ v13 ∧ v13 ≤ ((1759319900783941 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v13]
  let v14 : ℝ := jacobian y 7 6
  have h14 : ((-14145450437925655174083 : ℝ) / 200000000000000000000000) ≤ v14 ∧ v14 ≤ ((-7072725215950157735069 : ℝ) / 100000000000000000000000) := by
    simpa [v14,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 6
  let v15 : ℝ := v13*v14
  have h15 : ((-27629423705594645033279 : ℝ) / 1000000000000000000000000) ≤ v15 ∧ v15 ≤ ((-27629423693825725805079 : ℝ) / 1000000000000000000000000) := mul_interval h13 h14 (by norm_num) (by norm_num)
  let v16 : ℝ := v12+v15
  have h16 : ((-515960894976933 : ℝ) / 40000000000000000000000) ≤ v16 ∧ v16 ≤ ((2579804011579009 : ℝ) / 200000000000000000000000) := add_interval h12 h15 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 0 0 = v16 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h16 (by norm_num) (by norm_num)

private theorem e_bound_0_1 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 0 1| ≤ ((1699145935416127 : ℝ) / 250000000000000000000000) := by
  let v0 : ℝ := ((-7689872965427469 : ℝ) / 281474976710656)
  have h0 : ((-7689872965427469 : ℝ) / 281474976710656) ≤ v0 ∧ v0 ≤ ((-7689872965427469 : ℝ) / 281474976710656) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 5 7
  have h1 : ((258656993837854629939027 : ℝ) / 200000000000000000000000) ≤ v1 ∧ v1 ≤ ((80830310585041675816059 : ℝ) / 62500000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 7
  let v2 : ℝ := v0*v1
  have h2 : ((-35332437855403086831056703 : ℝ) / 1000000000000000000000000) ≤ v2 ∧ v2 ≤ ((-8833109462680156548884179 : ℝ) / 250000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-5864275639152445 : ℝ) / 562949953421312)
  have h3 : ((-5864275639152445 : ℝ) / 562949953421312) ≤ v3 ∧ v3 ≤ ((-5864275639152445 : ℝ) / 562949953421312) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 6 7
  have h4 : ((-211574327710786693809299 : ℝ) / 500000000000000000000000) ≤ v4 ∧ v4 ≤ ((-211574327635688143215797 : ℝ) / 500000000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 7
  let v5 : ℝ := v3*v4
  have h5 : ((881591813185894959046581 : ℝ) / 200000000000000000000000) ≤ v5 ∧ v5 ≤ ((550994883436760616044079 : ℝ) / 125000000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((-15462239394736806017911899 : ℝ) / 500000000000000000000000) ≤ v6 ∧ v6 ≤ ((-7731119695806635316796021 : ℝ) / 250000000000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-5717564422701105 : ℝ) / 281474976710656)
  have h7 : ((-5717564422701105 : ℝ) / 281474976710656) ≤ v7 ∧ v7 ≤ ((-5717564422701105 : ℝ) / 281474976710656) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 4 7
  have h8 : ((-382483385496709632069843 : ℝ) / 250000000000000000000000) ≤ v8 ∧ v8 ≤ ((-95620846351602915583067 : ℝ) / 62500000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 7
  let v9 : ℝ := v7*v8
  have h9 : ((6215468024134834039279597 : ℝ) / 200000000000000000000000) ≤ v9 ∧ v9 ≤ ((31077340128011013638000509 : ℝ) / 1000000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((152861331200558160574187 : ℝ) / 1000000000000000000000000) ≤ v10 ∧ v10 ≤ ((6114453791378894832657 : ℝ) / 40000000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((1759319900783941 : ℝ) / 4503599627370496)
  have h11 : ((1759319900783941 : ℝ) / 4503599627370496) ≤ v11 ∧ v11 ≤ ((1759319900783941 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 7
  have h12 : ((-78260498791211800413401 : ℝ) / 200000000000000000000000) ≤ v12 ∧ v12 ≤ ((-195651246966186367427959 : ℝ) / 500000000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 7
  let v13 : ℝ := v11*v12
  have h13 : ((-152861337997141610040027 : ℝ) / 1000000000000000000000000) ≤ v13 ∧ v13 ≤ ((-152861337987888629151917 : ℝ) / 1000000000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-84957293118323 : ℝ) / 12500000000000000000000) ≤ v14 ∧ v14 ≤ ((1699145935416127 : ℝ) / 250000000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 0 1 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_0_2 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 0 2| ≤ ((308771927652181 : ℝ) / 4000000000000000000000) := by
  let v0 : ℝ := ((-7689872965427469 : ℝ) / 281474976710656)
  have h0 : ((-7689872965427469 : ℝ) / 281474976710656) ≤ v0 ∧ v0 ≤ ((-7689872965427469 : ℝ) / 281474976710656) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 5 8
  have h1 : ((7013347285928550056021 : ℝ) / 4000000000000000000000) ≤ v1 ∧ v1 ≤ ((27395887849477761289867 : ℝ) / 15625000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 8
  let v2 : ℝ := v0*v1
  have h2 : ((-23950508118284906083181361 : ℝ) / 500000000000000000000000) ≤ v2 ∧ v2 ≤ ((-47901016212407006510088893 : ℝ) / 1000000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-5864275639152445 : ℝ) / 562949953421312)
  have h3 : ((-5864275639152445 : ℝ) / 562949953421312) ≤ v3 ∧ v3 ≤ ((-5864275639152445 : ℝ) / 562949953421312) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 6 8
  have h4 : ((2061743844080346340918441 : ℝ) / 200000000000000000000000) ≤ v4 ∧ v4 ≤ ((2061743845047320678197891 : ℝ) / 200000000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 8
  let v5 : ℝ := v3*v4
  have h5 : ((-107386403810880679506523889 : ℝ) / 1000000000000000000000000) ≤ v5 ∧ v5 ≤ ((-21477280752103119613923409 : ℝ) / 200000000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((-155287420047450491672886611 : ℝ) / 1000000000000000000000000) ≤ v6 ∧ v6 ≤ ((-77643709986461302289852969 : ℝ) / 500000000000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-5717564422701105 : ℝ) / 281474976710656)
  have h7 : ((-5717564422701105 : ℝ) / 281474976710656) ≤ v7 ∧ v7 ≤ ((-5717564422701105 : ℝ) / 281474976710656) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 4 8
  have h8 : ((-7626462905965564659250679 : ℝ) / 1000000000000000000000000) ≤ v8 ∧ v8 ≤ ((-7626462902042735255970459 : ℝ) / 1000000000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 8
  let v9 : ℝ := v7*v8
  have h9 : ((154915344409436405811811821 : ℝ) / 1000000000000000000000000) ≤ v9 ∧ v9 ≤ ((77457672244560163450016473 : ℝ) / 500000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((-37207563801408586107479 : ℝ) / 100000000000000000000000) ≤ v10 ∧ v10 ≤ ((-11627358868821177489781 : ℝ) / 31250000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((1759319900783941 : ℝ) / 4503599627370496)
  have h11 : ((1759319900783941 : ℝ) / 4503599627370496) ≤ v11 ∧ v11 ≤ ((1759319900783941 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 8
  have h12 : ((38098343713861719391029 : ℝ) / 40000000000000000000000) ≤ v12 ∧ v12 ≤ ((952458593292201940752697 : ℝ) / 1000000000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 8
  let v13 : ℝ := v11*v12
  have h13 : ((18603778041055197401477 : ℝ) / 50000000000000000000000) ≤ v13 ∧ v13 ≤ ((93018890248799875401449 : ℝ) / 250000000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-308771927652181 : ℝ) / 4000000000000000000000) ≤ v14 ∧ v14 ≤ ((19298230455483201 : ℝ) / 250000000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 0 2 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_0_3 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 0 3| ≤ ((3086980868191403 : ℝ) / 1000000000000000000000000) := by
  let v0 : ℝ := ((-7689872965427469 : ℝ) / 281474976710656)
  have h0 : ((-7689872965427469 : ℝ) / 281474976710656) ≤ v0 ∧ v0 ≤ ((-7689872965427469 : ℝ) / 281474976710656) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 5 9
  have h1 : ((-36616236258947606092379 : ℝ) / 250000000000000000000000) ≤ v1 ∧ v1 ≤ ((-146464944970892504313817 : ℝ) / 1000000000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 9
  let v2 : ℝ := v0*v1
  have h2 : ((32011280970735021026193 : ℝ) / 8000000000000000000000) ≤ v2 ∧ v2 ≤ ((2000705061557441704697387 : ℝ) / 500000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-5864275639152445 : ℝ) / 562949953421312)
  have h3 : ((-5864275639152445 : ℝ) / 562949953421312) ≤ v3 ∧ v3 ≤ ((-5864275639152445 : ℝ) / 562949953421312) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 6 9
  have h4 : ((-31306286695260580317093 : ℝ) / 500000000000000000000000) ≤ v4 ∧ v4 ≤ ((-31306286654447633378177 : ℝ) / 500000000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 9
  let v5 : ℝ := v3*v4
  have h5 : ((652238065086409883583527 : ℝ) / 1000000000000000000000000) ≤ v5 ∧ v5 ≤ ((652238065936710586306157 : ℝ) / 1000000000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((1163412046607071877964413 : ℝ) / 250000000000000000000000) ≤ v6 ∧ v6 ≤ ((4653648189051593995700931 : ℝ) / 1000000000000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-5717564422701105 : ℝ) / 281474976710656)
  have h7 : ((-5717564422701105 : ℝ) / 281474976710656) ≤ v7 ∧ v7 ≤ ((-5717564422701105 : ℝ) / 281474976710656) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 4 9
  have h8 : ((90109138152039850910503 : ℝ) / 250000000000000000000000) ≤ v8 ∧ v8 ≤ ((360436552767771718715371 : ℝ) / 1000000000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 9
  let v9 : ℝ := v7*v8
  have h9 : ((-7321500599552312410171757 : ℝ) / 1000000000000000000000000) ≤ v9 ∧ v9 ≤ ((-7321500596310128309996829 : ℝ) / 1000000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((-533570482624804979662821 : ℝ) / 200000000000000000000000) ≤ v10 ∧ v10 ≤ ((-1333926203629267157147949 : ℝ) / 500000000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((1759319900783941 : ℝ) / 4503599627370496)
  have h11 : ((1759319900783941 : ℝ) / 4503599627370496) ≤ v11 ∧ v11 ≤ ((1759319900783941 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 9
  have h12 : ((21341590425028271142213 : ℝ) / 3125000000000000000000) ≤ v12 ∧ v12 ≤ ((6829308936798683676785057 : ℝ) / 1000000000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 9
  let v13 : ℝ := v11*v12
  have h13 : ((666963102509261375816119 : ℝ) / 250000000000000000000000) ≤ v13 ∧ v13 ≤ ((2667852410345515182487301 : ℝ) / 1000000000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-3086979395049629 : ℝ) / 1000000000000000000000000) ≤ v14 ∧ v14 ≤ ((3086980868191403 : ℝ) / 1000000000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 0 3 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_1_0 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 1 0| ≤ ((183044250735509 : ℝ) / 125000000000000000000000) := by
  let v0 : ℝ := ((-8569877571857449 : ℝ) / 144115188075855872)
  have h0 : ((-8569877571857449 : ℝ) / 144115188075855872) ≤ v0 ∧ v0 ≤ ((-8569877571857449 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 7 6
  have h1 : ((-14145450437925655174083 : ℝ) / 200000000000000000000000) ≤ v1 ∧ v1 ≤ ((-7072725215950157735069 : ℝ) / 100000000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 6
  let v2 : ℝ := v0*v1
  have h2 : ((2102914689608502744589 : ℝ) / 500000000000000000000000) ≤ v2 ∧ v2 ≤ ((2102914690504251906789 : ℝ) / 500000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((372160374982343 : ℝ) / 281474976710656)
  have h3 : ((372160374982343 : ℝ) / 281474976710656) ≤ v3 ∧ v3 ≤ ((372160374982343 : ℝ) / 281474976710656) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 6 6
  have h4 : ((-155834307137490777530731 : ℝ) / 1000000000000000000000000) ≤ v4 ∧ v4 ≤ ((-31166861409571967260273 : ℝ) / 200000000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 6
  let v5 : ℝ := v3*v4
  have h5 : ((-206040888100041918433731 : ℝ) / 1000000000000000000000000) ≤ v5 ∧ v5 ≤ ((-12877555498845859208903 : ℝ) / 62500000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((-201835058720824912944553 : ℝ) / 1000000000000000000000000) ≤ v6 ∧ v6 ≤ ((-20183505860052524352887 : ℝ) / 100000000000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((2624911170949731 : ℝ) / 1125899906842624)
  have h7 : ((2624911170949731 : ℝ) / 1125899906842624) ≤ v7 ∧ v7 ≤ ((2624911170949731 : ℝ) / 1125899906842624) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 4 6
  have h8 : ((-23870084181672384861613 : ℝ) / 500000000000000000000000) ≤ v8 ∧ v8 ≤ ((-1909606688811010103167 : ℝ) / 40000000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 6
  let v9 : ℝ := v7*v8
  have h9 : ((-111300925134085402177197 : ℝ) / 1000000000000000000000000) ≤ v9 ∧ v9 ≤ ((-111300922469145182812801 : ℝ) / 1000000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((-1252543935419641260487 : ℝ) / 4000000000000000000000) ≤ v10 ∧ v10 ≤ ((-313135981069670426341671 : ℝ) / 1000000000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((5402920345206155 : ℝ) / 2251799813685248)
  have h11 : ((5402920345206155 : ℝ) / 2251799813685248) ≤ v11 ∧ v11 ≤ ((5402920345206155 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 5 6
  have h12 : ((652535574979217430457 : ℝ) / 5000000000000000000000) ≤ v12 ∧ v12 ≤ ((130507115055637303510633 : ℝ) / 1000000000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 6
  let v13 : ℝ := v11*v12
  have h13 : ((156567991195278212342083 : ℝ) / 500000000000000000000000) ≤ v13 ∧ v13 ≤ ((313135982534024432225743 : ℝ) / 1000000000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-91522118152349 : ℝ) / 62500000000000000000000) ≤ v14 ∧ v14 ≤ ((183044250735509 : ℝ) / 125000000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 1 0 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_1_1 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 1 1| ≤ ((726657207045771 : ℝ) / 1000000000000000000000000) := by
  let v0 : ℝ := ((1 : ℝ) / 1)
  have h0 : ((1 : ℝ) / 1) ≤ v0 ∧ v0 ≤ ((1 : ℝ) / 1) := by constructor <;> norm_num [v0]
  let v1 : ℝ := ((-8569877571857449 : ℝ) / 144115188075855872)
  have h1 : ((-8569877571857449 : ℝ) / 144115188075855872) ≤ v1 ∧ v1 ≤ ((-8569877571857449 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v1]
  let v2 : ℝ := jacobian y 7 7
  have h2 : ((-78260498791211800413401 : ℝ) / 200000000000000000000000) ≤ v2 ∧ v2 ≤ ((-195651246966186367427959 : ℝ) / 500000000000000000000000) := by
    simpa [v2,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 7
  let v3 : ℝ := v1*v2
  have h3 : ((11634493599653900839421 : ℝ) / 500000000000000000000000) ≤ v3 ∧ v3 ≤ ((23268987200716316720481 : ℝ) / 1000000000000000000000000) := mul_interval h1 h2 (by norm_num) (by norm_num)
  let v4 : ℝ := v0+v3
  have h4 : ((511634493599653900839421 : ℝ) / 500000000000000000000000) ≤ v4 ∧ v4 ≤ ((1023268987200716316720481 : ℝ) / 1000000000000000000000000) := add_interval h0 h3 (by norm_num) (by norm_num)
  let v5 : ℝ := ((372160374982343 : ℝ) / 281474976710656)
  have h5 : ((372160374982343 : ℝ) / 281474976710656) ≤ v5 ∧ v5 ≤ ((372160374982343 : ℝ) / 281474976710656) := by constructor <;> norm_num [v5]
  let v6 : ℝ := jacobian y 6 7
  have h6 : ((-211574327710786693809299 : ℝ) / 500000000000000000000000) ≤ v6 ∧ v6 ≤ ((-211574327635688143215797 : ℝ) / 500000000000000000000000) := by
    simpa [v6,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 7
  let v7 : ℝ := v5*v6
  have h7 : ((-279739186970159535436727 : ℝ) / 500000000000000000000000) ≤ v7 ∧ v7 ≤ ((-111895674748346315907357 : ℝ) / 200000000000000000000000) := mul_interval h5 h6 (by norm_num) (by norm_num)
  let v8 : ℝ := v4+v7
  have h8 : ((115947653314747182701347 : ℝ) / 250000000000000000000000) ≤ v8 ∧ v8 ≤ ((28986913341186546073981 : ℝ) / 62500000000000000000000) := add_interval h4 h7 (by norm_num) (by norm_num)
  let v9 : ℝ := ((2624911170949731 : ℝ) / 1125899906842624)
  have h9 : ((2624911170949731 : ℝ) / 1125899906842624) ≤ v9 ∧ v9 ≤ ((2624911170949731 : ℝ) / 1125899906842624) := by constructor <;> norm_num [v9]
  let v10 : ℝ := jacobian y 4 7
  have h10 : ((-382483385496709632069843 : ℝ) / 250000000000000000000000) ≤ v10 ∧ v10 ≤ ((-95620846351602915583067 : ℝ) / 62500000000000000000000) := by
    simpa [v10,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 7
  let v11 : ℝ := v9*v10
  have h11 : ((-3566870927659896891476509 : ℝ) / 1000000000000000000000000) ≤ v11 ∧ v11 ≤ ((-1783435463408908976709553 : ℝ) / 500000000000000000000000) := mul_interval h9 h10 (by norm_num) (by norm_num)
  let v12 : ℝ := v8+v11
  have h12 : ((-3103080314400908160671121 : ℝ) / 1000000000000000000000000) ≤ v12 ∧ v12 ≤ ((-310308031335883321623541 : ℝ) / 100000000000000000000000) := add_interval h8 h11 (by norm_num) (by norm_num)
  let v13 : ℝ := ((5402920345206155 : ℝ) / 2251799813685248)
  have h13 : ((5402920345206155 : ℝ) / 2251799813685248) ≤ v13 ∧ v13 ≤ ((5402920345206155 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v13]
  let v14 : ℝ := jacobian y 5 7
  have h14 : ((258656993837854629939027 : ℝ) / 200000000000000000000000) ≤ v14 ∧ v14 ≤ ((80830310585041675816059 : ℝ) / 62500000000000000000000) := by
    simpa [v14,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 7
  let v15 : ℝ := v13*v14
  have h15 : ((62061606273485019072507 : ℝ) / 20000000000000000000000) ≤ v15 ∧ v15 ≤ ((775770078521372311574103 : ℝ) / 250000000000000000000000) := mul_interval h13 h14 (by norm_num) (by norm_num)
  let v16 : ℝ := v12+v15
  have h16 : ((-726657207045771 : ℝ) / 1000000000000000000000000) ≤ v16 ∧ v16 ≤ ((363328015030501 : ℝ) / 500000000000000000000000) := add_interval h12 h15 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 1 1 = v16 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h16 (by norm_num) (by norm_num)

private theorem e_bound_1_2 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 1 2| ≤ ((2210852973118251 : ℝ) / 250000000000000000000000) := by
  let v0 : ℝ := ((-8569877571857449 : ℝ) / 144115188075855872)
  have h0 : ((-8569877571857449 : ℝ) / 144115188075855872) ≤ v0 ∧ v0 ≤ ((-8569877571857449 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 7 8
  have h1 : ((38098343713861719391029 : ℝ) / 40000000000000000000000) ≤ v1 ∧ v1 ≤ ((952458593292201940752697 : ℝ) / 1000000000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 8
  let v2 : ℝ := v0*v1
  have h2 : ((-28319199543636517957323 : ℝ) / 500000000000000000000000) ≤ v2 ∧ v2 ≤ ((-14159599765192929021221 : ℝ) / 250000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((372160374982343 : ℝ) / 281474976710656)
  have h3 : ((372160374982343 : ℝ) / 281474976710656) ≤ v3 ∧ v3 ≤ ((372160374982343 : ℝ) / 281474976710656) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 6 8
  have h4 : ((2061743844080346340918441 : ℝ) / 200000000000000000000000) ≤ v4 ∧ v4 ≤ ((2061743845047320678197891 : ℝ) / 200000000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 8
  let v5 : ℝ := v3*v4
  have h5 : ((6814987348939629659404799 : ℝ) / 500000000000000000000000) ≤ v5 ∧ v5 ≤ ((2725994940854365272540537 : ℝ) / 200000000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((1696667037348998285361869 : ℝ) / 125000000000000000000000) ≤ v6 ∧ v6 ≤ ((13573336305211054646617801 : ℝ) / 1000000000000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((2624911170949731 : ℝ) / 1125899906842624)
  have h7 : ((2624911170949731 : ℝ) / 1125899906842624) ≤ v7 ∧ v7 ≤ ((2624911170949731 : ℝ) / 1125899906842624) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 4 8
  have h8 : ((-7626462905965564659250679 : ℝ) / 1000000000000000000000000) ≤ v8 ∧ v8 ≤ ((-7626462902042735255970459 : ℝ) / 1000000000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 8
  let v9 : ℝ := v7*v8
  have h9 : ((-17780255203006197596566847 : ℝ) / 1000000000000000000000000) ≤ v9 ∧ v9 ≤ ((-4445063798465138622344387 : ℝ) / 250000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((-841383780842842262734379 : ℝ) / 200000000000000000000000) ≤ v10 ∧ v10 ≤ ((-4206918888649499842759747 : ℝ) / 1000000000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((5402920345206155 : ℝ) / 2251799813685248)
  have h11 : ((5402920345206155 : ℝ) / 2251799813685248) ≤ v11 ∧ v11 ≤ ((5402920345206155 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 5 8
  have h12 : ((7013347285928550056021 : ℝ) / 4000000000000000000000) ≤ v12 ∧ v12 ≤ ((27395887849477761289867 : ℝ) / 15625000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 8
  let v13 : ℝ := v11*v12
  have h13 : ((2103459447685403600689499 : ℝ) / 500000000000000000000000) ≤ v13 ∧ v13 ≤ ((4206918897492911735232751 : ℝ) / 1000000000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-8843404112292897 : ℝ) / 1000000000000000000000000) ≤ v14 ∧ v14 ≤ ((2210852973118251 : ℝ) / 250000000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 1 2 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_1_3 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 1 3| ≤ ((1333424713739 : ℝ) / 3906250000000000000000) := by
  let v0 : ℝ := ((-8569877571857449 : ℝ) / 144115188075855872)
  have h0 : ((-8569877571857449 : ℝ) / 144115188075855872) ≤ v0 ∧ v0 ≤ ((-8569877571857449 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 7 9
  have h1 : ((21341590425028271142213 : ℝ) / 3125000000000000000000) ≤ v1 ∧ v1 ≤ ((6829308936798683676785057 : ℝ) / 1000000000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 9
  let v2 : ℝ := v0*v1
  have h2 : ((-406108074174326427064849 : ℝ) / 1000000000000000000000000) ≤ v2 ∧ v2 ≤ ((-406108074127370296026801 : ℝ) / 1000000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((372160374982343 : ℝ) / 281474976710656)
  have h3 : ((372160374982343 : ℝ) / 281474976710656) ≤ v3 ∧ v3 ≤ ((372160374982343 : ℝ) / 281474976710656) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 6 9
  have h4 : ((-31306286695260580317093 : ℝ) / 500000000000000000000000) ≤ v4 ∧ v4 ≤ ((-31306286654447633378177 : ℝ) / 500000000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 9
  let v5 : ℝ := v3*v4
  have h5 : ((-41392522816653756441059 : ℝ) / 500000000000000000000000) ≤ v5 ∧ v5 ≤ ((-82785045525383449333583 : ℝ) / 1000000000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((-488893119807633939946967 : ℝ) / 1000000000000000000000000) ≤ v6 ∧ v6 ≤ ((-954869374321784658907 : ℝ) / 1953125000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((2624911170949731 : ℝ) / 1125899906842624)
  have h7 : ((2624911170949731 : ℝ) / 1125899906842624) ≤ v7 ∧ v7 ≤ ((2624911170949731 : ℝ) / 1125899906842624) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 4 9
  have h8 : ((90109138152039850910503 : ℝ) / 250000000000000000000000) ≤ v8 ∧ v8 ≤ ((360436552767771718715371 : ℝ) / 1000000000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 9
  let v9 : ℝ := v7*v8
  have h9 : ((840317978187748355006153 : ℝ) / 1000000000000000000000000) ≤ v9 ∧ v9 ≤ ((210079494639966705840709 : ℝ) / 250000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((175712429190057207529593 : ℝ) / 500000000000000000000000) ≤ v10 ∧ v10 ≤ ((87856214726778269500613 : ℝ) / 250000000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((5402920345206155 : ℝ) / 2251799813685248)
  have h11 : ((5402920345206155 : ℝ) / 2251799813685248) ≤ v11 ∧ v11 ≤ ((5402920345206155 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 5 9
  have h12 : ((-36616236258947606092379 : ℝ) / 250000000000000000000000) ≤ v12 ∧ v12 ≤ ((-146464944970892504313817 : ℝ) / 1000000000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 9
  let v13 : ℝ := v11*v12
  have h13 : ((-35142485872147114177637 : ℝ) / 100000000000000000000000) ≤ v13 ∧ v13 ≤ ((-70284971713151291891783 : ℝ) / 200000000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-1333424713739 : ℝ) / 3906250000000000000000) ≤ v14 ∧ v14 ≤ ((341356618543537 : ℝ) / 1000000000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 1 3 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_2_0 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 2 0| ≤ ((27880119630483 : ℝ) / 200000000000000000000000) := by
  let v0 : ℝ := ((-5676625074002731 : ℝ) / 18014398509481984)
  have h0 : ((-5676625074002731 : ℝ) / 18014398509481984) ≤ v0 ∧ v0 ≤ ((-5676625074002731 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 5 6
  have h1 : ((652535574979217430457 : ℝ) / 5000000000000000000000) ≤ v1 ∧ v1 ≤ ((130507115055637303510633 : ℝ) / 1000000000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 6
  let v2 : ℝ := v0*v1
  have h2 : ((-41124879149900264002051 : ℝ) / 1000000000000000000000000) ≤ v2 ∧ v2 ≤ ((-41124879131058275852753 : ℝ) / 1000000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-1906405801350491 : ℝ) / 9007199254740992)
  have h3 : ((-1906405801350491 : ℝ) / 9007199254740992) ≤ v3 ∧ v3 ≤ ((-1906405801350491 : ℝ) / 9007199254740992) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 4 6
  have h4 : ((-23870084181672384861613 : ℝ) / 500000000000000000000000) ≤ v4 ∧ v4 ≤ ((-1909606688811010103167 : ℝ) / 40000000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 6
  let v5 : ℝ := v3*v4
  have h5 : ((631523526155137219249 : ℝ) / 62500000000000000000000) ≤ v5 ∧ v5 ≤ ((5052188330208464923277 : ℝ) / 500000000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((-31020502731418068494067 : ℝ) / 1000000000000000000000000) ≤ v6 ∧ v6 ≤ ((-31020502470641346006199 : ℝ) / 1000000000000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-901757038800969 : ℝ) / 4503599627370496)
  have h7 : ((-901757038800969 : ℝ) / 4503599627370496) ≤ v7 ∧ v7 ≤ ((-901757038800969 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 6 6
  have h8 : ((-155834307137490777530731 : ℝ) / 1000000000000000000000000) ≤ v8 ∧ v8 ≤ ((-31166861409571967260273 : ℝ) / 200000000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 6
  let v9 : ℝ := v7*v8
  have h9 : ((31202747778253727540609 : ℝ) / 1000000000000000000000000) ≤ v9 ∧ v9 ≤ ((31202747796200556485333 : ℝ) / 1000000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((91122523417829523271 : ℝ) / 500000000000000000000000) ≤ v10 ∧ v10 ≤ ((91122662779605239567 : ℝ) / 500000000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((5941539868098331 : ℝ) / 2305843009213693952)
  have h11 : ((5941539868098331 : ℝ) / 2305843009213693952) ≤ v11 ∧ v11 ≤ ((5941539868098331 : ℝ) / 2305843009213693952) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 6
  have h12 : ((-14145450437925655174083 : ℝ) / 200000000000000000000000) ≤ v12 ∧ v12 ≤ ((-7072725215950157735069 : ℝ) / 100000000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 6
  let v13 : ℝ := v11*v12
  have h13 : ((-182245186236257198957 : ℝ) / 1000000000000000000000000) ≤ v13 ∧ v13 ≤ ((-182245186158628765609 : ℝ) / 1000000000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-27880119630483 : ℝ) / 200000000000000000000000) ≤ v14 ∧ v14 ≤ ((5576023268541 : ℝ) / 40000000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 2 0 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_2_1 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 2 1| ≤ ((40147880246573 : ℝ) / 500000000000000000000000) := by
  let v0 : ℝ := ((-5676625074002731 : ℝ) / 18014398509481984)
  have h0 : ((-5676625074002731 : ℝ) / 18014398509481984) ≤ v0 ∧ v0 ≤ ((-5676625074002731 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 5 7
  have h1 : ((258656993837854629939027 : ℝ) / 200000000000000000000000) ≤ v1 ∧ v1 ≤ ((80830310585041675816059 : ℝ) / 62500000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 7
  let v2 : ℝ := v0*v1
  have h2 : ((-203767388654119556190837 : ℝ) / 500000000000000000000000) ≤ v2 ∧ v2 ≤ ((-407534777254230227963317 : ℝ) / 1000000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-1906405801350491 : ℝ) / 9007199254740992)
  have h3 : ((-1906405801350491 : ℝ) / 9007199254740992) ≤ v3 ∧ v3 ≤ ((-1906405801350491 : ℝ) / 9007199254740992) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 4 7
  have h4 : ((-382483385496709632069843 : ℝ) / 250000000000000000000000) ≤ v4 ∧ v4 ≤ ((-95620846351602915583067 : ℝ) / 62500000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 7
  let v5 : ℝ := v3*v4
  have h5 : ((323815882933935004172617 : ℝ) / 1000000000000000000000000) ≤ v5 ∧ v5 ≤ ((323815883010382551735097 : ℝ) / 1000000000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((-83718894374304108209057 : ℝ) / 1000000000000000000000000) ≤ v6 ∧ v6 ≤ ((-4185944712192383811411 : ℝ) / 50000000000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-901757038800969 : ℝ) / 4503599627370496)
  have h7 : ((-901757038800969 : ℝ) / 4503599627370496) ≤ v7 ∧ v7 ≤ ((-901757038800969 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 6 7
  have h8 : ((-211574327710786693809299 : ℝ) / 500000000000000000000000) ≤ v8 ∧ v8 ≤ ((-211574327635688143215797 : ℝ) / 500000000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 7
  let v9 : ℝ := v7*v8
  have h9 : ((21181794004905736356073 : ℝ) / 250000000000000000000000) ≤ v9 ∧ v9 ≤ ((84727176049696953864063 : ℝ) / 1000000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((201656329063767443047 : ℝ) / 200000000000000000000000) ≤ v10 ∧ v10 ≤ ((1008281805849277635843 : ℝ) / 1000000000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((5941539868098331 : ℝ) / 2305843009213693952)
  have h11 : ((5941539868098331 : ℝ) / 2305843009213693952) ≤ v11 ∧ v11 ≤ ((5941539868098331 : ℝ) / 2305843009213693952) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 7
  have h12 : ((-78260498791211800413401 : ℝ) / 200000000000000000000000) ≤ v12 ∧ v12 ≤ ((-195651246966186367427959 : ℝ) / 500000000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 7
  let v13 : ℝ := v11*v12
  have h13 : ((-1008281725614550309483 : ℝ) / 1000000000000000000000000) ≤ v13 ∧ v13 ≤ ((-1008281725553517142697 : ℝ) / 1000000000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-10036964136781 : ℝ) / 125000000000000000000000) ≤ v14 ∧ v14 ≤ ((40147880246573 : ℝ) / 500000000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 2 1 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_2_2 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 2 2| ≤ ((519554695846491 : ℝ) / 500000000000000000000000) := by
  let v0 : ℝ := ((1 : ℝ) / 1)
  have h0 : ((1 : ℝ) / 1) ≤ v0 ∧ v0 ≤ ((1 : ℝ) / 1) := by constructor <;> norm_num [v0]
  let v1 : ℝ := ((-5676625074002731 : ℝ) / 18014398509481984)
  have h1 : ((-5676625074002731 : ℝ) / 18014398509481984) ≤ v1 ∧ v1 ≤ ((-5676625074002731 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v1]
  let v2 : ℝ := jacobian y 5 8
  have h2 : ((7013347285928550056021 : ℝ) / 4000000000000000000000) ≤ v2 ∧ v2 ≤ ((27395887849477761289867 : ℝ) / 15625000000000000000000) := by
    simpa [v2,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 8
  let v3 : ℝ := v1*v2
  have h3 : ((-276252236892048969197977 : ℝ) / 500000000000000000000000) ≤ v3 ∧ v3 ≤ ((-27625223675269849948837 : ℝ) / 50000000000000000000000) := mul_interval h1 h2 (by norm_num) (by norm_num)
  let v4 : ℝ := v0+v3
  have h4 : ((223747763107951030802023 : ℝ) / 500000000000000000000000) ≤ v4 ∧ v4 ≤ ((22374776324730150051163 : ℝ) / 50000000000000000000000) := add_interval h0 h3 (by norm_num) (by norm_num)
  let v5 : ℝ := ((-1906405801350491 : ℝ) / 9007199254740992)
  have h5 : ((-1906405801350491 : ℝ) / 9007199254740992) ≤ v5 ∧ v5 ≤ ((-1906405801350491 : ℝ) / 9007199254740992) := by constructor <;> norm_num [v5]
  let v6 : ℝ := jacobian y 4 8
  have h6 : ((-7626462905965564659250679 : ℝ) / 1000000000000000000000000) ≤ v6 ∧ v6 ≤ ((-7626462902042735255970459 : ℝ) / 1000000000000000000000000) := by
    simpa [v6,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 8
  let v7 : ℝ := v5*v6
  have h7 : ((1614168034817905700394243 : ℝ) / 1000000000000000000000000) ≤ v7 ∧ v7 ≤ ((1614168035648186514731213 : ℝ) / 1000000000000000000000000) := mul_interval h5 h6 (by norm_num) (by norm_num)
  let v8 : ℝ := v4+v7
  have h8 : ((2061663561033807761998289 : ℝ) / 1000000000000000000000000) ≤ v8 ∧ v8 ≤ ((2061663562142789515754473 : ℝ) / 1000000000000000000000000) := add_interval h4 h7 (by norm_num) (by norm_num)
  let v9 : ℝ := ((-901757038800969 : ℝ) / 4503599627370496)
  have h9 : ((-901757038800969 : ℝ) / 4503599627370496) ≤ v9 ∧ v9 ≤ ((-901757038800969 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v9]
  let v10 : ℝ := jacobian y 6 8
  have h10 : ((2061743844080346340918441 : ℝ) / 200000000000000000000000) ≤ v10 ∧ v10 ≤ ((2061743845047320678197891 : ℝ) / 200000000000000000000000) := by
    simpa [v10,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 8
  let v11 : ℝ := v9*v10
  have h11 : ((-206411779277270809366439 : ℝ) / 100000000000000000000000) ≤ v11 ∧ v11 ≤ ((-1032058895902310177966589 : ℝ) / 500000000000000000000000) := mul_interval h9 h10 (by norm_num) (by norm_num)
  let v12 : ℝ := v8+v11
  have h12 : ((-2454231738900331666101 : ℝ) / 1000000000000000000000000) ≤ v12 ∧ v12 ≤ ((-490845932366168035741 : ℝ) / 200000000000000000000000) := add_interval h8 h11 (by norm_num) (by norm_num)
  let v13 : ℝ := ((5941539868098331 : ℝ) / 2305843009213693952)
  have h13 : ((5941539868098331 : ℝ) / 2305843009213693952) ≤ v13 ∧ v13 ≤ ((5941539868098331 : ℝ) / 2305843009213693952) := by constructor <;> norm_num [v13]
  let v14 : ℝ := jacobian y 7 8
  have h14 : ((38098343713861719391029 : ℝ) / 40000000000000000000000) ≤ v14 ∧ v14 ≤ ((952458593292201940752697 : ℝ) / 1000000000000000000000000) := by
    simpa [v14,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 8
  let v15 : ℝ := v13*v14
  have h15 : ((2454230699790939973119 : ℝ) / 1000000000000000000000000) ≤ v15 ∧ v15 ≤ ((2454230700939283743243 : ℝ) / 1000000000000000000000000) := mul_interval h13 h14 (by norm_num) (by norm_num)
  let v16 : ℝ := v12+v15
  have h16 : ((-519554695846491 : ℝ) / 500000000000000000000000) ≤ v16 ∧ v16 ≤ ((519554221782269 : ℝ) / 500000000000000000000000) := add_interval h12 h15 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 2 2 = v16 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h16 (by norm_num) (by norm_num)

private theorem e_bound_2_3 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 2 3| ≤ ((726115608071 : ℝ) / 20000000000000000000000) := by
  let v0 : ℝ := ((-5676625074002731 : ℝ) / 18014398509481984)
  have h0 : ((-5676625074002731 : ℝ) / 18014398509481984) ≤ v0 ∧ v0 ≤ ((-5676625074002731 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 5 9
  have h1 : ((-36616236258947606092379 : ℝ) / 250000000000000000000000) ≤ v1 ∧ v1 ≤ ((-146464944970892504313817 : ℝ) / 1000000000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 9
  let v2 : ℝ := v0*v1
  have h2 : ((721147602644223334737 : ℝ) / 15625000000000000000000) ≤ v2 ∧ v2 ≤ ((11538361647420166485739 : ℝ) / 250000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-1906405801350491 : ℝ) / 9007199254740992)
  have h3 : ((-1906405801350491 : ℝ) / 9007199254740992) ≤ v3 ∧ v3 ≤ ((-1906405801350491 : ℝ) / 9007199254740992) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 4 9
  have h4 : ((90109138152039850910503 : ℝ) / 250000000000000000000000) ≤ v4 ∧ v4 ≤ ((360436552767771718715371 : ℝ) / 1000000000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 9
  let v5 : ℝ := v3*v4
  have h5 : ((-15257536017171444214099 : ℝ) / 200000000000000000000000) ≤ v5 ∧ v5 ≤ ((-76287680052074706126943 : ℝ) / 1000000000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((-30134233516626927647327 : ℝ) / 1000000000000000000000000) ≤ v6 ∧ v6 ≤ ((-30134233462394040183987 : ℝ) / 1000000000000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-901757038800969 : ℝ) / 4503599627370496)
  have h7 : ((-901757038800969 : ℝ) / 4503599627370496) ≤ v7 ∧ v7 ≤ ((-901757038800969 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 6 9
  have h8 : ((-31306286695260580317093 : ℝ) / 500000000000000000000000) ≤ v8 ∧ v8 ≤ ((-31306286654447633378177 : ℝ) / 500000000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 9
  let v9 : ℝ := v7*v8
  have h9 : ((12536933424453607928823 : ℝ) / 1000000000000000000000000) ≤ v9 ∧ v9 ≤ ((6268466720398791978779 : ℝ) / 500000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((-2199662511521664964813 : ℝ) / 125000000000000000000000) ≤ v10 ∧ v10 ≤ ((-17597300021596456226429 : ℝ) / 1000000000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((5941539868098331 : ℝ) / 2305843009213693952)
  have h11 : ((5941539868098331 : ℝ) / 2305843009213693952) ≤ v11 ∧ v11 ≤ ((5941539868098331 : ℝ) / 2305843009213693952) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 9
  have h12 : ((21341590425028271142213 : ℝ) / 3125000000000000000000) ≤ v12 ∧ v12 ≤ ((6829308936798683676785057 : ℝ) / 1000000000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 9
  let v13 : ℝ := v11*v12
  have h13 : ((2199662506983444224447 : ℝ) / 125000000000000000000000) ≤ v13 ∧ v13 ≤ ((17597300057902236629979 : ℝ) / 1000000000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-2269110370183 : ℝ) / 62500000000000000000000) ≤ v14 ∧ v14 ≤ ((726115608071 : ℝ) / 20000000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 2 3 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_3_0 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 3 0| ≤ ((16219768504629 : ℝ) / 500000000000000000000000) := by
  let v0 : ℝ := ((-6811950088803285 : ℝ) / 144115188075855872)
  have h0 : ((-6811950088803285 : ℝ) / 144115188075855872) ≤ v0 ∧ v0 ≤ ((-6811950088803285 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 4 6
  have h1 : ((-23870084181672384861613 : ℝ) / 500000000000000000000000) ≤ v1 ∧ v1 ≤ ((-1909606688811010103167 : ℝ) / 40000000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 6
  let v2 : ℝ := v0*v1
  have h2 : ((1128276764848909771767 : ℝ) / 500000000000000000000000) ≤ v2 ∧ v2 ≤ ((2256553583727742432157 : ℝ) / 1000000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-1828646140081387 : ℝ) / 18014398509481984)
  have h3 : ((-1828646140081387 : ℝ) / 18014398509481984) ≤ v3 ∧ v3 ≤ ((-1828646140081387 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 5 6
  have h4 : ((652535574979217430457 : ℝ) / 5000000000000000000000) ≤ v4 ∧ v4 ≤ ((130507115055637303510633 : ℝ) / 1000000000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 6
  let v5 : ℝ := v3*v4
  have h5 : ((-13247810193275845351711 : ℝ) / 1000000000000000000000000) ≤ v5 ∧ v5 ≤ ((-13247810187206159851699 : ℝ) / 1000000000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((-10991256663578025808177 : ℝ) / 1000000000000000000000000) ≤ v6 ∧ v6 ≤ ((-5495628301739208709771 : ℝ) / 500000000000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-605344055995505 : ℝ) / 144115188075855872)
  have h7 : ((-605344055995505 : ℝ) / 144115188075855872) ≤ v7 ∧ v7 ≤ ((-605344055995505 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 6 6
  have h8 : ((-155834307137490777530731 : ℝ) / 1000000000000000000000000) ≤ v8 ∧ v8 ≤ ((-31166861409571967260273 : ℝ) / 200000000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 6
  let v9 : ℝ := v7*v8
  have h9 : ((26182770255123273333 : ℝ) / 40000000000000000000000) ≤ v9 ∧ v9 ≤ ((163642314188642317087 : ℝ) / 250000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((-2584171851799985993713 : ℝ) / 250000000000000000000000) ≤ v10 ∧ v10 ≤ ((-5168343673361924075597 : ℝ) / 500000000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((-329097342168993 : ℝ) / 2251799813685248)
  have h11 : ((-329097342168993 : ℝ) / 2251799813685248) ≤ v11 ∧ v11 ≤ ((-329097342168993 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 6
  have h12 : ((-14145450437925655174083 : ℝ) / 200000000000000000000000) ≤ v12 ∧ v12 ≤ ((-7072725215950157735069 : ℝ) / 100000000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 6
  let v13 : ℝ := v11*v12
  have h13 : ((5168343687380203482797 : ℝ) / 500000000000000000000000) ≤ v13 ∧ v13 ≤ ((10336687379163381133597 : ℝ) / 1000000000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-16219768504629 : ℝ) / 500000000000000000000000) ≤ v14 ∧ v14 ≤ ((32439532982403 : ℝ) / 1000000000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 3 0 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_3_1 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 3 1| ≤ ((24102139729 : ℝ) / 1250000000000000000000) := by
  let v0 : ℝ := ((-6811950088803285 : ℝ) / 144115188075855872)
  have h0 : ((-6811950088803285 : ℝ) / 144115188075855872) ≤ v0 ∧ v0 ≤ ((-6811950088803285 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 4 7
  have h1 : ((-382483385496709632069843 : ℝ) / 250000000000000000000000) ≤ v1 ∧ v1 ≤ ((-95620846351602915583067 : ℝ) / 62500000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 7
  let v2 : ℝ := v0*v1
  have h2 : ((72315979071229857944999 : ℝ) / 1000000000000000000000000) ≤ v2 ∧ v2 ≤ ((2259874346509451830719 : ℝ) / 31250000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-1828646140081387 : ℝ) / 18014398509481984)
  have h3 : ((-1828646140081387 : ℝ) / 18014398509481984) ≤ v3 ∧ v3 ≤ ((-1828646140081387 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 5 7
  have h4 : ((258656993837854629939027 : ℝ) / 200000000000000000000000) ≤ v4 ∧ v4 ≤ ((80830310585041675816059 : ℝ) / 62500000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 7
  let v5 : ℝ := v3*v4
  have h5 : ((-32820420926097635107633 : ℝ) / 250000000000000000000000) ≤ v5 ∧ v5 ≤ ((-131281683686992326397683 : ℝ) / 1000000000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((-58965704633160682485533 : ℝ) / 1000000000000000000000000) ≤ v6 ∧ v6 ≤ ((-2358628183947594712587 : ℝ) / 40000000000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-605344055995505 : ℝ) / 144115188075855872)
  have h7 : ((-605344055995505 : ℝ) / 144115188075855872) ≤ v7 ∧ v7 ≤ ((-605344055995505 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 6 7
  have h8 : ((-211574327710786693809299 : ℝ) / 500000000000000000000000) ≤ v8 ∧ v8 ≤ ((-211574327635688143215797 : ℝ) / 500000000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 7
  let v9 : ℝ := v7*v8
  have h9 : ((1777401304407917941899 : ℝ) / 1000000000000000000000000) ≤ v9 ∧ v9 ≤ ((1777401305038808576297 : ℝ) / 1000000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((-28594151664376382271817 : ℝ) / 500000000000000000000000) ≤ v10 ∧ v10 ≤ ((-28594151646825529619189 : ℝ) / 500000000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((-329097342168993 : ℝ) / 2251799813685248)
  have h11 : ((-329097342168993 : ℝ) / 2251799813685248) ≤ v11 ∧ v11 ≤ ((-329097342168993 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 7
  have h12 : ((-78260498791211800413401 : ℝ) / 200000000000000000000000) ≤ v12 ∧ v12 ≤ ((-195651246966186367427959 : ℝ) / 500000000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 7
  let v13 : ℝ := v11*v12
  have h13 : ((5718830330947105673521 : ℝ) / 100000000000000000000000) ≤ v13 ∧ v13 ≤ ((28594151656466385510789 : ℝ) / 500000000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-2410213476053 : ℝ) / 125000000000000000000000) ≤ v14 ∧ v14 ≤ ((24102139729 : ℝ) / 1250000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 3 1 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_3_2 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 3 2| ≤ ((180321409771479 : ℝ) / 1000000000000000000000000) := by
  let v0 : ℝ := ((-6811950088803285 : ℝ) / 144115188075855872)
  have h0 : ((-6811950088803285 : ℝ) / 144115188075855872) ≤ v0 ∧ v0 ≤ ((-6811950088803285 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 4 8
  have h1 : ((-7626462905965564659250679 : ℝ) / 1000000000000000000000000) ≤ v1 ∧ v1 ≤ ((-7626462902042735255970459 : ℝ) / 1000000000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 8
  let v2 : ℝ := v0*v1
  have h2 : ((360483064529466608736763 : ℝ) / 1000000000000000000000000) ≤ v2 ∧ v2 ≤ ((180241532357444275567231 : ℝ) / 500000000000000000000000) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-1828646140081387 : ℝ) / 18014398509481984)
  have h3 : ((-1828646140081387 : ℝ) / 18014398509481984) ≤ v3 ∧ v3 ≤ ((-1828646140081387 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 5 8
  have h4 : ((7013347285928550056021 : ℝ) / 4000000000000000000000) ≤ v4 ∧ v4 ≤ ((27395887849477761289867 : ℝ) / 15625000000000000000000) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 8
  let v5 : ℝ := v3*v4
  have h5 : ((-177981663434146065309571 : ℝ) / 1000000000000000000000000) ≤ v5 ∧ v5 ≤ ((-177981663344366417990597 : ℝ) / 1000000000000000000000000) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((22812675136915067928399 : ℝ) / 125000000000000000000000) ≤ v6 ∧ v6 ≤ ((36500280274104426628773 : ℝ) / 200000000000000000000000) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-605344055995505 : ℝ) / 144115188075855872)
  have h7 : ((-605344055995505 : ℝ) / 144115188075855872) ≤ v7 ∧ v7 ≤ ((-605344055995505 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 6 8
  have h8 : ((2061743844080346340918441 : ℝ) / 200000000000000000000000) ≤ v8 ∧ v8 ≤ ((2061743845047320678197891 : ℝ) / 200000000000000000000000) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 8
  let v9 : ℝ := v7*v8
  have h9 : ((-43300931645309552210973 : ℝ) / 1000000000000000000000000) ≤ v9 ∧ v9 ≤ ((-43300931625001069281879 : ℝ) / 1000000000000000000000000) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((139200469450010991216219 : ℝ) / 1000000000000000000000000) ≤ v10 ∧ v10 ≤ ((69600234872760531930993 : ℝ) / 500000000000000000000000) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((-329097342168993 : ℝ) / 2251799813685248)
  have h11 : ((-329097342168993 : ℝ) / 2251799813685248) ≤ v11 ∧ v11 ≤ ((-329097342168993 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 8
  have h12 : ((38098343713861719391029 : ℝ) / 40000000000000000000000) ≤ v12 ∧ v12 ≤ ((952458593292201940752697 : ℝ) / 1000000000000000000000000) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 8
  let v13 : ℝ := v11*v12
  have h13 : ((-69600234815166200493849 : ℝ) / 500000000000000000000000) ≤ v13 ∧ v13 ≤ ((-8700029347824998625631 : ℝ) / 62500000000000000000000) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((-180321409771479 : ℝ) / 1000000000000000000000000) ≤ v14 ∧ v14 ≤ ((18032108585189 : ℝ) / 100000000000000000000000) := add_interval h10 h13 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 3 2 = v14 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h14 (by norm_num) (by norm_num)

private theorem e_bound_3_3 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |(1-preconditioner*accelerationMatrix y) 3 3| ≤ ((32469928011973 : ℝ) / 500000000000000000000000) := by
  let v0 : ℝ := ((1 : ℝ) / 1)
  have h0 : ((1 : ℝ) / 1) ≤ v0 ∧ v0 ≤ ((1 : ℝ) / 1) := by constructor <;> norm_num [v0]
  let v1 : ℝ := ((-6811950088803285 : ℝ) / 144115188075855872)
  have h1 : ((-6811950088803285 : ℝ) / 144115188075855872) ≤ v1 ∧ v1 ≤ ((-6811950088803285 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v1]
  let v2 : ℝ := jacobian y 4 9
  have h2 : ((90109138152039850910503 : ℝ) / 250000000000000000000000) ≤ v2 ∧ v2 ≤ ((360436552767771718715371 : ℝ) / 1000000000000000000000000) := by
    simpa [v2,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 9
  let v3 : ℝ := v1*v2
  have h3 : ((-17036898334005043936493 : ℝ) / 1000000000000000000000000) ≤ v3 ∧ v3 ≤ ((-17036898326460584963397 : ℝ) / 1000000000000000000000000) := mul_interval h1 h2 (by norm_num) (by norm_num)
  let v4 : ℝ := v0+v3
  have h4 : ((982963101665994956063507 : ℝ) / 1000000000000000000000000) ≤ v4 ∧ v4 ≤ ((982963101673539415036603 : ℝ) / 1000000000000000000000000) := add_interval h0 h3 (by norm_num) (by norm_num)
  let v5 : ℝ := ((-1828646140081387 : ℝ) / 18014398509481984)
  have h5 : ((-1828646140081387 : ℝ) / 18014398509481984) ≤ v5 ∧ v5 ≤ ((-1828646140081387 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v5]
  let v6 : ℝ := jacobian y 5 9
  have h6 : ((-36616236258947606092379 : ℝ) / 250000000000000000000000) ≤ v6 ∧ v6 ≤ ((-146464944970892504313817 : ℝ) / 1000000000000000000000000) := by
    simpa [v6,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 9
  let v7 : ℝ := v5*v6
  have h7 : ((14867693536216604768537 : ℝ) / 1000000000000000000000000) ≤ v7 ∧ v7 ≤ ((14867693542804409015607 : ℝ) / 1000000000000000000000000) := mul_interval h5 h6 (by norm_num) (by norm_num)
  let v8 : ℝ := v4+v7
  have h8 : ((249457698800552890208011 : ℝ) / 250000000000000000000000) ≤ v8 ∧ v8 ≤ ((99783079521634382405221 : ℝ) / 100000000000000000000000) := add_interval h4 h7 (by norm_num) (by norm_num)
  let v9 : ℝ := ((-605344055995505 : ℝ) / 144115188075855872)
  have h9 : ((-605344055995505 : ℝ) / 144115188075855872) ≤ v9 ∧ v9 ≤ ((-605344055995505 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v9]
  let v10 : ℝ := jacobian y 6 9
  have h10 : ((-31306286695260580317093 : ℝ) / 500000000000000000000000) ≤ v10 ∧ v10 ≤ ((-31306286654447633378177 : ℝ) / 500000000000000000000000) := by
    simpa [v10,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 9
  let v11 : ℝ := v9*v10
  have h11 : ((32874873902232758013 : ℝ) / 125000000000000000000000) ≤ v11 ∧ v11 ≤ ((262998991560724952701 : ℝ) / 1000000000000000000000000) := mul_interval h9 h10 (by norm_num) (by norm_num)
  let v12 : ℝ := v8+v11
  have h12 : ((249523448548357355724037 : ℝ) / 250000000000000000000000) ≤ v12 ∧ v12 ≤ ((998093794207904549004911 : ℝ) / 1000000000000000000000000) := add_interval h8 h11 (by norm_num) (by norm_num)
  let v13 : ℝ := ((-329097342168993 : ℝ) / 2251799813685248)
  have h13 : ((-329097342168993 : ℝ) / 2251799813685248) ≤ v13 ∧ v13 ≤ ((-329097342168993 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v13]
  let v14 : ℝ := jacobian y 7 9
  have h14 : ((21341590425028271142213 : ℝ) / 3125000000000000000000) ≤ v14 ∧ v14 ≤ ((6829308936798683676785057 : ℝ) / 1000000000000000000000000) := by
    simpa [v14,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 9
  let v15 : ℝ := v13*v14
  have h15 : ((-499046897129184639460047 : ℝ) / 500000000000000000000000) ≤ v15 ∧ v15 ≤ ((-499046897071482483344653 : ℝ) / 500000000000000000000000) := mul_interval h13 h14 (by norm_num) (by norm_num)
  let v16 : ℝ := v12+v15
  have h16 : ((-32469928011973 : ℝ) / 500000000000000000000000) ≤ v16 ∧ v16 ≤ ((12987916463121 : ℝ) / 200000000000000000000000) := add_interval h12 h15 (by norm_num) (by norm_num)
  have he : (1-preconditioner*accelerationMatrix y) 3 3 = v16 := by
    simp only [Matrix.sub_apply,Matrix.one_apply,Fin.ext_iff,Matrix.mul_apply,accelerationMatrix,preconditioner,M2KernelCertificate.preconditioner,residualIndex,velocityIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h16 (by norm_num) (by norm_num)

private theorem approx_bound_0 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |approximateAcceleration y 0| ≤ ((1000 : ℝ) / 1) := by
  let v0 : ℝ := ((-7689872965427469 : ℝ) / 281474976710656)
  have h0 : ((-7689872965427469 : ℝ) / 281474976710656) ≤ v0 ∧ v0 ≤ ((-7689872965427469 : ℝ) / 281474976710656) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 5 4
  have h1 : ((0 : ℝ) / 1) ≤ v1 ∧ v1 ≤ ((0 : ℝ) / 1) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 4
  let v2 : ℝ := v0*v1
  have h2 : ((0 : ℝ) / 1) ≤ v2 ∧ v2 ≤ ((0 : ℝ) / 1) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-5864275639152445 : ℝ) / 562949953421312)
  have h3 : ((-5864275639152445 : ℝ) / 562949953421312) ≤ v3 ∧ v3 ≤ ((-5864275639152445 : ℝ) / 562949953421312) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 6 4
  have h4 : ((0 : ℝ) / 1) ≤ v4 ∧ v4 ≤ ((0 : ℝ) / 1) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 4
  let v5 : ℝ := v3*v4
  have h5 : ((0 : ℝ) / 1) ≤ v5 ∧ v5 ≤ ((0 : ℝ) / 1) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((0 : ℝ) / 1) ≤ v6 ∧ v6 ≤ ((0 : ℝ) / 1) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-5717564422701105 : ℝ) / 281474976710656)
  have h7 : ((-5717564422701105 : ℝ) / 281474976710656) ≤ v7 ∧ v7 ≤ ((-5717564422701105 : ℝ) / 281474976710656) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 4 4
  have h8 : ((0 : ℝ) / 1) ≤ v8 ∧ v8 ≤ ((0 : ℝ) / 1) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 4
  let v9 : ℝ := v7*v8
  have h9 : ((0 : ℝ) / 1) ≤ v9 ∧ v9 ≤ ((0 : ℝ) / 1) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((0 : ℝ) / 1) ≤ v10 ∧ v10 ≤ ((0 : ℝ) / 1) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((1759319900783941 : ℝ) / 4503599627370496)
  have h11 : ((1759319900783941 : ℝ) / 4503599627370496) ≤ v11 ∧ v11 ≤ ((1759319900783941 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 4
  have h12 : ((0 : ℝ) / 1) ≤ v12 ∧ v12 ≤ ((0 : ℝ) / 1) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 4
  let v13 : ℝ := v11*v12
  have h13 : ((0 : ℝ) / 1) ≤ v13 ∧ v13 ≤ ((0 : ℝ) / 1) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((0 : ℝ) / 1) ≤ v14 ∧ v14 ≤ ((0 : ℝ) / 1) := add_interval h10 h13 (by norm_num) (by norm_num)
  let v15 : ℝ := jacobian y 5 0
  have h15 : ((14471030679094404089679 : ℝ) / 1000000000000000000000000) ≤ v15 ∧ v15 ≤ ((7235515359098802834341 : ℝ) / 500000000000000000000000) := by
    simpa [v15,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 0
  let v16 : ℝ := v0*v15
  have h16 : ((-395347356280731142381789 : ℝ) / 1000000000000000000000000) ≤ v16 ∧ v16 ≤ ((-98836838803108731448583 : ℝ) / 250000000000000000000000) := mul_interval h0 h15 (by norm_num) (by norm_num)
  let v17 : ℝ := velocity y 0
  have h17 : ((4578839125515008337388553 : ℝ) / 2500000000000000000000000) ≤ v17 ∧ v17 ≤ ((4578839126572353912611447 : ℝ) / 2500000000000000000000000) := by simpa [v17,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 6
  let v18 : ℝ := v16*v17
  have h18 : ((-724092777410060880332913 : ℝ) / 1000000000000000000000000) ≤ v18 ∧ v18 ≤ ((-72409277528623076353699 : ℝ) / 100000000000000000000000) := mul_interval h16 h17 (by norm_num) (by norm_num)
  let v19 : ℝ := v14+v18
  have h19 : ((-724092777410060880332913 : ℝ) / 1000000000000000000000000) ≤ v19 ∧ v19 ≤ ((-72409277528623076353699 : ℝ) / 100000000000000000000000) := add_interval h14 h18 (by norm_num) (by norm_num)
  let v20 : ℝ := jacobian y 5 1
  have h20 : ((50815194354105460729557 : ℝ) / 1000000000000000000000000) ≤ v20 ∧ v20 ≤ ((50815194420457997287063 : ℝ) / 1000000000000000000000000) := by
    simpa [v20,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 1
  let v21 : ℝ := v0*v20
  have h21 : ((-1388266887427465393754559 : ℝ) / 1000000000000000000000000) ≤ v21 ∧ v21 ≤ ((-694133442807359805361579 : ℝ) / 500000000000000000000000) := mul_interval h0 h20 (by norm_num) (by norm_num)
  let v22 : ℝ := velocity y 1
  have h22 : ((-51791610787714331078253517 : ℝ) / 25000000000000000000000000) ≤ v22 ∧ v22 ≤ ((-51791610775820146421746483 : ℝ) / 25000000000000000000000000) := by simpa [v22,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 7
  let v23 : ℝ := v21*v22
  have h23 : ((1438011563854351736159987 : ℝ) / 500000000000000000000000) ≤ v23 ∧ v23 ≤ ((1438011566062298270996951 : ℝ) / 500000000000000000000000) := mul_interval h21 h22 (by norm_num) (by norm_num)
  let v24 : ℝ := v19+v23
  have h24 : ((2151930350298642591987061 : ℝ) / 1000000000000000000000000) ≤ v24 ∧ v24 ≤ ((134495647302397861153557 : ℝ) / 62500000000000000000000) := add_interval h19 h23 (by norm_num) (by norm_num)
  let v25 : ℝ := jacobian y 5 2
  have h25 : ((48193689742644681369447 : ℝ) / 100000000000000000000000) ≤ v25 ∧ v25 ≤ ((120484224418590333953647 : ℝ) / 250000000000000000000000) := by
    simpa [v25,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 2
  let v26 : ℝ := v0*v25
  have h26 : ((-6583237991130018851098257 : ℝ) / 500000000000000000000000) ≤ v26 ∧ v26 ≤ ((-13166475975487033566386267 : ℝ) / 1000000000000000000000000) := mul_interval h0 h25 (by norm_num) (by norm_num)
  let v27 : ℝ := velocity y 2
  have h27 : ((-5790678745077187 : ℝ) / 100000000000000000) ≤ v27 ∧ v27 ≤ ((-28953393614806863 : ℝ) / 500000000000000000) := by simpa [v27,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 8
  let v28 : ℝ := v26*v27
  have h28 : ((381214161438174240505821 : ℝ) / 500000000000000000000000) ≤ v28 ∧ v28 ≤ ((762428326180424781666507 : ℝ) / 1000000000000000000000000) := mul_interval h26 h27 (by norm_num) (by norm_num)
  let v29 : ℝ := v24+v28
  have h29 : ((2914358673174991072998703 : ℝ) / 1000000000000000000000000) ≤ v29 ∧ v29 ≤ ((2914358683018790560123419 : ℝ) / 1000000000000000000000000) := add_interval h24 h28 (by norm_num) (by norm_num)
  let v30 : ℝ := jacobian y 5 3
  have h30 : ((-46801914920349775960023 : ℝ) / 1000000000000000000000000) ≤ v30 ∧ v30 ≤ ((-11700478724808102304361 : ℝ) / 250000000000000000000000) := by
    simpa [v30,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 3
  let v31 : ℝ := v0*v30
  have h31 : ((1278624424521426201739513 : ℝ) / 1000000000000000000000000) ≤ v31 ∧ v31 ≤ ((1278624425098350905713129 : ℝ) / 1000000000000000000000000) := mul_interval h0 h30 (by norm_num) (by norm_num)
  let v32 : ℝ := velocity y 3
  have h32 : ((-9165702769420347 : ℝ) / 100000000000000000) ≤ v32 ∧ v32 ≤ ((-9165702747237029 : ℝ) / 100000000000000000) := by simpa [v32,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 9
  let v33 : ℝ := v31*v32
  have h33 : ((-58597457170862269675227 : ℝ) / 500000000000000000000000) ≤ v33 ∧ v33 ≤ ((-23438982801040802732723 : ℝ) / 200000000000000000000000) := mul_interval h31 h32 (by norm_num) (by norm_num)
  let v34 : ℝ := v29+v33
  have h34 : ((2797163758833266533648249 : ℝ) / 1000000000000000000000000) ≤ v34 ∧ v34 ≤ ((699290942253396636614951 : ℝ) / 250000000000000000000000) := add_interval h29 h33 (by norm_num) (by norm_num)
  let v35 : ℝ := jacobian y 6 0
  have h35 : ((19887945818055601641403 : ℝ) / 1000000000000000000000000) ≤ v35 ∧ v35 ≤ ((1242996619358249185917 : ℝ) / 62500000000000000000000) := by
    simpa [v35,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 0
  let v36 : ℝ := v3*v35
  have h36 : ((-207173650166266302628137 : ℝ) / 1000000000000000000000000) ≤ v36 ∧ v36 ≤ ((-20717364921126916668719 : ℝ) / 100000000000000000000000) := mul_interval h3 h35 (by norm_num) (by norm_num)
  let v37 : ℝ := v36*v17
  have h37 : ((-94861481537611320107173 : ℝ) / 250000000000000000000000) ≤ v37 ∧ v37 ≤ ((-189722962156856161592893 : ℝ) / 500000000000000000000000) := mul_interval h36 h17 (by norm_num) (by norm_num)
  let v38 : ℝ := v34+v37
  have h38 : ((2417717832682821253219557 : ℝ) / 1000000000000000000000000) ≤ v38 ∧ v38 ≤ ((1208858922349937111637009 : ℝ) / 500000000000000000000000) := add_interval h34 h37 (by norm_num) (by norm_num)
  let v39 : ℝ := jacobian y 6 1
  have h39 : ((4317271196776123736059 : ℝ) / 125000000000000000000000) ≤ v39 ∧ v39 ≤ ((6907633943676554482973 : ℝ) / 200000000000000000000000) := by
    simpa [v39,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 1
  let v40 : ℝ := v3*v39
  have h40 : ((-359785707538450967803977 : ℝ) / 1000000000000000000000000) ≤ v40 ∧ v40 ≤ ((-89946426509146505771543 : ℝ) / 250000000000000000000000) := mul_interval h3 h39 (by norm_num) (by norm_num)
  let v41 : ℝ := v40*v22
  have h41 : ((23292351562188135221107 : ℝ) / 31250000000000000000000) ≤ v41 ∧ v41 ≤ ((46584703329534676184483 : ℝ) / 62500000000000000000000) := mul_interval h40 h22 (by norm_num) (by norm_num)
  let v42 : ℝ := v38+v41
  have h42 : ((3163073082672841580294981 : ℝ) / 1000000000000000000000000) ≤ v42 ∧ v42 ≤ ((1581536548986214521112873 : ℝ) / 500000000000000000000000) := add_interval h38 h41 (by norm_num) (by norm_num)
  let v43 : ℝ := jacobian y 6 2
  have h43 : ((958132295892376553383313 : ℝ) / 1000000000000000000000000) ≤ v43 ∧ v43 ≤ ((47906614911072619327067 : ℝ) / 50000000000000000000000) := by
    simpa [v43,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 2
  let v44 : ℝ := v3*v43
  have h44 : ((-4990454179272426614306789 : ℝ) / 500000000000000000000000) ≤ v44 ∧ v44 ≤ ((-1996181666856552562332133 : ℝ) / 200000000000000000000000) := mul_interval h3 h43 (by norm_num) (by norm_num)
  let v45 : ℝ := v44*v27
  have h45 : ((577962335271590295405473 : ℝ) / 1000000000000000000000000) ≤ v45 ∧ v45 ≤ ((577962338883889170935483 : ℝ) / 1000000000000000000000000) := mul_interval h44 h27 (by norm_num) (by norm_num)
  let v46 : ℝ := v42+v45
  have h46 : ((1870517708972215937850227 : ℝ) / 500000000000000000000000) ≤ v46 ∧ v46 ≤ ((3741035436856318213161229 : ℝ) / 1000000000000000000000000) := add_interval h42 h45 (by norm_num) (by norm_num)
  let v47 : ℝ := jacobian y 6 3
  have h47 : ((-145958612457602976659 : ℝ) / 8000000000000000000000) ≤ v47 ∧ v47 ≤ ((-9122413255285573890587 : ℝ) / 500000000000000000000000) := by
    simpa [v47,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 3
  let v48 : ℝ := v3*v47
  have h48 : ((38011439914422272496641 : ℝ) / 200000000000000000000000) ≤ v48 ∧ v48 ≤ ((190057200057850143488949 : ℝ) / 1000000000000000000000000) := mul_interval h3 h47 (by norm_num) (by norm_num)
  let v49 : ℝ := v48*v32
  have h49 : ((-3484015609837027988473 : ℝ) / 200000000000000000000000) ≤ v49 ∧ v49 ≤ ((-4355019490625693519149 : ℝ) / 250000000000000000000000) := mul_interval h48 h32 (by norm_num) (by norm_num)
  let v50 : ℝ := v46+v49
  have h50 : ((3723615339895246735758089 : ℝ) / 1000000000000000000000000) ≤ v50 ∧ v50 ≤ ((3723615358893815439084633 : ℝ) / 1000000000000000000000000) := add_interval h46 h49 (by norm_num) (by norm_num)
  let v51 : ℝ := jacobian y 4 0
  have h51 : ((-20920238568579790742713 : ℝ) / 500000000000000000000000) ≤ v51 ∧ v51 ≤ ((-20920238360800254919879 : ℝ) / 500000000000000000000000) := by
    simpa [v51,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 0
  let v52 : ℝ := v7*v51
  have h52 : ((849900136516186113726543 : ℝ) / 1000000000000000000000000) ≤ v52 ∧ v52 ≤ ((424950072478691618301969 : ℝ) / 500000000000000000000000) := mul_interval h7 h51 (by norm_num) (by norm_num)
  let v53 : ℝ := v52*v17
  have h53 : ((1556622399144343931826519 : ℝ) / 1000000000000000000000000) ≤ v53 ∧ v53 ≤ ((1556622414964152655853609 : ℝ) / 1000000000000000000000000) := mul_interval h52 h17 (by norm_num) (by norm_num)
  let v54 : ℝ := v50+v53
  have h54 : ((165007429344987208362019 : ℝ) / 31250000000000000000000) ≤ v54 ∧ v54 ≤ ((2640118886928984047469121 : ℝ) / 500000000000000000000000) := add_interval h50 h53 (by norm_num) (by norm_num)
  let v55 : ℝ := jacobian y 4 1
  have h55 : ((-86771204945417368140751 : ℝ) / 500000000000000000000000) ≤ v55 ∧ v55 ≤ ((-173542409840748627089177 : ℝ) / 1000000000000000000000000) := by
    simpa [v55,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 1
  let v56 : ℝ := v7*v55
  have h56 : ((3525144294994499060684567 : ℝ) / 1000000000000000000000000) ≤ v56 ∧ v56 ≤ ((3525144296011891652154383 : ℝ) / 1000000000000000000000000) := mul_interval h7 h55 (by norm_num) (by norm_num)
  let v57 : ℝ := v56*v22
  have h57 : ((-1460583210796633031183709 : ℝ) / 200000000000000000000000) ≤ v57 ∧ v57 ≤ ((-3651458025099160211935159 : ℝ) / 500000000000000000000000) := mul_interval h56 h22 (by norm_num) (by norm_num)
  let v58 : ℝ := v54+v57
  have h58 : ((-2022678314943574488333937 : ℝ) / 1000000000000000000000000) ≤ v58 ∧ v58 ≤ ((-505669569085088082233019 : ℝ) / 250000000000000000000000) := add_interval h54 h57 (by norm_num) (by norm_num)
  let v59 : ℝ := jacobian y 4 2
  have h59 : ((-175556108140406758762831 : ℝ) / 100000000000000000000000) ≤ v59 ∧ v59 ≤ ((-175556108048133991859057 : ℝ) / 100000000000000000000000) := by
    simpa [v59,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 2
  let v60 : ℝ := v7*v59
  have h60 : ((35660482835591339795487503 : ℝ) / 1000000000000000000000000) ≤ v60 ∧ v60 ≤ ((8915120713583646591868607 : ℝ) / 250000000000000000000000) := mul_interval h7 h59 (by norm_num) (by norm_num)
  let v61 : ℝ := v60*v27
  have h61 : ((-412996800207569492173157 : ℝ) / 200000000000000000000000) ≤ v61 ∧ v61 ≤ ((-2064983992065880067421091 : ℝ) / 1000000000000000000000000) := mul_interval h60 h27 (by norm_num) (by norm_num)
  let v62 : ℝ := v58+v61
  have h62 : ((-2043831157990710974599861 : ℝ) / 500000000000000000000000) ≤ v62 ∧ v62 ≤ ((-4087662268406232396353167 : ℝ) / 1000000000000000000000000) := add_interval h58 h61 (by norm_num) (by norm_num)
  let v63 : ℝ := jacobian y 4 3
  have h63 : ((387002424629700218897 : ℝ) / 3906250000000000000000) ≤ v63 ∧ v63 ≤ ((49536310374971854504441 : ℝ) / 500000000000000000000000) := by
    simpa [v63,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 3
  let v64 : ℝ := v7*v63
  have h64 : ((-125778074991619841261413 : ℝ) / 62500000000000000000000) ≤ v64 ∧ v64 ≤ ((-2012449198957110485035723 : ℝ) / 1000000000000000000000000) := mul_interval h7 h63 (by norm_num) (by norm_num)
  let v65 : ℝ := v64*v32
  have h65 : ((9222755575778072964527 : ℝ) / 50000000000000000000000) ≤ v65 ∧ v65 ≤ ((184455112045288010773373 : ℝ) / 1000000000000000000000000) := mul_interval h64 h32 (by norm_num) (by norm_num)
  let v66 : ℝ := v62+v65
  have h66 : ((-1951603602232930244954591 : ℝ) / 500000000000000000000000) ≤ v66 ∧ v66 ≤ ((-1951603578180472192789897 : ℝ) / 500000000000000000000000) := add_interval h62 h65 (by norm_num) (by norm_num)
  let v67 : ℝ := jacobian y 7 0
  have h67 : ((466094240090983921433 : ℝ) / 200000000000000000000000) ≤ v67 ∧ v67 ≤ ((1165235615761669234849 : ℝ) / 500000000000000000000000) := by
    simpa [v67,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 0
  let v68 : ℝ := v11*v67
  have h68 : ((910392730349802956877 : ℝ) / 1000000000000000000000000) ≤ v68 ∧ v68 ≤ ((910392742486602875449 : ℝ) / 1000000000000000000000000) := mul_interval h11 h67 (by norm_num) (by norm_num)
  let v69 : ℝ := v68*v17
  have h69 : ((833708370662022512283 : ℝ) / 500000000000000000000000) ≤ v69 ∧ v69 ≤ ((1667416763938066650043 : ℝ) / 1000000000000000000000000) := mul_interval h68 h17 (by norm_num) (by norm_num)
  let v70 : ℝ := v66+v69
  have h70 : ((-487692473465567055610577 : ℝ) / 125000000000000000000000) ≤ v70 ∧ v70 ≤ ((-3901539739597006318929751 : ℝ) / 1000000000000000000000000) := add_interval h66 h69 (by norm_num) (by norm_num)
  let v71 : ℝ := jacobian y 7 1
  have h71 : ((4241889797437522854441 : ℝ) / 500000000000000000000000) ≤ v71 ∧ v71 ≤ ((1696755923596905032717 : ℝ) / 200000000000000000000000) := by
    simpa [v71,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 1
  let v72 : ℝ := v11*v71
  have h72 : ((662833444803485098459 : ℝ) / 200000000000000000000000) ≤ v72 ∧ v72 ≤ ((165708361652254284489 : ℝ) / 50000000000000000000000) := mul_interval h11 h71 (by norm_num) (by norm_num)
  let v73 : ℝ := v72*v22
  have h73 : ((-137316847535413772417 : ℝ) / 20000000000000000000000) ≤ v73 ∧ v73 ≤ ((-3432921178245816706087 : ℝ) / 500000000000000000000000) := mul_interval h72 h22 (by norm_num) (by norm_num)
  let v74 : ℝ := v70+v73
  have h74 : ((-1954202815050653566752733 : ℝ) / 500000000000000000000000) ≤ v74 ∧ v74 ≤ ((-156336223278139918093677 : ℝ) / 40000000000000000000000) := add_interval h70 h73 (by norm_num) (by norm_num)
  let v75 : ℝ := jacobian y 7 2
  have h75 : ((187498645815716978461599 : ℝ) / 1000000000000000000000000) ≤ v75 ∧ v75 ≤ ((187498646102469604336189 : ℝ) / 1000000000000000000000000) := by
    simpa [v75,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 2
  let v76 : ℝ := v11*v75
  have h76 : ((36622937899369932698821 : ℝ) / 500000000000000000000000) ≤ v76 ∧ v76 ≤ ((36622937955379529803901 : ℝ) / 500000000000000000000000) := mul_interval h11 h75 (by norm_num) (by norm_num)
  let v77 : ℝ := v76*v27
  have h77 : ((-4241433368009936327111 : ℝ) / 1000000000000000000000000) ≤ v77 ∧ v77 ≤ ((-4241433345324342710271 : ℝ) / 1000000000000000000000000) := mul_interval h76 h27 (by norm_num) (by norm_num)
  let v78 : ℝ := v74+v77
  have h78 : ((-3912647063469317069832577 : ℝ) / 1000000000000000000000000) ≤ v78 ∧ v78 ≤ ((-978161753824705573763049 : ℝ) / 250000000000000000000000) := add_interval h74 h77 (by norm_num) (by norm_num)
  let v79 : ℝ := jacobian y 7 3
  have h79 : ((112114839443909922027043 : ℝ) / 1000000000000000000000000) ≤ v79 ∧ v79 ≤ ((7007177488327404136947 : ℝ) / 62500000000000000000000) := by
    simpa [v79,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 3
  let v80 : ℝ := v11*v79
  have h80 : ((43797380879088594114039 : ℝ) / 1000000000000000000000000) ≤ v80 ∧ v80 ≤ ((10949345255841465932223 : ℝ) / 250000000000000000000000) := mul_interval h11 h79 (by norm_num) (by norm_num)
  let v81 : ℝ := v80*v32
  have h81 : ((-4014337765392226486011 : ℝ) / 1000000000000000000000000) ≤ v81 ∧ v81 ≤ ((-2007168871226244256599 : ℝ) / 500000000000000000000000) := mul_interval h80 h32 (by norm_num) (by norm_num)
  let v82 : ℝ := v78+v81
  have h82 : ((-979165350308677324079647 : ℝ) / 250000000000000000000000) ≤ v82 ∧ v82 ≤ ((-1958330676520637391782697 : ℝ) / 500000000000000000000000) := add_interval h78 h81 (by norm_num) (by norm_num)
  have he : approximateAcceleration y 0 = v82 := by
    simp only [approximateAcceleration,matrixCLM_apply,Matrix.mulVec,dotProduct,accelerationForcing,preconditioner,M2KernelCertificate.preconditioner,residualIndex,amplitudeIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h82 (by norm_num) (by norm_num)

private theorem gradient_bound_0 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |curvatureGradient y 0| ≤ ((2 : ℝ) / 1) := by
  let v0 : ℝ := jacobian y 9 6
  have h0 : ((-68481857285323689111453 : ℝ) / 250000000000000000000000) ≤ v0 ∧ v0 ≤ ((-273927429117514510828087 : ℝ) / 1000000000000000000000000) := by
    simpa [v0,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 6
  have he : curvatureGradient y 0 = v0 := by
    simp only [curvatureGradient,velocityIndex,Matrix.cons_val]
    norm_num [v0] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h0 (by norm_num) (by norm_num)

private theorem approx_bound_1 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |approximateAcceleration y 1| ≤ ((1000 : ℝ) / 1) := by
  let v0 : ℝ := ((-8569877571857449 : ℝ) / 144115188075855872)
  have h0 : ((-8569877571857449 : ℝ) / 144115188075855872) ≤ v0 ∧ v0 ≤ ((-8569877571857449 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 7 4
  have h1 : ((0 : ℝ) / 1) ≤ v1 ∧ v1 ≤ ((0 : ℝ) / 1) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 4
  let v2 : ℝ := v0*v1
  have h2 : ((0 : ℝ) / 1) ≤ v2 ∧ v2 ≤ ((0 : ℝ) / 1) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((372160374982343 : ℝ) / 281474976710656)
  have h3 : ((372160374982343 : ℝ) / 281474976710656) ≤ v3 ∧ v3 ≤ ((372160374982343 : ℝ) / 281474976710656) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 6 4
  have h4 : ((0 : ℝ) / 1) ≤ v4 ∧ v4 ≤ ((0 : ℝ) / 1) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 4
  let v5 : ℝ := v3*v4
  have h5 : ((0 : ℝ) / 1) ≤ v5 ∧ v5 ≤ ((0 : ℝ) / 1) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((0 : ℝ) / 1) ≤ v6 ∧ v6 ≤ ((0 : ℝ) / 1) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((2624911170949731 : ℝ) / 1125899906842624)
  have h7 : ((2624911170949731 : ℝ) / 1125899906842624) ≤ v7 ∧ v7 ≤ ((2624911170949731 : ℝ) / 1125899906842624) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 4 4
  have h8 : ((0 : ℝ) / 1) ≤ v8 ∧ v8 ≤ ((0 : ℝ) / 1) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 4
  let v9 : ℝ := v7*v8
  have h9 : ((0 : ℝ) / 1) ≤ v9 ∧ v9 ≤ ((0 : ℝ) / 1) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((0 : ℝ) / 1) ≤ v10 ∧ v10 ≤ ((0 : ℝ) / 1) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((5402920345206155 : ℝ) / 2251799813685248)
  have h11 : ((5402920345206155 : ℝ) / 2251799813685248) ≤ v11 ∧ v11 ≤ ((5402920345206155 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 5 4
  have h12 : ((0 : ℝ) / 1) ≤ v12 ∧ v12 ≤ ((0 : ℝ) / 1) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 4
  let v13 : ℝ := v11*v12
  have h13 : ((0 : ℝ) / 1) ≤ v13 ∧ v13 ≤ ((0 : ℝ) / 1) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((0 : ℝ) / 1) ≤ v14 ∧ v14 ≤ ((0 : ℝ) / 1) := add_interval h10 h13 (by norm_num) (by norm_num)
  let v15 : ℝ := jacobian y 7 0
  have h15 : ((466094240090983921433 : ℝ) / 200000000000000000000000) ≤ v15 ∧ v15 ≤ ((1165235615761669234849 : ℝ) / 500000000000000000000000) := by
    simpa [v15,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 0
  let v16 : ℝ := v0*v15
  have h16 : ((-138582569995180279337 : ℝ) / 1000000000000000000000000) ≤ v16 ∧ v16 ≤ ((-270669078413441623 : ℝ) / 1953125000000000000000) := mul_interval h0 h15 (by norm_num) (by norm_num)
  let v17 : ℝ := velocity y 0
  have h17 : ((4578839125515008337388553 : ℝ) / 2500000000000000000000000) ≤ v17 ∧ v17 ≤ ((4578839126572353912611447 : ℝ) / 2500000000000000000000000) := by simpa [v17,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 6
  let v18 : ℝ := v16*v17
  have h18 : ((-63454729375488337061 : ℝ) / 250000000000000000000000) ≤ v18 ∧ v18 ≤ ((-63454728514895680581 : ℝ) / 250000000000000000000000) := mul_interval h16 h17 (by norm_num) (by norm_num)
  let v19 : ℝ := v14+v18
  have h19 : ((-63454729375488337061 : ℝ) / 250000000000000000000000) ≤ v19 ∧ v19 ≤ ((-63454728514895680581 : ℝ) / 250000000000000000000000) := add_interval h14 h18 (by norm_num) (by norm_num)
  let v20 : ℝ := jacobian y 7 1
  have h20 : ((4241889797437522854441 : ℝ) / 500000000000000000000000) ≤ v20 ∧ v20 ≤ ((1696755923596905032717 : ℝ) / 200000000000000000000000) := by
    simpa [v20,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 1
  let v21 : ℝ := v0*v20
  have h21 : ((-504491952884787283983 : ℝ) / 1000000000000000000000000) ≤ v21 ∧ v21 ≤ ((-504491951510571198083 : ℝ) / 1000000000000000000000000) := mul_interval h0 h20 (by norm_num) (by norm_num)
  let v22 : ℝ := velocity y 1
  have h22 : ((-51791610787714331078253517 : ℝ) / 25000000000000000000000000) ≤ v22 ∧ v22 ≤ ((-51791610775820146421746483 : ℝ) / 25000000000000000000000000) := by simpa [v22,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 7
  let v23 : ℝ := v21*v22
  have h23 : ((522569015843388681157 : ℝ) / 500000000000000000000000) ≤ v23 ∧ v23 ≤ ((1045138034773712765841 : ℝ) / 1000000000000000000000000) := mul_interval h21 h22 (by norm_num) (by norm_num)
  let v24 : ℝ := v19+v23
  have h24 : ((79131911418482401407 : ℝ) / 100000000000000000000000) ≤ v24 ∧ v24 ≤ ((791319120714130043517 : ℝ) / 1000000000000000000000000) := add_interval h19 h23 (by norm_num) (by norm_num)
  let v25 : ℝ := jacobian y 7 2
  have h25 : ((187498645815716978461599 : ℝ) / 1000000000000000000000000) ≤ v25 ∧ v25 ≤ ((187498646102469604336189 : ℝ) / 1000000000000000000000000) := by
    simpa [v25,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 2
  let v26 : ℝ := v0*v25
  have h26 : ((-5574847673728259277559 : ℝ) / 500000000000000000000000) ≤ v26 ∧ v26 ≤ ((-11149695330404638528007 : ℝ) / 1000000000000000000000000) := mul_interval h0 h25 (by norm_num) (by norm_num)
  let v27 : ℝ := velocity y 2
  have h27 : ((-5790678745077187 : ℝ) / 100000000000000000) ≤ v27 ∧ v27 ≤ ((-28953393614806863 : ℝ) / 500000000000000000) := by simpa [v27,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 8
  let v28 : ℝ := v26*v27
  have h28 : ((40352689698297444727 : ℝ) / 62500000000000000000000) ≤ v28 ∧ v28 ≤ ((645643038626024633437 : ℝ) / 1000000000000000000000000) := mul_interval h26 h27 (by norm_num) (by norm_num)
  let v29 : ℝ := v24+v28
  have h29 : ((718481074678791564851 : ℝ) / 500000000000000000000000) ≤ v29 ∧ v29 ≤ ((718481079670077338477 : ℝ) / 500000000000000000000000) := add_interval h24 h28 (by norm_num) (by norm_num)
  let v30 : ℝ := jacobian y 7 3
  have h30 : ((112114839443909922027043 : ℝ) / 1000000000000000000000000) ≤ v30 ∧ v30 ≤ ((7007177488327404136947 : ℝ) / 62500000000000000000000) := by
    simpa [v30,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 3
  let v31 : ℝ := v0*v30
  have h31 : ((-3333480891278907806589 : ℝ) / 500000000000000000000000) ≤ v31 ∧ v31 ≤ ((-416685110037219980741 : ℝ) / 62500000000000000000000) := mul_interval h0 h30 (by norm_num) (by norm_num)
  let v32 : ℝ := velocity y 3
  have h32 : ((-9165702769420347 : ℝ) / 100000000000000000) ≤ v32 ∧ v32 ≤ ((-9165702747237029 : ℝ) / 100000000000000000) := by simpa [v32,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 9
  let v33 : ℝ := v31*v32
  have h33 : ((305536948624072872373 : ℝ) / 500000000000000000000000) ≤ v33 ∧ v33 ≤ ((9548029699064028727 : ℝ) / 15625000000000000000000) := mul_interval h31 h32 (by norm_num) (by norm_num)
  let v34 : ℝ := v29+v33
  have h34 : ((128002252912858054653 : ℝ) / 62500000000000000000000) ≤ v34 ∧ v34 ≤ ((1024018030040126257741 : ℝ) / 500000000000000000000000) := add_interval h29 h33 (by norm_num) (by norm_num)
  let v35 : ℝ := jacobian y 6 0
  have h35 : ((19887945818055601641403 : ℝ) / 1000000000000000000000000) ≤ v35 ∧ v35 ≤ ((1242996619358249185917 : ℝ) / 62500000000000000000000) := by
    simpa [v35,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 0
  let v36 : ℝ := v3*v35
  have h36 : ((6573857345838345816707 : ℝ) / 250000000000000000000000) ≤ v36 ∧ v36 ≤ ((5259085900913199623873 : ℝ) / 200000000000000000000000) := mul_interval h3 h35 (by norm_num) (by norm_num)
  let v37 : ℝ := v36*v17
  have h37 : ((12040254088271546037091 : ℝ) / 250000000000000000000000) ≤ v37 ∧ v37 ≤ ((12040254146553187979893 : ℝ) / 250000000000000000000000) := mul_interval h36 h17 (by norm_num) (by norm_num)
  let v38 : ℝ := v34+v37
  have h38 : ((12552263099922978255703 : ℝ) / 250000000000000000000000) ≤ v38 ∧ v38 ≤ ((25104526323146502217527 : ℝ) / 500000000000000000000000) := add_interval h34 h37 (by norm_num) (by norm_num)
  let v39 : ℝ := jacobian y 6 1
  have h39 : ((4317271196776123736059 : ℝ) / 125000000000000000000000) ≤ v39 ∧ v39 ≤ ((6907633943676554482973 : ℝ) / 200000000000000000000000) := by
    simpa [v39,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 1
  let v40 : ℝ := v3*v39
  have h40 : ((22832825656744701961097 : ℝ) / 500000000000000000000000) ≤ v40 ∧ v40 ≤ ((11416412876028247070027 : ℝ) / 250000000000000000000000) := mul_interval h3 h39 (by norm_num) (by norm_num)
  let v41 : ℝ := v40*v22
  have h41 : ((-47301952981368428255059 : ℝ) / 500000000000000000000000) ≤ v41 ∧ v41 ≤ ((-4730195277305126471093 : ℝ) / 50000000000000000000000) := mul_interval h40 h22 (by norm_num) (by norm_num)
  let v42 : ℝ := v38+v41
  have h42 : ((-22197426781522471743653 : ℝ) / 500000000000000000000000) ≤ v42 ∧ v42 ≤ ((-22197426449904762493403 : ℝ) / 500000000000000000000000) := add_interval h38 h41 (by norm_num) (by norm_num)
  let v43 : ℝ := jacobian y 6 2
  have h43 : ((958132295892376553383313 : ℝ) / 1000000000000000000000000) ≤ v43 ∧ v43 ≤ ((47906614911072619327067 : ℝ) / 50000000000000000000000) := by
    simpa [v43,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 2
  let v44 : ℝ := v3*v43
  have h44 : ((15835283063569963770679 : ℝ) / 12500000000000000000000) ≤ v44 ∧ v44 ≤ ((633411324082526425680893 : ℝ) / 500000000000000000000000) := mul_interval h3 h43 (by norm_num) (by norm_num)
  let v45 : ℝ := v44*v27
  have h45 : ((-73357629825117670379263 : ℝ) / 1000000000000000000000000) ≤ v45 ∧ v45 ≤ ((-73357629366628135852593 : ℝ) / 1000000000000000000000000) := mul_interval h44 h27 (by norm_num) (by norm_num)
  let v46 : ℝ := v42+v45
  have h46 : ((-117752483388162613866569 : ℝ) / 1000000000000000000000000) ≤ v46 ∧ v46 ≤ ((-117752482266437660839399 : ℝ) / 1000000000000000000000000) := add_interval h42 h45 (by norm_num) (by norm_num)
  let v47 : ℝ := jacobian y 6 3
  have h47 : ((-145958612457602976659 : ℝ) / 8000000000000000000000) ≤ v47 ∧ v47 ≤ ((-9122413255285573890587 : ℝ) / 500000000000000000000000) := by
    simpa [v47,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 3
  let v48 : ℝ := v3*v47
  have h48 : ((-4824586236662398535057 : ℝ) / 200000000000000000000000) ≤ v48 ∧ v48 ≤ ((-24122931121659799631817 : ℝ) / 1000000000000000000000000) := mul_interval h3 h47 (by norm_num) (by norm_num)
  let v49 : ℝ := v48*v32
  have h49 : ((276379520066508563657 : ℝ) / 125000000000000000000000) ≤ v49 ∧ v49 ≤ ((2211036171534191796089 : ℝ) / 1000000000000000000000000) := mul_interval h48 h32 (by norm_num) (by norm_num)
  let v50 : ℝ := v46+v49
  have h50 : ((-115541447227630545357313 : ℝ) / 1000000000000000000000000) ≤ v50 ∧ v50 ≤ ((-11554144609490346904331 : ℝ) / 100000000000000000000000) := add_interval h46 h49 (by norm_num) (by norm_num)
  let v51 : ℝ := jacobian y 4 0
  have h51 : ((-20920238568579790742713 : ℝ) / 500000000000000000000000) ≤ v51 ∧ v51 ≤ ((-20920238360800254919879 : ℝ) / 500000000000000000000000) := by
    simpa [v51,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 0
  let v52 : ℝ := v7*v51
  have h52 : ((-12193305902208018765617 : ℝ) / 125000000000000000000000) ≤ v52 ∧ v52 ≤ ((-97546446248834112283317 : ℝ) / 1000000000000000000000000) := mul_interval h7 h51 (by norm_num) (by norm_num)
  let v53 : ℝ := v52*v17
  have h53 : ((-178659795671346215858389 : ℝ) / 1000000000000000000000000) ≤ v53 ∧ v53 ≤ ((-178659793855643340823307 : ℝ) / 1000000000000000000000000) := mul_interval h52 h17 (by norm_num) (by norm_num)
  let v54 : ℝ := v50+v53
  have h54 : ((-147100621449488380607851 : ℝ) / 500000000000000000000000) ≤ v54 ∧ v54 ≤ ((-294201239950546809866617 : ℝ) / 1000000000000000000000000) := add_interval h50 h53 (by norm_num) (by norm_num)
  let v55 : ℝ := jacobian y 4 1
  have h55 : ((-86771204945417368140751 : ℝ) / 500000000000000000000000) ≤ v55 ∧ v55 ≤ ((-173542409840748627089177 : ℝ) / 1000000000000000000000000) := by
    simpa [v55,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 1
  let v56 : ℝ := v7*v55
  have h56 : ((-404594944530591137501353 : ℝ) / 1000000000000000000000000) ≤ v56 ∧ v56 ≤ ((-404594944413820910654963 : ℝ) / 1000000000000000000000000) := mul_interval h7 h55 (by norm_num) (by norm_num)
  let v57 : ℝ := v56*v22
  have h57 : ((52386559707363000577789 : ℝ) / 62500000000000000000000) ≤ v57 ∧ v57 ≤ ((419092477876104907029683 : ℝ) / 500000000000000000000000) := mul_interval h56 h22 (by norm_num) (by norm_num)
  let v58 : ℝ := v54+v57
  have h58 : ((271991856209415624014461 : ℝ) / 500000000000000000000000) ≤ v58 ∧ v58 ≤ ((543983715801663004192749 : ℝ) / 1000000000000000000000000) := add_interval h54 h57 (by norm_num) (by norm_num)
  let v59 : ℝ := jacobian y 4 2
  have h59 : ((-175556108140406758762831 : ℝ) / 100000000000000000000000) ≤ v59 ∧ v59 ≤ ((-175556108048133991859057 : ℝ) / 100000000000000000000000) := by
    simpa [v59,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 2
  let v60 : ℝ := v7*v59
  have h60 : ((-4092896593965391250339067 : ℝ) / 1000000000000000000000000) ≤ v60 ∧ v60 ≤ ((-2046448295907076846145989 : ℝ) / 500000000000000000000000) := mul_interval h7 h59 (by norm_num) (by norm_num)
  let v61 : ℝ := v60*v27
  have h61 : ((59251623023748344505991 : ℝ) / 250000000000000000000000) ≤ v61 ∧ v61 ≤ ((237006493124742047883459 : ℝ) / 1000000000000000000000000) := mul_interval h60 h27 (by norm_num) (by norm_num)
  let v62 : ℝ := v58+v61
  have h62 : ((390495102256912313026443 : ℝ) / 500000000000000000000000) ≤ v62 ∧ v62 ≤ ((48811888057900315754763 : ℝ) / 62500000000000000000000) := add_interval h58 h61 (by norm_num) (by norm_num)
  let v63 : ℝ := jacobian y 4 3
  have h63 : ((387002424629700218897 : ℝ) / 3906250000000000000000) ≤ v63 ∧ v63 ≤ ((49536310374971854504441 : ℝ) / 500000000000000000000000) := by
    simpa [v63,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 3
  let v64 : ℝ := v7*v63
  have h64 : ((230976863257440395063933 : ℝ) / 1000000000000000000000000) ≤ v64 ∧ v64 ≤ ((230976863361747815362887 : ℝ) / 1000000000000000000000000) := mul_interval h7 h63 (by norm_num) (by norm_num)
  let v65 : ℝ := v64*v32
  have h65 : ((-21170652761867970315349 : ℝ) / 1000000000000000000000000) ≤ v65 ∧ v65 ≤ ((-21170652701069130121473 : ℝ) / 1000000000000000000000000) := mul_interval h64 h32 (by norm_num) (by norm_num)
  let v66 : ℝ := v62+v65
  have h66 : ((759819551751956655737537 : ℝ) / 1000000000000000000000000) ≤ v66 ∧ v66 ≤ ((151963911245067184390947 : ℝ) / 200000000000000000000000) := add_interval h62 h65 (by norm_num) (by norm_num)
  let v67 : ℝ := jacobian y 5 0
  have h67 : ((14471030679094404089679 : ℝ) / 1000000000000000000000000) ≤ v67 ∧ v67 ≤ ((7235515359098802834341 : ℝ) / 500000000000000000000000) := by
    simpa [v67,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 0
  let v68 : ℝ := v11*v67
  have h68 : ((217009260761684689593 : ℝ) / 6250000000000000000000) ≤ v68 ∧ v68 ≤ ((8680370453923234112561 : ℝ) / 250000000000000000000000) := mul_interval h11 h67 (by norm_num) (by norm_num)
  let v69 : ℝ := v68*v17
  have h69 : ((635936316015802071171 : ℝ) / 10000000000000000000000) ≤ v69 ∧ v69 ≤ ((15898407947026531418909 : ℝ) / 250000000000000000000000) := mul_interval h68 h17 (by norm_num) (by norm_num)
  let v70 : ℝ := v66+v69
  have h70 : ((823413183353536862854637 : ℝ) / 1000000000000000000000000) ≤ v70 ∧ v70 ≤ ((823413188013442047630371 : ℝ) / 1000000000000000000000000) := add_interval h66 h69 (by norm_num) (by norm_num)
  let v71 : ℝ := jacobian y 5 1
  have h71 : ((50815194354105460729557 : ℝ) / 1000000000000000000000000) ≤ v71 ∧ v71 ≤ ((50815194420457997287063 : ℝ) / 1000000000000000000000000) := by
    simpa [v71,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 1
  let v72 : ℝ := v11*v71
  have h72 : ((3048122281483781997251 : ℝ) / 25000000000000000000000) ≤ v72 ∧ v72 ≤ ((121924891418556137952391 : ℝ) / 1000000000000000000000000) := mul_interval h11 h71 (by norm_num) (by norm_num)
  let v73 : ℝ := v72*v22
  have h73 : ((-252587460867367621819723 : ℝ) / 1000000000000000000000000) ≤ v73 ∧ v73 ≤ ((-7893358139985646662939 : ℝ) / 31250000000000000000000) := mul_interval h72 h22 (by norm_num) (by norm_num)
  let v74 : ℝ := v70+v73
  have h74 : ((285412861243084620517457 : ℝ) / 500000000000000000000000) ≤ v74 ∧ v74 ≤ ((570825727533901354416323 : ℝ) / 1000000000000000000000000) := add_interval h70 h73 (by norm_num) (by norm_num)
  let v75 : ℝ := jacobian y 5 2
  have h75 : ((48193689742644681369447 : ℝ) / 100000000000000000000000) ≤ v75 ∧ v75 ≤ ((120484224418590333953647 : ℝ) / 250000000000000000000000) := by
    simpa [v75,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 2
  let v76 : ℝ := v11*v75
  have h76 : ((144543636405085680999251 : ℝ) / 125000000000000000000000) ≤ v76 ∧ v76 ≤ ((578174545917763126844163 : ℝ) / 500000000000000000000000) := mul_interval h11 h75 (by norm_num) (by norm_num)
  let v77 : ℝ := v76*v27
  have h77 : ((-3348023053990645015237 : ℝ) / 50000000000000000000000) ≤ v77 ∧ v77 ≤ ((-16740115197407890341869 : ℝ) / 250000000000000000000000) := mul_interval h76 h27 (by norm_num) (by norm_num)
  let v78 : ℝ := v74+v77
  have h78 : ((251932630703178170365087 : ℝ) / 500000000000000000000000) ≤ v78 ∧ v78 ≤ ((503865266744269793048847 : ℝ) / 1000000000000000000000000) := add_interval h74 h77 (by norm_num) (by norm_num)
  let v79 : ℝ := jacobian y 5 3
  have h79 : ((-46801914920349775960023 : ℝ) / 1000000000000000000000000) ≤ v79 ∧ v79 ≤ ((-11700478724808102304361 : ℝ) / 250000000000000000000000) := by
    simpa [v79,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 3
  let v80 : ℝ := v11*v79
  have h80 : ((-112295514361877705332041 : ℝ) / 1000000000000000000000000) ≤ v80 ∧ v80 ≤ ((-112295514311209146911683 : ℝ) / 1000000000000000000000000) := mul_interval h11 h79 (by norm_num) (by norm_num)
  let v81 : ℝ := v80*v32
  have h81 : ((321646032507701495063 : ℝ) / 31250000000000000000000) ≤ v81 ∧ v81 ≤ ((1286584133725181042971 : ℝ) / 125000000000000000000000) := mul_interval h80 h32 (by norm_num) (by norm_num)
  let v82 : ℝ := v78+v81
  have h82 : ((51415793444660278857219 : ℝ) / 100000000000000000000000) ≤ v82 ∧ v82 ≤ ((102831587962814248278523 : ℝ) / 200000000000000000000000) := add_interval h78 h81 (by norm_num) (by norm_num)
  have he : approximateAcceleration y 1 = v82 := by
    simp only [approximateAcceleration,matrixCLM_apply,Matrix.mulVec,dotProduct,accelerationForcing,preconditioner,M2KernelCertificate.preconditioner,residualIndex,amplitudeIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h82 (by norm_num) (by norm_num)

private theorem gradient_bound_1 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |curvatureGradient y 1| ≤ ((2 : ℝ) / 1) := by
  let v0 : ℝ := jacobian y 9 7
  have h0 : ((-27740261258299526549517 : ℝ) / 125000000000000000000000) ≤ v0 ∧ v0 ≤ ((-887688360263508957861 : ℝ) / 4000000000000000000000) := by
    simpa [v0,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 7
  have he : curvatureGradient y 1 = v0 := by
    simp only [curvatureGradient,velocityIndex,Matrix.cons_val]
    norm_num [v0] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h0 (by norm_num) (by norm_num)

private theorem approx_bound_2 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |approximateAcceleration y 2| ≤ ((1000 : ℝ) / 1) := by
  let v0 : ℝ := ((-5676625074002731 : ℝ) / 18014398509481984)
  have h0 : ((-5676625074002731 : ℝ) / 18014398509481984) ≤ v0 ∧ v0 ≤ ((-5676625074002731 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 5 4
  have h1 : ((0 : ℝ) / 1) ≤ v1 ∧ v1 ≤ ((0 : ℝ) / 1) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 4
  let v2 : ℝ := v0*v1
  have h2 : ((0 : ℝ) / 1) ≤ v2 ∧ v2 ≤ ((0 : ℝ) / 1) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-1906405801350491 : ℝ) / 9007199254740992)
  have h3 : ((-1906405801350491 : ℝ) / 9007199254740992) ≤ v3 ∧ v3 ≤ ((-1906405801350491 : ℝ) / 9007199254740992) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 4 4
  have h4 : ((0 : ℝ) / 1) ≤ v4 ∧ v4 ≤ ((0 : ℝ) / 1) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 4
  let v5 : ℝ := v3*v4
  have h5 : ((0 : ℝ) / 1) ≤ v5 ∧ v5 ≤ ((0 : ℝ) / 1) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((0 : ℝ) / 1) ≤ v6 ∧ v6 ≤ ((0 : ℝ) / 1) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-901757038800969 : ℝ) / 4503599627370496)
  have h7 : ((-901757038800969 : ℝ) / 4503599627370496) ≤ v7 ∧ v7 ≤ ((-901757038800969 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 6 4
  have h8 : ((0 : ℝ) / 1) ≤ v8 ∧ v8 ≤ ((0 : ℝ) / 1) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 4
  let v9 : ℝ := v7*v8
  have h9 : ((0 : ℝ) / 1) ≤ v9 ∧ v9 ≤ ((0 : ℝ) / 1) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((0 : ℝ) / 1) ≤ v10 ∧ v10 ≤ ((0 : ℝ) / 1) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((5941539868098331 : ℝ) / 2305843009213693952)
  have h11 : ((5941539868098331 : ℝ) / 2305843009213693952) ≤ v11 ∧ v11 ≤ ((5941539868098331 : ℝ) / 2305843009213693952) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 4
  have h12 : ((0 : ℝ) / 1) ≤ v12 ∧ v12 ≤ ((0 : ℝ) / 1) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 4
  let v13 : ℝ := v11*v12
  have h13 : ((0 : ℝ) / 1) ≤ v13 ∧ v13 ≤ ((0 : ℝ) / 1) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((0 : ℝ) / 1) ≤ v14 ∧ v14 ≤ ((0 : ℝ) / 1) := add_interval h10 h13 (by norm_num) (by norm_num)
  let v15 : ℝ := jacobian y 5 0
  have h15 : ((14471030679094404089679 : ℝ) / 1000000000000000000000000) ≤ v15 ∧ v15 ≤ ((7235515359098802834341 : ℝ) / 500000000000000000000000) := by
    simpa [v15,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 0
  let v16 : ℝ := v0*v15
  have h16 : ((-4560053214008001721297 : ℝ) / 1000000000000000000000000) ≤ v16 ∧ v16 ≤ ((-2280026600842978763787 : ℝ) / 500000000000000000000000) := mul_interval h0 h15 (by norm_num) (by norm_num)
  let v17 : ℝ := velocity y 0
  have h17 : ((4578839125515008337388553 : ℝ) / 2500000000000000000000000) ≤ v17 ∧ v17 ≤ ((4578839126572353912611447 : ℝ) / 2500000000000000000000000) := by simpa [v17,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 6
  let v18 : ℝ := v16*v17
  have h18 : ((-4175950015110370771461 : ℝ) / 500000000000000000000000) ≤ v18 ∧ v18 ≤ ((-8351900005723857483259 : ℝ) / 1000000000000000000000000) := mul_interval h16 h17 (by norm_num) (by norm_num)
  let v19 : ℝ := v14+v18
  have h19 : ((-4175950015110370771461 : ℝ) / 500000000000000000000000) ≤ v19 ∧ v19 ≤ ((-8351900005723857483259 : ℝ) / 1000000000000000000000000) := add_interval h14 h18 (by norm_num) (by norm_num)
  let v20 : ℝ := jacobian y 5 1
  have h20 : ((50815194354105460729557 : ℝ) / 1000000000000000000000000) ≤ v20 ∧ v20 ≤ ((50815194420457997287063 : ℝ) / 1000000000000000000000000) := by
    simpa [v20,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 1
  let v21 : ℝ := v0*v20
  have h21 : ((-3202536089513769360199 : ℝ) / 200000000000000000000000) ≤ v21 ∧ v21 ≤ ((-3202536085332020271571 : ℝ) / 200000000000000000000000) := mul_interval h0 h20 (by norm_num) (by norm_num)
  let v22 : ℝ := velocity y 1
  have h22 : ((-51791610787714331078253517 : ℝ) / 25000000000000000000000000) ≤ v22 ∧ v22 ≤ ((-51791610775820146421746483 : ℝ) / 25000000000000000000000000) := by simpa [v22,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 7
  let v23 : ℝ := v21*v22
  have h23 : ((16586450242703472906051 : ℝ) / 500000000000000000000000) ≤ v23 ∧ v23 ≤ ((33172900536341161167737 : ℝ) / 1000000000000000000000000) := mul_interval h21 h22 (by norm_num) (by norm_num)
  let v24 : ℝ := v19+v23
  have h24 : ((1241050022759310213459 : ℝ) / 50000000000000000000000) ≤ v24 ∧ v24 ≤ ((12410500265308651842239 : ℝ) / 500000000000000000000000) := add_interval h19 h23 (by norm_num) (by norm_num)
  let v25 : ℝ := jacobian y 5 2
  have h25 : ((48193689742644681369447 : ℝ) / 100000000000000000000000) ≤ v25 ∧ v25 ≤ ((120484224418590333953647 : ℝ) / 250000000000000000000000) := by
    simpa [v25,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 2
  let v26 : ℝ := v0*v25
  have h26 : ((-4745813251802052961327 : ℝ) / 31250000000000000000000) ≤ v26 ∧ v26 ≤ ((-151866023979543863953861 : ℝ) / 1000000000000000000000000) := mul_interval h0 h25 (by norm_num) (by norm_num)
  let v27 : ℝ := velocity y 2
  have h27 : ((-5790678745077187 : ℝ) / 100000000000000000) ≤ v27 ∧ v27 ≤ ((-28953393614806863 : ℝ) / 500000000000000000) := by simpa [v27,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 8
  let v28 : ℝ := v26*v27
  have h28 : ((8794073537990862505881 : ℝ) / 1000000000000000000000000) ≤ v28 ∧ v28 ≤ ((2198518394025263689439 : ℝ) / 250000000000000000000000) := mul_interval h26 h27 (by norm_num) (by norm_num)
  let v29 : ℝ := v24+v28
  have h29 : ((33615073993177066775061 : ℝ) / 1000000000000000000000000) ≤ v29 ∧ v29 ≤ ((16807537053359179221117 : ℝ) / 500000000000000000000000) := add_interval h24 h28 (by norm_num) (by norm_num)
  let v30 : ℝ := jacobian y 5 3
  have h30 : ((-46801914920349775960023 : ℝ) / 1000000000000000000000000) ≤ v30 ∧ v30 ≤ ((-11700478724808102304361 : ℝ) / 250000000000000000000000) := by
    simpa [v30,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 3
  let v31 : ℝ := v0*v30
  have h31 : ((14748031886187267988461 : ℝ) / 1000000000000000000000000) ≤ v31 ∧ v31 ≤ ((737401594642084398919 : ℝ) / 50000000000000000000000) := mul_interval h0 h30 (by norm_num) (by norm_num)
  let v32 : ℝ := velocity y 3
  have h32 : ((-9165702769420347 : ℝ) / 100000000000000000) ≤ v32 ∧ v32 ≤ ((-9165702747237029 : ℝ) / 100000000000000000) := by simpa [v32,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 9
  let v33 : ℝ := v31*v32
  have h33 : ((-675880383818593308721 : ℝ) / 500000000000000000000000) ≤ v33 ∧ v33 ≤ ((-675880381877829724041 : ℝ) / 500000000000000000000000) := mul_interval h31 h32 (by norm_num) (by norm_num)
  let v34 : ℝ := v29+v33
  have h34 : ((32263313225539880157619 : ℝ) / 1000000000000000000000000) ≤ v34 ∧ v34 ≤ ((4032914167870337374269 : ℝ) / 125000000000000000000000) := add_interval h29 h33 (by norm_num) (by norm_num)
  let v35 : ℝ := jacobian y 4 0
  have h35 : ((-20920238568579790742713 : ℝ) / 500000000000000000000000) ≤ v35 ∧ v35 ≤ ((-20920238360800254919879 : ℝ) / 500000000000000000000000) := by
    simpa [v35,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 0
  let v36 : ℝ := v3*v35
  have h36 : ((8855685912726383667259 : ℝ) / 1000000000000000000000000) ≤ v36 ∧ v36 ≤ ((1771137200136188238427 : ℝ) / 200000000000000000000000) := mul_interval h3 h35 (by norm_num) (by norm_num)
  let v37 : ℝ := v36*v17
  have h37 : ((16219504456185461213501 : ℝ) / 1000000000000000000000000) ≤ v37 ∧ v37 ≤ ((16219504621022777081761 : ℝ) / 1000000000000000000000000) := mul_interval h36 h17 (by norm_num) (by norm_num)
  let v38 : ℝ := v34+v37
  have h38 : ((606035221021566767139 : ℝ) / 12500000000000000000000) ≤ v38 ∧ v38 ≤ ((48482817963985476075913 : ℝ) / 1000000000000000000000000) := add_interval h34 h37 (by norm_num) (by norm_num)
  let v39 : ℝ := jacobian y 4 1
  have h39 : ((-86771204945417368140751 : ℝ) / 500000000000000000000000) ≤ v39 ∧ v39 ≤ ((-173542409840748627089177 : ℝ) / 1000000000000000000000000) := by
    simpa [v39,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 1
  let v40 : ℝ := v3*v39
  have h40 : ((36730869113016120412261 : ℝ) / 1000000000000000000000000) ≤ v40 ∧ v40 ≤ ((18365434561808511902093 : ℝ) / 500000000000000000000000) := mul_interval h3 h39 (by norm_num) (by norm_num)
  let v41 : ℝ := v40*v22
  have h41 : ((-95117543877242334393 : ℝ) / 1250000000000000000000) ≤ v41 ∧ v41 ≤ ((-76094035062357003422521 : ℝ) / 1000000000000000000000000) := mul_interval h40 h22 (by norm_num) (by norm_num)
  let v42 : ℝ := v38+v41
  have h42 : ((-345140217750856576791 : ℝ) / 12500000000000000000000) ≤ v42 ∧ v42 ≤ ((-1725701068648220459163 : ℝ) / 62500000000000000000000) := add_interval h38 h41 (by norm_num) (by norm_num)
  let v43 : ℝ := jacobian y 4 2
  have h43 : ((-175556108140406758762831 : ℝ) / 100000000000000000000000) ≤ v43 ∧ v43 ≤ ((-175556108048133991859057 : ℝ) / 100000000000000000000000) := by
    simpa [v43,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 2
  let v44 : ℝ := v3*v43
  have h44 : ((725724131062167410647 : ℝ) / 1953125000000000000000) ≤ v44 ∧ v44 ≤ ((371570755299128311692001 : ℝ) / 1000000000000000000000000) := mul_interval h3 h43 (by norm_num) (by norm_num)
  let v45 : ℝ := v44*v27
  have h45 : ((-21516468750029388634319 : ℝ) / 1000000000000000000000000) ≤ v45 ∧ v45 ≤ ((-10758234328272187849721 : ℝ) / 500000000000000000000000) := mul_interval h44 h27 (by norm_num) (by norm_num)
  let v46 : ℝ := v42+v45
  have h46 : ((-49127686170097914777599 : ℝ) / 1000000000000000000000000) ≤ v46 ∧ v46 ≤ ((-982553715098318060921 : ℝ) / 20000000000000000000000) := add_interval h42 h45 (by norm_num) (by norm_num)
  let v47 : ℝ := jacobian y 4 3
  have h47 : ((387002424629700218897 : ℝ) / 3906250000000000000000) ≤ v47 ∧ v47 ≤ ((49536310374971854504441 : ℝ) / 500000000000000000000000) := by
    simpa [v47,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 3
  let v48 : ℝ := v3*v47
  have h48 : ((-20969073028252984602611 : ℝ) / 1000000000000000000000000) ≤ v48 ∧ v48 ≤ ((-10484536509391754194199 : ℝ) / 500000000000000000000000) := mul_interval h3 h47 (by norm_num) (by norm_num)
  let v49 : ℝ := v48*v32
  have h49 : ((240245362719097329803 : ℝ) / 125000000000000000000000) ≤ v49 ∧ v49 ≤ ((1921962907272358831449 : ℝ) / 1000000000000000000000000) := mul_interval h48 h32 (by norm_num) (by norm_num)
  let v50 : ℝ := v46+v49
  have h50 : ((-1888228930733805445567 : ℝ) / 40000000000000000000000) ≤ v50 ∧ v50 ≤ ((-47205722847643544214601 : ℝ) / 1000000000000000000000000) := add_interval h46 h49 (by norm_num) (by norm_num)
  let v51 : ℝ := jacobian y 6 0
  have h51 : ((19887945818055601641403 : ℝ) / 1000000000000000000000000) ≤ v51 ∧ v51 ≤ ((1242996619358249185917 : ℝ) / 62500000000000000000000) := by
    simpa [v51,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 0
  let v52 : ℝ := v7*v51
  have h52 : ((-398216908590182330119 : ℝ) / 100000000000000000000000) ≤ v52 ∧ v52 ≤ ((-3982169067545434499733 : ℝ) / 1000000000000000000000000) := mul_interval h7 h51 (by norm_num) (by norm_num)
  let v53 : ℝ := v52*v17
  have h53 : ((-729348464766165343329 : ℝ) / 100000000000000000000000) ≤ v53 ∧ v53 ≤ ((-7293484612357061389271 : ℝ) / 1000000000000000000000000) := mul_interval h52 h17 (by norm_num) (by norm_num)
  let v54 : ℝ := v50+v53
  have h54 : ((-10899841583201357914493 : ℝ) / 200000000000000000000000) ≤ v54 ∧ v54 ≤ ((-1703100233125018925121 : ℝ) / 31250000000000000000000) := add_interval h50 h53 (by norm_num) (by norm_num)
  let v55 : ℝ := jacobian y 6 1
  have h55 : ((4317271196776123736059 : ℝ) / 125000000000000000000000) ≤ v55 ∧ v55 ≤ ((6907633943676554482973 : ℝ) / 200000000000000000000000) := by
    simpa [v55,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 1
  let v56 : ℝ := v7*v55
  have h56 : ((-1383117516111826817503 : ℝ) / 200000000000000000000000) ≤ v56 ∧ v56 ≤ ((-864448443961397057791 : ℝ) / 125000000000000000000000) := mul_interval h7 h55 (by norm_num) (by norm_num)
  let v57 : ℝ := v56*v22
  have h57 : ((14326776750531855948941 : ℝ) / 1000000000000000000000000) ≤ v57 ∧ v57 ≤ ((716338840681339399263 : ℝ) / 50000000000000000000000) := mul_interval h56 h22 (by norm_num) (by norm_num)
  let v58 : ℝ := v54+v57
  have h58 : ((-10043107791368733405881 : ℝ) / 250000000000000000000000) ≤ v58 ∧ v58 ≤ ((-10043107661593454404653 : ℝ) / 250000000000000000000000) := add_interval h54 h57 (by norm_num) (by norm_num)
  let v59 : ℝ := jacobian y 6 2
  have h59 : ((958132295892376553383313 : ℝ) / 1000000000000000000000000) ≤ v59 ∧ v59 ≤ ((47906614911072619327067 : ℝ) / 50000000000000000000000) := by
    simpa [v59,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 2
  let v60 : ℝ := v7*v59
  have h60 : ((-191847103541974171241267 : ℝ) / 1000000000000000000000000) ≤ v60 ∧ v60 ≤ ((-47961775768905663101427 : ℝ) / 250000000000000000000000) := mul_interval h7 h59 (by norm_num) (by norm_num)
  let v61 : ℝ := v60*v27
  have h61 : ((2777312344604463496183 : ℝ) / 250000000000000000000000) ≤ v61 ∧ v61 ≤ ((11109249447851321511269 : ℝ) / 1000000000000000000000000) := mul_interval h60 h27 (by norm_num) (by norm_num)
  let v62 : ℝ := v58+v61
  have h62 : ((-3632897723382134954849 : ℝ) / 125000000000000000000000) ≤ v62 ∧ v62 ≤ ((-29063181198522496107343 : ℝ) / 1000000000000000000000000) := add_interval h58 h61 (by norm_num) (by norm_num)
  let v63 : ℝ := jacobian y 6 3
  have h63 : ((-145958612457602976659 : ℝ) / 8000000000000000000000) ≤ v63 ∧ v63 ≤ ((-9122413255285573890587 : ℝ) / 500000000000000000000000) := by
    simpa [v63,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 3
  let v64 : ℝ := v7*v63
  have h64 : ((3653166819630472152259 : ℝ) / 1000000000000000000000000) ≤ v64 ∧ v64 ≤ ((3653166828967055042953 : ℝ) / 1000000000000000000000000) := mul_interval h7 h63 (by norm_num) (by norm_num)
  let v65 : ℝ := v64*v32
  have h65 : ((-334838413214178835341 : ℝ) / 1000000000000000000000000) ≤ v65 ∧ v65 ≤ ((-334838411548021786089 : ℝ) / 1000000000000000000000000) := mul_interval h64 h32 (by norm_num) (by norm_num)
  let v66 : ℝ := v62+v65
  have h66 : ((-29398020200271258474133 : ℝ) / 1000000000000000000000000) ≤ v66 ∧ v66 ≤ ((-3674752451258814736679 : ℝ) / 125000000000000000000000) := add_interval h62 h65 (by norm_num) (by norm_num)
  let v67 : ℝ := jacobian y 7 0
  have h67 : ((466094240090983921433 : ℝ) / 200000000000000000000000) ≤ v67 ∧ v67 ≤ ((1165235615761669234849 : ℝ) / 500000000000000000000000) := by
    simpa [v67,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 0
  let v68 : ℝ := v11*v67
  have h68 : ((1501250030209087181 : ℝ) / 250000000000000000000000) ≤ v68 ∧ v68 ≤ ((6005000200891343177 : ℝ) / 1000000000000000000000000) := mul_interval h11 h67 (by norm_num) (by norm_num)
  let v69 : ℝ := v68*v17
  have h69 : ((2199674360160626111 : ℝ) / 200000000000000000000000) ≤ v69 ∧ v69 ≤ ((1099837194996645103 : ℝ) / 100000000000000000000000) := mul_interval h68 h17 (by norm_num) (by norm_num)
  let v70 : ℝ := v66+v69
  have h70 : ((-14693510914235227671789 : ℝ) / 500000000000000000000000) ≤ v70 ∧ v70 ≤ ((-14693510619060275721201 : ℝ) / 500000000000000000000000) := add_interval h66 h69 (by norm_num) (by norm_num)
  let v71 : ℝ := jacobian y 7 1
  have h71 : ((4241889797437522854441 : ℝ) / 500000000000000000000000) ≤ v71 ∧ v71 ≤ ((1696755923596905032717 : ℝ) / 200000000000000000000000) := by
    simpa [v71,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 1
  let v72 : ℝ := v11*v71
  have h72 : ((21860427832117754497 : ℝ) / 1000000000000000000000000) ≤ v72 ∧ v72 ≤ ((10930213945832346857 : ℝ) / 500000000000000000000000) := mul_interval h11 h71 (by norm_num) (by norm_num)
  let v73 : ℝ := v72*v22
  have h73 : ((-9057494184143939211 : ℝ) / 200000000000000000000000) ≤ v73 ∧ v73 ≤ ((-45287470786957941461 : ℝ) / 1000000000000000000000000) := mul_interval h72 h22 (by norm_num) (by norm_num)
  let v74 : ℝ := v70+v73
  have h74 : ((-29432309299391175039633 : ℝ) / 1000000000000000000000000) ≤ v74 ∧ v74 ≤ ((-29432308708907509383863 : ℝ) / 1000000000000000000000000) := add_interval h70 h73 (by norm_num) (by norm_num)
  let v75 : ℝ := jacobian y 7 2
  have h75 : ((187498645815716978461599 : ℝ) / 1000000000000000000000000) ≤ v75 ∧ v75 ≤ ((187498646102469604336189 : ℝ) / 1000000000000000000000000) := by
    simpa [v75,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 2
  let v76 : ℝ := v11*v75
  have h76 : ((483133793097398144803 : ℝ) / 1000000000000000000000000) ≤ v76 ∧ v76 ≤ ((483133793836282861633 : ℝ) / 1000000000000000000000000) := mul_interval h11 h75 (by norm_num) (by norm_num)
  let v77 : ℝ := v76*v27
  have h77 : ((-27976725909962668249 : ℝ) / 1000000000000000000000000) ≤ v77 ∧ v77 ≤ ((-13988362880163627507 : ℝ) / 500000000000000000000000) := mul_interval h76 h27 (by norm_num) (by norm_num)
  let v78 : ℝ := v74+v77
  have h78 : ((-14730143012650568853941 : ℝ) / 500000000000000000000000) ≤ v78 ∧ v78 ≤ ((-29460285434667836638877 : ℝ) / 1000000000000000000000000) := add_interval h74 h77 (by norm_num) (by norm_num)
  let v79 : ℝ := jacobian y 7 3
  have h79 : ((112114839443909922027043 : ℝ) / 1000000000000000000000000) ≤ v79 ∧ v79 ≤ ((7007177488327404136947 : ℝ) / 62500000000000000000000) := by
    simpa [v79,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 3
  let v80 : ℝ := v11*v79
  have h80 : ((288889913883855433113 : ℝ) / 1000000000000000000000000) ≤ v80 ∧ v80 ≤ ((9027809838609880479 : ℝ) / 31250000000000000000000) := mul_interval h11 h79 (by norm_num) (by norm_num)
  let v81 : ℝ := v80*v32
  have h81 : ((-413731108197734187 : ℝ) / 15625000000000000000000) ≤ v81 ∧ v81 ≤ ((-3309848846667903087 : ℝ) / 125000000000000000000000) := mul_interval h80 h32 (by norm_num) (by norm_num)
  let v82 : ℝ := v78+v81
  have h82 : ((-589735296324515853917 : ℝ) / 20000000000000000000000) ≤ v82 ∧ v82 ≤ ((-29486764225441179863573 : ℝ) / 1000000000000000000000000) := add_interval h78 h81 (by norm_num) (by norm_num)
  have he : approximateAcceleration y 2 = v82 := by
    simp only [approximateAcceleration,matrixCLM_apply,Matrix.mulVec,dotProduct,accelerationForcing,preconditioner,M2KernelCertificate.preconditioner,residualIndex,amplitudeIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h82 (by norm_num) (by norm_num)

private theorem gradient_bound_2 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |curvatureGradient y 2| ≤ ((2 : ℝ) / 1) := by
  let v0 : ℝ := jacobian y 9 8
  have h0 : ((-770981222685690422294011 : ℝ) / 1000000000000000000000000) ≤ v0 ∧ v0 ≤ ((-385490611161663940667689 : ℝ) / 500000000000000000000000) := by
    simpa [v0,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 8
  have he : curvatureGradient y 2 = v0 := by
    simp only [curvatureGradient,velocityIndex,Matrix.cons_val]
    norm_num [v0] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h0 (by norm_num) (by norm_num)

private theorem approx_bound_3 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |approximateAcceleration y 3| ≤ ((1000 : ℝ) / 1) := by
  let v0 : ℝ := ((-6811950088803285 : ℝ) / 144115188075855872)
  have h0 : ((-6811950088803285 : ℝ) / 144115188075855872) ≤ v0 ∧ v0 ≤ ((-6811950088803285 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v0]
  let v1 : ℝ := jacobian y 4 4
  have h1 : ((0 : ℝ) / 1) ≤ v1 ∧ v1 ≤ ((0 : ℝ) / 1) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 4
  let v2 : ℝ := v0*v1
  have h2 : ((0 : ℝ) / 1) ≤ v2 ∧ v2 ≤ ((0 : ℝ) / 1) := mul_interval h0 h1 (by norm_num) (by norm_num)
  let v3 : ℝ := ((-1828646140081387 : ℝ) / 18014398509481984)
  have h3 : ((-1828646140081387 : ℝ) / 18014398509481984) ≤ v3 ∧ v3 ≤ ((-1828646140081387 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v3]
  let v4 : ℝ := jacobian y 5 4
  have h4 : ((0 : ℝ) / 1) ≤ v4 ∧ v4 ≤ ((0 : ℝ) / 1) := by
    simpa [v4,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 4
  let v5 : ℝ := v3*v4
  have h5 : ((0 : ℝ) / 1) ≤ v5 ∧ v5 ≤ ((0 : ℝ) / 1) := mul_interval h3 h4 (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : ((0 : ℝ) / 1) ≤ v6 ∧ v6 ≤ ((0 : ℝ) / 1) := add_interval h2 h5 (by norm_num) (by norm_num)
  let v7 : ℝ := ((-605344055995505 : ℝ) / 144115188075855872)
  have h7 : ((-605344055995505 : ℝ) / 144115188075855872) ≤ v7 ∧ v7 ≤ ((-605344055995505 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v7]
  let v8 : ℝ := jacobian y 6 4
  have h8 : ((0 : ℝ) / 1) ≤ v8 ∧ v8 ≤ ((0 : ℝ) / 1) := by
    simpa [v8,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 4
  let v9 : ℝ := v7*v8
  have h9 : ((0 : ℝ) / 1) ≤ v9 ∧ v9 ≤ ((0 : ℝ) / 1) := mul_interval h7 h8 (by norm_num) (by norm_num)
  let v10 : ℝ := v6+v9
  have h10 : ((0 : ℝ) / 1) ≤ v10 ∧ v10 ≤ ((0 : ℝ) / 1) := add_interval h6 h9 (by norm_num) (by norm_num)
  let v11 : ℝ := ((-329097342168993 : ℝ) / 2251799813685248)
  have h11 : ((-329097342168993 : ℝ) / 2251799813685248) ≤ v11 ∧ v11 ≤ ((-329097342168993 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v11]
  let v12 : ℝ := jacobian y 7 4
  have h12 : ((0 : ℝ) / 1) ≤ v12 ∧ v12 ≤ ((0 : ℝ) / 1) := by
    simpa [v12,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 4
  let v13 : ℝ := v11*v12
  have h13 : ((0 : ℝ) / 1) ≤ v13 ∧ v13 ≤ ((0 : ℝ) / 1) := mul_interval h11 h12 (by norm_num) (by norm_num)
  let v14 : ℝ := v10+v13
  have h14 : ((0 : ℝ) / 1) ≤ v14 ∧ v14 ≤ ((0 : ℝ) / 1) := add_interval h10 h13 (by norm_num) (by norm_num)
  let v15 : ℝ := jacobian y 4 0
  have h15 : ((-20920238568579790742713 : ℝ) / 500000000000000000000000) ≤ v15 ∧ v15 ≤ ((-20920238360800254919879 : ℝ) / 500000000000000000000000) := by
    simpa [v15,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 0
  let v16 : ℝ := v0*v15
  have h16 : ((49442262631135542429 : ℝ) / 25000000000000000000000) ≤ v16 ∧ v16 ≤ ((247211315610977265227 : ℝ) / 125000000000000000000000) := mul_interval h0 h15 (by norm_num) (by norm_num)
  let v17 : ℝ := velocity y 0
  have h17 : ((4578839125515008337388553 : ℝ) / 2500000000000000000000000) ≤ v17 ∧ v17 ≤ ((4578839126572353912611447 : ℝ) / 2500000000000000000000000) := by simpa [v17,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 6
  let v18 : ℝ := v16*v17
  have h18 : ((1811105332715456338611 : ℝ) / 500000000000000000000000) ≤ v18 ∧ v18 ≤ ((3622210702243102914719 : ℝ) / 1000000000000000000000000) := mul_interval h16 h17 (by norm_num) (by norm_num)
  let v19 : ℝ := v14+v18
  have h19 : ((1811105332715456338611 : ℝ) / 500000000000000000000000) ≤ v19 ∧ v19 ≤ ((3622210702243102914719 : ℝ) / 1000000000000000000000000) := add_interval h14 h18 (by norm_num) (by norm_num)
  let v20 : ℝ := jacobian y 4 1
  have h20 : ((-86771204945417368140751 : ℝ) / 500000000000000000000000) ≤ v20 ∧ v20 ≤ ((-173542409840748627089177 : ℝ) / 1000000000000000000000000) := by
    simpa [v20,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 1
  let v21 : ℝ := v0*v20
  have h21 : ((8202898319805027669941 : ℝ) / 1000000000000000000000000) ≤ v21 ∧ v21 ≤ ((4101449161086233887367 : ℝ) / 500000000000000000000000) := mul_interval h0 h20 (by norm_num) (by norm_num)
  let v22 : ℝ := velocity y 1
  have h22 : ((-51791610787714331078253517 : ℝ) / 25000000000000000000000000) ≤ v22 ∧ v22 ≤ ((-51791610775820146421746483 : ℝ) / 25000000000000000000000000) := by simpa [v22,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 7
  let v23 : ℝ := v21*v22
  have h23 : ((-3398730537865210947837 : ℝ) / 200000000000000000000000) ≤ v23 ∧ v23 ≤ ((-3398730536103768357397 : ℝ) / 200000000000000000000000) := mul_interval h21 h22 (by norm_num) (by norm_num)
  let v24 : ℝ := v19+v23
  have h24 : ((-13371442023895142061963 : ℝ) / 1000000000000000000000000) ≤ v24 ∧ v24 ≤ ((-6685720989137869436133 : ℝ) / 500000000000000000000000) := add_interval h19 h23 (by norm_num) (by norm_num)
  let v25 : ℝ := jacobian y 4 2
  have h25 : ((-175556108140406758762831 : ℝ) / 100000000000000000000000) ≤ v25 ∧ v25 ≤ ((-175556108048133991859057 : ℝ) / 100000000000000000000000) := by
    simpa [v25,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 2
  let v26 : ℝ := v0*v25
  have h26 : ((82980805963281767551993 : ℝ) / 1000000000000000000000000) ≤ v26 ∧ v26 ≤ ((16596161201379340880383 : ℝ) / 200000000000000000000000) := mul_interval h0 h25 (by norm_num) (by norm_num)
  let v27 : ℝ := velocity y 2
  have h27 : ((-5790678745077187 : ℝ) / 100000000000000000) ≤ v27 ∧ v27 ≤ ((-28953393614806863 : ℝ) / 500000000000000000) := by simpa [v27,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 8
  let v28 : ℝ := v26*v27
  have h28 : ((-60064398699188763633 : ℝ) / 12500000000000000000000) ≤ v28 ∧ v28 ≤ ((-600643984382202397291 : ℝ) / 125000000000000000000000) := mul_interval h26 h27 (by norm_num) (by norm_num)
  let v29 : ℝ := v24+v28
  have h29 : ((-18176593919830243152603 : ℝ) / 1000000000000000000000000) ≤ v29 ∧ v29 ≤ ((-9088296926666679025297 : ℝ) / 500000000000000000000000) := add_interval h24 h28 (by norm_num) (by norm_num)
  let v30 : ℝ := jacobian y 4 3
  have h30 : ((387002424629700218897 : ℝ) / 3906250000000000000000) ≤ v30 ∧ v30 ≤ ((49536310374971854504441 : ℝ) / 500000000000000000000000) := by
    simpa [v30,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 3
  let v31 : ℝ := v0*v30
  have h31 : ((-1170726272376523173393 : ℝ) / 250000000000000000000000) ≤ v31 ∧ v31 ≤ ((-4682905087391327854003 : ℝ) / 1000000000000000000000000) := mul_interval h0 h30 (by norm_num) (by norm_num)
  let v32 : ℝ := velocity y 3
  have h32 : ((-9165702769420347 : ℝ) / 100000000000000000) ≤ v32 ∧ v32 ≤ ((-9165702747237029 : ℝ) / 100000000000000000) := by simpa [v32,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 9
  let v33 : ℝ := v31*v32
  have h33 : ((429221160245529530853 : ℝ) / 1000000000000000000000000) ≤ v33 ∧ v33 ≤ ((53652645184773289687 : ℝ) / 125000000000000000000000) := mul_interval h31 h32 (by norm_num) (by norm_num)
  let v34 : ℝ := v29+v33
  have h34 : ((-70989491038338854487 : ℝ) / 4000000000000000000000) ≤ v34 ∧ v34 ≤ ((-8873686345927585866549 : ℝ) / 500000000000000000000000) := add_interval h29 h33 (by norm_num) (by norm_num)
  let v35 : ℝ := jacobian y 5 0
  have h35 : ((14471030679094404089679 : ℝ) / 1000000000000000000000000) ≤ v35 ∧ v35 ≤ ((7235515359098802834341 : ℝ) / 500000000000000000000000) := by
    simpa [v35,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 0
  let v36 : ℝ := v3*v35
  have h36 : ((-367239495283489441329 : ℝ) / 250000000000000000000000) ≤ v36 ∧ v36 ≤ ((-1468957977164581902189 : ℝ) / 1000000000000000000000000) := mul_interval h3 h35 (by norm_num) (by norm_num)
  let v37 : ℝ := v36*v17
  have h37 : ((-269044891172275980441 : ℝ) / 100000000000000000000000) ≤ v37 ∧ v37 ≤ ((-2690448903831427913409 : ℝ) / 1000000000000000000000000) := mul_interval h36 h17 (by norm_num) (by norm_num)
  let v38 : ℝ := v34+v37
  have h38 : ((-255472770891343417827 : ℝ) / 12500000000000000000000) ≤ v38 ∧ v38 ≤ ((-20437821595686599646507 : ℝ) / 1000000000000000000000000) := add_interval h34 h37 (by norm_num) (by norm_num)
  let v39 : ℝ := jacobian y 5 1
  have h39 : ((50815194354105460729557 : ℝ) / 1000000000000000000000000) ≤ v39 ∧ v39 ≤ ((50815194420457997287063 : ℝ) / 1000000000000000000000000) := by
    simpa [v39,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 1
  let v40 : ℝ := v3*v39
  have h40 : ((-257913160646316280687 : ℝ) / 50000000000000000000000) ≤ v40 ∧ v40 ≤ ((-2579131603095431439191 : ℝ) / 500000000000000000000000) := mul_interval h3 h39 (by norm_num) (by norm_num)
  let v41 : ℝ := v40*v22
  have h41 : ((10686190410170850866781 : ℝ) / 1000000000000000000000000) ≤ v41 ∧ v41 ≤ ((10686190426578602848627 : ℝ) / 1000000000000000000000000) := mul_interval h40 h22 (by norm_num) (by norm_num)
  let v42 : ℝ := v38+v41
  have h42 : ((-9751631261136622559379 : ℝ) / 1000000000000000000000000) ≤ v42 ∧ v42 ≤ ((-243790779227699919947 : ℝ) / 25000000000000000000000) := add_interval h38 h41 (by norm_num) (by norm_num)
  let v43 : ℝ := jacobian y 5 2
  have h43 : ((48193689742644681369447 : ℝ) / 100000000000000000000000) ≤ v43 ∧ v43 ≤ ((120484224418590333953647 : ℝ) / 250000000000000000000000) := by
    simpa [v43,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 2
  let v44 : ℝ := v3*v43
  have h44 : ((-489215361385030984561 : ℝ) / 10000000000000000000000) ≤ v44 ∧ v44 ≤ ((-9784307222667446546899 : ℝ) / 200000000000000000000000) := mul_interval h3 h43 (by norm_num) (by norm_num)
  let v45 : ℝ := v44*v27
  have h45 : ((354111122832610397969 : ℝ) / 125000000000000000000000) ≤ v45 ∧ v45 ≤ ((708222248734388437391 : ℝ) / 250000000000000000000000) := mul_interval h44 h27 (by norm_num) (by norm_num)
  let v46 : ℝ := v42+v45
  have h46 : ((-6918742278475739375627 : ℝ) / 1000000000000000000000000) ≤ v46 ∧ v46 ≤ ((-1729685543542610762079 : ℝ) / 250000000000000000000000) := add_interval h42 h45 (by norm_num) (by norm_num)
  let v47 : ℝ := jacobian y 5 3
  have h47 : ((-46801914920349775960023 : ℝ) / 1000000000000000000000000) ≤ v47 ∧ v47 ≤ ((-11700478724808102304361 : ℝ) / 250000000000000000000000) := by
    simpa [v47,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 3
  let v48 : ℝ := v3*v47
  have h48 : ((4750874195652504768177 : ℝ) / 1000000000000000000000000) ≤ v48 ∧ v48 ≤ ((950174839559226799377 : ℝ) / 200000000000000000000000) := mul_interval h3 h47 (by norm_num) (by norm_num)
  let v49 : ℝ := v48*v32
  have h49 : ((-108862751979769236973 : ℝ) / 250000000000000000000000) ≤ v49 ∧ v49 ≤ ((-108862751667174183427 : ℝ) / 250000000000000000000000) := mul_interval h48 h32 (by norm_num) (by norm_num)
  let v50 : ℝ := v46+v49
  have h50 : ((-7354193286394816323519 : ℝ) / 1000000000000000000000000) ≤ v50 ∧ v50 ≤ ((-919274147604892472753 : ℝ) / 125000000000000000000000) := add_interval h46 h49 (by norm_num) (by norm_num)
  let v51 : ℝ := jacobian y 6 0
  have h51 : ((19887945818055601641403 : ℝ) / 1000000000000000000000000) ≤ v51 ∧ v51 ≤ ((1242996619358249185917 : ℝ) / 62500000000000000000000) := by
    simpa [v51,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 0
  let v52 : ℝ := v7*v51
  have h52 : ((-83537689560378259819 : ℝ) / 1000000000000000000000000) ≤ v52 ∧ v52 ≤ ((-16707537835059820839 : ℝ) / 200000000000000000000000) := mul_interval h7 h51 (by norm_num) (by norm_num)
  let v53 : ℝ := v52*v17
  have h53 : ((-38250564150251483889 : ℝ) / 250000000000000000000000) ≤ v53 ∧ v53 ≤ ((-15300225586038845131 : ℝ) / 100000000000000000000000) := mul_interval h52 h17 (by norm_num) (by norm_num)
  let v54 : ℝ := v50+v53
  have h54 : ((-300287821719832890363 : ℝ) / 40000000000000000000000) ≤ v54 ∧ v54 ≤ ((-3753597718349764116667 : ℝ) / 500000000000000000000000) := add_interval h50 h53 (by norm_num) (by norm_num)
  let v55 : ℝ := jacobian y 6 1
  have h55 : ((4317271196776123736059 : ℝ) / 125000000000000000000000) ≤ v55 ∧ v55 ≤ ((6907633943676554482973 : ℝ) / 200000000000000000000000) := by
    simpa [v55,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 1
  let v56 : ℝ := v7*v55
  have h56 : ((-145074755986039334181 : ℝ) / 1000000000000000000000000) ≤ v56 ∧ v56 ≤ ((-145074755380449156989 : ℝ) / 1000000000000000000000000) := mul_interval h7 h55 (by norm_num) (by norm_num)
  let v57 : ℝ := v56*v22
  have h57 : ((150273105281230846499 : ℝ) / 500000000000000000000000) ≤ v57 ∧ v57 ≤ ((150273105943031580169 : ℝ) / 500000000000000000000000) := mul_interval h56 h22 (by norm_num) (by norm_num)
  let v58 : ℝ := v54+v57
  have h58 : ((-7206649332433360566077 : ℝ) / 1000000000000000000000000) ≤ v58 ∧ v58 ≤ ((-1801662306203366268249 : ℝ) / 250000000000000000000000) := add_interval h54 h57 (by norm_num) (by norm_num)
  let v59 : ℝ := jacobian y 6 2
  have h59 : ((958132295892376553383313 : ℝ) / 1000000000000000000000000) ≤ v59 ∧ v59 ≤ ((47906614911072619327067 : ℝ) / 50000000000000000000000) := by
    simpa [v59,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 2
  let v60 : ℝ := v7*v59
  have h60 : ((-4024556324211869604009 : ℝ) / 1000000000000000000000000) ≤ v60 ∧ v60 ≤ ((-4024556314428777132013 : ℝ) / 1000000000000000000000000) := mul_interval h7 h59 (by norm_num) (by norm_num)
  let v61 : ℝ := v60*v27
  have h61 : ((116524563096612797453 : ℝ) / 500000000000000000000000) ≤ v61 ∧ v61 ≤ ((233049127649796456217 : ℝ) / 1000000000000000000000000) := mul_interval h60 h27 (by norm_num) (by norm_num)
  let v62 : ℝ := v58+v61
  have h62 : ((-6973600206240134971171 : ℝ) / 1000000000000000000000000) ≤ v62 ∧ v62 ≤ ((-6973600097163668616779 : ℝ) / 1000000000000000000000000) := add_interval h58 h61 (by norm_num) (by norm_num)
  let v63 : ℝ := jacobian y 6 3
  have h63 : ((-145958612457602976659 : ℝ) / 8000000000000000000000) ≤ v63 ∧ v63 ≤ ((-9122413255285573890587 : ℝ) / 500000000000000000000000) := by
    simpa [v63,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 3
  let v64 : ℝ := v7*v63
  have h64 : ((1915897524109355477 : ℝ) / 25000000000000000000000) ≤ v64 ∧ v64 ≤ ((76635901160236460551 : ℝ) / 1000000000000000000000000) := mul_interval h7 h63 (by norm_num) (by norm_num)
  let v65 : ℝ := v64*v32
  have h65 : ((-439013682188377069 : ℝ) / 62500000000000000000000) ≤ v65 ∧ v65 ≤ ((-7024218880061496599 : ℝ) / 1000000000000000000000000) := mul_interval h64 h32 (by norm_num) (by norm_num)
  let v66 : ℝ := v62+v65
  have h66 : ((-279224977006205960171 : ℝ) / 40000000000000000000000) ≤ v66 ∧ v66 ≤ ((-3490312158021865056689 : ℝ) / 500000000000000000000000) := add_interval h62 h65 (by norm_num) (by norm_num)
  let v67 : ℝ := jacobian y 7 0
  have h67 : ((466094240090983921433 : ℝ) / 200000000000000000000000) ≤ v67 ∧ v67 ≤ ((1165235615761669234849 : ℝ) / 500000000000000000000000) := by
    simpa [v67,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 0
  let v68 : ℝ := v11*v67
  have h68 : ((-170297529033110045787 : ℝ) / 500000000000000000000000) ≤ v68 ∧ v68 ≤ ((-170297526762807416993 : ℝ) / 500000000000000000000000) := mul_interval h11 h67 (by norm_num) (by norm_num)
  let v69 : ℝ := v68*v17
  have h69 : ((-623811991276316547331 : ℝ) / 1000000000000000000000000) ≤ v69 ∧ v69 ≤ ((-623811982815985473509 : ℝ) / 1000000000000000000000000) := mul_interval h68 h17 (by norm_num) (by norm_num)
  let v70 : ℝ := v66+v69
  have h70 : ((-3802218208215732775803 : ℝ) / 500000000000000000000000) ≤ v70 ∧ v70 ≤ ((-7604436298859715586887 : ℝ) / 1000000000000000000000000) := add_interval h66 h69 (by norm_num) (by norm_num)
  let v71 : ℝ := jacobian y 7 1
  have h71 : ((4241889797437522854441 : ℝ) / 500000000000000000000000) ≤ v71 ∧ v71 ≤ ((1696755923596905032717 : ℝ) / 200000000000000000000000) := by
    simpa [v71,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 1
  let v72 : ℝ := v11*v71
  have h72 : ((-1239892332727779765667 : ℝ) / 1000000000000000000000000) ≤ v72 ∧ v72 ≤ ((-309973082337590547519 : ℝ) / 250000000000000000000000) := mul_interval h11 h71 (by norm_num) (by norm_num)
  let v73 : ℝ := v72*v22
  have h73 : ((1284320418512779208219 : ℝ) / 500000000000000000000000) ≤ v73 ∧ v73 ≤ ((1284320422306167305461 : ℝ) / 500000000000000000000000) := mul_interval h72 h22 (by norm_num) (by norm_num)
  let v74 : ℝ := v70+v73
  have h74 : ((-78684305928217298987 : ℝ) / 15625000000000000000000) ≤ v74 ∧ v74 ≤ ((-1007159090849476195193 : ℝ) / 200000000000000000000000) := add_interval h70 h73 (by norm_num) (by norm_num)
  let v75 : ℝ := jacobian y 7 2
  have h75 : ((187498645815716978461599 : ℝ) / 1000000000000000000000000) ≤ v75 ∧ v75 ≤ ((187498646102469604336189 : ℝ) / 1000000000000000000000000) := by
    simpa [v75,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 2
  let v76 : ℝ := v11*v75
  have h76 : ((-3425332578277782431743 : ℝ) / 125000000000000000000000) ≤ v76 ∧ v76 ≤ ((-2740266058431377075891 : ℝ) / 100000000000000000000000) := mul_interval h11 h75 (by norm_num) (by norm_num)
  let v77 : ℝ := v76*v27
  have h77 : ((79340001799059003179 : ℝ) / 50000000000000000000000) ≤ v77 ∧ v77 ≤ ((396700011117071891579 : ℝ) / 250000000000000000000000) := mul_interval h76 h27 (by norm_num) (by norm_num)
  let v78 : ℝ := v74+v77
  have h78 : ((-862248885856181767897 : ℝ) / 250000000000000000000000) ≤ v78 ∧ v78 ≤ ((-3448995409779093409649 : ℝ) / 1000000000000000000000000) := add_interval h74 h77 (by norm_num) (by norm_num)
  let v79 : ℝ := jacobian y 7 3
  have h79 : ((112114839443909922027043 : ℝ) / 1000000000000000000000000) ≤ v79 ∧ v79 ≤ ((7007177488327404136947 : ℝ) / 62500000000000000000000) := by
    simpa [v79,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 3
  let v80 : ℝ := v11*v79
  have h80 : ((-8192712242003170333199 : ℝ) / 500000000000000000000000) ≤ v80 ∧ v80 ≤ ((-16385424430029498882831 : ℝ) / 1000000000000000000000000) := mul_interval h11 h79 (by norm_num) (by norm_num)
  let v81 : ℝ := v80*v32
  have h81 : ((750919648564830539843 : ℝ) / 500000000000000000000000) ≤ v81 ∧ v81 ≤ ((375459826427962192213 : ℝ) / 250000000000000000000000) := mul_interval h80 h32 (by norm_num) (by norm_num)
  let v82 : ℝ := v78+v81
  have h82 : ((-973578123147532995951 : ℝ) / 500000000000000000000000) ≤ v82 ∧ v82 ≤ ((-1947156104067244640797 : ℝ) / 1000000000000000000000000) := add_interval h78 h81 (by norm_num) (by norm_num)
  have he : approximateAcceleration y 3 = v82 := by
    simp only [approximateAcceleration,matrixCLM_apply,Matrix.mulVec,dotProduct,accelerationForcing,preconditioner,M2KernelCertificate.preconditioner,residualIndex,amplitudeIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h82 (by norm_num) (by norm_num)

private theorem gradient_bound_3 (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    |curvatureGradient y 3| ≤ ((2 : ℝ) / 1) := by
  let v0 : ℝ := jacobian y 9 9
  have h0 : ((183107489880450076869 : ℝ) / 6250000000000000000000) ≤ v0 ∧ v0 ≤ ((2929719838736338153881 : ℝ) / 100000000000000000000000) := by
    simpa [v0,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 9
  have he : curvatureGradient y 3 = v0 := by
    simp only [curvatureGradient,velocityIndex,Matrix.cons_val]
    norm_num [v0] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact abs_bound h0 (by norm_num) (by norm_num)

/-- A positive rational lower bound for the preconditioned curvature.
This is an approximation bound, not an assumed true acceleration. -/
theorem approximate_curvature_gt (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) :
    (9 : ℝ)/10 < curvature y (approximateAcceleration y) := by
  let v0 : ℝ := jacobian y 9 4
  have h0 : ((0 : ℝ) / 1) ≤ v0 ∧ v0 ≤ ((0 : ℝ) / 1) := by
    simpa [v0,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 4
  let v1 : ℝ := jacobian y 9 0
  have h1 : ((1402783614745257049539 : ℝ) / 500000000000000000000000) ≤ v1 ∧ v1 ≤ ((2805567252251778470663 : ℝ) / 1000000000000000000000000) := by
    simpa [v1,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 0
  let v2 : ℝ := velocity y 0
  have h2 : ((4578839125515008337388553 : ℝ) / 2500000000000000000000000) ≤ v2 ∧ v2 ≤ ((4578839126572353912611447 : ℝ) / 2500000000000000000000000) := by simpa [v2,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 6
  let v3 : ℝ := v1*v2
  have h3 : ((1027699279972312823001 : ℝ) / 200000000000000000000000) ≤ v3 ∧ v3 ≤ ((5138496442736212903391 : ℝ) / 1000000000000000000000000) := mul_interval h1 h2 (by norm_num) (by norm_num)
  let v4 : ℝ := v0+v3
  have h4 : ((1027699279972312823001 : ℝ) / 200000000000000000000000) ≤ v4 ∧ v4 ≤ ((5138496442736212903391 : ℝ) / 1000000000000000000000000) := add_interval h0 h3 (by norm_num) (by norm_num)
  let v5 : ℝ := jacobian y 9 1
  have h5 : ((207096321512736625933 : ℝ) / 1000000000000000000000000) ≤ v5 ∧ v5 ≤ ((207096322014022876887 : ℝ) / 1000000000000000000000000) := by
    simpa [v5,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 1
  let v6 : ℝ := velocity y 1
  have h6 : ((-51791610787714331078253517 : ℝ) / 25000000000000000000000000) ≤ v6 ∧ v6 ≤ ((-51791610775820146421746483 : ℝ) / 25000000000000000000000000) := by simpa [v6,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 7
  let v7 : ℝ := v5*v6
  have h7 : ((-85806816842539425079 : ℝ) / 200000000000000000000000) ≤ v7 ∧ v7 ≤ ((-214517041537835276849 : ℝ) / 500000000000000000000000) := mul_interval h5 h6 (by norm_num) (by norm_num)
  let v8 : ℝ := v4+v7
  have h8 : ((470946231564886698961 : ℝ) / 100000000000000000000000) ≤ v8 ∧ v8 ≤ ((4709462359660542349693 : ℝ) / 1000000000000000000000000) := add_interval h4 h7 (by norm_num) (by norm_num)
  let v9 : ℝ := jacobian y 9 2
  have h9 : ((-17747475412066499576709 : ℝ) / 200000000000000000000000) ≤ v9 ∧ v9 ≤ ((-44368688508402164893031 : ℝ) / 500000000000000000000000) := by
    simpa [v9,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 2
  let v10 : ℝ := velocity y 2
  have h10 : ((-5790678745077187 : ℝ) / 100000000000000000) ≤ v10 ∧ v10 ≤ ((-28953393614806863 : ℝ) / 500000000000000000) := by simpa [v10,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 8
  let v11 : ℝ := v9*v10
  have h11 : ((2569248205113051758947 : ℝ) / 500000000000000000000000) ≤ v11 ∧ v11 ≤ ((2569248216185836750251 : ℝ) / 500000000000000000000000) := mul_interval h9 h10 (by norm_num) (by norm_num)
  let v12 : ℝ := v8+v11
  have h12 : ((615497420367185656719 : ℝ) / 62500000000000000000000) ≤ v12 ∧ v12 ≤ ((1969591758406443170039 : ℝ) / 200000000000000000000000) := add_interval h8 h11 (by norm_num) (by norm_num)
  let v13 : ℝ := jacobian y 9 3
  have h13 : ((234043201545598053307 : ℝ) / 50000000000000000000000) ≤ v13 ∧ v13 ≤ ((2340432015993536838659 : ℝ) / 500000000000000000000000) := by
    simpa [v13,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 3
  let v14 : ℝ := velocity y 3
  have h14 : ((-9165702769420347 : ℝ) / 100000000000000000) ≤ v14 ∧ v14 ≤ ((-9165702747237029 : ℝ) / 100000000000000000) := by simpa [v14,velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 9
  let v15 : ℝ := v13*v14
  have h15 : ((-429034084212640129297 : ℝ) / 1000000000000000000000000) ≤ v15 ∧ v15 ≤ ((-214517041537863774897 : ℝ) / 500000000000000000000000) := mul_interval h13 h14 (by norm_num) (by norm_num)
  let v16 : ℝ := v12+v15
  have h16 : ((9418924641662330378207 : ℝ) / 1000000000000000000000000) ≤ v16 ∧ v16 ≤ ((9418924708956488300401 : ℝ) / 1000000000000000000000000) := add_interval h12 h15 (by norm_num) (by norm_num)
  let v17 : ℝ := jacobian y 9 6
  have h17 : ((-68481857285323689111453 : ℝ) / 250000000000000000000000) ≤ v17 ∧ v17 ≤ ((-273927429117514510828087 : ℝ) / 1000000000000000000000000) := by
    simpa [v17,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 6
  let v18 : ℝ := ((-7689872965427469 : ℝ) / 281474976710656)
  have h18 : ((-7689872965427469 : ℝ) / 281474976710656) ≤ v18 ∧ v18 ≤ ((-7689872965427469 : ℝ) / 281474976710656) := by constructor <;> norm_num [v18]
  let v19 : ℝ := jacobian y 5 4
  have h19 : ((0 : ℝ) / 1) ≤ v19 ∧ v19 ≤ ((0 : ℝ) / 1) := by
    simpa [v19,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 4
  let v20 : ℝ := v18*v19
  have h20 : ((0 : ℝ) / 1) ≤ v20 ∧ v20 ≤ ((0 : ℝ) / 1) := mul_interval h18 h19 (by norm_num) (by norm_num)
  let v21 : ℝ := ((-5864275639152445 : ℝ) / 562949953421312)
  have h21 : ((-5864275639152445 : ℝ) / 562949953421312) ≤ v21 ∧ v21 ≤ ((-5864275639152445 : ℝ) / 562949953421312) := by constructor <;> norm_num [v21]
  let v22 : ℝ := jacobian y 6 4
  have h22 : ((0 : ℝ) / 1) ≤ v22 ∧ v22 ≤ ((0 : ℝ) / 1) := by
    simpa [v22,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 4
  let v23 : ℝ := v21*v22
  have h23 : ((0 : ℝ) / 1) ≤ v23 ∧ v23 ≤ ((0 : ℝ) / 1) := mul_interval h21 h22 (by norm_num) (by norm_num)
  let v24 : ℝ := v20+v23
  have h24 : ((0 : ℝ) / 1) ≤ v24 ∧ v24 ≤ ((0 : ℝ) / 1) := add_interval h20 h23 (by norm_num) (by norm_num)
  let v25 : ℝ := ((-5717564422701105 : ℝ) / 281474976710656)
  have h25 : ((-5717564422701105 : ℝ) / 281474976710656) ≤ v25 ∧ v25 ≤ ((-5717564422701105 : ℝ) / 281474976710656) := by constructor <;> norm_num [v25]
  let v26 : ℝ := jacobian y 4 4
  have h26 : ((0 : ℝ) / 1) ≤ v26 ∧ v26 ≤ ((0 : ℝ) / 1) := by
    simpa [v26,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 4
  let v27 : ℝ := v25*v26
  have h27 : ((0 : ℝ) / 1) ≤ v27 ∧ v27 ≤ ((0 : ℝ) / 1) := mul_interval h25 h26 (by norm_num) (by norm_num)
  let v28 : ℝ := v24+v27
  have h28 : ((0 : ℝ) / 1) ≤ v28 ∧ v28 ≤ ((0 : ℝ) / 1) := add_interval h24 h27 (by norm_num) (by norm_num)
  let v29 : ℝ := ((1759319900783941 : ℝ) / 4503599627370496)
  have h29 : ((1759319900783941 : ℝ) / 4503599627370496) ≤ v29 ∧ v29 ≤ ((1759319900783941 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v29]
  let v30 : ℝ := jacobian y 7 4
  have h30 : ((0 : ℝ) / 1) ≤ v30 ∧ v30 ≤ ((0 : ℝ) / 1) := by
    simpa [v30,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 4
  let v31 : ℝ := v29*v30
  have h31 : ((0 : ℝ) / 1) ≤ v31 ∧ v31 ≤ ((0 : ℝ) / 1) := mul_interval h29 h30 (by norm_num) (by norm_num)
  let v32 : ℝ := v28+v31
  have h32 : ((0 : ℝ) / 1) ≤ v32 ∧ v32 ≤ ((0 : ℝ) / 1) := add_interval h28 h31 (by norm_num) (by norm_num)
  let v33 : ℝ := jacobian y 5 0
  have h33 : ((14471030679094404089679 : ℝ) / 1000000000000000000000000) ≤ v33 ∧ v33 ≤ ((7235515359098802834341 : ℝ) / 500000000000000000000000) := by
    simpa [v33,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 0
  let v34 : ℝ := v18*v33
  have h34 : ((-395347356280731142381789 : ℝ) / 1000000000000000000000000) ≤ v34 ∧ v34 ≤ ((-98836838803108731448583 : ℝ) / 250000000000000000000000) := mul_interval h18 h33 (by norm_num) (by norm_num)
  let v35 : ℝ := v34*v2
  have h35 : ((-724092777410060880332913 : ℝ) / 1000000000000000000000000) ≤ v35 ∧ v35 ≤ ((-72409277528623076353699 : ℝ) / 100000000000000000000000) := mul_interval h34 h2 (by norm_num) (by norm_num)
  let v36 : ℝ := v32+v35
  have h36 : ((-724092777410060880332913 : ℝ) / 1000000000000000000000000) ≤ v36 ∧ v36 ≤ ((-72409277528623076353699 : ℝ) / 100000000000000000000000) := add_interval h32 h35 (by norm_num) (by norm_num)
  let v37 : ℝ := jacobian y 5 1
  have h37 : ((50815194354105460729557 : ℝ) / 1000000000000000000000000) ≤ v37 ∧ v37 ≤ ((50815194420457997287063 : ℝ) / 1000000000000000000000000) := by
    simpa [v37,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 1
  let v38 : ℝ := v18*v37
  have h38 : ((-1388266887427465393754559 : ℝ) / 1000000000000000000000000) ≤ v38 ∧ v38 ≤ ((-694133442807359805361579 : ℝ) / 500000000000000000000000) := mul_interval h18 h37 (by norm_num) (by norm_num)
  let v39 : ℝ := v38*v6
  have h39 : ((1438011563854351736159987 : ℝ) / 500000000000000000000000) ≤ v39 ∧ v39 ≤ ((1438011566062298270996951 : ℝ) / 500000000000000000000000) := mul_interval h38 h6 (by norm_num) (by norm_num)
  let v40 : ℝ := v36+v39
  have h40 : ((2151930350298642591987061 : ℝ) / 1000000000000000000000000) ≤ v40 ∧ v40 ≤ ((134495647302397861153557 : ℝ) / 62500000000000000000000) := add_interval h36 h39 (by norm_num) (by norm_num)
  let v41 : ℝ := jacobian y 5 2
  have h41 : ((48193689742644681369447 : ℝ) / 100000000000000000000000) ≤ v41 ∧ v41 ≤ ((120484224418590333953647 : ℝ) / 250000000000000000000000) := by
    simpa [v41,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 2
  let v42 : ℝ := v18*v41
  have h42 : ((-6583237991130018851098257 : ℝ) / 500000000000000000000000) ≤ v42 ∧ v42 ≤ ((-13166475975487033566386267 : ℝ) / 1000000000000000000000000) := mul_interval h18 h41 (by norm_num) (by norm_num)
  let v43 : ℝ := v42*v10
  have h43 : ((381214161438174240505821 : ℝ) / 500000000000000000000000) ≤ v43 ∧ v43 ≤ ((762428326180424781666507 : ℝ) / 1000000000000000000000000) := mul_interval h42 h10 (by norm_num) (by norm_num)
  let v44 : ℝ := v40+v43
  have h44 : ((2914358673174991072998703 : ℝ) / 1000000000000000000000000) ≤ v44 ∧ v44 ≤ ((2914358683018790560123419 : ℝ) / 1000000000000000000000000) := add_interval h40 h43 (by norm_num) (by norm_num)
  let v45 : ℝ := jacobian y 5 3
  have h45 : ((-46801914920349775960023 : ℝ) / 1000000000000000000000000) ≤ v45 ∧ v45 ≤ ((-11700478724808102304361 : ℝ) / 250000000000000000000000) := by
    simpa [v45,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 5 3
  let v46 : ℝ := v18*v45
  have h46 : ((1278624424521426201739513 : ℝ) / 1000000000000000000000000) ≤ v46 ∧ v46 ≤ ((1278624425098350905713129 : ℝ) / 1000000000000000000000000) := mul_interval h18 h45 (by norm_num) (by norm_num)
  let v47 : ℝ := v46*v14
  have h47 : ((-58597457170862269675227 : ℝ) / 500000000000000000000000) ≤ v47 ∧ v47 ≤ ((-23438982801040802732723 : ℝ) / 200000000000000000000000) := mul_interval h46 h14 (by norm_num) (by norm_num)
  let v48 : ℝ := v44+v47
  have h48 : ((2797163758833266533648249 : ℝ) / 1000000000000000000000000) ≤ v48 ∧ v48 ≤ ((699290942253396636614951 : ℝ) / 250000000000000000000000) := add_interval h44 h47 (by norm_num) (by norm_num)
  let v49 : ℝ := jacobian y 6 0
  have h49 : ((19887945818055601641403 : ℝ) / 1000000000000000000000000) ≤ v49 ∧ v49 ≤ ((1242996619358249185917 : ℝ) / 62500000000000000000000) := by
    simpa [v49,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 0
  let v50 : ℝ := v21*v49
  have h50 : ((-207173650166266302628137 : ℝ) / 1000000000000000000000000) ≤ v50 ∧ v50 ≤ ((-20717364921126916668719 : ℝ) / 100000000000000000000000) := mul_interval h21 h49 (by norm_num) (by norm_num)
  let v51 : ℝ := v50*v2
  have h51 : ((-94861481537611320107173 : ℝ) / 250000000000000000000000) ≤ v51 ∧ v51 ≤ ((-189722962156856161592893 : ℝ) / 500000000000000000000000) := mul_interval h50 h2 (by norm_num) (by norm_num)
  let v52 : ℝ := v48+v51
  have h52 : ((2417717832682821253219557 : ℝ) / 1000000000000000000000000) ≤ v52 ∧ v52 ≤ ((1208858922349937111637009 : ℝ) / 500000000000000000000000) := add_interval h48 h51 (by norm_num) (by norm_num)
  let v53 : ℝ := jacobian y 6 1
  have h53 : ((4317271196776123736059 : ℝ) / 125000000000000000000000) ≤ v53 ∧ v53 ≤ ((6907633943676554482973 : ℝ) / 200000000000000000000000) := by
    simpa [v53,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 1
  let v54 : ℝ := v21*v53
  have h54 : ((-359785707538450967803977 : ℝ) / 1000000000000000000000000) ≤ v54 ∧ v54 ≤ ((-89946426509146505771543 : ℝ) / 250000000000000000000000) := mul_interval h21 h53 (by norm_num) (by norm_num)
  let v55 : ℝ := v54*v6
  have h55 : ((23292351562188135221107 : ℝ) / 31250000000000000000000) ≤ v55 ∧ v55 ≤ ((46584703329534676184483 : ℝ) / 62500000000000000000000) := mul_interval h54 h6 (by norm_num) (by norm_num)
  let v56 : ℝ := v52+v55
  have h56 : ((3163073082672841580294981 : ℝ) / 1000000000000000000000000) ≤ v56 ∧ v56 ≤ ((1581536548986214521112873 : ℝ) / 500000000000000000000000) := add_interval h52 h55 (by norm_num) (by norm_num)
  let v57 : ℝ := jacobian y 6 2
  have h57 : ((958132295892376553383313 : ℝ) / 1000000000000000000000000) ≤ v57 ∧ v57 ≤ ((47906614911072619327067 : ℝ) / 50000000000000000000000) := by
    simpa [v57,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 2
  let v58 : ℝ := v21*v57
  have h58 : ((-4990454179272426614306789 : ℝ) / 500000000000000000000000) ≤ v58 ∧ v58 ≤ ((-1996181666856552562332133 : ℝ) / 200000000000000000000000) := mul_interval h21 h57 (by norm_num) (by norm_num)
  let v59 : ℝ := v58*v10
  have h59 : ((577962335271590295405473 : ℝ) / 1000000000000000000000000) ≤ v59 ∧ v59 ≤ ((577962338883889170935483 : ℝ) / 1000000000000000000000000) := mul_interval h58 h10 (by norm_num) (by norm_num)
  let v60 : ℝ := v56+v59
  have h60 : ((1870517708972215937850227 : ℝ) / 500000000000000000000000) ≤ v60 ∧ v60 ≤ ((3741035436856318213161229 : ℝ) / 1000000000000000000000000) := add_interval h56 h59 (by norm_num) (by norm_num)
  let v61 : ℝ := jacobian y 6 3
  have h61 : ((-145958612457602976659 : ℝ) / 8000000000000000000000) ≤ v61 ∧ v61 ≤ ((-9122413255285573890587 : ℝ) / 500000000000000000000000) := by
    simpa [v61,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 6 3
  let v62 : ℝ := v21*v61
  have h62 : ((38011439914422272496641 : ℝ) / 200000000000000000000000) ≤ v62 ∧ v62 ≤ ((190057200057850143488949 : ℝ) / 1000000000000000000000000) := mul_interval h21 h61 (by norm_num) (by norm_num)
  let v63 : ℝ := v62*v14
  have h63 : ((-3484015609837027988473 : ℝ) / 200000000000000000000000) ≤ v63 ∧ v63 ≤ ((-4355019490625693519149 : ℝ) / 250000000000000000000000) := mul_interval h62 h14 (by norm_num) (by norm_num)
  let v64 : ℝ := v60+v63
  have h64 : ((3723615339895246735758089 : ℝ) / 1000000000000000000000000) ≤ v64 ∧ v64 ≤ ((3723615358893815439084633 : ℝ) / 1000000000000000000000000) := add_interval h60 h63 (by norm_num) (by norm_num)
  let v65 : ℝ := jacobian y 4 0
  have h65 : ((-20920238568579790742713 : ℝ) / 500000000000000000000000) ≤ v65 ∧ v65 ≤ ((-20920238360800254919879 : ℝ) / 500000000000000000000000) := by
    simpa [v65,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 0
  let v66 : ℝ := v25*v65
  have h66 : ((849900136516186113726543 : ℝ) / 1000000000000000000000000) ≤ v66 ∧ v66 ≤ ((424950072478691618301969 : ℝ) / 500000000000000000000000) := mul_interval h25 h65 (by norm_num) (by norm_num)
  let v67 : ℝ := v66*v2
  have h67 : ((1556622399144343931826519 : ℝ) / 1000000000000000000000000) ≤ v67 ∧ v67 ≤ ((1556622414964152655853609 : ℝ) / 1000000000000000000000000) := mul_interval h66 h2 (by norm_num) (by norm_num)
  let v68 : ℝ := v64+v67
  have h68 : ((165007429344987208362019 : ℝ) / 31250000000000000000000) ≤ v68 ∧ v68 ≤ ((2640118886928984047469121 : ℝ) / 500000000000000000000000) := add_interval h64 h67 (by norm_num) (by norm_num)
  let v69 : ℝ := jacobian y 4 1
  have h69 : ((-86771204945417368140751 : ℝ) / 500000000000000000000000) ≤ v69 ∧ v69 ≤ ((-173542409840748627089177 : ℝ) / 1000000000000000000000000) := by
    simpa [v69,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 1
  let v70 : ℝ := v25*v69
  have h70 : ((3525144294994499060684567 : ℝ) / 1000000000000000000000000) ≤ v70 ∧ v70 ≤ ((3525144296011891652154383 : ℝ) / 1000000000000000000000000) := mul_interval h25 h69 (by norm_num) (by norm_num)
  let v71 : ℝ := v70*v6
  have h71 : ((-1460583210796633031183709 : ℝ) / 200000000000000000000000) ≤ v71 ∧ v71 ≤ ((-3651458025099160211935159 : ℝ) / 500000000000000000000000) := mul_interval h70 h6 (by norm_num) (by norm_num)
  let v72 : ℝ := v68+v71
  have h72 : ((-2022678314943574488333937 : ℝ) / 1000000000000000000000000) ≤ v72 ∧ v72 ≤ ((-505669569085088082233019 : ℝ) / 250000000000000000000000) := add_interval h68 h71 (by norm_num) (by norm_num)
  let v73 : ℝ := jacobian y 4 2
  have h73 : ((-175556108140406758762831 : ℝ) / 100000000000000000000000) ≤ v73 ∧ v73 ≤ ((-175556108048133991859057 : ℝ) / 100000000000000000000000) := by
    simpa [v73,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 2
  let v74 : ℝ := v25*v73
  have h74 : ((35660482835591339795487503 : ℝ) / 1000000000000000000000000) ≤ v74 ∧ v74 ≤ ((8915120713583646591868607 : ℝ) / 250000000000000000000000) := mul_interval h25 h73 (by norm_num) (by norm_num)
  let v75 : ℝ := v74*v10
  have h75 : ((-412996800207569492173157 : ℝ) / 200000000000000000000000) ≤ v75 ∧ v75 ≤ ((-2064983992065880067421091 : ℝ) / 1000000000000000000000000) := mul_interval h74 h10 (by norm_num) (by norm_num)
  let v76 : ℝ := v72+v75
  have h76 : ((-2043831157990710974599861 : ℝ) / 500000000000000000000000) ≤ v76 ∧ v76 ≤ ((-4087662268406232396353167 : ℝ) / 1000000000000000000000000) := add_interval h72 h75 (by norm_num) (by norm_num)
  let v77 : ℝ := jacobian y 4 3
  have h77 : ((387002424629700218897 : ℝ) / 3906250000000000000000) ≤ v77 ∧ v77 ≤ ((49536310374971854504441 : ℝ) / 500000000000000000000000) := by
    simpa [v77,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 4 3
  let v78 : ℝ := v25*v77
  have h78 : ((-125778074991619841261413 : ℝ) / 62500000000000000000000) ≤ v78 ∧ v78 ≤ ((-2012449198957110485035723 : ℝ) / 1000000000000000000000000) := mul_interval h25 h77 (by norm_num) (by norm_num)
  let v79 : ℝ := v78*v14
  have h79 : ((9222755575778072964527 : ℝ) / 50000000000000000000000) ≤ v79 ∧ v79 ≤ ((184455112045288010773373 : ℝ) / 1000000000000000000000000) := mul_interval h78 h14 (by norm_num) (by norm_num)
  let v80 : ℝ := v76+v79
  have h80 : ((-1951603602232930244954591 : ℝ) / 500000000000000000000000) ≤ v80 ∧ v80 ≤ ((-1951603578180472192789897 : ℝ) / 500000000000000000000000) := add_interval h76 h79 (by norm_num) (by norm_num)
  let v81 : ℝ := jacobian y 7 0
  have h81 : ((466094240090983921433 : ℝ) / 200000000000000000000000) ≤ v81 ∧ v81 ≤ ((1165235615761669234849 : ℝ) / 500000000000000000000000) := by
    simpa [v81,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 0
  let v82 : ℝ := v29*v81
  have h82 : ((910392730349802956877 : ℝ) / 1000000000000000000000000) ≤ v82 ∧ v82 ≤ ((910392742486602875449 : ℝ) / 1000000000000000000000000) := mul_interval h29 h81 (by norm_num) (by norm_num)
  let v83 : ℝ := v82*v2
  have h83 : ((833708370662022512283 : ℝ) / 500000000000000000000000) ≤ v83 ∧ v83 ≤ ((1667416763938066650043 : ℝ) / 1000000000000000000000000) := mul_interval h82 h2 (by norm_num) (by norm_num)
  let v84 : ℝ := v80+v83
  have h84 : ((-487692473465567055610577 : ℝ) / 125000000000000000000000) ≤ v84 ∧ v84 ≤ ((-3901539739597006318929751 : ℝ) / 1000000000000000000000000) := add_interval h80 h83 (by norm_num) (by norm_num)
  let v85 : ℝ := jacobian y 7 1
  have h85 : ((4241889797437522854441 : ℝ) / 500000000000000000000000) ≤ v85 ∧ v85 ≤ ((1696755923596905032717 : ℝ) / 200000000000000000000000) := by
    simpa [v85,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 1
  let v86 : ℝ := v29*v85
  have h86 : ((662833444803485098459 : ℝ) / 200000000000000000000000) ≤ v86 ∧ v86 ≤ ((165708361652254284489 : ℝ) / 50000000000000000000000) := mul_interval h29 h85 (by norm_num) (by norm_num)
  let v87 : ℝ := v86*v6
  have h87 : ((-137316847535413772417 : ℝ) / 20000000000000000000000) ≤ v87 ∧ v87 ≤ ((-3432921178245816706087 : ℝ) / 500000000000000000000000) := mul_interval h86 h6 (by norm_num) (by norm_num)
  let v88 : ℝ := v84+v87
  have h88 : ((-1954202815050653566752733 : ℝ) / 500000000000000000000000) ≤ v88 ∧ v88 ≤ ((-156336223278139918093677 : ℝ) / 40000000000000000000000) := add_interval h84 h87 (by norm_num) (by norm_num)
  let v89 : ℝ := jacobian y 7 2
  have h89 : ((187498645815716978461599 : ℝ) / 1000000000000000000000000) ≤ v89 ∧ v89 ≤ ((187498646102469604336189 : ℝ) / 1000000000000000000000000) := by
    simpa [v89,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 2
  let v90 : ℝ := v29*v89
  have h90 : ((36622937899369932698821 : ℝ) / 500000000000000000000000) ≤ v90 ∧ v90 ≤ ((36622937955379529803901 : ℝ) / 500000000000000000000000) := mul_interval h29 h89 (by norm_num) (by norm_num)
  let v91 : ℝ := v90*v10
  have h91 : ((-4241433368009936327111 : ℝ) / 1000000000000000000000000) ≤ v91 ∧ v91 ≤ ((-4241433345324342710271 : ℝ) / 1000000000000000000000000) := mul_interval h90 h10 (by norm_num) (by norm_num)
  let v92 : ℝ := v88+v91
  have h92 : ((-3912647063469317069832577 : ℝ) / 1000000000000000000000000) ≤ v92 ∧ v92 ≤ ((-978161753824705573763049 : ℝ) / 250000000000000000000000) := add_interval h88 h91 (by norm_num) (by norm_num)
  let v93 : ℝ := jacobian y 7 3
  have h93 : ((112114839443909922027043 : ℝ) / 1000000000000000000000000) ≤ v93 ∧ v93 ≤ ((7007177488327404136947 : ℝ) / 62500000000000000000000) := by
    simpa [v93,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 7 3
  let v94 : ℝ := v29*v93
  have h94 : ((43797380879088594114039 : ℝ) / 1000000000000000000000000) ≤ v94 ∧ v94 ≤ ((10949345255841465932223 : ℝ) / 250000000000000000000000) := mul_interval h29 h93 (by norm_num) (by norm_num)
  let v95 : ℝ := v94*v14
  have h95 : ((-4014337765392226486011 : ℝ) / 1000000000000000000000000) ≤ v95 ∧ v95 ≤ ((-2007168871226244256599 : ℝ) / 500000000000000000000000) := mul_interval h94 h14 (by norm_num) (by norm_num)
  let v96 : ℝ := v92+v95
  have h96 : ((-979165350308677324079647 : ℝ) / 250000000000000000000000) ≤ v96 ∧ v96 ≤ ((-1958330676520637391782697 : ℝ) / 500000000000000000000000) := add_interval h92 h95 (by norm_num) (by norm_num)
  let v97 : ℝ := v17*v96
  have h97 : ((536440487581261137663259 : ℝ) / 500000000000000000000000) ≤ v97 ∧ v97 ≤ ((1072880988457165061871121 : ℝ) / 1000000000000000000000000) := mul_interval h17 h96 (by norm_num) (by norm_num)
  let v98 : ℝ := v16+v97
  have h98 : ((43291995992167384228189 : ℝ) / 40000000000000000000000) ≤ v98 ∧ v98 ≤ ((541149956583060775085761 : ℝ) / 500000000000000000000000) := add_interval h16 h97 (by norm_num) (by norm_num)
  let v99 : ℝ := jacobian y 9 7
  have h99 : ((-27740261258299526549517 : ℝ) / 125000000000000000000000) ≤ v99 ∧ v99 ≤ ((-887688360263508957861 : ℝ) / 4000000000000000000000) := by
    simpa [v99,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 7
  let v100 : ℝ := ((-8569877571857449 : ℝ) / 144115188075855872)
  have h100 : ((-8569877571857449 : ℝ) / 144115188075855872) ≤ v100 ∧ v100 ≤ ((-8569877571857449 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v100]
  let v101 : ℝ := v100*v30
  have h101 : ((0 : ℝ) / 1) ≤ v101 ∧ v101 ≤ ((0 : ℝ) / 1) := mul_interval h100 h30 (by norm_num) (by norm_num)
  let v102 : ℝ := ((372160374982343 : ℝ) / 281474976710656)
  have h102 : ((372160374982343 : ℝ) / 281474976710656) ≤ v102 ∧ v102 ≤ ((372160374982343 : ℝ) / 281474976710656) := by constructor <;> norm_num [v102]
  let v103 : ℝ := v102*v22
  have h103 : ((0 : ℝ) / 1) ≤ v103 ∧ v103 ≤ ((0 : ℝ) / 1) := mul_interval h102 h22 (by norm_num) (by norm_num)
  let v104 : ℝ := v101+v103
  have h104 : ((0 : ℝ) / 1) ≤ v104 ∧ v104 ≤ ((0 : ℝ) / 1) := add_interval h101 h103 (by norm_num) (by norm_num)
  let v105 : ℝ := ((2624911170949731 : ℝ) / 1125899906842624)
  have h105 : ((2624911170949731 : ℝ) / 1125899906842624) ≤ v105 ∧ v105 ≤ ((2624911170949731 : ℝ) / 1125899906842624) := by constructor <;> norm_num [v105]
  let v106 : ℝ := v105*v26
  have h106 : ((0 : ℝ) / 1) ≤ v106 ∧ v106 ≤ ((0 : ℝ) / 1) := mul_interval h105 h26 (by norm_num) (by norm_num)
  let v107 : ℝ := v104+v106
  have h107 : ((0 : ℝ) / 1) ≤ v107 ∧ v107 ≤ ((0 : ℝ) / 1) := add_interval h104 h106 (by norm_num) (by norm_num)
  let v108 : ℝ := ((5402920345206155 : ℝ) / 2251799813685248)
  have h108 : ((5402920345206155 : ℝ) / 2251799813685248) ≤ v108 ∧ v108 ≤ ((5402920345206155 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v108]
  let v109 : ℝ := v108*v19
  have h109 : ((0 : ℝ) / 1) ≤ v109 ∧ v109 ≤ ((0 : ℝ) / 1) := mul_interval h108 h19 (by norm_num) (by norm_num)
  let v110 : ℝ := v107+v109
  have h110 : ((0 : ℝ) / 1) ≤ v110 ∧ v110 ≤ ((0 : ℝ) / 1) := add_interval h107 h109 (by norm_num) (by norm_num)
  let v111 : ℝ := v100*v81
  have h111 : ((-138582569995180279337 : ℝ) / 1000000000000000000000000) ≤ v111 ∧ v111 ≤ ((-270669078413441623 : ℝ) / 1953125000000000000000) := mul_interval h100 h81 (by norm_num) (by norm_num)
  let v112 : ℝ := v111*v2
  have h112 : ((-63454729375488337061 : ℝ) / 250000000000000000000000) ≤ v112 ∧ v112 ≤ ((-63454728514895680581 : ℝ) / 250000000000000000000000) := mul_interval h111 h2 (by norm_num) (by norm_num)
  let v113 : ℝ := v110+v112
  have h113 : ((-63454729375488337061 : ℝ) / 250000000000000000000000) ≤ v113 ∧ v113 ≤ ((-63454728514895680581 : ℝ) / 250000000000000000000000) := add_interval h110 h112 (by norm_num) (by norm_num)
  let v114 : ℝ := v100*v85
  have h114 : ((-504491952884787283983 : ℝ) / 1000000000000000000000000) ≤ v114 ∧ v114 ≤ ((-504491951510571198083 : ℝ) / 1000000000000000000000000) := mul_interval h100 h85 (by norm_num) (by norm_num)
  let v115 : ℝ := v114*v6
  have h115 : ((522569015843388681157 : ℝ) / 500000000000000000000000) ≤ v115 ∧ v115 ≤ ((1045138034773712765841 : ℝ) / 1000000000000000000000000) := mul_interval h114 h6 (by norm_num) (by norm_num)
  let v116 : ℝ := v113+v115
  have h116 : ((79131911418482401407 : ℝ) / 100000000000000000000000) ≤ v116 ∧ v116 ≤ ((791319120714130043517 : ℝ) / 1000000000000000000000000) := add_interval h113 h115 (by norm_num) (by norm_num)
  let v117 : ℝ := v100*v89
  have h117 : ((-5574847673728259277559 : ℝ) / 500000000000000000000000) ≤ v117 ∧ v117 ≤ ((-11149695330404638528007 : ℝ) / 1000000000000000000000000) := mul_interval h100 h89 (by norm_num) (by norm_num)
  let v118 : ℝ := v117*v10
  have h118 : ((40352689698297444727 : ℝ) / 62500000000000000000000) ≤ v118 ∧ v118 ≤ ((645643038626024633437 : ℝ) / 1000000000000000000000000) := mul_interval h117 h10 (by norm_num) (by norm_num)
  let v119 : ℝ := v116+v118
  have h119 : ((718481074678791564851 : ℝ) / 500000000000000000000000) ≤ v119 ∧ v119 ≤ ((718481079670077338477 : ℝ) / 500000000000000000000000) := add_interval h116 h118 (by norm_num) (by norm_num)
  let v120 : ℝ := v100*v93
  have h120 : ((-3333480891278907806589 : ℝ) / 500000000000000000000000) ≤ v120 ∧ v120 ≤ ((-416685110037219980741 : ℝ) / 62500000000000000000000) := mul_interval h100 h93 (by norm_num) (by norm_num)
  let v121 : ℝ := v120*v14
  have h121 : ((305536948624072872373 : ℝ) / 500000000000000000000000) ≤ v121 ∧ v121 ≤ ((9548029699064028727 : ℝ) / 15625000000000000000000) := mul_interval h120 h14 (by norm_num) (by norm_num)
  let v122 : ℝ := v119+v121
  have h122 : ((128002252912858054653 : ℝ) / 62500000000000000000000) ≤ v122 ∧ v122 ≤ ((1024018030040126257741 : ℝ) / 500000000000000000000000) := add_interval h119 h121 (by norm_num) (by norm_num)
  let v123 : ℝ := v102*v49
  have h123 : ((6573857345838345816707 : ℝ) / 250000000000000000000000) ≤ v123 ∧ v123 ≤ ((5259085900913199623873 : ℝ) / 200000000000000000000000) := mul_interval h102 h49 (by norm_num) (by norm_num)
  let v124 : ℝ := v123*v2
  have h124 : ((12040254088271546037091 : ℝ) / 250000000000000000000000) ≤ v124 ∧ v124 ≤ ((12040254146553187979893 : ℝ) / 250000000000000000000000) := mul_interval h123 h2 (by norm_num) (by norm_num)
  let v125 : ℝ := v122+v124
  have h125 : ((12552263099922978255703 : ℝ) / 250000000000000000000000) ≤ v125 ∧ v125 ≤ ((25104526323146502217527 : ℝ) / 500000000000000000000000) := add_interval h122 h124 (by norm_num) (by norm_num)
  let v126 : ℝ := v102*v53
  have h126 : ((22832825656744701961097 : ℝ) / 500000000000000000000000) ≤ v126 ∧ v126 ≤ ((11416412876028247070027 : ℝ) / 250000000000000000000000) := mul_interval h102 h53 (by norm_num) (by norm_num)
  let v127 : ℝ := v126*v6
  have h127 : ((-47301952981368428255059 : ℝ) / 500000000000000000000000) ≤ v127 ∧ v127 ≤ ((-4730195277305126471093 : ℝ) / 50000000000000000000000) := mul_interval h126 h6 (by norm_num) (by norm_num)
  let v128 : ℝ := v125+v127
  have h128 : ((-22197426781522471743653 : ℝ) / 500000000000000000000000) ≤ v128 ∧ v128 ≤ ((-22197426449904762493403 : ℝ) / 500000000000000000000000) := add_interval h125 h127 (by norm_num) (by norm_num)
  let v129 : ℝ := v102*v57
  have h129 : ((15835283063569963770679 : ℝ) / 12500000000000000000000) ≤ v129 ∧ v129 ≤ ((633411324082526425680893 : ℝ) / 500000000000000000000000) := mul_interval h102 h57 (by norm_num) (by norm_num)
  let v130 : ℝ := v129*v10
  have h130 : ((-73357629825117670379263 : ℝ) / 1000000000000000000000000) ≤ v130 ∧ v130 ≤ ((-73357629366628135852593 : ℝ) / 1000000000000000000000000) := mul_interval h129 h10 (by norm_num) (by norm_num)
  let v131 : ℝ := v128+v130
  have h131 : ((-117752483388162613866569 : ℝ) / 1000000000000000000000000) ≤ v131 ∧ v131 ≤ ((-117752482266437660839399 : ℝ) / 1000000000000000000000000) := add_interval h128 h130 (by norm_num) (by norm_num)
  let v132 : ℝ := v102*v61
  have h132 : ((-4824586236662398535057 : ℝ) / 200000000000000000000000) ≤ v132 ∧ v132 ≤ ((-24122931121659799631817 : ℝ) / 1000000000000000000000000) := mul_interval h102 h61 (by norm_num) (by norm_num)
  let v133 : ℝ := v132*v14
  have h133 : ((276379520066508563657 : ℝ) / 125000000000000000000000) ≤ v133 ∧ v133 ≤ ((2211036171534191796089 : ℝ) / 1000000000000000000000000) := mul_interval h132 h14 (by norm_num) (by norm_num)
  let v134 : ℝ := v131+v133
  have h134 : ((-115541447227630545357313 : ℝ) / 1000000000000000000000000) ≤ v134 ∧ v134 ≤ ((-11554144609490346904331 : ℝ) / 100000000000000000000000) := add_interval h131 h133 (by norm_num) (by norm_num)
  let v135 : ℝ := v105*v65
  have h135 : ((-12193305902208018765617 : ℝ) / 125000000000000000000000) ≤ v135 ∧ v135 ≤ ((-97546446248834112283317 : ℝ) / 1000000000000000000000000) := mul_interval h105 h65 (by norm_num) (by norm_num)
  let v136 : ℝ := v135*v2
  have h136 : ((-178659795671346215858389 : ℝ) / 1000000000000000000000000) ≤ v136 ∧ v136 ≤ ((-178659793855643340823307 : ℝ) / 1000000000000000000000000) := mul_interval h135 h2 (by norm_num) (by norm_num)
  let v137 : ℝ := v134+v136
  have h137 : ((-147100621449488380607851 : ℝ) / 500000000000000000000000) ≤ v137 ∧ v137 ≤ ((-294201239950546809866617 : ℝ) / 1000000000000000000000000) := add_interval h134 h136 (by norm_num) (by norm_num)
  let v138 : ℝ := v105*v69
  have h138 : ((-404594944530591137501353 : ℝ) / 1000000000000000000000000) ≤ v138 ∧ v138 ≤ ((-404594944413820910654963 : ℝ) / 1000000000000000000000000) := mul_interval h105 h69 (by norm_num) (by norm_num)
  let v139 : ℝ := v138*v6
  have h139 : ((52386559707363000577789 : ℝ) / 62500000000000000000000) ≤ v139 ∧ v139 ≤ ((419092477876104907029683 : ℝ) / 500000000000000000000000) := mul_interval h138 h6 (by norm_num) (by norm_num)
  let v140 : ℝ := v137+v139
  have h140 : ((271991856209415624014461 : ℝ) / 500000000000000000000000) ≤ v140 ∧ v140 ≤ ((543983715801663004192749 : ℝ) / 1000000000000000000000000) := add_interval h137 h139 (by norm_num) (by norm_num)
  let v141 : ℝ := v105*v73
  have h141 : ((-4092896593965391250339067 : ℝ) / 1000000000000000000000000) ≤ v141 ∧ v141 ≤ ((-2046448295907076846145989 : ℝ) / 500000000000000000000000) := mul_interval h105 h73 (by norm_num) (by norm_num)
  let v142 : ℝ := v141*v10
  have h142 : ((59251623023748344505991 : ℝ) / 250000000000000000000000) ≤ v142 ∧ v142 ≤ ((237006493124742047883459 : ℝ) / 1000000000000000000000000) := mul_interval h141 h10 (by norm_num) (by norm_num)
  let v143 : ℝ := v140+v142
  have h143 : ((390495102256912313026443 : ℝ) / 500000000000000000000000) ≤ v143 ∧ v143 ≤ ((48811888057900315754763 : ℝ) / 62500000000000000000000) := add_interval h140 h142 (by norm_num) (by norm_num)
  let v144 : ℝ := v105*v77
  have h144 : ((230976863257440395063933 : ℝ) / 1000000000000000000000000) ≤ v144 ∧ v144 ≤ ((230976863361747815362887 : ℝ) / 1000000000000000000000000) := mul_interval h105 h77 (by norm_num) (by norm_num)
  let v145 : ℝ := v144*v14
  have h145 : ((-21170652761867970315349 : ℝ) / 1000000000000000000000000) ≤ v145 ∧ v145 ≤ ((-21170652701069130121473 : ℝ) / 1000000000000000000000000) := mul_interval h144 h14 (by norm_num) (by norm_num)
  let v146 : ℝ := v143+v145
  have h146 : ((759819551751956655737537 : ℝ) / 1000000000000000000000000) ≤ v146 ∧ v146 ≤ ((151963911245067184390947 : ℝ) / 200000000000000000000000) := add_interval h143 h145 (by norm_num) (by norm_num)
  let v147 : ℝ := v108*v33
  have h147 : ((217009260761684689593 : ℝ) / 6250000000000000000000) ≤ v147 ∧ v147 ≤ ((8680370453923234112561 : ℝ) / 250000000000000000000000) := mul_interval h108 h33 (by norm_num) (by norm_num)
  let v148 : ℝ := v147*v2
  have h148 : ((635936316015802071171 : ℝ) / 10000000000000000000000) ≤ v148 ∧ v148 ≤ ((15898407947026531418909 : ℝ) / 250000000000000000000000) := mul_interval h147 h2 (by norm_num) (by norm_num)
  let v149 : ℝ := v146+v148
  have h149 : ((823413183353536862854637 : ℝ) / 1000000000000000000000000) ≤ v149 ∧ v149 ≤ ((823413188013442047630371 : ℝ) / 1000000000000000000000000) := add_interval h146 h148 (by norm_num) (by norm_num)
  let v150 : ℝ := v108*v37
  have h150 : ((3048122281483781997251 : ℝ) / 25000000000000000000000) ≤ v150 ∧ v150 ≤ ((121924891418556137952391 : ℝ) / 1000000000000000000000000) := mul_interval h108 h37 (by norm_num) (by norm_num)
  let v151 : ℝ := v150*v6
  have h151 : ((-252587460867367621819723 : ℝ) / 1000000000000000000000000) ≤ v151 ∧ v151 ≤ ((-7893358139985646662939 : ℝ) / 31250000000000000000000) := mul_interval h150 h6 (by norm_num) (by norm_num)
  let v152 : ℝ := v149+v151
  have h152 : ((285412861243084620517457 : ℝ) / 500000000000000000000000) ≤ v152 ∧ v152 ≤ ((570825727533901354416323 : ℝ) / 1000000000000000000000000) := add_interval h149 h151 (by norm_num) (by norm_num)
  let v153 : ℝ := v108*v41
  have h153 : ((144543636405085680999251 : ℝ) / 125000000000000000000000) ≤ v153 ∧ v153 ≤ ((578174545917763126844163 : ℝ) / 500000000000000000000000) := mul_interval h108 h41 (by norm_num) (by norm_num)
  let v154 : ℝ := v153*v10
  have h154 : ((-3348023053990645015237 : ℝ) / 50000000000000000000000) ≤ v154 ∧ v154 ≤ ((-16740115197407890341869 : ℝ) / 250000000000000000000000) := mul_interval h153 h10 (by norm_num) (by norm_num)
  let v155 : ℝ := v152+v154
  have h155 : ((251932630703178170365087 : ℝ) / 500000000000000000000000) ≤ v155 ∧ v155 ≤ ((503865266744269793048847 : ℝ) / 1000000000000000000000000) := add_interval h152 h154 (by norm_num) (by norm_num)
  let v156 : ℝ := v108*v45
  have h156 : ((-112295514361877705332041 : ℝ) / 1000000000000000000000000) ≤ v156 ∧ v156 ≤ ((-112295514311209146911683 : ℝ) / 1000000000000000000000000) := mul_interval h108 h45 (by norm_num) (by norm_num)
  let v157 : ℝ := v156*v14
  have h157 : ((321646032507701495063 : ℝ) / 31250000000000000000000) ≤ v157 ∧ v157 ≤ ((1286584133725181042971 : ℝ) / 125000000000000000000000) := mul_interval h156 h14 (by norm_num) (by norm_num)
  let v158 : ℝ := v155+v157
  have h158 : ((51415793444660278857219 : ℝ) / 100000000000000000000000) ≤ v158 ∧ v158 ≤ ((102831587962814248278523 : ℝ) / 200000000000000000000000) := add_interval h155 h157 (by norm_num) (by norm_num)
  let v159 : ℝ := v99*v158
  have h159 : ((-114103004627771041075799 : ℝ) / 1000000000000000000000000) ≤ v159 ∧ v159 ≤ ((-22820600687268877922053 : ℝ) / 200000000000000000000000) := mul_interval h99 h158 (by norm_num) (by norm_num)
  let v160 : ℝ := v98+v159
  have h160 : ((484098447588206782314463 : ℝ) / 500000000000000000000000) ≤ v160 ∧ v160 ≤ ((968196909729777160561257 : ℝ) / 1000000000000000000000000) := add_interval h98 h159 (by norm_num) (by norm_num)
  let v161 : ℝ := jacobian y 9 8
  have h161 : ((-770981222685690422294011 : ℝ) / 1000000000000000000000000) ≤ v161 ∧ v161 ≤ ((-385490611161663940667689 : ℝ) / 500000000000000000000000) := by
    simpa [v161,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 8
  let v162 : ℝ := ((-5676625074002731 : ℝ) / 18014398509481984)
  have h162 : ((-5676625074002731 : ℝ) / 18014398509481984) ≤ v162 ∧ v162 ≤ ((-5676625074002731 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v162]
  let v163 : ℝ := v162*v19
  have h163 : ((0 : ℝ) / 1) ≤ v163 ∧ v163 ≤ ((0 : ℝ) / 1) := mul_interval h162 h19 (by norm_num) (by norm_num)
  let v164 : ℝ := ((-1906405801350491 : ℝ) / 9007199254740992)
  have h164 : ((-1906405801350491 : ℝ) / 9007199254740992) ≤ v164 ∧ v164 ≤ ((-1906405801350491 : ℝ) / 9007199254740992) := by constructor <;> norm_num [v164]
  let v165 : ℝ := v164*v26
  have h165 : ((0 : ℝ) / 1) ≤ v165 ∧ v165 ≤ ((0 : ℝ) / 1) := mul_interval h164 h26 (by norm_num) (by norm_num)
  let v166 : ℝ := v163+v165
  have h166 : ((0 : ℝ) / 1) ≤ v166 ∧ v166 ≤ ((0 : ℝ) / 1) := add_interval h163 h165 (by norm_num) (by norm_num)
  let v167 : ℝ := ((-901757038800969 : ℝ) / 4503599627370496)
  have h167 : ((-901757038800969 : ℝ) / 4503599627370496) ≤ v167 ∧ v167 ≤ ((-901757038800969 : ℝ) / 4503599627370496) := by constructor <;> norm_num [v167]
  let v168 : ℝ := v167*v22
  have h168 : ((0 : ℝ) / 1) ≤ v168 ∧ v168 ≤ ((0 : ℝ) / 1) := mul_interval h167 h22 (by norm_num) (by norm_num)
  let v169 : ℝ := v166+v168
  have h169 : ((0 : ℝ) / 1) ≤ v169 ∧ v169 ≤ ((0 : ℝ) / 1) := add_interval h166 h168 (by norm_num) (by norm_num)
  let v170 : ℝ := ((5941539868098331 : ℝ) / 2305843009213693952)
  have h170 : ((5941539868098331 : ℝ) / 2305843009213693952) ≤ v170 ∧ v170 ≤ ((5941539868098331 : ℝ) / 2305843009213693952) := by constructor <;> norm_num [v170]
  let v171 : ℝ := v170*v30
  have h171 : ((0 : ℝ) / 1) ≤ v171 ∧ v171 ≤ ((0 : ℝ) / 1) := mul_interval h170 h30 (by norm_num) (by norm_num)
  let v172 : ℝ := v169+v171
  have h172 : ((0 : ℝ) / 1) ≤ v172 ∧ v172 ≤ ((0 : ℝ) / 1) := add_interval h169 h171 (by norm_num) (by norm_num)
  let v173 : ℝ := v162*v33
  have h173 : ((-4560053214008001721297 : ℝ) / 1000000000000000000000000) ≤ v173 ∧ v173 ≤ ((-2280026600842978763787 : ℝ) / 500000000000000000000000) := mul_interval h162 h33 (by norm_num) (by norm_num)
  let v174 : ℝ := v173*v2
  have h174 : ((-4175950015110370771461 : ℝ) / 500000000000000000000000) ≤ v174 ∧ v174 ≤ ((-8351900005723857483259 : ℝ) / 1000000000000000000000000) := mul_interval h173 h2 (by norm_num) (by norm_num)
  let v175 : ℝ := v172+v174
  have h175 : ((-4175950015110370771461 : ℝ) / 500000000000000000000000) ≤ v175 ∧ v175 ≤ ((-8351900005723857483259 : ℝ) / 1000000000000000000000000) := add_interval h172 h174 (by norm_num) (by norm_num)
  let v176 : ℝ := v162*v37
  have h176 : ((-3202536089513769360199 : ℝ) / 200000000000000000000000) ≤ v176 ∧ v176 ≤ ((-3202536085332020271571 : ℝ) / 200000000000000000000000) := mul_interval h162 h37 (by norm_num) (by norm_num)
  let v177 : ℝ := v176*v6
  have h177 : ((16586450242703472906051 : ℝ) / 500000000000000000000000) ≤ v177 ∧ v177 ≤ ((33172900536341161167737 : ℝ) / 1000000000000000000000000) := mul_interval h176 h6 (by norm_num) (by norm_num)
  let v178 : ℝ := v175+v177
  have h178 : ((1241050022759310213459 : ℝ) / 50000000000000000000000) ≤ v178 ∧ v178 ≤ ((12410500265308651842239 : ℝ) / 500000000000000000000000) := add_interval h175 h177 (by norm_num) (by norm_num)
  let v179 : ℝ := v162*v41
  have h179 : ((-4745813251802052961327 : ℝ) / 31250000000000000000000) ≤ v179 ∧ v179 ≤ ((-151866023979543863953861 : ℝ) / 1000000000000000000000000) := mul_interval h162 h41 (by norm_num) (by norm_num)
  let v180 : ℝ := v179*v10
  have h180 : ((8794073537990862505881 : ℝ) / 1000000000000000000000000) ≤ v180 ∧ v180 ≤ ((2198518394025263689439 : ℝ) / 250000000000000000000000) := mul_interval h179 h10 (by norm_num) (by norm_num)
  let v181 : ℝ := v178+v180
  have h181 : ((33615073993177066775061 : ℝ) / 1000000000000000000000000) ≤ v181 ∧ v181 ≤ ((16807537053359179221117 : ℝ) / 500000000000000000000000) := add_interval h178 h180 (by norm_num) (by norm_num)
  let v182 : ℝ := v162*v45
  have h182 : ((14748031886187267988461 : ℝ) / 1000000000000000000000000) ≤ v182 ∧ v182 ≤ ((737401594642084398919 : ℝ) / 50000000000000000000000) := mul_interval h162 h45 (by norm_num) (by norm_num)
  let v183 : ℝ := v182*v14
  have h183 : ((-675880383818593308721 : ℝ) / 500000000000000000000000) ≤ v183 ∧ v183 ≤ ((-675880381877829724041 : ℝ) / 500000000000000000000000) := mul_interval h182 h14 (by norm_num) (by norm_num)
  let v184 : ℝ := v181+v183
  have h184 : ((32263313225539880157619 : ℝ) / 1000000000000000000000000) ≤ v184 ∧ v184 ≤ ((4032914167870337374269 : ℝ) / 125000000000000000000000) := add_interval h181 h183 (by norm_num) (by norm_num)
  let v185 : ℝ := v164*v65
  have h185 : ((8855685912726383667259 : ℝ) / 1000000000000000000000000) ≤ v185 ∧ v185 ≤ ((1771137200136188238427 : ℝ) / 200000000000000000000000) := mul_interval h164 h65 (by norm_num) (by norm_num)
  let v186 : ℝ := v185*v2
  have h186 : ((16219504456185461213501 : ℝ) / 1000000000000000000000000) ≤ v186 ∧ v186 ≤ ((16219504621022777081761 : ℝ) / 1000000000000000000000000) := mul_interval h185 h2 (by norm_num) (by norm_num)
  let v187 : ℝ := v184+v186
  have h187 : ((606035221021566767139 : ℝ) / 12500000000000000000000) ≤ v187 ∧ v187 ≤ ((48482817963985476075913 : ℝ) / 1000000000000000000000000) := add_interval h184 h186 (by norm_num) (by norm_num)
  let v188 : ℝ := v164*v69
  have h188 : ((36730869113016120412261 : ℝ) / 1000000000000000000000000) ≤ v188 ∧ v188 ≤ ((18365434561808511902093 : ℝ) / 500000000000000000000000) := mul_interval h164 h69 (by norm_num) (by norm_num)
  let v189 : ℝ := v188*v6
  have h189 : ((-95117543877242334393 : ℝ) / 1250000000000000000000) ≤ v189 ∧ v189 ≤ ((-76094035062357003422521 : ℝ) / 1000000000000000000000000) := mul_interval h188 h6 (by norm_num) (by norm_num)
  let v190 : ℝ := v187+v189
  have h190 : ((-345140217750856576791 : ℝ) / 12500000000000000000000) ≤ v190 ∧ v190 ≤ ((-1725701068648220459163 : ℝ) / 62500000000000000000000) := add_interval h187 h189 (by norm_num) (by norm_num)
  let v191 : ℝ := v164*v73
  have h191 : ((725724131062167410647 : ℝ) / 1953125000000000000000) ≤ v191 ∧ v191 ≤ ((371570755299128311692001 : ℝ) / 1000000000000000000000000) := mul_interval h164 h73 (by norm_num) (by norm_num)
  let v192 : ℝ := v191*v10
  have h192 : ((-21516468750029388634319 : ℝ) / 1000000000000000000000000) ≤ v192 ∧ v192 ≤ ((-10758234328272187849721 : ℝ) / 500000000000000000000000) := mul_interval h191 h10 (by norm_num) (by norm_num)
  let v193 : ℝ := v190+v192
  have h193 : ((-49127686170097914777599 : ℝ) / 1000000000000000000000000) ≤ v193 ∧ v193 ≤ ((-982553715098318060921 : ℝ) / 20000000000000000000000) := add_interval h190 h192 (by norm_num) (by norm_num)
  let v194 : ℝ := v164*v77
  have h194 : ((-20969073028252984602611 : ℝ) / 1000000000000000000000000) ≤ v194 ∧ v194 ≤ ((-10484536509391754194199 : ℝ) / 500000000000000000000000) := mul_interval h164 h77 (by norm_num) (by norm_num)
  let v195 : ℝ := v194*v14
  have h195 : ((240245362719097329803 : ℝ) / 125000000000000000000000) ≤ v195 ∧ v195 ≤ ((1921962907272358831449 : ℝ) / 1000000000000000000000000) := mul_interval h194 h14 (by norm_num) (by norm_num)
  let v196 : ℝ := v193+v195
  have h196 : ((-1888228930733805445567 : ℝ) / 40000000000000000000000) ≤ v196 ∧ v196 ≤ ((-47205722847643544214601 : ℝ) / 1000000000000000000000000) := add_interval h193 h195 (by norm_num) (by norm_num)
  let v197 : ℝ := v167*v49
  have h197 : ((-398216908590182330119 : ℝ) / 100000000000000000000000) ≤ v197 ∧ v197 ≤ ((-3982169067545434499733 : ℝ) / 1000000000000000000000000) := mul_interval h167 h49 (by norm_num) (by norm_num)
  let v198 : ℝ := v197*v2
  have h198 : ((-729348464766165343329 : ℝ) / 100000000000000000000000) ≤ v198 ∧ v198 ≤ ((-7293484612357061389271 : ℝ) / 1000000000000000000000000) := mul_interval h197 h2 (by norm_num) (by norm_num)
  let v199 : ℝ := v196+v198
  have h199 : ((-10899841583201357914493 : ℝ) / 200000000000000000000000) ≤ v199 ∧ v199 ≤ ((-1703100233125018925121 : ℝ) / 31250000000000000000000) := add_interval h196 h198 (by norm_num) (by norm_num)
  let v200 : ℝ := v167*v53
  have h200 : ((-1383117516111826817503 : ℝ) / 200000000000000000000000) ≤ v200 ∧ v200 ≤ ((-864448443961397057791 : ℝ) / 125000000000000000000000) := mul_interval h167 h53 (by norm_num) (by norm_num)
  let v201 : ℝ := v200*v6
  have h201 : ((14326776750531855948941 : ℝ) / 1000000000000000000000000) ≤ v201 ∧ v201 ≤ ((716338840681339399263 : ℝ) / 50000000000000000000000) := mul_interval h200 h6 (by norm_num) (by norm_num)
  let v202 : ℝ := v199+v201
  have h202 : ((-10043107791368733405881 : ℝ) / 250000000000000000000000) ≤ v202 ∧ v202 ≤ ((-10043107661593454404653 : ℝ) / 250000000000000000000000) := add_interval h199 h201 (by norm_num) (by norm_num)
  let v203 : ℝ := v167*v57
  have h203 : ((-191847103541974171241267 : ℝ) / 1000000000000000000000000) ≤ v203 ∧ v203 ≤ ((-47961775768905663101427 : ℝ) / 250000000000000000000000) := mul_interval h167 h57 (by norm_num) (by norm_num)
  let v204 : ℝ := v203*v10
  have h204 : ((2777312344604463496183 : ℝ) / 250000000000000000000000) ≤ v204 ∧ v204 ≤ ((11109249447851321511269 : ℝ) / 1000000000000000000000000) := mul_interval h203 h10 (by norm_num) (by norm_num)
  let v205 : ℝ := v202+v204
  have h205 : ((-3632897723382134954849 : ℝ) / 125000000000000000000000) ≤ v205 ∧ v205 ≤ ((-29063181198522496107343 : ℝ) / 1000000000000000000000000) := add_interval h202 h204 (by norm_num) (by norm_num)
  let v206 : ℝ := v167*v61
  have h206 : ((3653166819630472152259 : ℝ) / 1000000000000000000000000) ≤ v206 ∧ v206 ≤ ((3653166828967055042953 : ℝ) / 1000000000000000000000000) := mul_interval h167 h61 (by norm_num) (by norm_num)
  let v207 : ℝ := v206*v14
  have h207 : ((-334838413214178835341 : ℝ) / 1000000000000000000000000) ≤ v207 ∧ v207 ≤ ((-334838411548021786089 : ℝ) / 1000000000000000000000000) := mul_interval h206 h14 (by norm_num) (by norm_num)
  let v208 : ℝ := v205+v207
  have h208 : ((-29398020200271258474133 : ℝ) / 1000000000000000000000000) ≤ v208 ∧ v208 ≤ ((-3674752451258814736679 : ℝ) / 125000000000000000000000) := add_interval h205 h207 (by norm_num) (by norm_num)
  let v209 : ℝ := v170*v81
  have h209 : ((1501250030209087181 : ℝ) / 250000000000000000000000) ≤ v209 ∧ v209 ≤ ((6005000200891343177 : ℝ) / 1000000000000000000000000) := mul_interval h170 h81 (by norm_num) (by norm_num)
  let v210 : ℝ := v209*v2
  have h210 : ((2199674360160626111 : ℝ) / 200000000000000000000000) ≤ v210 ∧ v210 ≤ ((1099837194996645103 : ℝ) / 100000000000000000000000) := mul_interval h209 h2 (by norm_num) (by norm_num)
  let v211 : ℝ := v208+v210
  have h211 : ((-14693510914235227671789 : ℝ) / 500000000000000000000000) ≤ v211 ∧ v211 ≤ ((-14693510619060275721201 : ℝ) / 500000000000000000000000) := add_interval h208 h210 (by norm_num) (by norm_num)
  let v212 : ℝ := v170*v85
  have h212 : ((21860427832117754497 : ℝ) / 1000000000000000000000000) ≤ v212 ∧ v212 ≤ ((10930213945832346857 : ℝ) / 500000000000000000000000) := mul_interval h170 h85 (by norm_num) (by norm_num)
  let v213 : ℝ := v212*v6
  have h213 : ((-9057494184143939211 : ℝ) / 200000000000000000000000) ≤ v213 ∧ v213 ≤ ((-45287470786957941461 : ℝ) / 1000000000000000000000000) := mul_interval h212 h6 (by norm_num) (by norm_num)
  let v214 : ℝ := v211+v213
  have h214 : ((-29432309299391175039633 : ℝ) / 1000000000000000000000000) ≤ v214 ∧ v214 ≤ ((-29432308708907509383863 : ℝ) / 1000000000000000000000000) := add_interval h211 h213 (by norm_num) (by norm_num)
  let v215 : ℝ := v170*v89
  have h215 : ((483133793097398144803 : ℝ) / 1000000000000000000000000) ≤ v215 ∧ v215 ≤ ((483133793836282861633 : ℝ) / 1000000000000000000000000) := mul_interval h170 h89 (by norm_num) (by norm_num)
  let v216 : ℝ := v215*v10
  have h216 : ((-27976725909962668249 : ℝ) / 1000000000000000000000000) ≤ v216 ∧ v216 ≤ ((-13988362880163627507 : ℝ) / 500000000000000000000000) := mul_interval h215 h10 (by norm_num) (by norm_num)
  let v217 : ℝ := v214+v216
  have h217 : ((-14730143012650568853941 : ℝ) / 500000000000000000000000) ≤ v217 ∧ v217 ≤ ((-29460285434667836638877 : ℝ) / 1000000000000000000000000) := add_interval h214 h216 (by norm_num) (by norm_num)
  let v218 : ℝ := v170*v93
  have h218 : ((288889913883855433113 : ℝ) / 1000000000000000000000000) ≤ v218 ∧ v218 ≤ ((9027809838609880479 : ℝ) / 31250000000000000000000) := mul_interval h170 h93 (by norm_num) (by norm_num)
  let v219 : ℝ := v218*v14
  have h219 : ((-413731108197734187 : ℝ) / 15625000000000000000000) ≤ v219 ∧ v219 ≤ ((-3309848846667903087 : ℝ) / 125000000000000000000000) := mul_interval h218 h14 (by norm_num) (by norm_num)
  let v220 : ℝ := v217+v219
  have h220 : ((-589735296324515853917 : ℝ) / 20000000000000000000000) ≤ v220 ∧ v220 ≤ ((-29486764225441179863573 : ℝ) / 1000000000000000000000000) := add_interval h217 h219 (by norm_num) (by norm_num)
  let v221 : ℝ := v161*v220
  have h221 : ((22733741524890417344787 : ℝ) / 1000000000000000000000000) ≤ v221 ∧ v221 ≤ ((710429437220598728109 : ℝ) / 31250000000000000000000) := mul_interval h161 h220 (by norm_num) (by norm_num)
  let v222 : ℝ := v160+v221
  have h222 : ((990930636701303981973713 : ℝ) / 1000000000000000000000000) ≤ v222 ∧ v222 ≤ ((198186130344167263972149 : ℝ) / 200000000000000000000000) := add_interval h160 h221 (by norm_num) (by norm_num)
  let v223 : ℝ := jacobian y 9 9
  have h223 : ((183107489880450076869 : ℝ) / 6250000000000000000000) ≤ v223 ∧ v223 ≤ ((2929719838736338153881 : ℝ) / 100000000000000000000000) := by
    simpa [v223,jacobian,M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,Matrix.of_apply,Matrix.cons_val] using M2TangencyJacobianBounds.entry_bounds y hx 9 9
  let v224 : ℝ := ((-6811950088803285 : ℝ) / 144115188075855872)
  have h224 : ((-6811950088803285 : ℝ) / 144115188075855872) ≤ v224 ∧ v224 ≤ ((-6811950088803285 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v224]
  let v225 : ℝ := v224*v26
  have h225 : ((0 : ℝ) / 1) ≤ v225 ∧ v225 ≤ ((0 : ℝ) / 1) := mul_interval h224 h26 (by norm_num) (by norm_num)
  let v226 : ℝ := ((-1828646140081387 : ℝ) / 18014398509481984)
  have h226 : ((-1828646140081387 : ℝ) / 18014398509481984) ≤ v226 ∧ v226 ≤ ((-1828646140081387 : ℝ) / 18014398509481984) := by constructor <;> norm_num [v226]
  let v227 : ℝ := v226*v19
  have h227 : ((0 : ℝ) / 1) ≤ v227 ∧ v227 ≤ ((0 : ℝ) / 1) := mul_interval h226 h19 (by norm_num) (by norm_num)
  let v228 : ℝ := v225+v227
  have h228 : ((0 : ℝ) / 1) ≤ v228 ∧ v228 ≤ ((0 : ℝ) / 1) := add_interval h225 h227 (by norm_num) (by norm_num)
  let v229 : ℝ := ((-605344055995505 : ℝ) / 144115188075855872)
  have h229 : ((-605344055995505 : ℝ) / 144115188075855872) ≤ v229 ∧ v229 ≤ ((-605344055995505 : ℝ) / 144115188075855872) := by constructor <;> norm_num [v229]
  let v230 : ℝ := v229*v22
  have h230 : ((0 : ℝ) / 1) ≤ v230 ∧ v230 ≤ ((0 : ℝ) / 1) := mul_interval h229 h22 (by norm_num) (by norm_num)
  let v231 : ℝ := v228+v230
  have h231 : ((0 : ℝ) / 1) ≤ v231 ∧ v231 ≤ ((0 : ℝ) / 1) := add_interval h228 h230 (by norm_num) (by norm_num)
  let v232 : ℝ := ((-329097342168993 : ℝ) / 2251799813685248)
  have h232 : ((-329097342168993 : ℝ) / 2251799813685248) ≤ v232 ∧ v232 ≤ ((-329097342168993 : ℝ) / 2251799813685248) := by constructor <;> norm_num [v232]
  let v233 : ℝ := v232*v30
  have h233 : ((0 : ℝ) / 1) ≤ v233 ∧ v233 ≤ ((0 : ℝ) / 1) := mul_interval h232 h30 (by norm_num) (by norm_num)
  let v234 : ℝ := v231+v233
  have h234 : ((0 : ℝ) / 1) ≤ v234 ∧ v234 ≤ ((0 : ℝ) / 1) := add_interval h231 h233 (by norm_num) (by norm_num)
  let v235 : ℝ := v224*v65
  have h235 : ((49442262631135542429 : ℝ) / 25000000000000000000000) ≤ v235 ∧ v235 ≤ ((247211315610977265227 : ℝ) / 125000000000000000000000) := mul_interval h224 h65 (by norm_num) (by norm_num)
  let v236 : ℝ := v235*v2
  have h236 : ((1811105332715456338611 : ℝ) / 500000000000000000000000) ≤ v236 ∧ v236 ≤ ((3622210702243102914719 : ℝ) / 1000000000000000000000000) := mul_interval h235 h2 (by norm_num) (by norm_num)
  let v237 : ℝ := v234+v236
  have h237 : ((1811105332715456338611 : ℝ) / 500000000000000000000000) ≤ v237 ∧ v237 ≤ ((3622210702243102914719 : ℝ) / 1000000000000000000000000) := add_interval h234 h236 (by norm_num) (by norm_num)
  let v238 : ℝ := v224*v69
  have h238 : ((8202898319805027669941 : ℝ) / 1000000000000000000000000) ≤ v238 ∧ v238 ≤ ((4101449161086233887367 : ℝ) / 500000000000000000000000) := mul_interval h224 h69 (by norm_num) (by norm_num)
  let v239 : ℝ := v238*v6
  have h239 : ((-3398730537865210947837 : ℝ) / 200000000000000000000000) ≤ v239 ∧ v239 ≤ ((-3398730536103768357397 : ℝ) / 200000000000000000000000) := mul_interval h238 h6 (by norm_num) (by norm_num)
  let v240 : ℝ := v237+v239
  have h240 : ((-13371442023895142061963 : ℝ) / 1000000000000000000000000) ≤ v240 ∧ v240 ≤ ((-6685720989137869436133 : ℝ) / 500000000000000000000000) := add_interval h237 h239 (by norm_num) (by norm_num)
  let v241 : ℝ := v224*v73
  have h241 : ((82980805963281767551993 : ℝ) / 1000000000000000000000000) ≤ v241 ∧ v241 ≤ ((16596161201379340880383 : ℝ) / 200000000000000000000000) := mul_interval h224 h73 (by norm_num) (by norm_num)
  let v242 : ℝ := v241*v10
  have h242 : ((-60064398699188763633 : ℝ) / 12500000000000000000000) ≤ v242 ∧ v242 ≤ ((-600643984382202397291 : ℝ) / 125000000000000000000000) := mul_interval h241 h10 (by norm_num) (by norm_num)
  let v243 : ℝ := v240+v242
  have h243 : ((-18176593919830243152603 : ℝ) / 1000000000000000000000000) ≤ v243 ∧ v243 ≤ ((-9088296926666679025297 : ℝ) / 500000000000000000000000) := add_interval h240 h242 (by norm_num) (by norm_num)
  let v244 : ℝ := v224*v77
  have h244 : ((-1170726272376523173393 : ℝ) / 250000000000000000000000) ≤ v244 ∧ v244 ≤ ((-4682905087391327854003 : ℝ) / 1000000000000000000000000) := mul_interval h224 h77 (by norm_num) (by norm_num)
  let v245 : ℝ := v244*v14
  have h245 : ((429221160245529530853 : ℝ) / 1000000000000000000000000) ≤ v245 ∧ v245 ≤ ((53652645184773289687 : ℝ) / 125000000000000000000000) := mul_interval h244 h14 (by norm_num) (by norm_num)
  let v246 : ℝ := v243+v245
  have h246 : ((-70989491038338854487 : ℝ) / 4000000000000000000000) ≤ v246 ∧ v246 ≤ ((-8873686345927585866549 : ℝ) / 500000000000000000000000) := add_interval h243 h245 (by norm_num) (by norm_num)
  let v247 : ℝ := v226*v33
  have h247 : ((-367239495283489441329 : ℝ) / 250000000000000000000000) ≤ v247 ∧ v247 ≤ ((-1468957977164581902189 : ℝ) / 1000000000000000000000000) := mul_interval h226 h33 (by norm_num) (by norm_num)
  let v248 : ℝ := v247*v2
  have h248 : ((-269044891172275980441 : ℝ) / 100000000000000000000000) ≤ v248 ∧ v248 ≤ ((-2690448903831427913409 : ℝ) / 1000000000000000000000000) := mul_interval h247 h2 (by norm_num) (by norm_num)
  let v249 : ℝ := v246+v248
  have h249 : ((-255472770891343417827 : ℝ) / 12500000000000000000000) ≤ v249 ∧ v249 ≤ ((-20437821595686599646507 : ℝ) / 1000000000000000000000000) := add_interval h246 h248 (by norm_num) (by norm_num)
  let v250 : ℝ := v226*v37
  have h250 : ((-257913160646316280687 : ℝ) / 50000000000000000000000) ≤ v250 ∧ v250 ≤ ((-2579131603095431439191 : ℝ) / 500000000000000000000000) := mul_interval h226 h37 (by norm_num) (by norm_num)
  let v251 : ℝ := v250*v6
  have h251 : ((10686190410170850866781 : ℝ) / 1000000000000000000000000) ≤ v251 ∧ v251 ≤ ((10686190426578602848627 : ℝ) / 1000000000000000000000000) := mul_interval h250 h6 (by norm_num) (by norm_num)
  let v252 : ℝ := v249+v251
  have h252 : ((-9751631261136622559379 : ℝ) / 1000000000000000000000000) ≤ v252 ∧ v252 ≤ ((-243790779227699919947 : ℝ) / 25000000000000000000000) := add_interval h249 h251 (by norm_num) (by norm_num)
  let v253 : ℝ := v226*v41
  have h253 : ((-489215361385030984561 : ℝ) / 10000000000000000000000) ≤ v253 ∧ v253 ≤ ((-9784307222667446546899 : ℝ) / 200000000000000000000000) := mul_interval h226 h41 (by norm_num) (by norm_num)
  let v254 : ℝ := v253*v10
  have h254 : ((354111122832610397969 : ℝ) / 125000000000000000000000) ≤ v254 ∧ v254 ≤ ((708222248734388437391 : ℝ) / 250000000000000000000000) := mul_interval h253 h10 (by norm_num) (by norm_num)
  let v255 : ℝ := v252+v254
  have h255 : ((-6918742278475739375627 : ℝ) / 1000000000000000000000000) ≤ v255 ∧ v255 ≤ ((-1729685543542610762079 : ℝ) / 250000000000000000000000) := add_interval h252 h254 (by norm_num) (by norm_num)
  let v256 : ℝ := v226*v45
  have h256 : ((4750874195652504768177 : ℝ) / 1000000000000000000000000) ≤ v256 ∧ v256 ≤ ((950174839559226799377 : ℝ) / 200000000000000000000000) := mul_interval h226 h45 (by norm_num) (by norm_num)
  let v257 : ℝ := v256*v14
  have h257 : ((-108862751979769236973 : ℝ) / 250000000000000000000000) ≤ v257 ∧ v257 ≤ ((-108862751667174183427 : ℝ) / 250000000000000000000000) := mul_interval h256 h14 (by norm_num) (by norm_num)
  let v258 : ℝ := v255+v257
  have h258 : ((-7354193286394816323519 : ℝ) / 1000000000000000000000000) ≤ v258 ∧ v258 ≤ ((-919274147604892472753 : ℝ) / 125000000000000000000000) := add_interval h255 h257 (by norm_num) (by norm_num)
  let v259 : ℝ := v229*v49
  have h259 : ((-83537689560378259819 : ℝ) / 1000000000000000000000000) ≤ v259 ∧ v259 ≤ ((-16707537835059820839 : ℝ) / 200000000000000000000000) := mul_interval h229 h49 (by norm_num) (by norm_num)
  let v260 : ℝ := v259*v2
  have h260 : ((-38250564150251483889 : ℝ) / 250000000000000000000000) ≤ v260 ∧ v260 ≤ ((-15300225586038845131 : ℝ) / 100000000000000000000000) := mul_interval h259 h2 (by norm_num) (by norm_num)
  let v261 : ℝ := v258+v260
  have h261 : ((-300287821719832890363 : ℝ) / 40000000000000000000000) ≤ v261 ∧ v261 ≤ ((-3753597718349764116667 : ℝ) / 500000000000000000000000) := add_interval h258 h260 (by norm_num) (by norm_num)
  let v262 : ℝ := v229*v53
  have h262 : ((-145074755986039334181 : ℝ) / 1000000000000000000000000) ≤ v262 ∧ v262 ≤ ((-145074755380449156989 : ℝ) / 1000000000000000000000000) := mul_interval h229 h53 (by norm_num) (by norm_num)
  let v263 : ℝ := v262*v6
  have h263 : ((150273105281230846499 : ℝ) / 500000000000000000000000) ≤ v263 ∧ v263 ≤ ((150273105943031580169 : ℝ) / 500000000000000000000000) := mul_interval h262 h6 (by norm_num) (by norm_num)
  let v264 : ℝ := v261+v263
  have h264 : ((-7206649332433360566077 : ℝ) / 1000000000000000000000000) ≤ v264 ∧ v264 ≤ ((-1801662306203366268249 : ℝ) / 250000000000000000000000) := add_interval h261 h263 (by norm_num) (by norm_num)
  let v265 : ℝ := v229*v57
  have h265 : ((-4024556324211869604009 : ℝ) / 1000000000000000000000000) ≤ v265 ∧ v265 ≤ ((-4024556314428777132013 : ℝ) / 1000000000000000000000000) := mul_interval h229 h57 (by norm_num) (by norm_num)
  let v266 : ℝ := v265*v10
  have h266 : ((116524563096612797453 : ℝ) / 500000000000000000000000) ≤ v266 ∧ v266 ≤ ((233049127649796456217 : ℝ) / 1000000000000000000000000) := mul_interval h265 h10 (by norm_num) (by norm_num)
  let v267 : ℝ := v264+v266
  have h267 : ((-6973600206240134971171 : ℝ) / 1000000000000000000000000) ≤ v267 ∧ v267 ≤ ((-6973600097163668616779 : ℝ) / 1000000000000000000000000) := add_interval h264 h266 (by norm_num) (by norm_num)
  let v268 : ℝ := v229*v61
  have h268 : ((1915897524109355477 : ℝ) / 25000000000000000000000) ≤ v268 ∧ v268 ≤ ((76635901160236460551 : ℝ) / 1000000000000000000000000) := mul_interval h229 h61 (by norm_num) (by norm_num)
  let v269 : ℝ := v268*v14
  have h269 : ((-439013682188377069 : ℝ) / 62500000000000000000000) ≤ v269 ∧ v269 ≤ ((-7024218880061496599 : ℝ) / 1000000000000000000000000) := mul_interval h268 h14 (by norm_num) (by norm_num)
  let v270 : ℝ := v267+v269
  have h270 : ((-279224977006205960171 : ℝ) / 40000000000000000000000) ≤ v270 ∧ v270 ≤ ((-3490312158021865056689 : ℝ) / 500000000000000000000000) := add_interval h267 h269 (by norm_num) (by norm_num)
  let v271 : ℝ := v232*v81
  have h271 : ((-170297529033110045787 : ℝ) / 500000000000000000000000) ≤ v271 ∧ v271 ≤ ((-170297526762807416993 : ℝ) / 500000000000000000000000) := mul_interval h232 h81 (by norm_num) (by norm_num)
  let v272 : ℝ := v271*v2
  have h272 : ((-623811991276316547331 : ℝ) / 1000000000000000000000000) ≤ v272 ∧ v272 ≤ ((-623811982815985473509 : ℝ) / 1000000000000000000000000) := mul_interval h271 h2 (by norm_num) (by norm_num)
  let v273 : ℝ := v270+v272
  have h273 : ((-3802218208215732775803 : ℝ) / 500000000000000000000000) ≤ v273 ∧ v273 ≤ ((-7604436298859715586887 : ℝ) / 1000000000000000000000000) := add_interval h270 h272 (by norm_num) (by norm_num)
  let v274 : ℝ := v232*v85
  have h274 : ((-1239892332727779765667 : ℝ) / 1000000000000000000000000) ≤ v274 ∧ v274 ≤ ((-309973082337590547519 : ℝ) / 250000000000000000000000) := mul_interval h232 h85 (by norm_num) (by norm_num)
  let v275 : ℝ := v274*v6
  have h275 : ((1284320418512779208219 : ℝ) / 500000000000000000000000) ≤ v275 ∧ v275 ≤ ((1284320422306167305461 : ℝ) / 500000000000000000000000) := mul_interval h274 h6 (by norm_num) (by norm_num)
  let v276 : ℝ := v273+v275
  have h276 : ((-78684305928217298987 : ℝ) / 15625000000000000000000) ≤ v276 ∧ v276 ≤ ((-1007159090849476195193 : ℝ) / 200000000000000000000000) := add_interval h273 h275 (by norm_num) (by norm_num)
  let v277 : ℝ := v232*v89
  have h277 : ((-3425332578277782431743 : ℝ) / 125000000000000000000000) ≤ v277 ∧ v277 ≤ ((-2740266058431377075891 : ℝ) / 100000000000000000000000) := mul_interval h232 h89 (by norm_num) (by norm_num)
  let v278 : ℝ := v277*v10
  have h278 : ((79340001799059003179 : ℝ) / 50000000000000000000000) ≤ v278 ∧ v278 ≤ ((396700011117071891579 : ℝ) / 250000000000000000000000) := mul_interval h277 h10 (by norm_num) (by norm_num)
  let v279 : ℝ := v276+v278
  have h279 : ((-862248885856181767897 : ℝ) / 250000000000000000000000) ≤ v279 ∧ v279 ≤ ((-3448995409779093409649 : ℝ) / 1000000000000000000000000) := add_interval h276 h278 (by norm_num) (by norm_num)
  let v280 : ℝ := v232*v93
  have h280 : ((-8192712242003170333199 : ℝ) / 500000000000000000000000) ≤ v280 ∧ v280 ≤ ((-16385424430029498882831 : ℝ) / 1000000000000000000000000) := mul_interval h232 h93 (by norm_num) (by norm_num)
  let v281 : ℝ := v280*v14
  have h281 : ((750919648564830539843 : ℝ) / 500000000000000000000000) ≤ v281 ∧ v281 ≤ ((375459826427962192213 : ℝ) / 250000000000000000000000) := mul_interval h280 h14 (by norm_num) (by norm_num)
  let v282 : ℝ := v279+v281
  have h282 : ((-973578123147532995951 : ℝ) / 500000000000000000000000) ≤ v282 ∧ v282 ≤ ((-1947156104067244640797 : ℝ) / 1000000000000000000000000) := add_interval h279 h281 (by norm_num) (by norm_num)
  let v283 : ℝ := v223*v282
  have h283 : ((-28523111419450171369 : ℝ) / 500000000000000000000000) ≤ v283 ∧ v283 ≤ ((-14261554664845983793 : ℝ) / 250000000000000000000000) := mul_interval h223 h282 (by norm_num) (by norm_num)
  let v284 : ℝ := v222+v283
  have h284 : ((39634943619138603265239 : ℝ) / 40000000000000000000000) ≤ v284 ∧ v284 ≤ ((990873605502176935925573 : ℝ) / 1000000000000000000000000) := add_interval h222 h283 (by norm_num) (by norm_num)
  have he : curvature y (approximateAcceleration y) = v284 := by
    simp only [curvature,curvatureConstant,curvatureGradient,velocityIndex,approximateAcceleration,matrixCLM_apply,Matrix.mulVec,dotProduct,accelerationForcing,preconditioner,M2KernelCertificate.preconditioner,residualIndex,amplitudeIndex,Fin.sum_univ_four,Matrix.of_apply,Matrix.cons_val]
    norm_num [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284] <;> (try simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring
  rw [he]
  exact lt_of_lt_of_le (by norm_num) h284.1

private theorem entry_defect_bound (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) (i j : Fin 4) :
    |(1-preconditioner*accelerationMatrix y) i j| ≤ radius i j := by
  fin_cases i <;> fin_cases j
  · exact e_bound_0_0 y hx
  · exact e_bound_0_1 y hx
  · exact e_bound_0_2 y hx
  · exact e_bound_0_3 y hx
  · exact e_bound_1_0 y hx
  · exact e_bound_1_1 y hx
  · exact e_bound_1_2 y hx
  · exact e_bound_1_3 y hx
  · exact e_bound_2_0 y hx
  · exact e_bound_2_1 y hx
  · exact e_bound_2_2 y hx
  · exact e_bound_2_3 y hx
  · exact e_bound_3_0 y hx
  · exact e_bound_3_1 y hx
  · exact e_bound_3_2 y hx
  · exact e_bound_3_3 y hx

/-- Actual acceleration-block row defects, uniform over the full joint box. -/
theorem acceleration_row_defect_bound (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) (i : Fin 4) :
    ∑ j, |(1-preconditioner*accelerationMatrix y) i j| < (1 : ℝ)/1000000 := by
  calc
    _ ≤ ∑ j, radius i j := Finset.sum_le_sum (fun j _ => entry_defect_bound y hx i j)
    _ < _ := by
      fin_cases i
      · rw [Fin.sum_univ_four]
        change (((515960894976933 : ℝ) / 40000000000000000000000)+((1699145935416127 : ℝ) / 250000000000000000000000)+((308771927652181 : ℝ) / 4000000000000000000000)+((3086980868191403 : ℝ) / 1000000000000000000000000)) < (1 : ℝ)/1000000
        norm_num
      · rw [Fin.sum_univ_four]
        change (((183044250735509 : ℝ) / 125000000000000000000000)+((726657207045771 : ℝ) / 1000000000000000000000000)+((2210852973118251 : ℝ) / 250000000000000000000000)+((1333424713739 : ℝ) / 3906250000000000000000)) < (1 : ℝ)/1000000
        norm_num
      · rw [Fin.sum_univ_four]
        change (((27880119630483 : ℝ) / 200000000000000000000000)+((40147880246573 : ℝ) / 500000000000000000000000)+((519554695846491 : ℝ) / 500000000000000000000000)+((726115608071 : ℝ) / 20000000000000000000000)) < (1 : ℝ)/1000000
        norm_num
      · rw [Fin.sum_univ_four]
        change (((16219768504629 : ℝ) / 500000000000000000000000)+((24102139729 : ℝ) / 1250000000000000000000)+((180321409771479 : ℝ) / 1000000000000000000000000)+((32469928011973 : ℝ) / 500000000000000000000000)) < (1 : ℝ)/1000000
        norm_num

/-- The exact preconditioned acceleration vector has a proved norm bound. -/
theorem approximate_acceleration_norm (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) : ‖approximateAcceleration y‖ ≤ (1000 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1000)).mpr
  intro i
  fin_cases i
  · change |approximateAcceleration y 0| ≤ (1000 : ℝ)
    simpa only [div_one] using approx_bound_0 y hx
  · change |approximateAcceleration y 1| ≤ (1000 : ℝ)
    simpa only [div_one] using approx_bound_1 y hx
  · change |approximateAcceleration y 2| ≤ (1000 : ℝ)
    simpa only [div_one] using approx_bound_2 y hx
  · change |approximateAcceleration y 3| ≤ (1000 : ℝ)
    simpa only [div_one] using approx_bound_3 y hx

/-- The true curvature response has a uniform scalar pairing budget. -/
theorem curvature_gradient_bound (y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i) : (∑ i, |curvatureGradient y i|) ≤ (10 : ℝ) := by
  have h0 := gradient_bound_0 y hx
  have h1 := gradient_bound_1 y hx
  have h2 := gradient_bound_2 y hx
  have h3 := gradient_bound_3 y hx
  simp only [Fin.sum_univ_four]
  linarith

end FMSA.Convergence.M2CurvatureCertificate

/-- info: 'FMSA.Convergence.M2CurvatureCertificate.approximate_curvature_gt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2CurvatureCertificate.approximate_curvature_gt

/-- info: 'FMSA.Convergence.M2CurvatureCertificate.acceleration_row_defect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2CurvatureCertificate.acceleration_row_defect_bound

/-- info: 'FMSA.Convergence.M2CurvatureCertificate.approximate_acceleration_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2CurvatureCertificate.approximate_acceleration_norm

/-- info: 'FMSA.Convergence.M2CurvatureCertificate.curvature_gradient_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2CurvatureCertificate.curvature_gradient_bound
