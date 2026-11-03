import MSAConvergence.BHResidualPolynomials
import MSAConvergence.VacuumFiberCertificate

/-! Exact formal partials of the literal BH polynomials are the coordinates
of the ORIGINAL amplitude derivative. Finite row-defect certificates therefore
imply actual endpoint regularity, without a root or canonicity premise. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.BHPolynomialJacobian
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Paper.ActualAnalyticBranch
open FMSA.Convergence.BHResidualPolynomials
open FMSA.Convergence.RegularEndpointContinuation
variable {N : ℕ} {T : Type*} [Fintype T]
local instance : DecidableEq (AmpIndex T N) := Classical.decEq _

/-- Formal partial differentiation agrees with differentiation along EVERY
real line. Coefficients remain exact real numbers. -/
theorem polynomial_line_hasDerivAt {I : Type*} [Fintype I]
    (P : MvPolynomial I ℝ) (v w : I → ℝ) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (v+t • w) P)
      (∑ i, MvPolynomial.eval v (MvPolynomial.pderiv i P)*w i) 0 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simpa [MvPolynomial.pderiv_C] using hasDerivAt_const (0 : ℝ) c
  | add p q hp hq =>
    convert! hp.add hq using 1 <;> simp [map_add,Finset.sum_add_distrib,add_mul]
    rfl
  | mul_X p j hp =>
    have hx : HasDerivAt (fun t : ℝ => v j+t*w j) (w j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w j)).const_add (v j)
    have hd := hp.mul hx
    convert! hd using 1
    · ext t; simp [map_mul]
    · simp [Pi.single_apply,Finset.sum_add_distrib,mul_add,
        Finset.mul_sum,apply_ite,mul_left_comm,mul_comm]
      ring

def amplitudeEquiv : (TailMatrix T N × TailMatrix T N) ≃ₗ[ℝ] (AmpIndex T N → ℝ) where
  toFun := amplitudeValues
  invFun v := (fun u i j => v (false,u,i,j), fun u i j => v (true,u,i,j))
  map_add' a b := by funext ⟨c,u,i,j⟩; cases c <;> rfl
  map_smul' c a := by funext ⟨b,u,i,j⟩; cases b <;> rfl
  left_inv a := by apply Prod.ext <;> rfl
  right_inv v := by funext ⟨b,u,i,j⟩; cases b <;> rfl

def amplitudeCoordinates : (TailMatrix T N × TailMatrix T N) ≃L[ℝ] (AmpIndex T N → ℝ) :=
  (amplitudeEquiv (T := T) (N := N)).toContinuousLinearEquiv

/-- ALL original amplitude coordinates, with Dt before G; no reduced X variables. -/
def jacobian (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a : TailMatrix T N × TailMatrix T N) : Matrix (AmpIndex T N) (AmpIndex T N) ℝ :=
  fun i j => MvPolynomial.eval (amplitudeValues a)
    (MvPolynomial.pderiv j (endpointPoly z rho sigma K b i))

/-- This is exactly the partial consumed by the actual analytic IFT. -/
def actualPartial (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    (TailMatrix T N × TailMatrix T N) →L[ℝ] (TailMatrix T N × TailMatrix T N) :=
  (fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (b,a)).comp
    (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))

/-- Formal polynomial Jacobian multiplication is the exact actual amplitude
partial, for every state and physical data, including nonroots and singular points. -/
theorem actual_partial_coordinates
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a h : TailMatrix T N × TailMatrix T N) (i : AmpIndex T N) :
    amplitudeValues (actualPartial z rho sigma K b a h) i =
      ∑ j, jacobian z rho sigma K b a i j*amplitudeValues h j := by
  let R := FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K
  let c : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (amplitudeCoordinates (T := T) (N := N)).toContinuousLinearMap
  have hl : HasDerivAt (fun t : ℝ => (b,a+t • h)) (0,h) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) b).prodMk
      (((hasDerivAt_id (0 : ℝ)).smul_const h).const_add a)
  have hr : HasFDerivAt R (fderiv ℝ R (b,a)) (b,a) :=
    (residual_analyticAt z rho sigma K (b,a)).differentiableAt.hasFDerivAt
  have hr' : HasFDerivAt R (fderiv ℝ R (b,a)) (b,a+(0 : ℝ) • h) := by simpa using hr
  have hd := c.hasFDerivAt.comp_hasDerivAt 0 (hr'.comp_hasDerivAt 0 hl)
  have hp := polynomial_line_hasDerivAt (endpointPoly z rho sigma K b i)
    (amplitudeValues a) (amplitudeValues h)
  have he : (fun t : ℝ => MvPolynomial.eval (amplitudeValues a+t • amplitudeValues h)
      (endpointPoly z rho sigma K b i)) = (fun t : ℝ => c (R (b,a+t • h))) := by
    funext t
    have hv : amplitudeValues a+t • amplitudeValues h = amplitudeValues (a+t • h) := by
      exact ((amplitudeEquiv (T := T) (N := N)).map_add a (t • h)).trans
        (congrArg (fun f => amplitudeValues a+f) ((amplitudeEquiv (T := T) (N := N)).map_smul t h)) |>.symm
    rw [hv,eval_endpointPoly]
    rfl
  rw [he] at hp
  simpa [jacobian,actualPartial,c,R,Function.comp_def,amplitudeCoordinates,amplitudeEquiv]
    using hd.unique hp

/-- Coordinate form of the actual partial as literal matrix multiplication. -/
theorem actual_partial_mulVec
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a h : TailMatrix T N × TailMatrix T N) :
    (jacobian z rho sigma K b a).mulVec (amplitudeValues h) =
      amplitudeValues (actualPartial z rho sigma K b a h) := by
  funext i
  exact (actual_partial_coordinates z rho sigma K b a h i).symm

/-- Injectivity of the matrix is equivalent to injectivity of the ORIGINAL
amplitude partial; both directions include empty species/tail families. -/
theorem actual_partial_injective_iff
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    Function.Injective (actualPartial z rho sigma K b a) ↔
      Function.Injective (jacobian z rho sigma K b a).mulVec := by
  let e := amplitudeEquiv (T := T) (N := N)
  constructor
  · intro hi x y hxy
    have hx : amplitudeValues (e.symm x) = x := e.apply_symm_apply x
    have hy : amplitudeValues (e.symm y) = y := e.apply_symm_apply y
    have hL : actualPartial z rho sigma K b a (e.symm x) =
        actualPartial z rho sigma K b a (e.symm y) := by
      apply amplitude_values_injective
      rw [← actual_partial_mulVec,← actual_partial_mulVec,hx,hy]
      exact hxy
    have he := congrArg amplitudeValues (hi hL)
    simpa only [hx,hy] using he
  · intro hi x y hxy
    apply amplitude_values_injective
    apply hi
    rw [actual_partial_mulVec,actual_partial_mulVec,hxy]

/-- Actual endpoint regularity is EXACTLY nonsingularity of the formal
polynomial Jacobian. No root, symmetry, positivity or canonicity premise. -/
theorem endpoint_regular_iff_jacobian_isUnit
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    EndpointRegular z rho sigma K b a ↔ IsUnit (jacobian z rho sigma K b a) := by
  classical
  rw [← Matrix.mulVec_injective_iff_isUnit,← actual_partial_injective_iff]
  constructor
  · rintro ⟨e,he⟩
    have he' : e.toContinuousLinearMap = actualPartial z rho sigma K b a := he
    rw [← he']
    exact e.injective
  · intro hi
    let L := actualPartial z rho sigma K b a
    have hk : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hi
    have hs : L.range = ⊤ := LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi)
    exact ⟨ContinuousLinearEquiv.ofBijective L hk hs,ContinuousLinearEquiv.coe_ofBijective L hk hs⟩

/-- Determinant criterion for the exact actual endpoint partial. -/
theorem endpoint_regular_iff_jacobian_det_ne_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    EndpointRegular z rho sigma K b a ↔ (jacobian z rho sigma K b a).det ≠ 0 := by
  classical
  rw [endpoint_regular_iff_jacobian_isUnit,Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]

/-- Exact row-defect certificate: no assumed inverse of C is required.
The argument also handles an empty coordinate family. -/
theorem matrix_injective_of_row_defect {I : Type*} [Fintype I] [DecidableEq I]
    (J C : Matrix I I ℝ) (hrow : ∀ i, ∑ j, |(1-C*J) i j| < 1) :
    Function.Injective J.mulVec := by
  have hzero : ∀ x : I → ℝ, J.mulVec x = 0 → x = 0 := by
    intro x hx
    by_contra hn
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hf
      apply hn
      funext i
      exact not_ne_iff.mp (not_exists.mp hf i)
    obtain ⟨k,_hk,hmax⟩ := Finset.exists_max_image Finset.univ (fun j => |x j|)
      ⟨i,Finset.mem_univ i⟩
    have hpos : 0 < |x k| := (abs_pos.mpr hi).trans_le (hmax i (Finset.mem_univ i))
    have hfix : (1-C*J).mulVec x = x := by
      rw [Matrix.sub_mulVec,Matrix.one_mulVec,← Matrix.mulVec_mulVec,hx]
      simp
    have he : |x k| ≤ (∑ j, |(1-C*J) k j|)*|x k| := by
      calc
        |x k| = |∑ j, (1-C*J) k j*x j| := by rw [← congrFun hfix k]; rfl
        _ ≤ ∑ j, |(1-C*J) k j*x j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |(1-C*J) k j| * |x k| := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hmax j hj) (abs_nonneg _)
        _ = (∑ j, |(1-C*J) k j|)*|x k| := (Finset.sum_mul ..).symm
    have hlt := mul_lt_mul_of_pos_right (hrow k) hpos
    linarith
  intro x y hxy
  have hz : J.mulVec (x-y) = 0 := by rw [Matrix.mulVec_sub,hxy,sub_self]
  exact sub_eq_zero.mp (hzero (x-y) hz)

/-- A row-defect certificate on the FORMAL polynomial matrix gives true
endpoint regularity. The analytic enclosure inequalities are explicit goals. -/
theorem endpoint_regular_of_row_defect
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a : TailMatrix T N × TailMatrix T N)
    (C : Matrix (AmpIndex T N) (AmpIndex T N) ℝ)
    (hrow : ∀ i, ∑ j, |(1-C*jacobian z rho sigma K b a) i j| < 1) :
    EndpointRegular z rho sigma K b a := by
  classical
  rw [endpoint_regular_iff_jacobian_isUnit,← Matrix.mulVec_injective_iff_isUnit]
  exact matrix_injective_of_row_defect _ C hrow

/-- The exact vacuum elimination multipliers have no amplitude dependence. -/
theorem vacuum_multiplier_pderiv (z : T → ℝ) (i j k : AmpIndex T N) :
    MvPolynomial.pderiv k (VacuumFiberCertificate.multiplier z i j) = 0 := by
  cases hi : i.1 <;> simp [VacuumFiberCertificate.multiplier,hi,apply_ite]

def vacuumPreconditioner (z : T → ℝ) : Matrix (AmpIndex T N) (AmpIndex T N) ℝ :=
  fun i j => MvPolynomial.eval (0 : AmpIndex T N → ℝ) (VacuumFiberCertificate.multiplier z i j)

/-- Differentiating the ALREADY PROVED vacuum ideal identity constructs an
explicit exact left inverse of the actual polynomial Jacobian, at EVERY
amplitude point, arbitrary strengths/coupling and unequal diameters. -/
theorem vacuum_jacobian_left_inverse (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (K : TailMatrix T N) (b : ℝ)
    (a : TailMatrix T N × TailMatrix T N) :
    vacuumPreconditioner z*jacobian z 0 sigma K b a = 1 := by
  classical
  ext i j
  have h := congrArg (MvPolynomial.pderiv j)
    (VacuumFiberCertificate.certificate_identity z hz sigma K b i)
  have hm : ∀ k, MvPolynomial.eval (amplitudeValues a) (VacuumFiberCertificate.multiplier z i k) =
      vacuumPreconditioner z i k := by
    intro k
    cases hi : i.1 <;> simp [VacuumFiberCertificate.multiplier,vacuumPreconditioner,hi,apply_ite]
  have he := congrArg (MvPolynomial.eval (amplitudeValues a)) h
  simpa [BHFiniteFiberCertificates.coordinatePolynomial,VacuumFiberCertificate.eliminant,
    MvPolynomial.pderiv_C,vacuum_multiplier_pderiv,hm,jacobian,Matrix.mul_apply,Matrix.one_apply,
    Pi.single_apply,apply_ite,eq_comm]
    using he.symm

/-- A concrete, data-only instance of the polynomial certificate bridge:
ALL vacuum amplitude points are actual-partial regular. No root, canonical
seed, finite-fiber assumption or supplied enclosure/inverse is needed. -/
theorem vacuum_endpoint_regular (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (K : TailMatrix T N) (b : ℝ)
    (a : TailMatrix T N × TailMatrix T N) : EndpointRegular z 0 sigma K b a := by
  apply endpoint_regular_of_row_defect z 0 sigma K b a (vacuumPreconditioner z)
  intro i
  rw [vacuum_jacobian_left_inverse z hz sigma K b a]
  simp

/-- Exact polynomial row certificates feed the existing whole-cluster-limit
result for ANY continuous actual root prefix, with no canonical premise. -/
theorem actual_cluster_limit_of_row_defect
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (C : Matrix (AmpIndex T N) (AmpIndex T N) ℝ)
    (hrow : ∀ i, ∑ j, |(1-C*jacobian z rho sigma K b a) i j| < 1) :
    Tendsto p (𝓝[<] b) (𝓝 a) :=
  IsolatedEndpointLimits.actual_regular_cluster_has_limit z rho sigma K p b hb hp hroot a u hu ht ha
    (endpoint_regular_of_row_defect z rho sigma K b a C hrow)

end FMSA.Convergence.BHPolynomialJacobian

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.polynomial_line_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.polynomial_line_hasDerivAt

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.actual_partial_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.actual_partial_coordinates

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.actual_partial_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.actual_partial_mulVec

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.actual_partial_injective_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.actual_partial_injective_iff

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.endpoint_regular_iff_jacobian_isUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.endpoint_regular_iff_jacobian_isUnit

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.endpoint_regular_iff_jacobian_det_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.endpoint_regular_iff_jacobian_det_ne_zero

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.matrix_injective_of_row_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.matrix_injective_of_row_defect

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.endpoint_regular_of_row_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.endpoint_regular_of_row_defect

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.vacuum_multiplier_pderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.vacuum_multiplier_pderiv

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.vacuum_jacobian_left_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.vacuum_jacobian_left_inverse

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.vacuum_endpoint_regular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.vacuum_endpoint_regular

/-- info: 'FMSA.Convergence.BHPolynomialJacobian.actual_cluster_limit_of_row_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHPolynomialJacobian.actual_cluster_limit_of_row_defect
