import MSAConvergence.BHFiniteFiberCertificates

/-! A CONSTRUCTED exact coordinate-elimination certificate for the actual
zero-density BH system, arbitrary finite species/tails and positive rates.
This supplies real eliminants/multipliers, not an assumed certificate. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.VacuumFiberCertificate
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.BHFiniteFiberCertificates
variable {N : ℕ} {T : Type*} [Fintype T]

def rootPoint (z : T → ℝ) (sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) : TailMatrix T N × TailMatrix T N :=
  (nonlinearZeroDensityDt z (b • K),nonlinearZeroDensityG z sigma (b • K))

def eliminant (z : T → ℝ) (sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (i : AmpIndex T N) : Polynomial ℝ :=
  Polynomial.X-Polynomial.C (amplitudeValues (rootPoint z sigma K b) i)

def multiplier (z : T → ℝ) (i j : AmpIndex T N) : FiberPoly T N := by
  classical
  exact if i.1 then
    (if j = i then MvPolynomial.C ((2*Real.pi)⁻¹) else 0)+
      ∑ v, if j = (false,v,i.2.2.1,i.2.2.2) then
        MvPolynomial.C (z v/(z i.2.1+z v)/(2*Real.pi)) else 0
  else if j = i then 1 else 0

/-- The certificate point is a genuine actual vacuum root, for every
coupling, arbitrary finite strengths and unequal diameters. -/
theorem rootPoint_is_actual (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (K : TailMatrix T N) (b : ℝ) :
    IsRoot z 0 sigma (b • K) (rootPoint z sigma K b).1 (rootPoint z sigma K b).2 :=
  nonlinearRoot_zero_density_exists z sigma (b • K) (fun u => (hz u).ne')

/-- Every constructed coordinate eliminant is nonzero and linear. -/
theorem eliminant_ne_zero (z : T → ℝ) (sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (i : AmpIndex T N) : eliminant z sigma K b i ≠ 0 :=
  Polynomial.X_sub_C_ne_zero _

/-- The vacuum first residual is exactly Dt minus its explicit root value. -/
theorem first_residual (z : T → ℝ) (sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a : TailMatrix T N × TailMatrix T N) (u : T) (i j : Fin N) :
    (FMSA.ExactMSA.MultiTailMixture.residual z 0 sigma K (b,a)).1 u i j =
      a.1 u i j-2*Real.pi*b*K u i j/z u := by
  simp [FMSA.ExactMSA.MultiTailMixture.residual,firstLHS,mul_ite]

/-- The honest vacuum source is affine in ALL original Dt coordinates. -/
theorem source_affine (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : Fin N → ℝ)
    (a : TailMatrix T N × TailMatrix T N) (u : T) (i j : Fin N) :
    secondRHS z 0 sigma a.1 a.2 u i j =
      2*Real.pi*((1+z u*edgeHi sigma i j)/(z u)^2)+
        ∑ v, z v/(z u+z v)*a.1 v i j := by
  simp only [secondRHS,nonlinearA_zero_density,nonlinearQp_zero_density,nonlinearC_zero_density]
  rw [add_div,add_div,Finset.sum_div]
  have hterm : (∑ v, ((z u)^2*z v/(z u+z v)*a.1 v i j)/(z u)^2) =
      ∑ v, z v/(z u+z v)*a.1 v i j := by
    apply Finset.sum_congr rfl
    intro v _
    field_simp [(hz u).ne',(add_pos (hz u) (hz v)).ne']
    <;> ring
  rw [hterm]
  field_simp [(hz u).ne']
  <;> ring

/-- The original G-coordinate difference is a proved linear combination
of the ACTUAL residual coordinates, with exact real coefficients. -/
theorem second_resolver (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (K : TailMatrix T N) (b : ℝ)
    (a : TailMatrix T N × TailMatrix T N) (u : T) (i j : Fin N) :
    2*Real.pi*(a.2 u i j-(rootPoint z sigma K b).2 u i j) =
      (FMSA.ExactMSA.MultiTailMixture.residual z 0 sigma K (b,a)).2 u i j+
        ∑ v, z v/(z u+z v)*(FMSA.ExactMSA.MultiTailMixture.residual z 0 sigma K (b,a)).1 v i j := by
  simp only [first_residual]
  change 2*Real.pi*(a.2 u i j-(rootPoint z sigma K b).2 u i j) =
    (secondLHS z 0 sigma a.1 a.2 u i j-secondRHS z 0 sigma a.1 a.2 u i j)+_
  rw [source_affine z hz sigma a u i j]
  simp only [secondLHS,Pi.zero_apply,zero_mul,sub_zero,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,rootPoint,nonlinearZeroDensityG,
    Pi.smul_apply,smul_eq_mul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hterm : (∑ v, z v/(z u+z v)*(2*Real.pi*b*K v i j/z v)) =
      2*Real.pi*∑ v, b*K v i j/(z u+z v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    field_simp [(hz v).ne',(add_pos (hz u) (hz v)).ne']
    <;> ring
  rw [hterm]
  ring

/-- The explicit multiplier matrix contracts to the intended triangular
combination of endpoint residual POLYNOMIALS, not merely their zeros. -/
theorem multiplier_sum (z : T → ℝ) (sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (i : AmpIndex T N) :
    (∑ j, multiplier z i j*endpointPoly z 0 sigma K b j) =
      if i.1 then MvPolynomial.C ((2*Real.pi)⁻¹)*endpointPoly z 0 sigma K b i+
        ∑ v, MvPolynomial.C (z v/(z i.2.1+z v)/(2*Real.pi))*
          endpointPoly z 0 sigma K b (false,v,i.2.2.1,i.2.2.2)
      else endpointPoly z 0 sigma K b i := by
  classical
  cases hi : i.1
  · simp [multiplier,hi,ite_mul]
  · simp only [multiplier,hi,if_true,add_mul,Finset.sum_add_distrib]
    rw [show (∑ j, (∑ v, if j = (false,v,i.2.2.1,i.2.2.2) then
          MvPolynomial.C (z v/(z i.2.1+z v)/(2*Real.pi)) else 0)*endpointPoly z 0 sigma K b j) =
        ∑ v, MvPolynomial.C (z v/(z i.2.1+z v)/(2*Real.pi))*
          endpointPoly z 0 sigma K b (false,v,i.2.2.1,i.2.2.2) by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp [ite_mul]]
    simp [ite_mul]

/-- The complete saturated ideal identity is PROVED for the actual vacuum
polynomials. All eliminants/multipliers are explicitly constructed. -/
theorem certificate_identity (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (K : TailMatrix T N) (b : ℝ) (i : AmpIndex T N) :
    (1 : FiberPoly T N)*coordinatePolynomial (eliminant z sigma K b i) i =
      ∑ j, multiplier z i j*endpointPoly z 0 sigma K b j := by
  rw [one_mul,multiplier_sum]
  apply MvPolynomial.funext
  intro x
  let a : TailMatrix T N × TailMatrix T N :=
    (fun u k l => x (false,u,k,l),fun u k l => x (true,u,k,l))
  have hx : amplitudeValues a = x := by
    funext j
    rcases j with ⟨tag,u,k,l⟩
    cases tag <;> rfl
  rw [← hx]
  simp only [eval_coordinatePolynomial,eliminant,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  rcases i with ⟨tag,u,k,l⟩
  cases tag
  · simp only [Bool.false_eq_true,if_false,eval_endpointPoly,amplitudeValues,first_residual,
      rootPoint,nonlinearZeroDensityDt,Pi.smul_apply,smul_eq_mul]
    ring
  · simp only [if_true,map_add,map_mul,map_sum,MvPolynomial.eval_C,eval_endpointPoly,amplitudeValues,
      Bool.false_eq_true,if_false]
    have he := second_resolver z hz sigma K b a u k l
    have hs : (∑ v, z v/(z u+z v)/(2*Real.pi)*
          (FMSA.ExactMSA.MultiTailMixture.residual z 0 sigma K (b,a)).1 v k l) =
        (∑ v, z v/(z u+z v)*
          (FMSA.ExactMSA.MultiTailMixture.residual z 0 sigma K (b,a)).1 v k l)/(2*Real.pi) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      ring
    rw [hs]
    rw [inv_mul_eq_div,← add_div,← he]
    exact (mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero pi_ne_zero)).symm

/-- A real instance of the exact elimination-certificate structure, with
unit saturation and nonzero LINEAR coordinate eliminants, for arbitrary
finite mixtures/tails at vacuum. No certificate-existence premise. -/
def certificate (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (K : TailMatrix T N) (b : ℝ) :
    CoordinateFiberCertificate z 0 sigma K b where
  eliminant := eliminant z sigma K b
  nonzero := eliminant_ne_zero z sigma K b
  saturation := 1
  multiplier := multiplier z
  identity := certificate_identity z hz sigma K b

/-- The ACTUAL fiber checker is instantiated, not assumed: all vacuum
endpoint fibers are finite, including zero coupling and inactive tails. -/
theorem actual_vacuum_fiber_finite (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (K : TailMatrix T N) (b : ℝ) :
    {a : TailMatrix T N × TailMatrix T N | IsRoot z 0 sigma (b • K) a.1 a.2}.Finite :=
  actual_fiber_finite_of_certificate z 0 sigma K b (certificate z hz sigma K b) rfl

end FMSA.Convergence.VacuumFiberCertificate

/-- info: 'FMSA.Convergence.VacuumFiberCertificate.rootPoint_is_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.VacuumFiberCertificate.rootPoint_is_actual

/-- info: 'FMSA.Convergence.VacuumFiberCertificate.eliminant_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.VacuumFiberCertificate.eliminant_ne_zero

/-- info: 'FMSA.Convergence.VacuumFiberCertificate.first_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.VacuumFiberCertificate.first_residual

/-- info: 'FMSA.Convergence.VacuumFiberCertificate.source_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.VacuumFiberCertificate.source_affine

/-- info: 'FMSA.Convergence.VacuumFiberCertificate.second_resolver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.VacuumFiberCertificate.second_resolver

/-- info: 'FMSA.Convergence.VacuumFiberCertificate.multiplier_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.VacuumFiberCertificate.multiplier_sum

/-- info: 'FMSA.Convergence.VacuumFiberCertificate.certificate_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.VacuumFiberCertificate.certificate_identity

/-- info: 'FMSA.Convergence.VacuumFiberCertificate.actual_vacuum_fiber_finite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.VacuumFiberCertificate.actual_vacuum_fiber_finite
