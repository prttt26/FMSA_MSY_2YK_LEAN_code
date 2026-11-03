import MSAConvergence.IsolatedEndpointLimits

/-! Literal polynomial representation of the ACTUAL BH residual in coupling
and every finite Dt/G amplitude. Rates, density and diameters are fixed REAL
coefficients. No denominator involving an amplitude is introduced. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.BHResidualPolynomials
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.ExactMSA.Breakpoint MSAMixture
variable {N : ℕ} {T : Type*} [Fintype T]

abbrev AmpIndex (T : Type*) (N : ℕ) := Bool × T × Fin N × Fin N
abbrev VarIndex (T : Type*) (N : ℕ) := Option (AmpIndex T N)
abbrev Poly (T : Type*) (N : ℕ) := MvPolynomial (VarIndex T N) ℝ

def amplitudeValues (a : TailMatrix T N × TailMatrix T N) (i : AmpIndex T N) : ℝ :=
  if i.1 then a.2 i.2.1 i.2.2.1 i.2.2.2 else a.1 i.2.1 i.2.2.1 i.2.2.2

def pointValues (x : ℝ × (TailMatrix T N × TailMatrix T N)) : VarIndex T N → ℝ :=
  fun i => i.elim x.1 (amplitudeValues x.2)

def dVar (u : T) (i j : Fin N) : Poly T N := MvPolynomial.X (some (false,u,i,j))
def gVar (u : T) (i j : Fin N) : Poly T N := MvPolynomial.X (some (true,u,i,j))
def tauVar : Poly T N := MvPolynomial.X none

def gammaPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (u : T) (i j : Fin N) : Poly T N :=
  MvPolynomial.C (if i = j then 1 else 0)-
    MvPolynomial.C (2*Real.pi*rho j*exp (-z u*sigMix sigma i j)/z u)*gVar u i j

def wPoly (z : T → ℝ) (rho : Fin N → ℝ) (u : T) (i j : Fin N) : Poly T N :=
  MvPolynomial.C (2*Real.pi/z u)*∑ l, MvPolynomial.C (rho l)*gVar u i l*dVar u l j

def cPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (u : T) (i j : Fin N) : Poly T N :=
  ∑ l, gammaPoly z rho sigma u i l*dVar u l j*MvPolynomial.C (exp (z u*(sigma l-sigma i)/2))

def mPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (u : T) (j : Fin N) : Poly T N :=
  MvPolynomial.C (-(1/z u))*∑ l, MvPolynomial.C (rho l)*
    (wPoly z rho u l j+MvPolynomial.C (1+z u*sigma l)*cPoly z rho sigma u l j)

def nPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (u : T) (j : Fin N) : Poly T N :=
  ∑ l, MvPolynomial.C (rho l)*
    (MvPolynomial.C ((1+z u*((sigma j-sigma l)/2))/(z u)^2)*wPoly z rho u l j+
      MvPolynomial.C ((1+z u*sigma l+(z u*sigma l)^2/2)/(z u)^2+
        ((sigma j-sigma l)/2)*(1+z u*sigma l)/z u)*cPoly z rho sigma u l j)

def aPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (j : Fin N) : Poly T N :=
  MvPolynomial.C (Qppphys rho sigma j j)+∑ u,
    (MvPolynomial.C (Qppphys rho sigma j j)*mPoly z rho sigma u j+
      MvPolynomial.C (2*Real.pi^2*xi2 rho sigma/(vacMix rho sigma)^2)*nPoly z rho sigma u j)

def qpPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (i j : Fin N) : Poly T N :=
  MvPolynomial.C (Q0phys rho sigma i j)+∑ u,
    (MvPolynomial.C (Q0phys rho sigma i j)*mPoly z rho sigma u j+
      MvPolynomial.C (Qppphys rho sigma i i)*nPoly z rho sigma u j)

def qhatPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (s : ℝ) (i j : Fin N) : Poly T N :=
  MvPolynomial.C (exp (-s*edgeLo sigma i j))*
    (MvPolynomial.C ((1-s*sigma i-exp (-s*sigma i))/s^2)*qpPoly z rho sigma i j+
      MvPolynomial.C ((1-s*sigma i+(s*sigma i)^2/2-exp (-s*sigma i))/s^3)*aPoly z rho sigma j+
      ∑ u, (wPoly z rho u i j*MvPolynomial.C ((s+z u)⁻¹)+
        cPoly z rho sigma u i j*MvPolynomial.C (1-exp (-s*sigma i))*MvPolynomial.C s⁻¹))+
    ∑ u, cPoly z rho sigma u i j*MvPolynomial.C (exp (-s*edgeHi sigma i j))*MvPolynomial.C ((s+z u)⁻¹)

def firstPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (u : T) (i j : Fin N) : Poly T N :=
  (∑ l, dVar u i l*(MvPolynomial.C (if l = j then 1 else 0)-
    MvPolynomial.C (rho l)*MvPolynomial.C (exp (z u*edgeLo sigma j l))*qhatPoly z rho sigma (z u) j l))-
    MvPolynomial.C (2*Real.pi)*tauVar*MvPolynomial.C (K u i j)*MvPolynomial.C (z u)⁻¹

def secondPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (u : T) (i j : Fin N) : Poly T N :=
  MvPolynomial.C (2*Real.pi)*(∑ l, gVar u i l*(MvPolynomial.C (if l = j then 1 else 0)-
    MvPolynomial.C (rho l)*MvPolynomial.C (exp (z u*edgeLo sigma l j))*qhatPoly z rho sigma (z u) l j))-
    (aPoly z rho sigma j+MvPolynomial.C (z u)*qpPoly z rho sigma i j+
      ∑ v, MvPolynomial.C ((z u)^2*z v/(z u+z v))*cPoly z rho sigma v i j)*MvPolynomial.C ((z u)^2)⁻¹

def residualPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (i : AmpIndex T N) : Poly T N :=
  if i.1 then secondPoly z rho sigma i.2.1 i.2.2.1 i.2.2.2
  else firstPoly z rho sigma K i.2.1 i.2.2.1 i.2.2.2

omit [Fintype T] in
/-- Dt coordinate evaluation is literal, for all finite species/tail sets. -/
theorem eval_dVar (x : ℝ × (TailMatrix T N × TailMatrix T N)) (u : T) (i j : Fin N) :
    MvPolynomial.eval (pointValues x) (dVar u i j) = x.2.1 u i j := by
  simp [dVar,pointValues,amplitudeValues]

omit [Fintype T] in
/-- G coordinate evaluation is literal and uses no positivity hypothesis. -/
theorem eval_gVar (x : ℝ × (TailMatrix T N × TailMatrix T N)) (u : T) (i j : Fin N) :
    MvPolynomial.eval (pointValues x) (gVar u i j) = x.2.2 u i j := by
  simp [gVar,pointValues,amplitudeValues]

omit [Fintype T] in
/-- Coupling is an independent polynomial variable, not absorbed in amplitudes. -/
theorem eval_tauVar (x : ℝ × (TailMatrix T N × TailMatrix T N)) :
    MvPolynomial.eval (pointValues x) (tauVar : Poly T N) = x.1 := by
  simp [tauVar,pointValues]

omit [Fintype T] in
/-- The polynomial gamma is EXACTLY the actual finite physical dictionary. -/
theorem eval_gammaPoly (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) (u : T) (i j : Fin N) :
    MvPolynomial.eval (pointValues x) (gammaPoly z rho sigma u i j) = gam (z u) rho sigma (x.2.2 u) i j := by
  simp only [gammaPoly,map_sub,map_mul,MvPolynomial.eval_C,eval_gVar]
  unfold gam
  ring

omit [Fintype T] in
/-- True W evaluation, retaining the ordered finite matrix products. -/
theorem eval_wPoly (z : T → ℝ) (rho : Fin N → ℝ)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) (u : T) (i j : Fin N) :
    MvPolynomial.eval (pointValues x) (wPoly z rho u i j) = W z rho x.2.1 x.2.2 u i j := by
  simp only [wPoly,map_mul,map_sum,MvPolynomial.eval_C,eval_gVar,eval_dVar,W,Wt]

/-- True C evaluation, including all unequal-diameter edge coefficients. -/
theorem eval_cPoly (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) (u : T) (i j : Fin N) :
    MvPolynomial.eval (pointValues x) (cPoly z rho sigma u i j) =
      FMSA.ExactMSA.MultiTailMixture.C z rho sigma x.2.1 x.2.2 u i j := by
  simp only [cPoly,map_sum,map_mul,MvPolynomial.eval_C,eval_gammaPoly,eval_dVar,FMSA.ExactMSA.MultiTailMixture.C,Ct]

/-- The actual M moment has no amplitude denominator. -/
theorem eval_mPoly (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) (u : T) (j : Fin N) :
    MvPolynomial.eval (pointValues x) (mPoly z rho sigma u j) = mixM (z u) rho sigma (x.2.2 u) (x.2.1 u) j := by
  simp only [mPoly,map_mul,map_sum,map_add,MvPolynomial.eval_C,eval_wPoly,eval_cPoly,mixM,W,FMSA.ExactMSA.MultiTailMixture.C]

/-- The actual N moment has fixed-data coefficients only. -/
theorem eval_nPoly (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) (u : T) (j : Fin N) :
    MvPolynomial.eval (pointValues x) (nPoly z rho sigma u j) = mixN (z u) rho sigma (x.2.2 u) (x.2.1 u) j := by
  simp only [nPoly,map_sum,map_mul,map_add,MvPolynomial.eval_C,eval_wPoly,eval_cPoly,mixN,W,FMSA.ExactMSA.MultiTailMixture.C]

/-- True A evaluation, before using any BH root equation. -/
theorem eval_aPoly (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) (j : Fin N) :
    MvPolynomial.eval (pointValues x) (aPoly z rho sigma j) = amplitudeA z rho sigma x.2.1 x.2.2 j := by
  simp only [aPoly,map_add,map_sum,map_mul,MvPolynomial.eval_C,eval_mPoly,eval_nPoly,amplitudeA,mixDA]

/-- True Qp evaluation retains its distinct row/column physical coefficients. -/
theorem eval_qpPoly (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) (i j : Fin N) :
    MvPolynomial.eval (pointValues x) (qpPoly z rho sigma i j) = amplitudeQp z rho sigma x.2.1 x.2.2 i j := by
  simp only [qpPoly,map_add,map_sum,map_mul,MvPolynomial.eval_C,eval_mPoly,eval_nPoly,amplitudeQp,mixDqp]

/-- The real finite transform evaluated at any FIXED frequency is an honest
amplitude polynomial; this is exactly dressedQhat, with no root premise. -/
theorem eval_qhatPoly (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) (s : ℝ) (i j : Fin N) :
    MvPolynomial.eval (pointValues x) (qhatPoly z rho sigma s i j) = dressedQhat z rho sigma x.2.1 x.2.2 s i j := by
  simp only [qhatPoly,map_add,map_mul,map_sum,MvPolynomial.eval_C,eval_qpPoly,eval_aPoly,eval_wPoly,eval_cPoly,
    dressedQhat,Qhat,div_eq_mul_inv]

/-- First polynomial residual evaluation is the EXACT original first entry. -/
theorem eval_firstPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) (u : T) (i j : Fin N) :
    MvPolynomial.eval (pointValues x) (firstPoly z rho sigma K u i j) =
      (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K x).1 u i j := by
  simp only [firstPoly,map_sub,map_sum,map_mul,MvPolynomial.eval_C,eval_dVar,eval_qhatPoly,eval_tauVar,
    FMSA.ExactMSA.MultiTailMixture.residual,firstLHS,div_eq_mul_inv]

/-- Second polynomial residual evaluation is the EXACT original second entry. -/
theorem eval_secondPoly (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) (u : T) (i j : Fin N) :
    MvPolynomial.eval (pointValues x) (secondPoly z rho sigma u i j) =
      secondLHS z rho sigma x.2.1 x.2.2 u i j-secondRHS z rho sigma x.2.1 x.2.2 u i j := by
  simp only [secondPoly,map_sub,map_mul,map_sum,map_add,MvPolynomial.eval_C,eval_gVar,eval_qhatPoly,eval_aPoly,eval_qpPoly,eval_cPoly,
    secondLHS,secondRHS,div_eq_mul_inv]

/-- Every coordinate of the genuine residual is the evaluation of the literal
finite polynomial system, for ALL data and ALL amplitudes/couplings. -/
theorem eval_residualPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (x : ℝ × (TailMatrix T N × TailMatrix T N)) (i : AmpIndex T N) :
    MvPolynomial.eval (pointValues x) (residualPoly z rho sigma K i) =
      amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K x) i := by
  rcases i with ⟨b,u,i,j⟩
  cases b
  · simpa only [residualPoly,amplitudeValues,Bool.false_eq_true,ite_false] using eval_firstPoly z rho sigma K x u i j
  · simpa only [residualPoly,amplitudeValues,ite_true,FMSA.ExactMSA.MultiTailMixture.residual] using eval_secondPoly z rho sigma x u i j

omit [Fintype T] in
/-- The coordinate encoding loses no actual amplitude direction. No new
norm or quotient amplitude space is introduced by the polynomial interface. -/
theorem amplitude_values_injective : Function.Injective (amplitudeValues (T := T) (N := N)) := by
  intro a b he
  apply Prod.ext
  · funext u i j
    simpa only [amplitudeValues,Bool.false_eq_true,ite_false] using congrFun he (false,u,i,j)
  · funext u i j
    simpa only [amplitudeValues,ite_true] using congrFun he (true,u,i,j)

omit [Fintype T] in
/-- Vanishing of all polynomial coordinates is exactly vanishing of the
ORIGINAL full amplitude pair, including empty index families. -/
theorem amplitude_values_zero_iff (a : TailMatrix T N × TailMatrix T N) :
    (∀ i : AmpIndex T N, amplitudeValues a i = 0) ↔ a = 0 := by
  constructor
  · intro h
    apply amplitude_values_injective
    funext i
    rw [h i]
    rcases i with ⟨b,u,i,j⟩
    cases b <;> simp [amplitudeValues]
  · intro h
    subst a
    intro i
    rcases i with ⟨b,u,i,j⟩
    cases b <;> simp [amplitudeValues]

/-- Polynomial zero conditions are equivalent to the TRUE actual BH root,
not merely necessary constraints or a component-projected surrogate. -/
theorem actual_root_iff_polynomial_zeros (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (t : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    IsRoot z rho sigma (t • K) a.1 a.2 ↔
      ∀ i : AmpIndex T N, MvPolynomial.eval (pointValues (t,a)) (residualPoly z rho sigma K i) = 0 := by
  rw [← residual_eq_zero_iff z rho sigma K a.1 a.2 t,← amplitude_values_zero_iff]
  simp only [eval_residualPoly]

def specializeTime (b : ℝ) : Poly T N →+* MvPolynomial (AmpIndex T N) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => i.elim (MvPolynomial.C b) MvPolynomial.X)

def endpointPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (i : AmpIndex T N) : MvPolynomial (AmpIndex T N) ℝ :=
  specializeTime b (residualPoly z rho sigma K i)

omit [Fintype T] in
/-- Specializing coupling and then evaluating amplitudes is exactly the
original full evaluation at (b,a), including ALL real b and a. -/
theorem eval_specializeTime (b : ℝ) (a : TailMatrix T N × TailMatrix T N) (P : Poly T N) :
    MvPolynomial.eval (amplitudeValues a) (specializeTime b P) =
      MvPolynomial.eval (pointValues (b,a)) P := by
  have hh : (MvPolynomial.eval (amplitudeValues a)).comp (specializeTime b) =
      MvPolynomial.eval (pointValues (b,a)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [specializeTime]
    · intro i
      cases i <;> simp [specializeTime,pointValues]
  exact RingHom.congr_fun hh P

/-- Every specialized endpoint polynomial is a literal actual residual
coordinate, not a float/rationalized approximation of its physical data. -/
theorem eval_endpointPoly (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (b : ℝ) (a : TailMatrix T N × TailMatrix T N) (i : AmpIndex T N) :
    MvPolynomial.eval (amplitudeValues a) (endpointPoly z rho sigma K b i) =
      amplitudeValues (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (b,a)) i := by
  rw [endpointPoly,eval_specializeTime,eval_residualPoly]

/-- The genuine actual endpoint fiber is EXACTLY the common real zero set
of the specialized finite polynomial system. No finiteness is inferred. -/
theorem actual_endpoint_root_iff_polynomial_zeros (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (b : ℝ) (a : TailMatrix T N × TailMatrix T N) :
    IsRoot z rho sigma (b • K) a.1 a.2 ↔
      ∀ i : AmpIndex T N, MvPolynomial.eval (amplitudeValues a) (endpointPoly z rho sigma K b i) = 0 := by
  rw [actual_root_iff_polynomial_zeros]
  simp only [endpointPoly,eval_specializeTime]

end FMSA.Convergence.BHResidualPolynomials

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_dVar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_dVar

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_gVar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_gVar

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_tauVar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_tauVar

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_gammaPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_gammaPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_wPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_wPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_cPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_cPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_mPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_mPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_nPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_nPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_aPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_aPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_qpPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_qpPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_qhatPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_qhatPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_firstPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_firstPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_secondPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_secondPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_residualPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_residualPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.amplitude_values_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.amplitude_values_injective

/-- info: 'FMSA.Convergence.BHResidualPolynomials.amplitude_values_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.amplitude_values_zero_iff

/-- info: 'FMSA.Convergence.BHResidualPolynomials.actual_root_iff_polynomial_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.actual_root_iff_polynomial_zeros

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_specializeTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_specializeTime

/-- info: 'FMSA.Convergence.BHResidualPolynomials.eval_endpointPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.eval_endpointPoly

/-- info: 'FMSA.Convergence.BHResidualPolynomials.actual_endpoint_root_iff_polynomial_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHResidualPolynomials.actual_endpoint_root_iff_polynomial_zeros
