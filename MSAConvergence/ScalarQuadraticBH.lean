import MSAConvergence.BHFiniteFiberCertificates

/-! Exact quadratic reduction of the ACTUAL one-species finite-tail BH
system by X_u = Dt_u * G_u. No physical coefficient is approximated.
Equivalence requires nonzero Dt, discharged internally for active tails
at nonzero coupling/rates. Degree bounds do not assert finite fibers. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.ScalarQuadraticBH
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.BHFiniteFiberCertificates
variable {T : Type*} [Fintype T]

abbrev State (T : Type*) := (T → ℝ) × (T → ℝ)
abbrev Poly (T : Type*) := MvPolynomial (Bool × T) ℝ

def values (q : State T) (i : Bool × T) : ℝ := if i.1 then q.2 i.2 else q.1 i.2

def encode (a : TailMatrix T 1 × TailMatrix T 1) : State T :=
  (fun u => a.1 u 0 0, fun u => a.1 u 0 0*a.2 u 0 0)

def decode (q : State T) : TailMatrix T 1 × TailMatrix T 1 :=
  (fun u _ _ => q.1 u, fun u _ _ => q.2 u/q.1 u)

def dVar (u : T) : Poly T := MvPolynomial.X (false,u)
def xVar (u : T) : Poly T := MvPolynomial.X (true,u)

def wPoly (z : T → ℝ) (rho : Fin 1 → ℝ) (u : T) : Poly T :=
  MvPolynomial.C (2*Real.pi/z u*rho 0)*xVar u

def cPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) : Poly T :=
  dVar u-MvPolynomial.C (exp (-z u*sigma 0))*wPoly z rho u

def mPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) : Poly T :=
  MvPolynomial.C (-(1/z u)*rho 0)*
    (wPoly z rho u+MvPolynomial.C (1+z u*sigma 0)*cPoly z rho sigma u)

def nPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) : Poly T :=
  MvPolynomial.C (rho 0/(z u)^2)*
    (wPoly z rho u+MvPolynomial.C (1+z u*sigma 0+(z u*sigma 0)^2/2)*cPoly z rho sigma u)

def aPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) : Poly T :=
  MvPolynomial.C (Qppphys rho sigma 0 0)+∑ u,
    (MvPolynomial.C (Qppphys rho sigma 0 0)*mPoly z rho sigma u+
      MvPolynomial.C (2*Real.pi^2*xi2 rho sigma/(vacMix rho sigma)^2)*nPoly z rho sigma u)

def qpPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) : Poly T :=
  MvPolynomial.C (Q0phys rho sigma 0 0)+∑ u,
    (MvPolynomial.C (Q0phys rho sigma 0 0)*mPoly z rho sigma u+
      MvPolynomial.C (Qppphys rho sigma 0 0)*nPoly z rho sigma u)

def qhatPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (s : ℝ) : Poly T :=
  MvPolynomial.C ((1-s*sigma 0-exp (-s*sigma 0))/s^2)*qpPoly z rho sigma+
    MvPolynomial.C ((1-s*sigma 0+(s*sigma 0)^2/2-exp (-s*sigma 0))/s^3)*aPoly z rho sigma+
    (∑ u, (wPoly z rho u*MvPolynomial.C ((s+z u)⁻¹)+
      cPoly z rho sigma u*MvPolynomial.C ((1-exp (-s*sigma 0))/s)))+
    ∑ u, cPoly z rho sigma u*MvPolynomial.C (exp (-s*sigma 0)/(s+z u))

def factorPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) : Poly T :=
  1-MvPolynomial.C (rho 0)*qhatPoly z rho sigma (z u)

def sourcePoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) : Poly T :=
  (aPoly z rho sigma+MvPolynomial.C (z u)*qpPoly z rho sigma+
    ∑ v, MvPolynomial.C ((z u)^2*z v/(z u+z v))*cPoly z rho sigma v)*
      MvPolynomial.C ((z u)^2)⁻¹

def firstPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (u : T) : Poly T :=
  dVar u*factorPoly z rho sigma u-MvPolynomial.C (2*Real.pi*b*K u 0 0/z u)

def secondPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) : Poly T :=
  MvPolynomial.C (2*Real.pi)*xVar u*factorPoly z rho sigma u-dVar u*sourcePoly z rho sigma u

def ReducedRoot (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (q : State T) : Prop :=
  ∀ u, MvPolynomial.eval (values q) (firstPoly z rho sigma K b u) = 0 ∧
    MvPolynomial.eval (values q) (secondPoly z rho sigma u) = 0

omit [Fintype T] in
/-- Nonzero Dt makes X=Dt*G an invertible change of the original amplitudes. -/
theorem decode_encode (a : TailMatrix T 1 × TailMatrix T 1)
    (hD : ∀ u, a.1 u 0 0 ≠ 0) : decode (encode a) = a := by
  apply Prod.ext <;> funext u i j <;> fin_cases i <;> fin_cases j
  · rfl
  · simp [decode,encode,mul_div_cancel_left₀, hD]

omit [Fintype T] in
/-- Every reduced state with nonzero first coordinates has its exact inverse. -/
theorem encode_decode (q : State T) (hD : ∀ u, q.1 u ≠ 0) : encode (decode q) = q := by
  apply Prod.ext <;> funext u
  · rfl
  · change q.1 u*(q.2 u/q.1 u) = q.2 u
    field_simp [hD u]

omit [Fintype T] in
/-- Evaluation uses original Dt coordinates and the literal product Dt*G. -/
theorem eval_dVar (q : State T) (u : T) :
    MvPolynomial.eval (values q) (dVar u) = q.1 u := by simp [dVar,values]

omit [Fintype T] in
/-- The second coordinate is X, not the old G or an approximated transform. -/
theorem eval_xVar (q : State T) (u : T) :
    MvPolynomial.eval (values q) (xVar u) = q.2 u := by simp [xVar,values]

omit [Fintype T] in
/-- The linear W polynomial evaluates to the ACTUAL scalar W at every amplitude. -/
theorem eval_wPoly (z : T → ℝ) (rho : Fin 1 → ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) (u : T) :
    MvPolynomial.eval (values (encode a)) (wPoly z rho u) = W z rho a.1 a.2 u 0 0 := by
  simp [wPoly,eval_xVar,encode,W,Wt]
  ring

omit [Fintype T] in
/-- C is affine in Dt,X, including its exact physical exponential coefficient. -/
theorem eval_cPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) (u : T) :
    MvPolynomial.eval (values (encode a)) (cPoly z rho sigma u) =
      FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2 u 0 0 := by
  simp only [cPoly,map_sub,map_mul,MvPolynomial.eval_C,eval_dVar,eval_wPoly]
  simp [encode,FMSA.ExactMSA.MultiTailMixture.C,Ct,gam,sigMix,W,Wt]
  ring

omit [Fintype T] in
/-- The full scalar M moment is exactly linearized, without sign assumptions. -/
theorem eval_mPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) (u : T) :
    MvPolynomial.eval (values (encode a)) (mPoly z rho sigma u) =
      mixM (z u) rho sigma (a.2 u) (a.1 u) 0 := by
  simp [mPoly,eval_wPoly,eval_cPoly,mixM,W,FMSA.ExactMSA.MultiTailMixture.C]
  ring

omit [Fintype T] in
/-- The full scalar N moment is linearized with the original diameter terms. -/
theorem eval_nPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) (u : T) :
    MvPolynomial.eval (values (encode a)) (nPoly z rho sigma u) =
      mixN (z u) rho sigma (a.2 u) (a.1 u) 0 := by
  simp [nPoly,eval_wPoly,eval_cPoly,mixN,W,FMSA.ExactMSA.MultiTailMixture.C]
  ring

/-- Actual A retains every tail, including repeated rates and empty families. -/
theorem eval_aPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) :
    MvPolynomial.eval (values (encode a)) (aPoly z rho sigma) = amplitudeA z rho sigma a.1 a.2 0 := by
  simp only [aPoly,map_add,map_sum,map_mul,MvPolynomial.eval_C,eval_mPoly,eval_nPoly,amplitudeA,mixDA]

/-- Actual Qp is affine in the reduced coordinates. -/
theorem eval_qpPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) :
    MvPolynomial.eval (values (encode a)) (qpPoly z rho sigma) = amplitudeQp z rho sigma a.1 a.2 0 0 := by
  simp only [qpPoly,map_add,map_sum,map_mul,MvPolynomial.eval_C,eval_mPoly,eval_nPoly,amplitudeQp,mixDqp]

/-- The entire actual finite transform at any FIXED frequency is affine. -/
theorem eval_qhatPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) (s : ℝ) :
    MvPolynomial.eval (values (encode a)) (qhatPoly z rho sigma s) = dressedQhat z rho sigma a.1 a.2 s 0 0 := by
  simp only [qhatPoly,map_add,map_mul,map_sum,MvPolynomial.eval_C,eval_qpPoly,eval_aPoly,
    eval_wPoly,eval_cPoly,dressedQhat,Qhat,edgeLo,edgeHi,sub_self,zero_div,mul_zero,exp_zero,one_mul]
  simp only [show (sigma 0+sigma 0)/2 = sigma 0 by ring,div_eq_mul_inv]
  ring

/-- The reduced first factor is the literal scalar BH factor. -/
theorem eval_factorPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) (u : T) :
    MvPolynomial.eval (values (encode a)) (factorPoly z rho sigma u) =
      1-rho 0*dressedQhat z rho sigma a.1 a.2 (z u) 0 0 := by
  simp [factorPoly,eval_qhatPoly]

/-- The reduced source is the ORIGINAL second BH right side. -/
theorem eval_sourcePoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) (u : T) :
    MvPolynomial.eval (values (encode a)) (sourcePoly z rho sigma u) = secondRHS z rho sigma a.1 a.2 u 0 0 := by
  simp only [sourcePoly,map_mul,map_add,map_sum,MvPolynomial.eval_C,map_inv₀,eval_aPoly,
    eval_qpPoly,eval_cPoly,secondRHS,div_eq_mul_inv]

/-- First reduced residual is EXACTLY the original first scalar residual. -/
theorem eval_firstPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (a : TailMatrix T 1 × TailMatrix T 1) (u : T) :
    MvPolynomial.eval (values (encode a)) (firstPoly z rho sigma K b u) =
      (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (b,a)).1 u 0 0 := by
  simp only [firstPoly,map_sub,map_mul,MvPolynomial.eval_C,eval_dVar,eval_factorPoly]
  simp [encode,FMSA.ExactMSA.MultiTailMixture.residual,firstLHS,edgeLo]

/-- Second reduced residual is Dt TIMES the original second residual.
No direction of equivalence discards this multiplier without proving Dt nonzero. -/
theorem eval_secondPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) (u : T) :
    MvPolynomial.eval (values (encode a)) (secondPoly z rho sigma u) =
      a.1 u 0 0*(secondLHS z rho sigma a.1 a.2 u 0 0-secondRHS z rho sigma a.1 a.2 u 0 0) := by
  simp only [secondPoly,map_sub,map_mul,MvPolynomial.eval_C,eval_dVar,eval_xVar,
    eval_factorPoly,eval_sourcePoly]
  simp [encode,secondLHS,edgeLo]
  ring

/-- Exact root equivalence on the nonzero-Dt chart; no canonical premise. -/
theorem actual_root_iff_reduced_of_nonzero
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1) (b : ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) (hD : ∀ u, a.1 u 0 0 ≠ 0) :
    IsRoot z rho sigma (b • K) a.1 a.2 ↔ ReducedRoot z rho sigma K b (encode a) := by
  constructor
  · intro h u
    constructor
    · rw [eval_firstPoly]
      simp [FMSA.ExactMSA.MultiTailMixture.residual,h.1 u 0 0,mul_assoc]
    · rw [eval_secondPoly,h.2 u 0 0,sub_self,mul_zero]
  · intro h
    constructor
    · intro u i j
      fin_cases i
      fin_cases j
      have he := (h u).1
      rw [eval_firstPoly] at he
      simpa [FMSA.ExactMSA.MultiTailMixture.residual,sub_eq_zero,mul_assoc] using he
    · intro u i j
      fin_cases i
      fin_cases j
      have he := (h u).2
      rw [eval_secondPoly] at he
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (hD u))

/-- Nonzero coupling, rate and active strength FORCE Dt nonzero at every
actual scalar root. This excludes spurious roots from the reverse substitution. -/
theorem actual_dt_ne_zero_of_active
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (hb : b ≠ 0) (a : TailMatrix T 1 × TailMatrix T 1)
    (ha : IsRoot z rho sigma (b • K) a.1 a.2) (u : T) (hz : z u ≠ 0) (hK : K u 0 0 ≠ 0) :
    a.1 u 0 0 ≠ 0 := by
  have hn : 2*Real.pi*b*K u 0 0/z u ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hb) hK) hz
  intro hzero
  have he := scalar_first_factor_equation z rho sigma K b a ha u
  rw [hzero,zero_mul] at he
  exact hn he.symm

/-- Every reduced active root also has nonzero Dt, from ITS first equation. -/
theorem reduced_dt_ne_zero_of_active
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (hb : b ≠ 0) (q : State T) (hq : ReducedRoot z rho sigma K b q)
    (u : T) (hz : z u ≠ 0) (hK : K u 0 0 ≠ 0) : q.1 u ≠ 0 := by
  have hn : 2*Real.pi*b*K u 0 0/z u ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hb) hK) hz
  intro hzero
  have he := (hq u).1
  simp only [firstPoly,map_sub,map_mul,MvPolynomial.eval_C,eval_dVar,hzero,zero_mul,zero_sub,neg_eq_zero] at he
  exact hn he

/-- All actual roots map to reduced quadratic roots, including inactive tails
and zero coupling; only the reverse map needs nonzero-Dt control. -/
theorem actual_root_gives_reduced
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1) (b : ℝ)
    (a : TailMatrix T 1 × TailMatrix T 1) (ha : IsRoot z rho sigma (b • K) a.1 a.2) :
    ReducedRoot z rho sigma K b (encode a) := by
  intro u
  constructor
  · rw [eval_firstPoly]
    simp [FMSA.ExactMSA.MultiTailMixture.residual,ha.1 u 0 0,mul_assoc]
  · rw [eval_secondPoly,ha.2 u 0 0,sub_self,mul_zero]

/-- Reduced roots recover TRUE original roots for all active tails at nonzero
coupling/rates. No sign, density, diameter, vacancy or distinct-rate premise. -/
theorem reduced_root_decodes_actual
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (hb : b ≠ 0) (hz : ∀ u, z u ≠ 0) (hK : ∀ u, K u 0 0 ≠ 0)
    (q : State T) (hq : ReducedRoot z rho sigma K b q) :
    IsRoot z rho sigma (b • K) (decode q).1 (decode q).2 := by
  have hD := fun u => reduced_dt_ne_zero_of_active z rho sigma K b hb q hq u (hz u) (hK u)
  apply (actual_root_iff_reduced_of_nonzero z rho sigma K b (decode q) hD).mpr
  simpa only [encode_decode q hD] using hq

/-- The original active endpoint fiber is exactly the decoded reduced fiber.
This is a genuine root-set correspondence, not a count of equations. -/
theorem active_fiber_eq_decode_image
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (hb : b ≠ 0) (hz : ∀ u, z u ≠ 0) (hK : ∀ u, K u 0 0 ≠ 0) :
    {a : TailMatrix T 1 × TailMatrix T 1 | IsRoot z rho sigma (b • K) a.1 a.2} =
      decode '' {q : State T | ReducedRoot z rho sigma K b q} := by
  ext a
  constructor
  · intro ha
    exact ⟨encode a,actual_root_gives_reduced z rho sigma K b a ha,
      decode_encode a (fun u => actual_dt_ne_zero_of_active z rho sigma K b hb a ha u (hz u) (hK u))⟩
  · rintro ⟨q,hq,rfl⟩
    exact reduced_root_decodes_actual z rho sigma K b hb hz hK q hq

/-- Finite reduced fibers transfer to the actual endpoint. Finiteness must
still be PROVED by elimination or another argument; quadratic degree alone
is not that proof. -/
theorem active_fiber_finite_of_reduced
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (hb : b ≠ 0) (hz : ∀ u, z u ≠ 0) (hK : ∀ u, K u 0 0 ≠ 0)
    (hf : {q : State T | ReducedRoot z rho sigma K b q}.Finite) :
    {a : TailMatrix T 1 × TailMatrix T 1 | IsRoot z rho sigma (b • K) a.1 a.2}.Finite := by
  rw [active_fiber_eq_decode_image z rho sigma K b hb hz hK]
  exact hf.image decode

omit [Fintype T] in
private theorem degree_add_le {p q : Poly T} {n : ℕ}
    (hp : p.totalDegree ≤ n) (hq : q.totalDegree ≤ n) : (p+q).totalDegree ≤ n :=
  (MvPolynomial.totalDegree_add _ _).trans (max_le hp hq)

omit [Fintype T] in
private theorem degree_sub_le {p q : Poly T} {n : ℕ}
    (hp : p.totalDegree ≤ n) (hq : q.totalDegree ≤ n) : (p-q).totalDegree ≤ n :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le hp hq)

omit [Fintype T] in
private theorem degree_cmul_le (c : ℝ) {p : Poly T} {n : ℕ} (hp : p.totalDegree ≤ n) :
    (MvPolynomial.C c*p).totalDegree ≤ n := by
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hp)

omit [Fintype T] in
private theorem degree_mulc_le (c : ℝ) {p : Poly T} {n : ℕ} (hp : p.totalDegree ≤ n) :
    (p*MvPolynomial.C c).totalDegree ≤ n := by
  rw [mul_comm]
  exact degree_cmul_le c hp

omit [Fintype T] in
private theorem degree_mul_le {p q : Poly T} {m n : ℕ}
    (hp : p.totalDegree ≤ m) (hq : q.totalDegree ≤ n) : (p*q).totalDegree ≤ m+n :=
  (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp hq)

private theorem degree_sum_le (f : T → Poly T) {n : ℕ} (hf : ∀ u, (f u).totalDegree ≤ n) :
    (∑ u, f u).totalDegree ≤ n := by
  classical
  refine Finset.induction_on (Finset.univ : Finset T) ?_ ?_
  · simp
  · intro u s hu hs
    rw [Finset.sum_insert hu]
    exact degree_add_le (hf u) hs

/-- Every W coordinate is linear in X; constants stay exact REAL data. -/
theorem degree_wPoly (z : T → ℝ) (rho : Fin 1 → ℝ) (u : T) :
    (wPoly z rho u).totalDegree ≤ 1 := by
  unfold wPoly
  apply degree_cmul_le
  simp [xVar]

/-- C has degree at most one in Dt,X, even at degenerate physical data. -/
theorem degree_cPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) :
    (cPoly z rho sigma u).totalDegree ≤ 1 := by
  exact degree_sub_le (by simp [dVar]) (degree_cmul_le _ (degree_wPoly z rho u))

/-- M is affine in the reduced amplitudes. -/
theorem degree_mPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) :
    (mPoly z rho sigma u).totalDegree ≤ 1 := by
  exact degree_cmul_le _ (degree_add_le (degree_wPoly z rho u)
    (degree_cmul_le _ (degree_cPoly z rho sigma u)))

/-- N is affine in the reduced amplitudes. -/
theorem degree_nPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) :
    (nPoly z rho sigma u).totalDegree ≤ 1 := by
  exact degree_cmul_le _ (degree_add_le (degree_wPoly z rho u)
    (degree_cmul_le _ (degree_cPoly z rho sigma u)))

/-- The ENTIRE finite-tail A dictionary has total degree at most one. -/
theorem degree_aPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) :
    (aPoly z rho sigma).totalDegree ≤ 1 := by
  apply degree_add_le (by simp)
  apply degree_sum_le
  intro u
  exact degree_add_le (degree_cmul_le _ (degree_mPoly z rho sigma u))
    (degree_cmul_le _ (degree_nPoly z rho sigma u))

/-- The ENTIRE finite-tail Qp dictionary has total degree at most one. -/
theorem degree_qpPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) :
    (qpPoly z rho sigma).totalDegree ≤ 1 := by
  apply degree_add_le (by simp)
  apply degree_sum_le
  intro u
  exact degree_add_le (degree_cmul_le _ (degree_mPoly z rho sigma u))
    (degree_cmul_le _ (degree_nPoly z rho sigma u))

/-- At every FIXED frequency the full scalar transform remains affine. -/
theorem degree_qhatPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (s : ℝ) :
    (qhatPoly z rho sigma s).totalDegree ≤ 1 := by
  apply degree_add_le
  · apply degree_add_le
    · exact degree_add_le (degree_cmul_le _ (degree_qpPoly z rho sigma))
        (degree_cmul_le _ (degree_aPoly z rho sigma))
    · apply degree_sum_le
      intro u
      exact degree_add_le (degree_mulc_le _ (degree_wPoly z rho u))
        (degree_mulc_le _ (degree_cPoly z rho sigma u))
  · apply degree_sum_le
    intro u
    exact degree_mulc_le _ (degree_cPoly z rho sigma u)

/-- The honest rate factor has degree at most one, with no zero-free premise. -/
theorem degree_factorPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) :
    (factorPoly z rho sigma u).totalDegree ≤ 1 := by
  exact degree_sub_le (by simp) (degree_cmul_le _ (degree_qhatPoly z rho sigma (z u)))

/-- The honest second source is affine; it has no amplitude denominator. -/
theorem degree_sourcePoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) :
    (sourcePoly z rho sigma u).totalDegree ≤ 1 := by
  apply degree_mulc_le
  apply degree_add_le
  · exact degree_add_le (degree_aPoly z rho sigma) (degree_cmul_le _ (degree_qpPoly z rho sigma))
  · apply degree_sum_le
    intro v
    exact degree_cmul_le _ (degree_cPoly z rho sigma v)

/-- Every first reduced BH equation is an ACTUAL quadratic polynomial,
not a floating degree estimate or a generic finite-fiber assertion. -/
theorem degree_firstPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (u : T) : (firstPoly z rho sigma K b u).totalDegree ≤ 2 := by
  apply degree_sub_le _ (by simp)
  exact degree_mul_le (by simp [dVar]) (degree_factorPoly z rho sigma u)

/-- Every second reduced BH equation has degree at most two in Dt,X.
Only the amplitudes are variables; coupling is fixed for an endpoint fiber. -/
theorem degree_secondPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (u : T) :
    (secondPoly z rho sigma u).totalDegree ≤ 2 := by
  apply degree_sub_le
  · apply degree_mul_le _ (degree_factorPoly z rho sigma u)
    apply degree_cmul_le
    simp [xVar]
  · exact degree_mul_le (by simp [dVar]) (degree_sourcePoly z rho sigma u)

/-- The inverse image identity makes the correspondence genuinely two-sided
for all active scalar tails, without an assumed finite root count. -/
theorem reduced_fiber_eq_encode_image
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (hb : b ≠ 0) (hz : ∀ u, z u ≠ 0) (hK : ∀ u, K u 0 0 ≠ 0) :
    {q : State T | ReducedRoot z rho sigma K b q} =
      encode '' {a : TailMatrix T 1 × TailMatrix T 1 | IsRoot z rho sigma (b • K) a.1 a.2} := by
  ext q
  constructor
  · intro hq
    exact ⟨decode q,reduced_root_decodes_actual z rho sigma K b hb hz hK q hq,
      encode_decode q (fun u => reduced_dt_ne_zero_of_active z rho sigma K b hb q hq u (hz u) (hK u))⟩
  · rintro ⟨a,ha,rfl⟩
    exact actual_root_gives_reduced z rho sigma K b a ha

/-- Global finiteness is equivalent for the actual and quadratic active fibers.
This does not assert either condition holds at every physical state. -/
theorem active_fiber_finite_iff_reduced
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (hb : b ≠ 0) (hz : ∀ u, z u ≠ 0) (hK : ∀ u, K u 0 0 ≠ 0) :
    {a : TailMatrix T 1 × TailMatrix T 1 | IsRoot z rho sigma (b • K) a.1 a.2}.Finite ↔
      {q : State T | ReducedRoot z rho sigma K b q}.Finite := by
  constructor
  · intro ha
    rw [reduced_fiber_eq_encode_image z rho sigma K b hb hz hK]
    exact ha.image encode
  · exact active_fiber_finite_of_reduced z rho sigma K b hb hz hK

/-- A finite QUADRATIC endpoint fiber supplies the whole limit at a true
approaching actual cluster, including singular roots. The old prefix may
contain zero coupling; nonzero coupling is used only at the endpoint. -/
theorem actual_cluster_limit_of_reduced_finite_fiber
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (hb : 0 < b) (hz : ∀ u, z u ≠ 0) (hK : ∀ u, K u 0 0 ≠ 0)
    (p : ℝ → TailMatrix T 1 × TailMatrix T 1) (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (a : TailMatrix T 1 × TailMatrix T 1) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (hf : {q : State T | ReducedRoot z rho sigma K b q}.Finite) :
    Tendsto p (𝓝[<] b) (𝓝 a) :=
  FMSA.Convergence.IsolatedEndpointLimits.actual_finite_fiber_cluster_has_limit
    z rho sigma K p b hb hp hroot a u hu ht ha
    (active_fiber_finite_of_reduced z rho sigma K b hb.ne' hz hK hf)

/-- Zero Dt,X solves the multiplied system at zero coupling for ANY data.
This records the chart degeneracy rather than silently asserting equivalence. -/
theorem reduced_zero_at_zero_coupling
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1) :
    ReducedRoot z rho sigma K 0 (0 : State T) := by
  intro u
  simp [firstPoly,secondPoly,eval_dVar,eval_xVar]

/-- A concrete physical vacuum counterexample to unconditional reverse
substitution: z=sigma=1 and tau=0 require true G=2, but decode(0,0) has G=0. -/
theorem decoded_zero_not_actual_at_vacuum
    (K : TailMatrix T 1) (u : T) :
    ¬IsRoot (fun _ : T => 1) 0 (fun _ : Fin 1 => 1) (0 • K)
      (decode (0 : State T)).1 (decode (0 : State T)).2 := by
  intro h
  have he := ((nonlinearRoot_zero_density_iff (fun _ : T => 1) (fun _ : Fin 1 => 1)
    (0 • K) (decode (0 : State T)).1 (decode (0 : State T)).2 (by intro _; norm_num)).mp h).2 u 0 0
  norm_num [decode,edgeHi] at he

/-- Verified spurious quadratic root at zero coupling; the active/nonzero
conditions of the two-sided correspondence cannot simply be dropped. -/
theorem zero_coupling_reduction_has_spurious_root (K : TailMatrix T 1) (u : T) :
    ReducedRoot (fun _ : T => 1) 0 (fun _ : Fin 1 => 1) K 0 (0 : State T) ∧
      ¬IsRoot (fun _ : T => 1) 0 (fun _ : Fin 1 => 1) (0 • K)
        (decode (0 : State T)).1 (decode (0 : State T)).2 :=
  ⟨reduced_zero_at_zero_coupling _ _ _ _,decoded_zero_not_actual_at_vacuum K u⟩

end FMSA.Convergence.ScalarQuadraticBH

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.decode_encode

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.encode_decode

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_dVar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_dVar

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_xVar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_xVar

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_wPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_wPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_cPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_cPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_mPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_mPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_nPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_nPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_aPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_aPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_qpPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_qpPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_qhatPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_qhatPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_factorPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_factorPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_sourcePoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_sourcePoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_firstPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_firstPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.eval_secondPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.eval_secondPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.actual_root_iff_reduced_of_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.actual_root_iff_reduced_of_nonzero

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.actual_dt_ne_zero_of_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.actual_dt_ne_zero_of_active

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.reduced_dt_ne_zero_of_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.reduced_dt_ne_zero_of_active

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.actual_root_gives_reduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.actual_root_gives_reduced

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.reduced_root_decodes_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.reduced_root_decodes_actual

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.active_fiber_eq_decode_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.active_fiber_eq_decode_image

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.active_fiber_finite_of_reduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.active_fiber_finite_of_reduced

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.degree_wPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.degree_wPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.degree_cPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.degree_cPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.degree_mPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.degree_mPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.degree_nPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.degree_nPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.degree_aPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.degree_aPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.degree_qpPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.degree_qpPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.degree_qhatPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.degree_qhatPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.degree_factorPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.degree_factorPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.degree_sourcePoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.degree_sourcePoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.degree_firstPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.degree_firstPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.degree_secondPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.degree_secondPoly

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.reduced_fiber_eq_encode_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.reduced_fiber_eq_encode_image

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.active_fiber_finite_iff_reduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.active_fiber_finite_iff_reduced

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.actual_cluster_limit_of_reduced_finite_fiber' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.actual_cluster_limit_of_reduced_finite_fiber

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.reduced_zero_at_zero_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.reduced_zero_at_zero_coupling

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.decoded_zero_not_actual_at_vacuum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.decoded_zero_not_actual_at_vacuum

/-- info: 'FMSA.Convergence.ScalarQuadraticBH.zero_coupling_reduction_has_spurious_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarQuadraticBH.zero_coupling_reduction_has_spurious_root
