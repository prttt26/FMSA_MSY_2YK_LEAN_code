import MSAConvergence.BHResidualPolynomials

/-! Checkable coordinate-elimination identities for actual BH endpoint
fibers. Certificate hypotheses are explicit proof DATA, never new axioms
or an assertion that a square polynomial system is automatically finite. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.BHFiniteFiberCertificates
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.IsolatedEndpointLimits
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.MaximalCanonicalBranch
variable {N : ℕ} {T : Type*} [Fintype T]

abbrev FiberPoly (T : Type*) (N : ℕ) := MvPolynomial (AmpIndex T N) ℝ

def coordinatePolynomial (P : Polynomial ℝ) (i : AmpIndex T N) : FiberPoly T N :=
  P.eval₂ MvPolynomial.C (MvPolynomial.X i)

omit [Fintype T] in
/-- A univariate coordinate eliminant is evaluated at the TRUE original
amplitude coordinate, with no rationalization of physical coefficients. -/
theorem eval_coordinatePolynomial (P : Polynomial ℝ) (i : AmpIndex T N)
    (a : TailMatrix T N × TailMatrix T N) :
    MvPolynomial.eval (amplitudeValues a) (coordinatePolynomial P i) = P.eval (amplitudeValues a i) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [coordinatePolynomial,Polynomial.eval₂_add,map_add,Polynomial.eval_add] using congrArg₂ (·+·) hP hQ
  | monomial n r => simp [coordinatePolynomial,Polynomial.eval₂_monomial,Polynomial.eval_monomial]

/-- Nonzero univariate annihilators for EVERY actual amplitude coordinate
make a set of amplitude pairs finite, regardless of repeated roots or
Jacobian rank. This is a proved finite-root/product argument. -/
theorem finite_set_of_coordinate_annihilators
    (S : Set (TailMatrix T N × TailMatrix T N)) (P : AmpIndex T N → Polynomial ℝ)
    (hP : ∀ i, P i ≠ 0)
    (hroot : ∀ a ∈ S, ∀ i, (P i).eval (amplitudeValues a i) = 0) : S.Finite := by
  classical
  let A := fun i : AmpIndex T N => {x : ℝ // Polynomial.IsRoot (P i) x}
  letI : ∀ i : AmpIndex T N, Fintype (A i) := fun i => (Polynomial.finite_setOf_isRoot (hP i)).fintype
  let f : S → ∀ i : AmpIndex T N, A i := fun a i => ⟨amplitudeValues a.val i,hroot a.val a.property i⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply amplitude_values_injective
    funext i
    exact congrArg Subtype.val (congrFun h i)
  letI : Finite S := Finite.of_injective f hf
  exact Set.toFinite S

/-- Exact polynomial DATA for coordinate elimination. A saturation factor
is allowed; its nonvanishing on the relevant roots must be proved separately.
Each identity is an equality of actual MvPolynomials and can be independently
checked by normalization or a symbolic algebra certificate. -/
structure CoordinateFiberCertificate (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (b : ℝ) where
  eliminant : AmpIndex T N → Polynomial ℝ
  nonzero : ∀ i, eliminant i ≠ 0
  saturation : FiberPoly T N
  multiplier : AmpIndex T N → AmpIndex T N → FiberPoly T N
  identity : ∀ i, saturation*coordinatePolynomial (eliminant i) i =
    ∑ j, multiplier i j*endpointPoly z rho sigma K b j

/-- Actual BH roots annihilate certified eliminants whenever the exact
saturation factor is nonzero. No finiteness conclusion is assumed. -/
theorem certificate_coordinate_zero (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (b : ℝ) (C : CoordinateFiberCertificate z rho sigma K b)
    (a : TailMatrix T N × TailMatrix T N) (ha : IsRoot z rho sigma (b • K) a.1 a.2)
    (hsat : MvPolynomial.eval (amplitudeValues a) C.saturation ≠ 0) :
    ∀ i, (C.eliminant i).eval (amplitudeValues a i) = 0 := by
  have hroot := (actual_endpoint_root_iff_polynomial_zeros z rho sigma K b a).mp ha
  intro i
  have hi := congrArg (MvPolynomial.eval (amplitudeValues a)) (C.identity i)
  simp only [map_mul,eval_coordinatePolynomial,map_sum,hroot,mul_zero,Finset.sum_const_zero] at hi
  exact (mul_eq_zero.mp hi).resolve_left hsat

/-- A unit-saturation certificate proves the ENTIRE actual endpoint root
fiber finite. Finiteness is derived from the literal identities, not supplied. -/
theorem actual_fiber_finite_of_certificate (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (b : ℝ) (C : CoordinateFiberCertificate z rho sigma K b)
    (hC : C.saturation = 1) :
    {a : TailMatrix T N × TailMatrix T N | IsRoot z rho sigma (b • K) a.1 a.2}.Finite := by
  apply finite_set_of_coordinate_annihilators _ C.eliminant C.nonzero
  intro a ha
  exact certificate_coordinate_zero z rho sigma K b C a ha (by simp [hC])

/-- Saturated identities prove finiteness ONLY on the relevant actual
canonical-closure fiber when nonvanishing is certified there. Other algebraic
components are not silently required to be finite. -/
theorem canonical_fiber_finite_of_certificate (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (b : ℝ) (C : CoordinateFiberCertificate z rho sigma K b)
    (hsat : ∀ a : TailMatrix T N × TailMatrix T N, IsRoot z rho sigma (b • K) a.1 a.2 →
      a ∈ closure (canonicalAmplitudes z rho sigma) → MvPolynomial.eval (amplitudeValues a) C.saturation ≠ 0) :
    {a : TailMatrix T N × TailMatrix T N |
      IsRoot z rho sigma (b • K) a.1 a.2 ∧ a ∈ closure (canonicalAmplitudes z rho sigma)}.Finite := by
  apply finite_set_of_coordinate_annihilators _ C.eliminant C.nonzero
  intro a ha
  exact certificate_coordinate_zero z rho sigma K b C a ha.1 (hsat a ha.1 ha.2)

/-- Exact unit-saturation elimination identities give the full endpoint
limit of an actual approaching cluster, including SINGULAR roots, without
any assumed finiteness, Jacobian inverse, or full endpoint limit. -/
theorem actual_cluster_limit_of_certificate (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (C : CoordinateFiberCertificate z rho sigma K b) (hC : C.saturation = 1) :
    Tendsto p (𝓝[<] b) (𝓝 a) :=
  actual_finite_fiber_cluster_has_limit z rho sigma K p b hb hp hroot a u hu ht ha
    (actual_fiber_finite_of_certificate z rho sigma K b C hC)

/-- The same complete singular-cluster limit conclusion needs only a
certificate saturated away from zero on the actual canonical-closure roots. -/
theorem canonical_cluster_limit_of_certificate (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (a : TailMatrix T N × TailMatrix T N) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Ico 0 b) (ht : Tendsto u atTop (𝓝 b))
    (ha : Tendsto (fun n => p (u n)) atTop (𝓝 a))
    (C : CoordinateFiberCertificate z rho sigma K b)
    (hsat : ∀ d : TailMatrix T N × TailMatrix T N, IsRoot z rho sigma (b • K) d.1 d.2 →
      d ∈ closure (canonicalAmplitudes z rho sigma) → MvPolynomial.eval (amplitudeValues d) C.saturation ≠ 0) :
    Tendsto p (𝓝[<] b) (𝓝 a) :=
  canonical_finite_fiber_cluster_has_limit z rho sigma K p b hb hp hroot hcanon a u hu ht ha
    (canonical_fiber_finite_of_certificate z rho sigma K b C hsat)

/-- For the already CONSTRUCTED physical scalar maximal branch, exact
saturated elimination data discharge the remaining finite-fiber premise and
give its full actual physical Fourier-zero limiting root. No amplitude bound
or limit is supplied; the certificate identities/nonvanishing stay explicit. -/
theorem scalar_maximal_limit_of_certificate
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i) (K : TailMatrix T 1)
    (hv : vacMix rho sigma ≠ 0) (seed : TailMatrix T 1 × TailMatrix T 1)
    (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤)
    (C : CoordinateFiberCertificate z rho sigma K M.bound.toReal)
    (hsat : ∀ a : TailMatrix T 1 × TailMatrix T 1, IsRoot z rho sigma (M.bound.toReal • K) a.1 a.2 →
      a ∈ closure (canonicalAmplitudes z rho sigma) → MvPolynomial.eval (amplitudeValues a) C.saturation ≠ 0) :
    ∃ a : TailMatrix T 1 × TailMatrix T 1, IsRoot z rho sigma (M.bound.toReal • K) a.1 a.2 ∧
      a ∈ closure (canonicalAmplitudes z rho sigma) ∧ a ∉ canonicalAmplitudes z rho sigma ∧
      Tendsto M.path (𝓝[<] M.bound.toReal) (𝓝 a) ∧
      ∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2) k).det = 0 :=
  scalar_maximal_limit_of_finite_canonical_fiber z hz rho sigma hsigma hrho K hv seed M hfinite
    (canonical_fiber_finite_of_certificate z rho sigma K M.bound.toReal C hsat)

/-- The exact scalar first-BH factor, specialized at the endpoint coupling.
Its nonzero value will follow from the ACTUAL first equation at an active tail. -/
def scalarFirstFactorPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (b : ℝ) (u : T) : FiberPoly T 1 :=
  1-MvPolynomial.C (rho 0)*MvPolynomial.C (exp (z u*MSAMixture.edgeLo sigma 0 0))*
    specializeTime b (qhatPoly z rho sigma (z u) 0 0)

def scalarRateSaturation (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (b : ℝ) : FiberPoly T 1 :=
  ∏ u, scalarFirstFactorPoly z rho sigma b u

/-- The saturating factor evaluates to the literal scalar first BH matrix
entry. This is a true real finite transform, not a sampled surrogate. -/
theorem eval_scalarFirstFactorPoly (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (b : ℝ) (a : TailMatrix T 1 × TailMatrix T 1) (u : T) :
    MvPolynomial.eval (amplitudeValues a) (scalarFirstFactorPoly z rho sigma b u) =
      1-rho 0*exp (z u*MSAMixture.edgeLo sigma 0 0)*dressedQhat z rho sigma a.1 a.2 (z u) 0 0 := by
  simp only [scalarFirstFactorPoly,map_sub,map_one,map_mul,MvPolynomial.eval_C,eval_specializeTime,eval_qhatPoly]

/-- The first ACTUAL BH equation relates Dt and the saturating factor.
No canonicity or Jacobian assumption is used. -/
theorem scalar_first_factor_equation (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix T 1) (b : ℝ) (a : TailMatrix T 1 × TailMatrix T 1)
    (ha : IsRoot z rho sigma (b • K) a.1 a.2) (u : T) :
    a.1 u 0 0*MvPolynomial.eval (amplitudeValues a) (scalarFirstFactorPoly z rho sigma b u) =
      2*Real.pi*b*K u 0 0/z u := by
  rw [eval_scalarFirstFactorPoly]
  have he := ha.1 u 0 0
  simpa [firstLHS,mul_assoc] using he

/-- At nonzero coupling with an active tail and nonzero rate, the scalar
first-BH factor is nonzero at EVERY actual root, even outside canonical
closure. This discharges, rather than assumes, saturation nonvanishing. -/
theorem scalar_first_factor_ne_zero_of_active
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (hb : b ≠ 0) (a : TailMatrix T 1 × TailMatrix T 1)
    (ha : IsRoot z rho sigma (b • K) a.1 a.2) (u : T) (hz : z u ≠ 0) (hK : K u 0 0 ≠ 0) :
    MvPolynomial.eval (amplitudeValues a) (scalarFirstFactorPoly z rho sigma b u) ≠ 0 := by
  have hn : 2*Real.pi*b*K u 0 0/z u ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hb) hK) hz
  intro hzero
  have he := scalar_first_factor_equation z rho sigma K b a ha u
  rw [hzero,mul_zero] at he
  exact hn he.symm

/-- The entire positive-rate saturation product is nonzero at actual roots
when all indexed tails are active. Empty/repeated tail families are retained. -/
theorem scalar_rate_saturation_ne_zero
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (hb : b ≠ 0) (hz : ∀ u, z u ≠ 0) (hK : ∀ u, K u 0 0 ≠ 0)
    (a : TailMatrix T 1 × TailMatrix T 1) (ha : IsRoot z rho sigma (b • K) a.1 a.2) :
    MvPolynomial.eval (amplitudeValues a) (scalarRateSaturation z rho sigma b) ≠ 0 := by
  rw [scalarRateSaturation,map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun u _ => scalar_first_factor_ne_zero_of_active z rho sigma K b hb a ha u (hz u) (hK u))

/-- A scalar certificate saturated by ANY natural power of the PROVED
active-rate factor product
makes the WHOLE endpoint fiber finite, with no supplied nonvanishing,
finiteness, canonicity or Jacobian premise. Exact identities stay explicit. -/
theorem scalar_fiber_finite_of_rate_saturated_certificate
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (b : ℝ) (hb : b ≠ 0) (hz : ∀ u, z u ≠ 0) (hK : ∀ u, K u 0 0 ≠ 0)
    (C : CoordinateFiberCertificate z rho sigma K b) (power : ℕ)
    (hC : C.saturation = scalarRateSaturation z rho sigma b ^ power) :
    {a : TailMatrix T 1 × TailMatrix T 1 | IsRoot z rho sigma (b • K) a.1 a.2}.Finite := by
  apply finite_set_of_coordinate_annihilators _ C.eliminant C.nonzero
  intro a ha
  apply certificate_coordinate_zero z rho sigma K b C a ha
  rw [hC,map_pow]
  exact pow_ne_zero power (scalar_rate_saturation_ne_zero z rho sigma K b hb hz hK a ha)

/-- For an active-tail physical scalar maximal branch, exact power-rate-saturated
elimination identities alone supply its full physical Fourier-zero endpoint
limit, including singular isolated roots. Every nonvanishing/bound/limit
premise is internally discharged; existence of these identities is NOT assumed
for arbitrary data and remains a concrete certificate construction obligation. -/
theorem scalar_maximal_limit_of_rate_saturated_certificate
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i) (K : TailMatrix T 1)
    (hK : ∀ u, K u 0 0 ≠ 0) (hv : vacMix rho sigma ≠ 0)
    (seed : TailMatrix T 1 × TailMatrix T 1) (M : MaximalBranch z rho sigma K seed) (hfinite : M.bound ≠ ⊤)
    (C : CoordinateFiberCertificate z rho sigma K M.bound.toReal) (power : ℕ)
    (hC : C.saturation = scalarRateSaturation z rho sigma M.bound.toReal ^ power) :
    ∃ a : TailMatrix T 1 × TailMatrix T 1, IsRoot z rho sigma (M.bound.toReal • K) a.1 a.2 ∧
      a ∈ closure (canonicalAmplitudes z rho sigma) ∧ a ∉ canonicalAmplitudes z rho sigma ∧
      Tendsto M.path (𝓝[<] M.bound.toReal) (𝓝 a) ∧
      ∃ k : ℝ, (fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (FMSA.ExactMSA.MultiTailMixture.C z rho sigma a.1 a.2) k).det = 0 := by
  have hb : 0 < M.bound.toReal := ENNReal.toReal_pos (ne_of_gt M.positive) hfinite
  have hf := scalar_fiber_finite_of_rate_saturated_certificate z rho sigma K M.bound.toReal hb.ne'
    (fun u => (hz u).ne') hK C power hC
  exact scalar_maximal_limit_of_finite_canonical_fiber z hz rho sigma hsigma hrho K hv seed M hfinite
    (hf.subset (fun _ h => h.1))

end FMSA.Convergence.BHFiniteFiberCertificates

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.eval_coordinatePolynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.eval_coordinatePolynomial

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.finite_set_of_coordinate_annihilators' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.finite_set_of_coordinate_annihilators

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.certificate_coordinate_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.certificate_coordinate_zero

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.actual_fiber_finite_of_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.actual_fiber_finite_of_certificate

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.canonical_fiber_finite_of_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.canonical_fiber_finite_of_certificate

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.actual_cluster_limit_of_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.actual_cluster_limit_of_certificate

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.canonical_cluster_limit_of_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.canonical_cluster_limit_of_certificate

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.scalar_maximal_limit_of_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.scalar_maximal_limit_of_certificate

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.eval_scalarFirstFactorPoly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.eval_scalarFirstFactorPoly

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.scalar_first_factor_equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.scalar_first_factor_equation

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.scalar_first_factor_ne_zero_of_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.scalar_first_factor_ne_zero_of_active

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.scalar_rate_saturation_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.scalar_rate_saturation_ne_zero

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.scalar_fiber_finite_of_rate_saturated_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.scalar_fiber_finite_of_rate_saturated_certificate

/-- info: 'FMSA.Convergence.BHFiniteFiberCertificates.scalar_maximal_limit_of_rate_saturated_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.BHFiniteFiberCertificates.scalar_maximal_limit_of_rate_saturated_certificate
