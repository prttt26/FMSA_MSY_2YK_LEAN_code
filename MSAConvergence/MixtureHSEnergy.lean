import MSAConvergence.FiniteKernelLaplace

/-! A collective phase-preserving energy identity for the physical mixture
HS Baxter factor. No no-spinodal or homotopy axiom is used. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.MixtureHSEnergy
variable {N : ℕ}

def numerator (A B : ℂ) (k sigma : ℝ) : ℂ :=
  A*(1-Complex.I*(k : ℂ)*(sigma : ℂ)/2)+B*(Complex.I*(k : ℂ)+(k : ℂ)^2*(sigma : ℂ))

def delayPart (A B : ℂ) (k sigma : ℝ) : ℂ :=
  A*(1+Complex.I*(k : ℂ)*(sigma : ℂ)/2)+B*Complex.I*(k : ℂ)

def moment (rho : Fin N → ℝ) (y : Fin N → ℂ) : ℂ := ∑ i, (rho i : ℂ)*y i

def diameterMoment (rho sigma : Fin N → ℝ) (y : Fin N → ℂ) : ℂ :=
  ∑ i, ((rho i*sigma i : ℝ) : ℂ)*y i

def secondMoment (rho sigma : Fin N → ℝ) : ℝ := ∑ i, rho i*sigma i^2

/-- Exact row energy expansion before using any physical moment relation. -/
theorem row_energy_expansion (A B y : ℂ) (k sigma : ℝ) :
    Complex.normSq (numerator A B k sigma+Complex.I*(k : ℂ)^3*y)-
      Complex.normSq (delayPart A B k sigma) =
    k^6*Complex.normSq y+sigma^2*(k^4*Complex.normSq B-k^3*(starRingEnd ℂ A*B).im)-
      2*k^3*(starRingEnd ℂ (numerator A B k sigma)*y).im := by
  simp only [numerator,delayPart,Complex.normSq_apply,Complex.add_re,Complex.sub_re,
    Complex.mul_re,Complex.div_ofNat_re,← Complex.ofReal_pow,Complex.one_re,Complex.I_re,
    Complex.ofReal_re,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.div_ofNat_im,
    Complex.one_im,Complex.I_im,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
  ring

/-- The exact linear moment expression for the imaginary source pairing. -/
theorem row_pairing_expansion (A B y : ℂ) (k sigma : ℝ) :
    (starRingEnd ℂ (numerator A B k sigma)*y).im =
      (A.re-k*B.im)*y.im-(A.im+k*B.re)*y.re+
        sigma*((k*A.im/2+k^2*B.re)*y.im-(-k*A.re/2+k^2*B.im)*y.re) := by
  simp only [numerator,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.div_ofNat_re,Complex.div_ofNat_im,
    ← Complex.ofReal_pow,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
  ring

/-- Physical moment coefficients cancel the ENTIRE collective correction.
No inequality discarding phase or separate exponential terms is substituted. -/
theorem moment_correction_cancels (U V : ℂ) (c m2 k : ℝ) :
    let A : ℂ := (2*c : ℝ)*U+(c^2*m2 : ℝ)*V
    let B : ℂ := (c : ℂ)*V
    m2*(k^4*Complex.normSq B-k^3*(starRingEnd ℂ A*B).im)-
      2*k^3*((A.re-k*B.im)*U.im-(A.im+k*B.re)*U.re+
        (k*A.im/2+k^2*B.re)*V.im-(-k*A.re/2+k^2*B.im)*V.re) = 0 := by
  dsimp only
  simp only [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
  ring

/-- Weighted imaginary pairings retain exactly the two density moments. -/
theorem weighted_pairing_sum (rho sigma : Fin N → ℝ) (y : Fin N → ℂ) (A B : ℂ) (k : ℝ) :
    (∑ i, rho i*(starRingEnd ℂ (numerator A B k (sigma i))*y i).im) =
      (A.re-k*B.im)*(moment rho y).im-(A.im+k*B.re)*(moment rho y).re+
        (k*A.im/2+k^2*B.re)*(diameterMoment rho sigma y).im-
          (-k*A.re/2+k^2*B.im)*(diameterMoment rho sigma y).re := by
  simp_rw [row_pairing_expansion]
  simp only [moment,diameterMoment,Complex.re_sum,Complex.im_sum,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The collective HS energy identity for arbitrary finite N, REAL weights,
complex vector and real frequency. Positivity is only needed by its consumer. -/
theorem collective_energy_identity (rho sigma : Fin N → ℝ) (y : Fin N → ℂ) (c k : ℝ) :
    let A : ℂ := (2*c : ℝ)*moment rho y+(c^2*secondMoment rho sigma : ℝ)*diameterMoment rho sigma y
    let B : ℂ := (c : ℂ)*diameterMoment rho sigma y
    (∑ i, rho i*(Complex.normSq (numerator A B k (sigma i)+Complex.I*(k : ℂ)^3*y i)-
      Complex.normSq (delayPart A B k (sigma i)))) = k^6*∑ i, rho i*Complex.normSq (y i) := by
  dsimp only
  let A : ℂ := (2*c : ℝ)*moment rho y+(c^2*secondMoment rho sigma : ℝ)*diameterMoment rho sigma y
  let B : ℂ := (c : ℂ)*diameterMoment rho sigma y
  change (∑ i, rho i*(Complex.normSq (numerator A B k (sigma i)+Complex.I*(k : ℂ)^3*y i)-
    Complex.normSq (delayPart A B k (sigma i)))) = _
  simp_rw [row_energy_expansion]
  have he : (∑ i, rho i*(k^6*Complex.normSq (y i)+(sigma i)^2*(k^4*Complex.normSq B-k^3*(starRingEnd ℂ A*B).im)-
      2*k^3*(starRingEnd ℂ (numerator A B k (sigma i))*y i).im)) =
      k^6*∑ i, rho i*Complex.normSq (y i)+
      secondMoment rho sigma*(k^4*Complex.normSq B-k^3*(starRingEnd ℂ A*B).im)-
      2*k^3*∑ i, rho i*(starRingEnd ℂ (numerator A B k (sigma i))*y i).im := by
    simp only [secondMoment,Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,weighted_pairing_sum]
  have hcancel := moment_correction_cancels (moment rho y) (diameterMoment rho sigma y) c (secondMoment rho sigma) k
  change secondMoment rho sigma*(k^4*Complex.normSq B-k^3*(starRingEnd ℂ A*B).im)-
    2*k^3*((A.re-k*B.im)*(moment rho y).im-(A.im+k*B.re)*(moment rho y).re+
      (k*A.im/2+k^2*B.re)*(diameterMoment rho sigma y).im-
      (-k*A.re/2+k^2*B.im)*(diameterMoment rho sigma y).re) = 0 at hcancel
  linarith

/-- Collective row-norm equality kills the density-weighted vector,
including every zero-density species without division by density. -/
theorem weighted_vector_zero_of_row_norms
    (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i) (y : Fin N → ℂ) (c k : ℝ) (hk : k ≠ 0)
    (hrow : ∀ i,
      let A : ℂ := (2*c : ℝ)*moment rho y+(c^2*secondMoment rho sigma : ℝ)*diameterMoment rho sigma y
      let B : ℂ := (c : ℂ)*diameterMoment rho sigma y
      Complex.normSq (numerator A B k (sigma i)+Complex.I*(k : ℂ)^3*y i) =
        Complex.normSq (delayPart A B k (sigma i))) :
    ∀ i, (rho i : ℂ)*y i = 0 := by
  have he := collective_energy_identity rho sigma y c k
  simp_rw [hrow,sub_self,mul_zero] at he
  have hsum : (∑ i, rho i*Complex.normSq (y i)) = 0 :=
    (mul_eq_zero.mp (by simpa only [Finset.sum_const_zero] using he.symm)).resolve_left (pow_ne_zero 6 hk)
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hrho j) (Complex.normSq_nonneg (y j)))).mp hsum i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hi with h | h
  · simp [h]
  · simp [Complex.normSq_eq_zero.mp h]

/-- Weighted-vector zero kills BOTH density moments even for tracers. -/
theorem moments_zero_of_weighted_zero (rho sigma : Fin N → ℝ) (y : Fin N → ℂ)
    (hz : ∀ i, (rho i : ℂ)*y i = 0) : moment rho y = 0 ∧ diameterMoment rho sigma y = 0 := by
  constructor
  · exact Finset.sum_eq_zero (fun i _ => hz i)
  · unfold diameterMoment
    apply Finset.sum_eq_zero
    intro i _
    rw [Complex.ofReal_mul]
    calc
      _ = (sigma i : ℂ)*((rho i : ℂ)*y i) := by ring
      _ = 0 := by rw [hz,mul_zero]

/-- Unit-modulus delays cannot have a nonzero kernel vector for the physical
HS moment coefficients. ALL nonnegative densities, arbitrary finite N,
independent phases and tracers are retained; no spinodal premise is supplied. -/
theorem vector_zero_of_unit_phase_rows
    (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i) (y phase : Fin N → ℂ)
    (c k : ℝ) (hk : k ≠ 0) (hphase : ∀ i, Complex.normSq (phase i) = 1)
    (hrow : ∀ i,
      let A : ℂ := (2*c : ℝ)*moment rho y+(c^2*secondMoment rho sigma : ℝ)*diameterMoment rho sigma y
      let B : ℂ := (c : ℂ)*diameterMoment rho sigma y
      numerator A B k (sigma i)+Complex.I*(k : ℂ)^3*y i = phase i*delayPart A B k (sigma i)) : y = 0 := by
  have hnorm : ∀ i,
      let A : ℂ := (2*c : ℝ)*moment rho y+(c^2*secondMoment rho sigma : ℝ)*diameterMoment rho sigma y
      let B : ℂ := (c : ℂ)*diameterMoment rho sigma y
      Complex.normSq (numerator A B k (sigma i)+Complex.I*(k : ℂ)^3*y i) =
        Complex.normSq (delayPart A B k (sigma i)) := by
    intro i
    dsimp only
    rw [hrow i,Complex.normSq_mul,hphase,one_mul]
  have hw := weighted_vector_zero_of_row_norms rho sigma hrho y c k hk hnorm
  obtain ⟨hU,hV⟩ := moments_zero_of_weighted_zero rho sigma y hw
  funext i
  have hi := hrow i
  simp only [hU,hV,mul_zero,add_zero,numerator,delayPart,zero_mul,zero_add] at hi
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  exact (mul_eq_zero.mp hi).resolve_left (mul_ne_zero Complex.I_ne_zero (pow_ne_zero 3 hkC))

/-- The genuine Fourier-axis exponential has unit modulus-squared. -/
theorem exp_axis_normSq (k sigma : ℝ) :
    Complex.normSq (Complex.exp (-Complex.I*(k : ℂ)*(sigma : ℂ))) = 1 := by
  rw [Complex.normSq_eq_norm_sq,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_re,Complex.I_re,neg_zero,Complex.ofReal_re,Complex.neg_im,
    Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,Real.exp_zero,one_pow]

end FMSA.Convergence.MixtureHSEnergy

/-- info: 'FMSA.Convergence.MixtureHSEnergy.row_energy_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSEnergy.row_energy_expansion

/-- info: 'FMSA.Convergence.MixtureHSEnergy.row_pairing_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSEnergy.row_pairing_expansion

/-- info: 'FMSA.Convergence.MixtureHSEnergy.moment_correction_cancels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSEnergy.moment_correction_cancels

/-- info: 'FMSA.Convergence.MixtureHSEnergy.weighted_pairing_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSEnergy.weighted_pairing_sum

/-- info: 'FMSA.Convergence.MixtureHSEnergy.collective_energy_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSEnergy.collective_energy_identity

/-- info: 'FMSA.Convergence.MixtureHSEnergy.weighted_vector_zero_of_row_norms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSEnergy.weighted_vector_zero_of_row_norms

/-- info: 'FMSA.Convergence.MixtureHSEnergy.moments_zero_of_weighted_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSEnergy.moments_zero_of_weighted_zero

/-- info: 'FMSA.Convergence.MixtureHSEnergy.vector_zero_of_unit_phase_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSEnergy.vector_zero_of_unit_phase_rows

/-- info: 'FMSA.Convergence.MixtureHSEnergy.exp_axis_normSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSEnergy.exp_axis_normSq

