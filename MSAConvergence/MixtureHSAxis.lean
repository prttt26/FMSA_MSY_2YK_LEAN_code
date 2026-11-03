import MSAConvergence.MixtureHSEnergy

/-! Actual physical mixture HS axis nonvanishing from collective energy,
retaining all species and zero-density tracers. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.MixtureHSAxis
open FMSA.Convergence.MixtureHSEnergy
open FMSA.ExactMSA.MultiTailMixture FMSA.MatrixQ0
variable {N : ℕ}

def phi1 (s : ℂ) (sigma : ℝ) : ℂ := (1-s*(sigma : ℂ)-Complex.exp (-s*(sigma : ℂ)))/s^2

def phi2 (s : ℂ) (sigma : ℝ) : ℂ :=
  (1-s*(sigma : ℂ)+(s*(sigma : ℂ))^2/2-Complex.exp (-s*(sigma : ℂ)))/s^3

def hsA (rho sigma : Fin N → ℝ) (c : ℝ) (j : Fin N) : ℝ :=
  2*c+c^2*secondMoment rho sigma*sigma j

def hsQp (rho sigma : Fin N → ℝ) (c : ℝ) (i j : Fin N) : ℝ :=
  sigma i/2*hsA rho sigma c j+c*sigma j

def bareHS (rho sigma : Fin N → ℝ) (c : ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (hsQp rho sigma c i j : ℂ)*phi1 s (sigma i)+(hsA rho sigma c j : ℂ)*phi2 s (sigma i)

def columnFactor (rho sigma : Fin N → ℝ) (c : ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  1-bareHS rho sigma c s*Matrix.diagonal (fun i => (rho i : ℂ))

def rowFactor (rho sigma : Fin N → ℝ) (c : ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  1-Matrix.diagonal (fun i => (rho i : ℂ))*bareHS rho sigma c s

/-- Actual physical A coefficients have the required rank-two moment sum. -/
theorem weighted_A_sum (rho sigma : Fin N → ℝ) (y : Fin N → ℂ) (c : ℝ) :
    (∑ j, (rho j : ℂ)*(hsA rho sigma c j : ℂ)*y j) =
      (2*c : ℝ)*moment rho y+(c^2*secondMoment rho sigma : ℝ)*diameterMoment rho sigma y := by
  simp only [hsA,moment,diameterMoment,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Qp moment is sigma_i/2 times the A moment plus c times the first
weighted diameter moment, with NO equal-diameter hypothesis. -/
theorem weighted_qp_sum (rho sigma : Fin N → ℝ) (y : Fin N → ℂ) (c : ℝ) (i : Fin N) :
    (∑ j, (rho j : ℂ)*(hsQp rho sigma c i j : ℂ)*y j) =
      (sigma i : ℂ)/2*((2*c : ℝ)*moment rho y+(c^2*secondMoment rho sigma : ℝ)*diameterMoment rho sigma y)+
        (c : ℂ)*diameterMoment rho sigma y := by
  rw [← weighted_A_sum rho sigma y c]
  simp only [hsQp,diameterMoment,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_ofNat,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Literal free HS matrix multiplication retains exactly both moments. -/
theorem bare_mul_density_vector (rho sigma : Fin N → ℝ) (y : Fin N → ℂ) (c : ℝ) (s : ℂ) (i : Fin N) :
    (bareHS rho sigma c s*Matrix.diagonal (fun j => (rho j : ℂ))).mulVec y i =
      ((sigma i : ℂ)/2*((2*c : ℝ)*moment rho y+(c^2*secondMoment rho sigma : ℝ)*diameterMoment rho sigma y)+
        (c : ℂ)*diameterMoment rho sigma y)*phi1 s (sigma i)+
      ((2*c : ℝ)*moment rho y+(c^2*secondMoment rho sigma : ℝ)*diameterMoment rho sigma y)*phi2 s (sigma i) := by
  change (∑ j, (bareHS rho sigma c s*Matrix.diagonal (fun j => (rho j : ℂ))) i j*y j) = _
  simp only [Matrix.mul_diagonal,bareHS]
  calc
    _ = (∑ j, (rho j : ℂ)*(hsQp rho sigma c i j : ℂ)*y j)*phi1 s (sigma i)+
        (∑ j, (rho j : ℂ)*(hsA rho sigma c j : ℂ)*y j)*phi2 s (sigma i) := by
      rw [Finset.sum_mul,Finset.sum_mul,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = _ := by rw [weighted_qp_sum,weighted_A_sum]

/-- Exact cleared core transform, before setting s on the Fourier axis. -/
theorem cleared_core_symbol (A B s : ℂ) (sigma : ℝ) (hs : s ≠ 0) :
    s^3*(((sigma : ℂ)/2*A+B)*phi1 s sigma+A*phi2 s sigma) =
      A*(1-s*(sigma : ℂ)/2)+B*s*(1-s*(sigma : ℂ))-
        Complex.exp (-s*(sigma : ℂ))*(A*(1+s*(sigma : ℂ)/2)+B*s) := by
  unfold phi1 phi2
  field_simp [hs]
  ring

/-- The physical column-density HS factor has ZERO kernel on every nonzero
Fourier frequency. Nonnegative densities include arbitrary tracers. -/
theorem column_factor_axis_kernel_zero (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (c k : ℝ) (hk : k ≠ 0) (y : Fin N → ℂ)
    (hy : (columnFactor rho sigma c (Complex.I*(k : ℂ))).mulVec y = 0) : y = 0 := by
  let s : ℂ := Complex.I*(k : ℂ)
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hs : s ≠ 0 := mul_ne_zero Complex.I_ne_zero hkC
  have hs2 : s*s = -(k : ℂ)^2 := by
    change (Complex.I*(k : ℂ))*(Complex.I*(k : ℂ)) = _
    calc
      _ = (Complex.I*Complex.I)*(k : ℂ)^2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have hs3 : s^3 = -Complex.I*(k : ℂ)^3 := by
    dsimp only [s]
    rw [mul_pow,Complex.I_pow_three]
  apply vector_zero_of_unit_phase_rows rho sigma hrho y
    (fun i => Complex.exp (-Complex.I*(k : ℂ)*(sigma i : ℂ))) c k hk (fun i => exp_axis_normSq k (sigma i))
  intro i
  dsimp only
  let A : ℂ := (2*c : ℝ)*moment rho y+(c^2*secondMoment rho sigma : ℝ)*diameterMoment rho sigma y
  let B : ℂ := (c : ℂ)*diameterMoment rho sigma y
  change numerator A B k (sigma i)+Complex.I*(k : ℂ)^3*y i =
    Complex.exp (-Complex.I*(k : ℂ)*(sigma i : ℂ))*delayPart A B k (sigma i)
  have hroot : y i = ((sigma i : ℂ)/2*A+B)*phi1 s (sigma i)+A*phi2 s (sigma i) := by
    have h := congrFun hy i
    rw [columnFactor,Matrix.sub_mulVec,Matrix.one_mulVec] at h
    have hrow := sub_eq_zero.mp h
    exact hrow.trans (bare_mul_density_vector rho sigma y c s i)
  have he := (congrArg (fun q : ℂ => s^3*q) hroot).trans (cleared_core_symbol A B s (sigma i) hs)
  have hB : B*s*(1-s*(sigma i : ℂ)) = B*(Complex.I*(k : ℂ)+(k : ℂ)^2*(sigma i : ℂ)) := by
    calc
      _ = B*s-B*(s*s)*(sigma i : ℂ) := by ring
      _ = _ := by rw [hs2]; dsimp only [s]; ring
  have hphase : Complex.exp (-s*(sigma i : ℂ)) = Complex.exp (-Complex.I*(k : ℂ)*(sigma i : ℂ)) := by
    congr 1
    dsimp only [s]
    ring
  rw [hs3,hB,hphase] at he
  dsimp only [s] at he
  unfold numerator delayPart
  linear_combination -he

/-- General-N physical HS column factor is invertible on the punctured
Fourier axis, with no no-spinodal axiom or density inverse. -/
theorem column_factor_axis_isUnit (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (c k : ℝ) (hk : k ≠ 0) : IsUnit (columnFactor rho sigma c (Complex.I*(k : ℂ))) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hzero : (columnFactor rho sigma c (Complex.I*(k : ℂ))).mulVec (x-y) = 0 := by
    rw [Matrix.mulVec_sub,hxy,sub_self]
  exact sub_eq_zero.mp (column_factor_axis_kernel_zero rho sigma hrho c k hk (x-y) hzero)

/-- The row-density factor used by the actual causal kernel has the SAME
nonzero determinant, by Sylvester, including zero-density rows. -/
theorem row_factor_axis_isUnit (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (c k : ℝ) (hk : k ≠ 0) : IsUnit (rowFactor rho sigma c (Complex.I*(k : ℂ))) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [rowFactor,Matrix.det_one_sub_mul_comm]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (column_factor_axis_isUnit rho sigma hrho c k hk)

/-- Honest static polynomial-core integral, independent of formal phi(0). -/
def staticCore (rho sigma : Fin N → ℝ) (c : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => -(sigma i : ℂ)^3/12*(hsA rho sigma c j : ℂ)-
    (c : ℂ)*(sigma i : ℂ)^2/2*(sigma j : ℂ)

def staticColumnFactor (rho sigma : Fin N → ℝ) (c : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  1-staticCore rho sigma c*Matrix.diagonal (fun i => (rho i : ℂ))

def staticRowFactor (rho sigma : Fin N → ℝ) (c : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  1-Matrix.diagonal (fun i => (rho i : ℂ))*staticCore rho sigma c

/-- Static free core formula is exactly the integral of the real polynomial. -/
theorem static_core_eq_polynomial_moments (rho sigma : Fin N → ℝ) (c : ℝ) (i j : Fin N) :
    staticCore rho sigma c i j = -(sigma i : ℂ)^2/2*(hsQp rho sigma c i j : ℂ)+
      (sigma i : ℂ)^3/6*(hsA rho sigma c j : ℂ) := by
  unfold staticCore hsQp
  push_cast
  ring

/-- The static matrix equation retains the SAME two moments as the axis
identity, with actual finite integral values at the origin. -/
theorem static_mul_density_vector (rho sigma : Fin N → ℝ) (y : Fin N → ℂ) (c : ℝ) (i : Fin N) :
    (staticCore rho sigma c*Matrix.diagonal (fun j => (rho j : ℂ))).mulVec y i =
      -(sigma i : ℂ)^3/12*((2*c : ℝ)*moment rho y+(c^2*secondMoment rho sigma : ℝ)*diameterMoment rho sigma y)-
        (c : ℂ)*(sigma i : ℂ)^2/2*diameterMoment rho sigma y := by
  change (∑ j, (staticCore rho sigma c*Matrix.diagonal (fun j => (rho j : ℂ))) i j*y j) = _
  simp only [Matrix.mul_diagonal,staticCore]
  rw [← weighted_A_sum rho sigma y c]
  unfold diameterMoment
  simp only [Complex.ofReal_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The origin factor is nonsingular by positive moment coefficients,
without an axis puncture or a value assigned to a 1/s formula. -/
theorem static_column_kernel_zero (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (hsigma : ∀ i, 0 ≤ sigma i) (c : ℝ) (hc : 0 ≤ c) (y : Fin N → ℂ)
    (hy : (staticColumnFactor rho sigma c).mulVec y = 0) : y = 0 := by
  let U := moment rho y
  let V := diameterMoment rho sigma y
  let A : ℂ := (2*c : ℝ)*U+(c^2*secondMoment rho sigma : ℝ)*V
  let m3 : ℝ := ∑ i, rho i*sigma i^3
  have hm3 : 0 ≤ m3 := Finset.sum_nonneg (fun i _ => mul_nonneg (hrho i) (pow_nonneg (hsigma i) 3))
  have hrow (i : Fin N) : y i = -(sigma i : ℂ)^3/12*A-(c : ℂ)*(sigma i : ℂ)^2/2*V := by
    have h := congrFun hy i
    rw [staticColumnFactor,Matrix.sub_mulVec,Matrix.one_mulVec] at h
    exact (sub_eq_zero.mp h).trans (static_mul_density_vector rho sigma y c i)
  have hU : U = -(m3 : ℂ)/12*A-(c : ℂ)*(secondMoment rho sigma : ℂ)/2*V := by
    calc
      U = ∑ i, (rho i : ℂ)*y i := rfl
      _ = ∑ i, (rho i : ℂ)*(-(sigma i : ℂ)^3/12*A-(c : ℂ)*(sigma i : ℂ)^2/2*V) :=
        Finset.sum_congr rfl (fun i _ => congrArg (fun q : ℂ => (rho i : ℂ)*q) (hrow i))
      _ = _ := by
        dsimp only [m3]
        unfold secondMoment
        simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow,
          neg_div,neg_mul,Finset.sum_mul,Finset.mul_sum,Finset.sum_div,← Finset.sum_neg_distrib,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hAeq : (1+(c : ℂ)*(m3 : ℂ)/6)*A = 0 := by
    have hdef : A = (2*c : ℝ)*U+(c^2*secondMoment rho sigma : ℝ)*V := rfl
    push_cast at hdef
    linear_combination (2*(c : ℂ))*hU+hdef
  have ha : 1+(c : ℂ)*(m3 : ℂ)/6 ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : 0 < 1+c*m3/6))
  have hA0 : A = 0 := (mul_eq_zero.mp hAeq).resolve_left ha
  have hV : V = -(c : ℂ)*(m3 : ℂ)/2*V := by
    calc
      V = ∑ i, ((rho i*sigma i : ℝ) : ℂ)*y i := rfl
      _ = ∑ i, ((rho i*sigma i : ℝ) : ℂ)*(-(c : ℂ)*(sigma i : ℂ)^2/2*V) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hrow,hA0,mul_zero,zero_sub]
        ring
      _ = _ := by
        dsimp only [m3]
        simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow,
          Finset.sum_mul,Finset.mul_sum,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hVeq : (1+(c : ℂ)*(m3 : ℂ)/2)*V = 0 := by linear_combination hV
  have hv : 1+(c : ℂ)*(m3 : ℂ)/2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : 0 < 1+c*m3/2))
  have hV0 : V = 0 := (mul_eq_zero.mp hVeq).resolve_left hv
  funext i
  simpa only [hA0,hV0,mul_zero,sub_zero,Pi.zero_apply] using hrow i

/-- The actual finite static row-density factor is invertible, tracers and
vacuum included, without a no-spinodal or compressibility axiom. -/
theorem static_row_factor_isUnit (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (hsigma : ∀ i, 0 ≤ sigma i) (c : ℝ) (hc : 0 ≤ c) : IsUnit (staticRowFactor rho sigma c) := by
  have hunit : IsUnit (staticColumnFactor rho sigma c) := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro x y hxy
    have hz : (staticColumnFactor rho sigma c).mulVec (x-y) = 0 := by rw [Matrix.mulVec_sub,hxy,sub_self]
    exact sub_eq_zero.mp (static_column_kernel_zero rho sigma hrho hsigma c hc (x-y) hz)
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [staticRowFactor,Matrix.det_one_sub_mul_comm]
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit

end FMSA.Convergence.MixtureHSAxis

/-- info: 'FMSA.Convergence.MixtureHSAxis.weighted_A_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSAxis.weighted_A_sum

/-- info: 'FMSA.Convergence.MixtureHSAxis.weighted_qp_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSAxis.weighted_qp_sum

/-- info: 'FMSA.Convergence.MixtureHSAxis.bare_mul_density_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSAxis.bare_mul_density_vector

/-- info: 'FMSA.Convergence.MixtureHSAxis.cleared_core_symbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSAxis.cleared_core_symbol

/-- info: 'FMSA.Convergence.MixtureHSAxis.column_factor_axis_kernel_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSAxis.column_factor_axis_kernel_zero

/-- info: 'FMSA.Convergence.MixtureHSAxis.column_factor_axis_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSAxis.column_factor_axis_isUnit

/-- info: 'FMSA.Convergence.MixtureHSAxis.row_factor_axis_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSAxis.row_factor_axis_isUnit

/-- info: 'FMSA.Convergence.MixtureHSAxis.static_core_eq_polynomial_moments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSAxis.static_core_eq_polynomial_moments

/-- info: 'FMSA.Convergence.MixtureHSAxis.static_mul_density_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSAxis.static_mul_density_vector

/-- info: 'FMSA.Convergence.MixtureHSAxis.static_column_kernel_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSAxis.static_column_kernel_zero

/-- info: 'FMSA.Convergence.MixtureHSAxis.static_row_factor_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSAxis.static_row_factor_isUnit

