import MSAConvergence.ScalarFourierTail

set_option linter.style.header false

/-! The exponential/rational split of the ACTUAL pure-fluid multi-tail
Blum–Høye factor. This is Step 1 of the proposed H-function route, with no
distinct-rate or root assumption. Poles at `s = 0` and `s = -z_t` are kept
explicit; the identity is only asserted away from them. -/
noncomputable section
open Real
open scoped BigOperators
namespace FMSA.Convergence.PureFluidExponentialSplit
open FMSA.ExactMSA
variable {T : Type*} [Fintype T]

private theorem head_split (ρ A q s : ℝ) (hs : s ≠ 0) :
    1 - ρ * (phi1 s * q + phi2 s * A) =
      (1 - ρ*A/s^3 + ρ*(A-q)/s^2 + ρ*(q-A/2)/s) +
        exp (-s) * (ρ*A/s^3 + ρ*q/s^2) := by
  unfold phi1 phi2
  field_simp [hs]
  ring

private theorem tail_split (ρ W C s z : ℝ) :
    -ρ * ((W + C * exp (-s))/(s+z) + C*(1-exp (-s))/s) =
      -ρ*(W/(s+z)+C/s) + exp (-s)*(ρ*C*(1/s-1/(s+z))) := by
  ring

/-- Rational part `P(s)` in `F(s) = P(s) + e⁻ˢ Ŝ(s)`.
All coefficients are the actual finite-tail BH amplitudes. -/
def rationalPart (xi : ℝ) (z D G : T → ℝ) (s : ℝ) : ℝ :=
  let ρ := rhoOf xi
  let A := MultiTail.amplitudeA xi z D G
  let q := MultiTail.amplitudeQp xi z D G
  1 - ρ*A/s^3 + ρ*(A-q)/s^2 + ρ*(q-A/2)/s -
    ∑ t, ρ*(MultiTail.W xi z D G t/(s+z t) + MultiTail.C xi z D G t/s)

/-- The coefficient of the exponential in the actual finite-tail factor. -/
def exponentialPart (xi : ℝ) (z D G : T → ℝ) (s : ℝ) : ℝ :=
  let ρ := rhoOf xi
  let A := MultiTail.amplitudeA xi z D G
  let q := MultiTail.amplitudeQp xi z D G
  ρ*A/s^3 + ρ*q/s^2 +
    ∑ t, ρ*MultiTail.C xi z D G t*(1/s-1/(s+z t))

/-- Exact exponential/rational separation of the ORIGINAL BH factor. -/
theorem factor_split (xi : ℝ) (z D G : T → ℝ) (s : ℝ) (hs : s ≠ 0) :
    MultiTail.factor xi z D G s =
      rationalPart xi z D G s + exp (-s)*exponentialPart xi z D G s := by
  let ρ := rhoOf xi
  let A := MultiTail.amplitudeA xi z D G
  let q := MultiTail.amplitudeQp xi z D G
  let W := MultiTail.W xi z D G
  let C := MultiTail.C xi z D G
  have hhead := head_split ρ A q s hs
  have htail (t : T) := tail_split ρ (W t) (C t) s (z t)
  simp only [MultiTail.factor, MultiTail.Qhat] at hhead htail ⊢
  simp only [rationalPart, exponentialPart]
  rw [mul_add, Finset.mul_sum]
  have hsum := Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => htail t)
  dsimp only [ρ, A, q, W, C] at hhead hsum
  rw [Finset.sum_add_distrib] at hsum
  have hneg₁ :
      (∑ t, -rhoOf xi *
        ((MultiTail.W xi z D G t + MultiTail.C xi z D G t * exp (-s))/(s+z t) +
          MultiTail.C xi z D G t*(1-exp (-s))/s)) =
      -(∑ t, rhoOf xi *
        ((MultiTail.W xi z D G t + MultiTail.C xi z D G t * exp (-s))/(s+z t) +
          MultiTail.C xi z D G t*(1-exp (-s))/s)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hneg₂ :
      (∑ t, -rhoOf xi *
        (MultiTail.W xi z D G t/(s+z t) + MultiTail.C xi z D G t/s)) =
      -(∑ t, rhoOf xi *
        (MultiTail.W xi z D G t/(s+z t) + MultiTail.C xi z D G t/s)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hneg₁, hneg₂] at hsum
  conv at hsum => rhs; rhs; rw [← Finset.mul_sum]
  linear_combination hhead + hsum

/-- The exponential coefficient is the actual second BH source multiplied
by density and divided by frequency. No new source is introduced. -/
theorem exponentialPart_eq_secondRHS (xi : ℝ) (z D G : T → ℝ) (s : ℝ)
    (hs : s ≠ 0) (hcross : ∀ t, s + z t ≠ 0) :
    exponentialPart xi z D G s =
      rhoOf xi * MultiTail.secondRHS xi z D G s / s := by
  let ρ := rhoOf xi
  let A := MultiTail.amplitudeA xi z D G
  let q := MultiTail.amplitudeQp xi z D G
  let C := MultiTail.C xi z D G
  have htail (t : T) :
      ρ*C t*(1/s-1/(s+z t)) = ρ*(s^2*z t/(s+z t)*C t)/s^3 := by
    field_simp [hs, hcross t]
    ring
  have hsum :
      (∑ t, ρ*C t*(1/s-1/(s+z t))) =
        ρ*(∑ t, s^2*z t/(s+z t)*C t)/s^3 := by
    calc
      _ = ∑ t, ρ*(s^2*z t/(s+z t)*C t)/s^3 := by
        apply Finset.sum_congr rfl
        intro t _
        exact htail t
      _ = ρ*(∑ t, s^2*z t/(s+z t)*C t)/s^3 := by
        rw [Finset.mul_sum, Finset.sum_div]
  simp only [exponentialPart, MultiTail.secondRHS]
  dsimp only [ρ, A, q, C] at hsum
  rw [hsum]
  field_simp [hs]

end FMSA.Convergence.PureFluidExponentialSplit
/-- info: 'FMSA.Convergence.PureFluidExponentialSplit.factor_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidExponentialSplit.factor_split
/-- info: 'FMSA.Convergence.PureFluidExponentialSplit.exponentialPart_eq_secondRHS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidExponentialSplit.exponentialPart_eq_secondRHS
