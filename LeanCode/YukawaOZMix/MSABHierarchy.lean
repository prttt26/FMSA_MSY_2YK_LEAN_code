import LeanCode.YukawaOZMix.MixtureRealSpace
import LeanCode.YukawaOZMix.MSAMixtureBreakpointOrders

/-!
# Positive-order OZ coefficients through a Baxter B hierarchy

Coefficients are normalized Taylor coefficients (derivative / factorial).
The raw B_n = Qp^T H_n Qp needs a lower-order source correction for n > 1.
Subtracting that source before dressing gives C_n = Qm correctedB_n Qm^T.
This algebra alone does not prove that correctedB_n has a finite spatial form.
The separate fixed-basis results below preserve finite spatial representations
at each finite order and at strict finite truncation, without series convergence.
The physical normalized OZ line and the actual fixed-basis representation
are explicit inputs; no arbitrary RDF is asserted to have a finite form.
-/
noncomputable section
open Matrix
open scoped BigOperators
namespace FMSA.ExactMSA.BHierarchy

section Matrices
variable {N : ℕ}

def lowerSource (H C : ℕ → Matrix (Fin N) (Fin N) ℂ) (n : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ j ∈ Finset.range (n - 1), H (j + 1) * C (n - (j + 1))

theorem lower_source_one (H C : ℕ → Matrix (Fin N) (Fin N) ℂ) :
    lowerSource H C 1 = 0 := by simp [lowerSource]

theorem lower_source_two (H C : ℕ → Matrix (Fin N) (Fin N) ℂ) :
    lowerSource H C 2 = H 1 * C 1 := by simp [lowerSource]

def rawB (Qp Hn : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Qpᵀ * Hn * Qp

def correctedB (Qp S0 Hn R : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ := Qpᵀ * (Hn - R * S0) * Qp

theorem corrected_b_eq_raw_sub (Qp S0 Hn R : Matrix (Fin N) (Fin N) ℂ) :
    correctedB Qp S0 Hn R = rawB Qp Hn - Qpᵀ * (R * S0) * Qp := by
  simp [correctedB, rawB, Matrix.mul_sub, Matrix.sub_mul]

theorem oz_order_dcf (T0 S0 Hn Cn R : Matrix (Fin N) (Fin N) ℂ)
    (hTS : T0 * S0 = 1) (hline : Hn * T0 = S0 * Cn + R) :
    Cn = T0 * Hn * T0 - T0 * R := by
  have h : T0 * Hn * T0 = Cn + T0 * R := by
    calc
      _ = T0 * (Hn * T0) := by rw [Matrix.mul_assoc]
      _ = T0 * (S0 * Cn + R) := by rw [hline]
      _ = _ := by rw [Matrix.mul_add, ← Matrix.mul_assoc, hTS, Matrix.one_mul]
  rw [h, add_sub_cancel_right]

theorem baxter_dressing (Qp Qm T0 X : Matrix (Fin N) (Fin N) ℂ)
    (hfact : T0 = Qp * Qmᵀ) (hsym : T0ᵀ = T0) :
    T0 * X * T0 = Qm * (Qpᵀ * X * Qp) * Qmᵀ := by
  have hleft : T0 = Qm * Qpᵀ := by
    rw [← hsym, hfact, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = (Qm * Qpᵀ) * X * (Qp * Qmᵀ) := by rw [← hleft, ← hfact]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem raw_b_dcf (Qp Qm T0 S0 Hn Cn R : Matrix (Fin N) (Fin N) ℂ)
    (hTS : T0 * S0 = 1) (hline : Hn * T0 = S0 * Cn + R)
    (hfact : T0 = Qp * Qmᵀ) (hsym : T0ᵀ = T0) :
    Cn = Qm * rawB Qp Hn * Qmᵀ - T0 * R := by
  rw [oz_order_dcf T0 S0 Hn Cn R hTS hline,
    baxter_dressing Qp Qm T0 Hn hfact hsym]
  rfl

theorem corrected_b_dcf (Qp Qm T0 S0 Hn Cn R : Matrix (Fin N) (Fin N) ℂ)
    (hTS : T0 * S0 = 1) (hline : Hn * T0 = S0 * Cn + R)
    (hfact : T0 = Qp * Qmᵀ) (hsym : T0ᵀ = T0) :
    Cn = Qm * correctedB Qp S0 Hn R * Qmᵀ := by
  have hST : S0 * T0 = 1 := mul_eq_one_comm.mp hTS
  have heff : (Hn - R * S0) * T0 = S0 * Cn := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hST, Matrix.mul_one, hline]
    abel
  exact FMSA.MixtureBaxterCore.star_of_first_order_oz Qp Qm T0 S0
    (Hn - R * S0) Cn (correctedB Qp S0 Hn R) heff hTS hfact hsym rfl

theorem hierarchy_dcf (H C : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (Qp Qm T0 S0 : Matrix (Fin N) (Fin N) ℂ) (n : ℕ)
    (hTS : T0 * S0 = 1)
    (hline : H n * T0 = S0 * C n + lowerSource H C n)
    (hfact : T0 = Qp * Qmᵀ) (hsym : T0ᵀ = T0) :
    C n = Qm * correctedB Qp S0 (H n) (lowerSource H C n) * Qmᵀ :=
  corrected_b_dcf Qp Qm T0 S0 (H n) (C n) (lowerSource H C n) hTS hline hfact hsym

theorem first_order_recovered (H C : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (Qp S0 : Matrix (Fin N) (Fin N) ℂ) :
    correctedB Qp S0 (H 1) (lowerSource H C 1) = rawB Qp (H 1) := by
  simp [lower_source_one, correctedB, rawB]

end Matrices

section FiniteBasis

def taylorCoeff (f : ℝ → ℝ) (n : ℕ) (K0 : ℝ) : ℝ :=
  iteratedDeriv n f K0 / (n.factorial : ℝ)

theorem coefficient_fixed_basis {I : Type*} (s : Finset I) (c b : I → ℝ → ℝ)
    (n : ℕ) (K0 r : ℝ) (hc : ∀ i ∈ s, ContDiffAt ℝ n (c i) K0) :
    taylorCoeff (fun K => ∑ i ∈ s, c i K * b i r) n K0 =
      ∑ i ∈ s, b i r * taylorCoeff (c i) n K0 := by
  unfold taylorCoeff
  rw [FMSA.ExactMSA.Breakpoint.iteratedDeriv_coeffBasis_eq_of_contDiffAt s c b n K0 r hc,
    Finset.sum_div]
  simp only [mul_div_assoc]

def strictTrunc (f : ℝ → ℝ → ℝ) (L : ℕ) (K0 tau r : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (L + 1), taylorCoeff (fun K => f K r) n K0 * tau ^ n

/-- Every finite truncation has the same finite spatial basis. Smooth coefficient
jets, not convergence of an infinite coupling series, are the only analytic input. -/
theorem truncation_fixed_basis {I : Type*} (s : Finset I) (c b : I → ℝ → ℝ)
    (L : ℕ) (K0 tau r : ℝ)
    (hc : ∀ n ≤ L, ∀ i ∈ s, ContDiffAt ℝ n (c i) K0) :
    strictTrunc (fun K r => ∑ i ∈ s, c i K * b i r) L K0 tau r =
      ∑ i ∈ s, b i r * (∑ n ∈ Finset.range (L + 1), taylorCoeff (c i) n K0 * tau ^ n) := by
  unfold strictTrunc
  have hcoeff : ∀ n ∈ Finset.range (L + 1),
      taylorCoeff (fun K => ∑ i ∈ s, c i K * b i r) n K0 =
        ∑ i ∈ s, b i r * taylorCoeff (c i) n K0 := by
    intro n hn
    exact coefficient_fixed_basis s c b n K0 r (hc n (by simpa using Finset.mem_range.mp hn))
  have hsum : (∑ n ∈ Finset.range (L + 1),
      taylorCoeff (fun K => ∑ i ∈ s, c i K * b i r) n K0 * tau ^ n) =
      ∑ n ∈ Finset.range (L + 1), (∑ i ∈ s, b i r * taylorCoeff (c i) n K0) * tau ^ n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hcoeff n hn]
  rw [hsum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

end FiniteBasis
end FMSA.ExactMSA.BHierarchy

/-- info: 'FMSA.ExactMSA.BHierarchy.lower_source_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BHierarchy.lower_source_one

/-- info: 'FMSA.ExactMSA.BHierarchy.lower_source_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BHierarchy.lower_source_two

/-- info: 'FMSA.ExactMSA.BHierarchy.corrected_b_eq_raw_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BHierarchy.corrected_b_eq_raw_sub

/-- info: 'FMSA.ExactMSA.BHierarchy.oz_order_dcf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BHierarchy.oz_order_dcf

/-- info: 'FMSA.ExactMSA.BHierarchy.baxter_dressing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BHierarchy.baxter_dressing

/-- info: 'FMSA.ExactMSA.BHierarchy.raw_b_dcf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BHierarchy.raw_b_dcf

/-- info: 'FMSA.ExactMSA.BHierarchy.corrected_b_dcf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BHierarchy.corrected_b_dcf

/-- info: 'FMSA.ExactMSA.BHierarchy.hierarchy_dcf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BHierarchy.hierarchy_dcf

/-- info: 'FMSA.ExactMSA.BHierarchy.first_order_recovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BHierarchy.first_order_recovered

/-- info: 'FMSA.ExactMSA.BHierarchy.coefficient_fixed_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BHierarchy.coefficient_fixed_basis

/-- info: 'FMSA.ExactMSA.BHierarchy.truncation_fixed_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BHierarchy.truncation_fixed_basis
