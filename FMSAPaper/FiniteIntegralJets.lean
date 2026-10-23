import FMSAPaper.FiniteBasisJets

/-! Coupling jets commute with integration of a fixed finite integrable
dictionary. Integrability and smoothness of the integrated function follow
from the representation, rather than being imposed as interchange premises. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Paper.FiniteIntegralJets
open ExactMSA.BSource FiniteBasis
variable {I : Type*} [Fintype I]

theorem jet_add (f g : ℝ → ℝ) (n : ℕ)
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0) :
    jet (fun s => f s + g s) n = jet f n + jet g n := by
  simp only [jet, iteratedDeriv_fun_add hf hg, add_div]

theorem jet_sub (f g : ℝ → ℝ) (n : ℕ)
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0) :
    jet (fun s => f s - g s) n = jet f n - jet g n := by
  simp only [jet, iteratedDeriv_fun_sub hf hg, sub_div]

theorem jet_const_mul (f : ℝ → ℝ) (c : ℝ) (n : ℕ) :
    jet (fun s => c * f s) n = c * jet f n := by
  simp only [jet, iteratedDeriv_const_mul_field]
  ring

theorem jet_neg (f : ℝ → ℝ) (n : ℕ) :
    jet (fun s => -f s) n = -jet f n := by
  simp only [jet, iteratedDeriv_fun_neg, neg_div]

theorem integrable_linear (a : I → ℝ) (b : I → ℝ → ℝ)
    (hb : ∀ i, Integrable (b i)) :
    Integrable (fun r => linear a (fun i => b i r)) :=
  integrable_finsetSum _ (fun i _ => (hb i).const_mul (a i))

theorem integral_linear (a : I → ℝ) (b : I → ℝ → ℝ)
    (hb : ∀ i, Integrable (b i)) :
    (∫ r : ℝ, linear a (fun i => b i r)) = linear a (fun i => ∫ r : ℝ, b i r) := by
  unfold linear
  rw [integral_finsetSum _ (fun i _ => (hb i).const_mul (a i))]
  simp only [integral_const_mul]

theorem integral_linear_contDiffAt (a : ℝ → I → ℝ) (b : I → ℝ → ℝ)
    (n : ℕ∞ω) (ha : ∀ i, ContDiffAt ℝ n (fun s => a s i) 0)
    (hb : ∀ i, Integrable (b i)) :
    ContDiffAt ℝ n (fun s => ∫ r : ℝ, linear (a s) (fun i => b i r)) 0 := by
  simp_rw [integral_linear _ b hb]
  exact ContDiffAt.sum (fun i _ => (ha i).mul contDiffAt_const)

theorem jet_integral_linear (a : ℝ → I → ℝ) (b : I → ℝ → ℝ)
    (n : ℕ) (ha : ∀ i, ContDiffAt ℝ n (fun s => a s i) 0)
    (hb : ∀ i, Integrable (b i)) :
    jet (fun s => ∫ r : ℝ, linear (a s) (fun i => b i r)) n =
      ∫ r : ℝ, jet (fun s => linear (a s) (fun i => b i r)) n := by
  simp_rw [integral_linear _ b hb, jet_linear _ _ n ha]
  exact (integral_linear _ b hb).symm

end FMSA.Paper.FiniteIntegralJets

/-- info: 'FMSA.Paper.FiniteIntegralJets.jet_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteIntegralJets.jet_add

/-- info: 'FMSA.Paper.FiniteIntegralJets.jet_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteIntegralJets.jet_sub

/-- info: 'FMSA.Paper.FiniteIntegralJets.jet_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteIntegralJets.jet_const_mul

/-- info: 'FMSA.Paper.FiniteIntegralJets.jet_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteIntegralJets.jet_neg

/-- info: 'FMSA.Paper.FiniteIntegralJets.integrable_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteIntegralJets.integrable_linear

/-- info: 'FMSA.Paper.FiniteIntegralJets.integral_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteIntegralJets.integral_linear

/-- info: 'FMSA.Paper.FiniteIntegralJets.integral_linear_contDiffAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteIntegralJets.integral_linear_contDiffAt

/-- info: 'FMSA.Paper.FiniteIntegralJets.jet_integral_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteIntegralJets.jet_integral_linear
