import LeanCode.YukawaOZMix.MSABSourceHierarchy

/-!
# Finite-basis coupling jets for the paper's Baxter relation

This module is included in the foundation's default paper proof collection. The bilinear
weights may include both ordinary integrals on the whole real line and jump
evaluations. No compact-support assumption or distinct-rate assumption is used.
Identifying these weights with the actual multirate BH factor remains a separate
physical obligation; this module does not assert that identification.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Paper.FiniteBasis

open ExactMSA.BSource

variable {I J : Type*} [Fintype I] [Fintype J]

def linear (x : I → ℝ) (L : I → ℝ) : ℝ := ∑ i, x i * L i

def bilinear (x : I → ℝ) (y : J → ℝ) (W : I → J → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * y j * W i j

theorem jet_sum (f : I → ℝ → ℝ) (n : ℕ)
    (hf : ∀ i, ContDiffAt ℝ n (f i) 0) :
    jet (fun t => ∑ i, f i t) n = ∑ i, jet (f i) n := by
  unfold jet
  rw [iteratedDeriv_fun_sum (fun i _ => hf i), Finset.sum_div]

theorem jet_mul_const (f : ℝ → ℝ) (c : ℝ) (n : ℕ) :
    jet (fun t => f t * c) n = jet f n * c := by
  simp only [jet, iteratedDeriv_mul_const_field]
  ring

theorem jet_linear (x : ℝ → I → ℝ) (L : I → ℝ) (n : ℕ)
    (hx : ∀ i, ContDiffAt ℝ n (fun t => x t i) 0) :
    jet (fun t => linear (x t) L) n = linear (fun i => jet (fun t => x t i) n) L := by
  unfold linear
  rw [jet_sum _ n (fun i => (hx i).mul contDiffAt_const)]
  simp_rw [jet_mul_const]

/-- Normalized Leibniz rule for any fixed finite bilinear kernel, including
noncompact tail integrals and the atomic part of a distributional derivative. -/
theorem jet_bilinear (x : ℝ → I → ℝ) (y : ℝ → J → ℝ)
    (W : I → J → ℝ) (n : ℕ)
    (hx : ∀ i, ContDiffAt ℝ n (fun t => x t i) 0)
    (hy : ∀ j, ContDiffAt ℝ n (fun t => y t j) 0) :
    jet (fun t => bilinear (x t) (y t) W) n =
      ∑ a ∈ Finset.range (n + 1),
        bilinear (fun i => jet (fun t => x t i) a)
          (fun j => jet (fun t => y t j) (n - a)) W := by
  unfold bilinear
  rw [jet_sum _ n (fun i => ContDiffAt.sum (fun j _ =>
    ((hx i).mul (hy j)).mul contDiffAt_const))]
  simp_rw [jet_sum _ n (fun j => ((hx _).mul (hy j)).mul contDiffAt_const)]
  simp_rw [jet_mul_const, normalized_mul _ _ n (hx _) (hy _), Finset.sum_mul]
  calc
    _ = ∑ i, ∑ a ∈ Finset.range (n + 1), ∑ j,
        jet (fun t => x t i) a * jet (fun t => y t j) (n - a) * W i j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Linear and bilinear terms in the Baxter relation, with all species weights
and the factor `-2*pi` absorbed into `W`. -/
theorem jet_linear_add_bilinear (x : ℝ → I → ℝ) (L : I → ℝ)
    (W : I → I → ℝ) (n : ℕ)
    (hx : ∀ i, ContDiffAt ℝ n (fun t => x t i) 0) :
    jet (fun t => linear (x t) L + bilinear (x t) (x t) W) n =
      linear (fun i => jet (fun t => x t i) n) L +
        ∑ a ∈ Finset.range (n + 1),
          bilinear (fun i => jet (fun t => x t i) a)
            (fun i => jet (fun t => x t i) (n - a)) W := by
  have hL : ContDiffAt ℝ n (fun t => linear (x t) L) 0 := by
    exact ContDiffAt.sum (fun i _ => (hx i).mul contDiffAt_const)
  have hW : ContDiffAt ℝ n (fun t => bilinear (x t) (x t) W) 0 := by
    exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
      ((hx i).mul (hx j)).mul contDiffAt_const))
  have hadd : jet (fun t => linear (x t) L + bilinear (x t) (x t) W) n =
      jet (fun t => linear (x t) L) n + jet (fun t => bilinear (x t) (x t) W) n := by
    unfold jet
    rw [iteratedDeriv_fun_add hL hW, add_div]
  rw [hadd, jet_linear _ _ _ hx, jet_bilinear _ _ _ _ hx hx]

/-- A local Baxter identity suffices: no global-in-coupling identity and no
convergence of an infinite Taylor series is needed. -/
theorem jet_of_local_baxter_identity (c : ℝ → ℝ) (x : ℝ → I → ℝ)
    (L : I → ℝ) (W : I → I → ℝ) (r : ℝ) (n : ℕ)
    (hx : ∀ i, ContDiffAt ℝ n (fun t => x t i) 0)
    (h : (fun t => r * c t) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => linear (x t) L + bilinear (x t) (x t) W)) :
    r * jet c n = linear (fun i => jet (fun t => x t i) n) L +
      ∑ a ∈ Finset.range (n + 1),
        bilinear (fun i => jet (fun t => x t i) a)
          (fun i => jet (fun t => x t i) (n - a)) W := by
  have he := congrArg (fun v : ℝ => v / (n.factorial : ℝ)) (h.iteratedDeriv_eq n)
  have hl : jet (fun t => r * c t) n = r * jet c n := by
    simp only [jet, iteratedDeriv_const_mul_field]
    ring
  change jet (fun t => r * c t) n =
    jet (fun t => linear (x t) L + bilinear (x t) (x t) W) n at he
  rw [hl, jet_linear_add_bilinear _ _ _ _ hx] at he
  exact he

/-- Finite expansions can be integrated on the entire line, provided each
basis product is integrable. Exponential tails are not truncated. -/
theorem integral_expansion (x : I → ℝ) (y : J → ℝ)
    (phi : I → ℝ → ℝ) (psi : J → ℝ → ℝ)
    (hint : ∀ i j, Integrable (fun t => phi i t * psi j t)) :
    (∫ t, linear x (fun i => phi i t) * linear y (fun j => psi j t)) =
      bilinear x y (fun i j => ∫ t, phi i t * psi j t) := by
  have hpoint (t : ℝ) :
      linear x (fun i => phi i t) * linear y (fun j => psi j t) =
        ∑ i, ∑ j, (x i * y j) * (phi i t * psi j t) := by
    simp only [linear, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hint i j).const_mul (x i * y j)))]
  unfold bilinear
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul (x i * y j))]
  simp_rw [integral_const_mul]

/-- Product of two finite evaluations, used for each jump atom. -/
theorem evaluation_expansion (x : I → ℝ) (y : J → ℝ) (p : I → ℝ) (q : J → ℝ) :
    linear x p * linear y q = bilinear x y (fun i j => p i * q j) := by
  simp only [linear, bilinear, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- An ordinary whole-line integral plus a jump at the shifted lower endpoint
is a fixed bilinear form in the factor coefficients. The supplied `jump`
is the jump amplitude of each derivative basis function. -/
theorem integral_add_jump_expansion (x : I → ℝ) (y : J → ℝ)
    (phi : I → ℝ → ℝ) (psi : J → ℝ → ℝ) (jump : J → ℝ) (edge : ℝ)
    (hint : ∀ i j, Integrable (fun t => phi i t * psi j t)) :
    (∫ t, linear x (fun i => phi i t) * linear y (fun j => psi j t)) +
        linear x (fun i => phi i edge) * linear y jump =
      bilinear x y (fun i j => (∫ t, phi i t * psi j t) + phi i edge * jump j) := by
  rw [integral_expansion x y phi psi hint, evaluation_expansion]
  simp only [bilinear, mul_add, Finset.sum_add_distrib]

theorem jet_integral_add_jump (x : ℝ → I → ℝ) (y : ℝ → J → ℝ)
    (phi : I → ℝ → ℝ) (psi : J → ℝ → ℝ) (jump : J → ℝ) (edge : ℝ) (n : ℕ)
    (hint : ∀ i j, Integrable (fun t => phi i t * psi j t))
    (hx : ∀ i, ContDiffAt ℝ n (fun t => x t i) 0)
    (hy : ∀ j, ContDiffAt ℝ n (fun t => y t j) 0) :
    jet (fun tau =>
      (∫ t, linear (x tau) (fun i => phi i t) * linear (y tau) (fun j => psi j t)) +
        linear (x tau) (fun i => phi i edge) * linear (y tau) jump) n =
      ∑ a ∈ Finset.range (n + 1), bilinear
        (fun i => jet (fun tau => x tau i) a)
        (fun j => jet (fun tau => y tau j) (n - a))
        (fun i j => (∫ t, phi i t * psi j t) + phi i edge * jump j) := by
  simp_rw [integral_add_jump_expansion _ _ phi psi jump edge hint]
  exact jet_bilinear _ _ _ _ hx hy

end FMSA.Paper.FiniteBasis

/-! Axiom-footprint gates for every theorem in this extension module. -/

/-- info: 'FMSA.Paper.FiniteBasis.jet_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteBasis.jet_sum

/-- info: 'FMSA.Paper.FiniteBasis.jet_mul_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteBasis.jet_mul_const

/-- info: 'FMSA.Paper.FiniteBasis.jet_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteBasis.jet_linear

/-- info: 'FMSA.Paper.FiniteBasis.jet_bilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteBasis.jet_bilinear

/-- info: 'FMSA.Paper.FiniteBasis.jet_linear_add_bilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteBasis.jet_linear_add_bilinear

/-- info: 'FMSA.Paper.FiniteBasis.jet_of_local_baxter_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteBasis.jet_of_local_baxter_identity

/-- info: 'FMSA.Paper.FiniteBasis.integral_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteBasis.integral_expansion

/-- info: 'FMSA.Paper.FiniteBasis.evaluation_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteBasis.evaluation_expansion

/-- info: 'FMSA.Paper.FiniteBasis.integral_add_jump_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteBasis.integral_add_jump_expansion

/-- info: 'FMSA.Paper.FiniteBasis.jet_integral_add_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FiniteBasis.jet_integral_add_jump
