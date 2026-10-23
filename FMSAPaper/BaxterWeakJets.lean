import FMSAPaper.BaxterSecondIntegralJets

/-! All coupling orders of the full reflected weak Baxter identity. Both
linear Dirac coefficients and the corrected convolution density are retained;
all exchanges of test integration and coupling jets are proved internally. -/
noncomputable section
open MeasureTheory Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Paper.BaxterWeakJets
open ExactMSA.MultiTailMixture ExactMSA.BSource MSAMixture
open ActualBaxterJets ActualBaxterBoundaryJets BaxterWeakPrimitive
open BaxterWeakJetBasis BaxterSecondIntegralJets FiniteBasis
variable {N : ℕ} {T : Type*} [Fintype T]

theorem lowerJump_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N => lowerJump z rho sigma p i j) := by
  simp_rw [lowerJump_eq_factor z rho sigma hsigma, factor, q_eq_basis]
  change ContDiff ℝ ∞ (fun p => ∑ b : BasisIndex T,
    bhCoefficient z rho sigma p i j b * basisQ z sigma b i j (edgeLo sigma i j))
  fun_prop

theorem fullPrimitive_weak_jet (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j : Fin N) (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hc : HasCompactSupport phi) :
    (∫ r : ℝ, jet (fun s => actualPrimitive z rho sigma (p s) i j r) n * deriv phi r) =
      (∫ r : ℝ, jet (fun s => actualSecondNumerator z rho sigma (p s) i j r) n * phi r) -
      jet (fun s => lowerJump z rho sigma (p s) i j) n * phi (edgeLo sigma i j) +
      jet (fun s => lowerJump z rho sigma (p s) j i) n * phi (-edgeLo sigma j i) := by
  let u := fun s => ∫ r : ℝ, actualSecondNumerator z rho sigma (p s) i j r * phi r
  let a := fun s => lowerJump z rho sigma (p s) i j
  let b := fun s => lowerJump z rho sigma (p s) j i
  have hu : ContDiffAt ℝ n u 0 :=
    (second_test_integral_contDiffAt z hz rho sigma hsigma p hp i j phi hphi.continuous hc).of_le
      (by exact_mod_cast le_top)
  have ha : ContDiffAt ℝ n a 0 :=
    ((lowerJump_contDiff z rho sigma hsigma i j).contDiffAt.comp 0 hp).of_le (by exact_mod_cast le_top)
  have hb : ContDiffAt ℝ n b 0 :=
    ((lowerJump_contDiff z rho sigma hsigma j i).contDiffAt.comp 0 hp).of_le (by exact_mod_cast le_top)
  have he : (fun s => ∫ r : ℝ, actualPrimitive z rho sigma (p s) i j r * deriv phi r) =
      (fun s => u s - a s * phi (edgeLo sigma i j) + b s * phi (-edgeLo sigma j i)) := by
    funext s
    exact fullPrimitive_weak_derivative z hz rho sigma _ _ _ _ hsigma i j phi hphi hc
  have hj := congrArg (fun f : ℝ → ℝ => jet f n) he
  have hr : jet (fun s => u s - a s * phi (edgeLo sigma i j) + b s * phi (-edgeLo sigma j i)) n =
      jet u n - jet a n * phi (edgeLo sigma i j) + jet b n * phi (-edgeLo sigma j i) := by
    simp only [jet,
      iteratedDeriv_fun_add (hu.sub (ha.mul contDiffAt_const)) (hb.mul contDiffAt_const),
      iteratedDeriv_fun_sub hu (ha.mul contDiffAt_const), iteratedDeriv_mul_const_field,
      add_div, sub_div]
    ring
  rw [hr, primitive_test_jet_integral z hz rho sigma hsigma p hp n i j (deriv phi)
    hphi.continuous_deriv_one hc.deriv] at hj
  dsimp only [u, a, b] at hj
  rw [second_test_jet_integral z hz rho sigma hsigma p hp n i j phi hphi.continuous hc] at hj
  exact hj

end FMSA.Paper.BaxterWeakJets

/-- info: 'FMSA.Paper.BaxterWeakJets.lowerJump_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakJets.lowerJump_contDiff

/-- info: 'FMSA.Paper.BaxterWeakJets.fullPrimitive_weak_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakJets.fullPrimitive_weak_jet
