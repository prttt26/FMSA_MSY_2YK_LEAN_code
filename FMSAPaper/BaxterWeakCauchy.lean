import FMSAPaper.BaxterWeakJets
import FMSAPaper.RadialIntegralJets

/-! Explicit all-order second-factor Cauchy density in the full reflected
weak identity, retaining linear and convolution lower-edge terms. -/
noncomputable section
open MeasureTheory Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Paper.BaxterWeakCauchy
open ExactMSA.MultiTailMixture ExactMSA.BSource MSAMixture
open ActualBaxterJets ActualBaxterBoundaryJets ActualBaxterSecondJets BaxterNormalization
open BaxterWeakJetBasis BaxterSecondIntegralJets BaxterWeakJets FiniteBasis FiniteIntegralJets
variable {N : ℕ} {T : Type*} [Fintype T]

def secondJetNumerator (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) (i j : Fin N) (r : ℝ) : ℝ :=
  -jet (fun s => factorPrime z rho sigma (p s) i j r) n +
    jet (fun s => factorPrime z rho sigma (p s) j i (-r)) n -
    ∑ l, rho l * ∑ a ∈ Finset.range (n+1),
      ((∫ t : ℝ, jet (fun s => factor z rho sigma (p s) i l t) a *
          jet (fun s => factorPrime z rho sigma (p s) j l (t-r)) (n-a)) +
        jet (fun s => factor z rho sigma (p s) i l (edgeLo sigma j l+r)) a *
          jet (fun s => lowerJump z rho sigma (p s) j l) (n-a))

theorem secondNumerator_jet_cauchy (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j : Fin N) (r : ℝ) :
    jet (fun s => actualSecondNumerator z rho sigma (p s) i j r) n =
      secondJetNumerator z rho sigma p n i j r := by
  have hc (a b : Fin N) (k : BasisIndex T) :
      ContDiffAt ℝ n (fun s => bhCoefficient z rho sigma (p s) a b k) 0 :=
    ((bhCoefficient_contDiff z rho sigma a b k).contDiffAt.comp 0 hp).of_le (by exact_mod_cast le_top)
  have hC (l : Fin N) : ContDiffAt ℝ n (fun s => actualSecondConvolution z rho sigma (p s) i j l r) 0 := by
    simp_rw [secondConvolution_eq_bilinear z hz rho sigma hsigma]
    exact ContDiffAt.sum (fun b _ => ContDiffAt.sum (fun c _ =>
      ((hc i l b).mul (hc j l c)).mul contDiffAt_const))
  have hi : ContDiffAt ℝ n (fun s => factorPrime z rho sigma (p s) i j r) 0 :=
    ((factorPrime_contDiff z rho sigma i j r).contDiffAt.comp 0 hp).of_le (by exact_mod_cast le_top)
  have hj : ContDiffAt ℝ n (fun s => factorPrime z rho sigma (p s) j i (-r)) 0 :=
    ((factorPrime_contDiff z rho sigma j i (-r)).contDiffAt.comp 0 hp).of_le (by exact_mod_cast le_top)
  change jet (fun s => -factorPrime z rho sigma (p s) i j r + factorPrime z rho sigma (p s) j i (-r) -
    ∑ l, rho l * actualSecondConvolution z rho sigma (p s) i j l r) n = _
  rw [jet_sub _ _ n (hi.neg.add hj) (ContDiffAt.sum (fun l _ => contDiffAt_const.mul (hC l))),
    jet_add _ _ n hi.neg hj, jet_neg, jet_sum _ n (fun l => contDiffAt_const.mul (hC l))]
  simp only [jet_const_mul, second_convolution_jet_cauchy z rho sigma hz hsigma p hp n, secondJetNumerator]

theorem fullPrimitive_weak_cauchy (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j : Fin N) (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hc : HasCompactSupport phi) :
    (∫ r : ℝ, jet (fun s => actualPrimitive z rho sigma (p s) i j r) n * deriv phi r) =
      (∫ r : ℝ, secondJetNumerator z rho sigma p n i j r * phi r) -
      jet (fun s => lowerJump z rho sigma (p s) i j) n * phi (edgeLo sigma i j) +
      jet (fun s => lowerJump z rho sigma (p s) j i) n * phi (-edgeLo sigma j i) := by
  simpa only [secondNumerator_jet_cauchy z hz rho sigma hsigma p hp n i j] using
    fullPrimitive_weak_jet z hz rho sigma hsigma p hp n i j phi hphi hc

end FMSA.Paper.BaxterWeakCauchy

/-- info: 'FMSA.Paper.BaxterWeakCauchy.secondNumerator_jet_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakCauchy.secondNumerator_jet_cauchy

/-- info: 'FMSA.Paper.BaxterWeakCauchy.fullPrimitive_weak_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterWeakCauchy.fullPrimitive_weak_cauchy
