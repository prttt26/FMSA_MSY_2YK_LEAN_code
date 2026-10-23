import FMSAPaper.ActualBaxterJets

/-! The actual lower-edge jump is retained in all-order Baxter convolution. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff BigOperators

namespace FMSA.Paper.ActualBaxterBoundaryJets

open ExactMSA.MultiTailMixture ExactMSA.BSource FiniteBasis ActualBaxterJets
open MSAMixture
variable {N : ℕ} {T : Type*} [Fintype T]

def lowerJump (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) : ℝ :=
  lowerValue sigma (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
    (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j

theorem lowerJump_eq_factor (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 <= sigma i) (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    lowerJump z rho sigma p i j = factor z rho sigma p i j (edgeLo sigma i j) :=
  (q_at_lowerEdge z sigma _ _ _ _ hsigma i j).symm

/-- The corrected convolution includes both its ordinary whole-line integral
and the actual lowerValue atom. All mixed-rate integrability is internal.
The theorem is algebraic in this corrected expression; spatial distributional
identification of a DCF is not hidden as an assumption. -/
theorem convolution_with_lowerJump_jet
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) (hp : ContDiffAt ℝ n p 0)
    (i j l : Fin N) (r : ℝ) :
    jet (fun s =>
      (∫ t : ℝ, factor z rho sigma (p s) j l t * factorPrime z rho sigma (p s) i l (t + r)) +
        factor z rho sigma (p s) j l (edgeLo sigma i l - r) * lowerJump z rho sigma (p s) i l) n =
      ∑ a ∈ Finset.range (n + 1), bilinear
        (fun b => jet (fun s => bhCoefficient z rho sigma (p s) j l b) a)
        (fun c => jet (fun s => bhCoefficient z rho sigma (p s) i l c) (n - a))
        (fun b c =>
          (∫ t : ℝ, basisQ z sigma b j l t * basisPrime z sigma c i l (t + r)) +
          basisQ z sigma b j l (edgeLo sigma i l - r) * basisQ z sigma c i l (edgeLo sigma i l)) := by
  have hInt (b c : BasisIndex T) :
      Integrable (fun t : ℝ => basisQ z sigma b j l t * basisPrime z sigma c i l (t + r)) := by
    simpa only [mul_comm] using basisConvolution_integrable z hz sigma hsigma c b i j l r
  have hc (i j : Fin N) (b : BasisIndex T) :
      ContDiffAt ℝ n (fun s => bhCoefficient z rho sigma (p s) i j b) 0 :=
    ((bhCoefficient_contDiff z rho sigma i j b).of_le
      (by exact_mod_cast le_top)).contDiffAt.comp 0 hp
  simp_rw [lowerJump_eq_factor z rho sigma hsigma, factor, factorPrime, q_eq_basis, qPrime_eq_basis]
  exact jet_integral_add_jump
    (fun s b => bhCoefficient z rho sigma (p s) j l b)
    (fun s c => bhCoefficient z rho sigma (p s) i l c)
    (fun b t => basisQ z sigma b j l t) (fun c t => basisPrime z sigma c i l (t + r))
    (fun c => basisQ z sigma c i l (edgeLo sigma i l)) (edgeLo sigma i l - r) n hInt (hc j l) (hc i l)

/-- In the ordered positive-radius convention the actual atom is zero, by
support geometry, at every coupling and hence at every Taylor order. -/
theorem ordered_lowerJump_jet_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ)
    (i j l : Fin N) (horder : sigma j <= sigma i) (r : ℝ) (hr : 0 < r) :
    jet (fun s => lowerJump z rho sigma (p s) i l *
      factor z rho sigma (p s) j l (edgeLo sigma i l - r)) n = 0 := by
  have he (s : ℝ) : lowerJump z rho sigma (p s) i l *
      factor z rho sigma (p s) j l (edgeLo sigma i l - r) = 0 :=
    lowerEdge_jump_product_zero z sigma _ _ _ _ i j l horder r hr
  simp_rw [he]
  simp [jet]

end FMSA.Paper.ActualBaxterBoundaryJets

/-- info: 'FMSA.Paper.ActualBaxterBoundaryJets.lowerJump_eq_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterBoundaryJets.lowerJump_eq_factor

/-- info: 'FMSA.Paper.ActualBaxterBoundaryJets.convolution_with_lowerJump_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterBoundaryJets.convolution_with_lowerJump_jet

/-- info: 'FMSA.Paper.ActualBaxterBoundaryJets.ordered_lowerJump_jet_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterBoundaryJets.ordered_lowerJump_jet_zero
