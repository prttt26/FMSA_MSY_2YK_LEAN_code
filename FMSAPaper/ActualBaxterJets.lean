import FMSAPaper.FiniteBasisJets
import LeanCode.YukawaOZMix.MSAMultiTailMixtureBasis

/-! All-order Cauchy convolution for the actual finite-tail Baxter factor.
The whole-line tail integrability is discharged by the foundation's mixed-rate
basis theorem; no assumption that different tails have different rates is used.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff BigOperators

namespace FMSA.Paper.ActualBaxterJets

open ExactMSA.MultiTailMixture ExactMSA.BSource FiniteBasis
variable {N : ℕ} {T : Type*} [Fintype T]

def factor (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  q z sigma (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
    (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j r

def factorPrime (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  qPrime z sigma (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
    (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j r

theorem factor_jet_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) (hp : ContDiffAt ℝ n p 0)
    (i j : Fin N) (r : ℝ) :
    jet (fun s => factor z rho sigma (p s) i j r) n =
      linear (fun b => jet (fun s => bhCoefficient z rho sigma (p s) i j b) n)
        (fun b => basisQ z sigma b i j r) := by
  simp_rw [factor, q_eq_basis]
  exact jet_linear _ _ _ (fun b =>
    ((bhCoefficient_contDiff z rho sigma i j b).of_le (by exact_mod_cast le_top)).contDiffAt.comp 0 hp)

theorem factorPrime_jet_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) (hp : ContDiffAt ℝ n p 0)
    (i j : Fin N) (r : ℝ) :
    jet (fun s => factorPrime z rho sigma (p s) i j r) n =
      linear (fun b => jet (fun s => bhCoefficient z rho sigma (p s) i j b) n)
        (fun b => basisPrime z sigma b i j r) := by
  simp_rw [factorPrime, qPrime_eq_basis]
  exact jet_linear _ _ _ (fun b =>
    ((bhCoefficient_contDiff z rho sigma i j b).of_le (by exact_mod_cast le_top)).contDiffAt.comp 0 hp)

/-- The actual infinite-tail convolution satisfies the normalized Cauchy
rule at every order. No derivative-under-the-integral premise remains. -/
theorem convolution_jet_cauchy
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j l : Fin N) (r : ℝ) :
    jet (fun s => ∫ t : ℝ,
      factorPrime z rho sigma (p s) i l (t + r) * factor z rho sigma (p s) j l t) n =
      ∑ a ∈ Finset.range (n + 1), ∫ t : ℝ,
        jet (fun s => factorPrime z rho sigma (p s) i l (t + r)) a *
        jet (fun s => factor z rho sigma (p s) j l t) (n - a) := by
  have hc (i j : Fin N) (b : BasisIndex T) :
      ContDiffAt ℝ n (fun s => bhCoefficient z rho sigma (p s) i j b) 0 :=
    ((bhCoefficient_contDiff z rho sigma i j b).contDiffAt.comp 0 hp).of_le
      (by exact_mod_cast le_top)
  have hfin (s : ℝ) : (∫ t : ℝ,
      factorPrime z rho sigma (p s) i l (t + r) * factor z rho sigma (p s) j l t) =
      bilinear (fun b => bhCoefficient z rho sigma (p s) i l b)
        (fun b => bhCoefficient z rho sigma (p s) j l b)
        (fun b c => basisConvolution z sigma b c i j l r) :=
    convolution_eq_basis z hz sigma _ _ _ _ hsigma i j l r
  simp_rw [hfin]
  rw [jet_bilinear _ _ _ n (hc i l) (hc j l)]
  apply Finset.sum_congr rfl
  intro a _
  have hpn (m : ℕ) : ContDiffAt ℝ m p 0 := hp.of_le (by exact_mod_cast le_top)
  simp_rw [factorPrime_jet_basis z rho sigma p a (hpn a),
    factor_jet_basis z rho sigma p (n - a) (hpn (n - a))]
  exact (integral_expansion _ _ (fun b t => basisPrime z sigma b i l (t + r))
    (fun c t => basisQ z sigma c j l t)
    (fun b c => basisConvolution_integrable z hz sigma hsigma b c i j l r)).symm

end FMSA.Paper.ActualBaxterJets

/-- info: 'FMSA.Paper.ActualBaxterJets.factor_jet_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterJets.factor_jet_basis

/-- info: 'FMSA.Paper.ActualBaxterJets.factorPrime_jet_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterJets.factorPrime_jet_basis

/-- info: 'FMSA.Paper.ActualBaxterJets.convolution_jet_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualBaxterJets.convolution_jet_cauchy
