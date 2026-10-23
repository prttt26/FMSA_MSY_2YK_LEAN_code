import FMSAPaper.ActualBaxterJets
import LeanCode.YukawaOZMix.MSAMultiTailMixtureTransform

/-! The actual root's exterior DCF is affine in coupling, so every higher
Taylor coefficient vanishes outside contact. No infinite-series premise. -/
noncomputable section
open Filter Topology
open scoped BigOperators

namespace FMSA.Paper.PhysicalExteriorJets

open ExactMSA.MultiTailMixture ExactMSA.BSource MSAMixture
variable {N : ℕ} {T : Type*} [Fintype T]

def rootCorrelation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  correlation z rho sigma (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
    (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j r

theorem exterior_locally_linear
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (i j : Fin N) (r : ℝ) (hr : edgeHi sigma i j < r) :
    (fun t => rootCorrelation z rho sigma (p t) i j r) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => t * ∑ u, K u i j * Real.exp (-z u * (r - edgeHi sigma i j)) / r) := by
  filter_upwards [hroot] with t ht
  rw [rootCorrelation, correlation_exterior_of_root z hz rho sigma (t • K) _ _ hsigma ht i j r hr]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem exterior_jet
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (i j : Fin N) (r : ℝ) (hr : edgeHi sigma i j < r) (n : ℕ) :
    jet (fun t => rootCorrelation z rho sigma (p t) i j r) n =
      if n = 1 then ∑ u, K u i j * Real.exp (-z u * (r - edgeHi sigma i j)) / r else 0 := by
  unfold jet
  rw [(exterior_locally_linear z rho sigma K hz hsigma p hroot i j r hr).iteratedDeriv_eq n,
    iteratedDeriv_mul_const_field]
  simp only [iteratedDeriv_fun_id_zero]
  by_cases hn : n = 1 <;> simp [hn]

theorem exterior_higher_jet_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (i j : Fin N) (r : ℝ) (hr : edgeHi sigma i j < r) (n : ℕ) (hn : 2 <= n) :
    jet (fun t => rootCorrelation z rho sigma (p t) i j r) n = 0 := by
  rw [exterior_jet z rho sigma K hz hsigma p hroot i j r hr n, if_neg (by omega)]

end FMSA.Paper.PhysicalExteriorJets

/-- info: 'FMSA.Paper.PhysicalExteriorJets.exterior_locally_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.PhysicalExteriorJets.exterior_locally_linear

/-- info: 'FMSA.Paper.PhysicalExteriorJets.exterior_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.PhysicalExteriorJets.exterior_jet

/-- info: 'FMSA.Paper.PhysicalExteriorJets.exterior_higher_jet_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.PhysicalExteriorJets.exterior_higher_jet_zero
