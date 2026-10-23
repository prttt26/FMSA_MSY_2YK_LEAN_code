import FMSAPaper.BaxterWeakCauchy

/-! Complete reflected weak Cauchy formula for every coupling coefficient of
the actual radial MSA DCF, for all species pairs. Root reciprocity, test/jet
interchange and lower-edge atoms are accounted for explicitly. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Paper.ActualRadialWeakJets
open ExactMSA.MultiTailMixture ExactMSA.BSource MSAMixture MatrixQ0
open ActualBaxterJets ActualBaxterBoundaryJets BaxterNormalization
open BaxterWeakJetBasis BaxterWeakCauchy FiniteIntegralJets ActualRadialWeak RadialIntegralJets
variable {N : ℕ} {T : Type*} [Fintype T]

theorem local_root_primitive_weak_jet (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (hv : vacMix rho sigma ≠ 0)
    (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (hroot : ∀ᶠ s in 𝓝 (0 : ℝ), IsRoot z rho sigma (s • K) (p s).1 (p s).2)
    (n : ℕ) (i j : Fin N) (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hc : HasCompactSupport phi) (hsupp : tsupport phi ⊆ Ioi (0 : ℝ)) :
    (∫ r : ℝ, jet (fun s => actualPrimitive z rho sigma (p s) i j r) n * deriv phi r) =
      2*π * ∫ r : ℝ, r * jet (fun s => orderedRadialCorrelation z rho sigma (s • K)
        (p s).1 (p s).2 i j r) n * phi r := by
  have hzero : phi 0 = 0 := by
    by_contra hn
    exact (lt_irrefl (0 : ℝ)) (hsupp (subset_tsupport phi hn))
  have he : (fun s => ∫ r : ℝ, actualPrimitive z rho sigma (p s) i j r * deriv phi r) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => 2*π * ∫ r : ℝ, r * orderedRadialCorrelation z rho sigma (s • K)
        (p s).1 (p s).2 i j r * phi r) := by
    filter_upwards [hroot] with s hs
    apply root_primitive_weak z hz rho sigma (s • K) (p s).1 (p s).2 hsigma hv hs _ i j phi hphi hc hsupp
    intro u a b
    simp only [Pi.smul_apply, smul_eq_mul, hK u a b]
  have hj := congrArg (fun x : ℝ => x / (n.factorial : ℝ)) (he.iteratedDeriv_eq n)
  change jet (fun s => ∫ r : ℝ, actualPrimitive z rho sigma (p s) i j r * deriv phi r) n =
    jet (fun s => 2*π * ∫ r : ℝ, r * orderedRadialCorrelation z rho sigma (s • K)
      (p s).1 (p s).2 i j r * phi r) n at hj
  rw [primitive_test_jet_integral z hz rho sigma hsigma p hp n i j (deriv phi)
    hphi.continuous_deriv_one hc.deriv, jet_const_mul,
    ordered_test_jet_integral z hz rho sigma hsigma (fun s => s • K) p hp n i j phi hphi.continuous hc hzero] at hj
  exact hj

theorem local_root_second_weak_cauchy (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (hv : vacMix rho sigma ≠ 0)
    (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (hroot : ∀ᶠ s in 𝓝 (0 : ℝ), IsRoot z rho sigma (s • K) (p s).1 (p s).2)
    (n : ℕ) (i j : Fin N) (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hc : HasCompactSupport phi) (hsupp : tsupport phi ⊆ Ioi (0 : ℝ)) :
    2*π * (∫ r : ℝ, r * jet (fun s => orderedRadialCorrelation z rho sigma (s • K)
      (p s).1 (p s).2 i j r) n * phi r) =
      (∫ r : ℝ, secondJetNumerator z rho sigma p n i j r * phi r) -
      jet (fun s => lowerJump z rho sigma (p s) i j) n * phi (edgeLo sigma i j) +
      jet (fun s => lowerJump z rho sigma (p s) j i) n * phi (-edgeLo sigma j i) := by
  rw [← local_root_primitive_weak_jet z hz rho sigma K hsigma hv hK p hp hroot n i j phi hphi hc hsupp]
  exact fullPrimitive_weak_cauchy z hz rho sigma hsigma p hp n i j phi hphi hc

def normalizedSecondJet (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) (i j : Fin N) (r : ℝ) : ℝ :=
  -jet (fun s => factorPrime z rho sigma (p s) i j r / (2*π)) n +
    jet (fun s => factorPrime z rho sigma (p s) j i (-r) / (2*π)) n -
    2*π * ∑ l, rho l * ∑ a ∈ Finset.range (n+1),
      ((∫ t : ℝ, jet (fun s => factor z rho sigma (p s) i l t / (2*π)) a *
          jet (fun s => factorPrime z rho sigma (p s) j l (t-r) / (2*π)) (n-a)) +
        jet (fun s => factor z rho sigma (p s) i l (edgeLo sigma j l+r) / (2*π)) a *
          jet (fun s => lowerJump z rho sigma (p s) j l / (2*π)) (n-a))

theorem normalizedSecondJet_eq (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) (i j : Fin N) (r : ℝ) :
    normalizedSecondJet z rho sigma p n i j r = secondJetNumerator z rho sigma p n i j r / (2*π) := by
  unfold normalizedSecondJet secondJetNumerator
  simp_rw [jet_div_const, div_mul_div_comm, integral_div, ← add_div]
  simp only [← Finset.sum_div, ← mul_div_assoc]
  field_simp

theorem normalized_local_root_weak_cauchy (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hsigma : ∀ i, 0 <= sigma i) (hv : vacMix rho sigma ≠ 0)
    (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (hroot : ∀ᶠ s in 𝓝 (0 : ℝ), IsRoot z rho sigma (s • K) (p s).1 (p s).2)
    (n : ℕ) (i j : Fin N) (phi : ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hc : HasCompactSupport phi) (hsupp : tsupport phi ⊆ Ioi (0 : ℝ)) :
    (∫ r : ℝ, r * jet (fun s => orderedRadialCorrelation z rho sigma (s • K)
      (p s).1 (p s).2 i j r) n * phi r) =
      (∫ r : ℝ, normalizedSecondJet z rho sigma p n i j r * phi r) -
      jet (fun s => lowerJump z rho sigma (p s) i j / (2*π)) n * phi (edgeLo sigma i j) +
      jet (fun s => lowerJump z rho sigma (p s) j i / (2*π)) n * phi (-edgeLo sigma j i) := by
  have h := local_root_second_weak_cauchy z hz rho sigma K hsigma hv hK p hp hroot n i j phi hphi hc hsupp
  have h2 : (2*π : ℝ) ≠ 0 := by positivity
  simp only [normalizedSecondJet_eq, jet_div_const, div_mul_eq_mul_div, integral_div]
  calc (∫ r : ℝ, r * jet (fun s => orderedRadialCorrelation z rho sigma (s • K)
          (p s).1 (p s).2 i j r) n * phi r)
        = (2*π * ∫ r : ℝ, r * jet (fun s => orderedRadialCorrelation z rho sigma (s • K)
          (p s).1 (p s).2 i j r) n * phi r) / (2*π) := by rw [mul_div_cancel_left₀ _ h2]
    _ = _ := by rw [h]; ring

end FMSA.Paper.ActualRadialWeakJets

/-- info: 'FMSA.Paper.ActualRadialWeakJets.local_root_primitive_weak_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRadialWeakJets.local_root_primitive_weak_jet

/-- info: 'FMSA.Paper.ActualRadialWeakJets.local_root_second_weak_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRadialWeakJets.local_root_second_weak_cauchy

/-- info: 'FMSA.Paper.ActualRadialWeakJets.normalizedSecondJet_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRadialWeakJets.normalizedSecondJet_eq

/-- info: 'FMSA.Paper.ActualRadialWeakJets.normalized_local_root_weak_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualRadialWeakJets.normalized_local_root_weak_cauchy
