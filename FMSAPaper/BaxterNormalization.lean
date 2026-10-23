import FMSAPaper.PhysicalExteriorJets
import LeanCode.YukawaOZMix.MSAMultiTailMixtureShell

/-! The paper normalization of the actual Baxter primitive, its spatial
DCF derivative, and its all-order coupling Cauchy sum. The whole-line primitive
includes reflection. Ordered positive radii remove that term by support. -/
noncomputable section
open MeasureTheory Filter Topology Real
open scoped ContDiff BigOperators

namespace FMSA.Paper.BaxterNormalization

open ExactMSA.MultiTailMixture ExactMSA.BSource MSAMixture
open ActualBaxterJets PhysicalExteriorJets FiniteBasis
variable {N : ℕ} {T : Type*} [Fintype T]

def normalizedPrimitive (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  (baxterPrimitive z rho sigma (amplitudeA z rho sigma p.1 p.2)
    (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2)
    (C z rho sigma p.1 p.2) i j r).re / (2 * π)

theorem primitive_hasDerivAt (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (horder : sigma j <= sigma i)
    (r : ℝ) (hr : 0 < r) (hrR : r ≠ edgeHi sigma i j) :
    HasDerivAt (normalizedPrimitive z rho sigma p i j)
      (-r * rootCorrelation z rho sigma p i j r) r := by
  have h := (baxterPrimitive_re_hasDerivAt z hz rho sigma
    (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
    (W z rho p.1 p.2) (C z rho sigma p.1 p.2) hsigma i j horder r hr hrR).div_const (2 * π)
  convert! h using 1
  unfold rootCorrelation
  field_simp

/-- The integrated identity crosses contact without a missing contact atom. -/
theorem primitive_shell_window (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (horder : sigma j <= sigma i)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    normalizedPrimitive z rho sigma p i j a - normalizedPrimitive z rho sigma p i j b =
      ∫ r in a..b, r * rootCorrelation z rho sigma p i j r := by
  unfold normalizedPrimitive
  rw [baxterPrimitive_positive_eq_ofReal z rho sigma _ _ _ _ i j horder a ha,
    baxterPrimitive_positive_eq_ofReal z rho sigma _ _ _ _ i j horder b hb]
  simp only [Complex.ofReal_re, ← sub_div]
  rw [orderedPrimitiveReal_shell_window z hz rho sigma _ _ _ _ hsigma i j horder a b ha hb]
  exact mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero pi_ne_zero)

theorem factorPrime_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (i j : Fin N) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N => factorPrime z rho sigma p i j r) := by
  simp only [factorPrime, qPrime_eq_basis]
  change ContDiff ℝ ∞ (fun p => ∑ b : BasisIndex T,
    bhCoefficient z rho sigma p i j b * basisPrime z sigma b i j r)
  fun_prop

theorem convolution_contDiff (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j l : Fin N) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : TailMatrix T N × TailMatrix T N => ∫ t : ℝ,
      factorPrime z rho sigma p i l (t + r) * factor z rho sigma p j l t) := by
  simp only [factorPrime, factor, convolution_eq_basis z hz sigma _ _ _ _ hsigma i j l r]
  change ContDiff ℝ ∞ (fun p => ∑ b : BasisIndex T, ∑ c : BasisIndex T,
    (bhCoefficient z rho sigma p i l b * bhCoefficient z rho sigma p j l c) *
      basisConvolution z sigma b c i j l r)
  fun_prop

/-- Assembled Cauchy identity for the actual DCF, with no convergence premise.
The q here is the foundation factor Q; the paper's factor is q = Q/(2*pi). -/
theorem correlation_jet_cauchy (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j : Fin N) (r : ℝ) (hr : r ≠ 0) :
    r * jet (fun s => rootCorrelation z rho sigma (p s) i j r) n =
      (-(jet (fun s => factorPrime z rho sigma (p s) i j r) n) +
        ∑ l, rho l * ∑ a ∈ Finset.range (n + 1), ∫ t : ℝ,
          jet (fun s => factorPrime z rho sigma (p s) i l (t + r)) a *
          jet (fun s => factor z rho sigma (p s) j l t) (n - a)) / (2 * π) := by
  let f := fun s => factorPrime z rho sigma (p s) i j r
  let g := fun l s => ∫ t : ℝ,
    factorPrime z rho sigma (p s) i l (t + r) * factor z rho sigma (p s) j l t
  have hf : ContDiffAt ℝ n f 0 :=
    ((factorPrime_contDiff z rho sigma i j r).contDiffAt.comp 0 hp).of_le
      (by exact_mod_cast le_top)
  have hg (l : Fin N) : ContDiffAt ℝ n (g l) 0 :=
    ((convolution_contDiff z hz rho sigma hsigma i j l r).contDiffAt.comp 0 hp).of_le
      (by exact_mod_cast le_top)
  have he : (fun s => r * rootCorrelation z rho sigma (p s) i j r) =
      (fun s => ((∑ l, rho l * g l s) - f s) / (2 * π)) := by
    funext s
    dsimp [rootCorrelation, correlation, f, g, factorPrime, factor]
    field_simp
    ring
  have hj := congrArg (fun h : ℝ → ℝ => jet h n) he
  have hsum : ContDiffAt ℝ n (fun s => ∑ l, rho l * g l s) 0 :=
    ContDiffAt.sum (fun l _ => contDiffAt_const.mul (hg l))
  simp only [jet, iteratedDeriv_const_mul_field, iteratedDeriv_div_const,
    iteratedDeriv_fun_sub hsum hf, iteratedDeriv_fun_sum (fun l _ => contDiffAt_const.mul (hg l))] at hj
  have hs : (∑ l, rho l * jet (g l) n) - jet f n =
      (∑ l, rho l * iteratedDeriv n (g l) 0 - iteratedDeriv n f 0) / (n.factorial : ℝ) := by
    simp only [jet, sub_div, Finset.sum_div, mul_div_assoc]
  have hmain : r * jet (fun s => rootCorrelation z rho sigma (p s) i j r) n =
      ((∑ l, rho l * jet (g l) n) - jet f n) / (2 * π) := by
    rw [hs]
    dsimp [jet]
    calc
      _ = (r * iteratedDeriv n (fun s => rootCorrelation z rho sigma (p s) i j r) 0) /
          (n.factorial : ℝ) := by ring
      _ = _ := by rw [hj]; ring
  rw [hmain]
  simp_rw [g, convolution_jet_cauchy z rho sigma hz hsigma p hp n i j]
  dsimp [f]
  ring

theorem jet_div_const (f : ℝ → ℝ) (c : ℝ) (n : ℕ) :
    jet (fun s => f s / c) n = jet f n / c := by
  simp only [jet, iteratedDeriv_div_const]
  ring

/-- The explicit paper convention q = Q/(2*pi), for the ordered positive-axis
DCF. The derivative on the first factor has the plus convolution sign after
integration by parts; this theorem does not silently drop lower-edge atoms
from the paper's reflected, second-factor distributional formula. -/
theorem normalized_correlation_jet_cauchy (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (hp : ContDiffAt ℝ ∞ p 0)
    (n : ℕ) (i j : Fin N) (r : ℝ) (hr : r ≠ 0) :
    r * jet (fun s => rootCorrelation z rho sigma (p s) i j r) n =
      -(jet (fun s => factorPrime z rho sigma (p s) i j r / (2 * π)) n) +
        2 * π * ∑ l, rho l * ∑ a ∈ Finset.range (n + 1), ∫ t : ℝ,
          jet (fun s => factorPrime z rho sigma (p s) i l (t + r) / (2 * π)) a *
          jet (fun s => factor z rho sigma (p s) j l t / (2 * π)) (n - a) := by
  rw [correlation_jet_cauchy z hz rho sigma hsigma p hp n i j r hr]
  simp_rw [jet_div_const]
  simp_rw [div_mul_div_comm]
  simp_rw [integral_div]
  simp only [← Finset.sum_div, ← mul_div_assoc]
  field_simp

end FMSA.Paper.BaxterNormalization

/-- info: 'FMSA.Paper.BaxterNormalization.primitive_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterNormalization.primitive_hasDerivAt

/-- info: 'FMSA.Paper.BaxterNormalization.primitive_shell_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterNormalization.primitive_shell_window

/-- info: 'FMSA.Paper.BaxterNormalization.factorPrime_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterNormalization.factorPrime_contDiff

/-- info: 'FMSA.Paper.BaxterNormalization.convolution_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterNormalization.convolution_contDiff

/-- info: 'FMSA.Paper.BaxterNormalization.correlation_jet_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterNormalization.correlation_jet_cauchy

/-- info: 'FMSA.Paper.BaxterNormalization.jet_div_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterNormalization.jet_div_const

/-- info: 'FMSA.Paper.BaxterNormalization.normalized_correlation_jet_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterNormalization.normalized_correlation_jet_cauchy
