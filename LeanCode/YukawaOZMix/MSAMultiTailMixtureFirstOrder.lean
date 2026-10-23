import LeanCode.YukawaOZMix.MSAMultiTailMixtureFamily
import LeanCode.YukawaOZMix.MSAMultiTailMixturePrimitive

/-! Actual first slope of a finite-tail unequal-diameter BH root family.
The HS-dressed amplitude identification is proved, not assumed. It is an
amplitude theorem, not yet a physical radial FMSA DCF/core/OZ certificate. -/
noncomputable section
open Real Filter Topology Set MSAMixture FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint
open scoped BigOperators ContDiff
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def firstOrderSource (z : ι → ℝ) (K : TailMatrix ι N) : TailMatrix ι N :=
  fun u i j => 2 * π * K u i j / z u

def firstOrderDt (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) : TailMatrix ι N :=
  rightBlock (inverseBlocks (baseFirst z ρ σ)) (firstOrderSource z K)

/-- Actual first BH map has derivative only in Dt at the PY seed. -/
theorem firstLHS_hasFDerivAt_base (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Gbase : TailMatrix ι N) :
    HasFDerivAt (fun p : TailMatrix ι N × TailMatrix ι N => firstLHS z ρ σ p.1 p.2)
      ((rightBlock (baseFirst z ρ σ)).comp (ContinuousLinearMap.fst ℝ _ _)) (0, Gbase) := by
  let E := TailMatrix ι N
  let P := E × E
  have hd := (residual_contDiff z ρ σ (0 : E)).differentiable (by simp : (∞ : ℕ∞ω) ≠ 0)
    |>.differentiableAt.hasFDerivAt (x := (0, (0, Gbase)))
  have hc := hd.comp (0, Gbase) (ContinuousLinearMap.inr ℝ ℝ P).hasFDerivAt
  have ht := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp (0, Gbase) hc
  rw [residual_partial_triangular] at ht
  have hlin : ∀ J : E →L[ℝ] E,
      (ContinuousLinearMap.fst ℝ E E).comp (triangular (baseFirst z ρ σ) (baseSecond z ρ σ) J) =
        (rightBlock (baseFirst z ρ σ)).comp (ContinuousLinearMap.fst ℝ E E) := by
    intro J
    rfl
  rw [hlin] at ht
  have he : (fun p : P => (residual z ρ σ (0 : E) (0, p)).1) =
      (fun p : P => firstLHS z ρ σ p.1 p.2) := by
    funext p u i j
    simp [residual]
  convert! ht using 1
  exact he.symm

/-- The slope is uniquely HS-dressed on the actual local branch. -/
theorem firstOrderDt_eq_of_family (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, baseSeed z ρ σ))
    (hroot : ∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2)
    (hd : HasDerivAt ψ d 0) : d.1 = firstOrderDt z ρ σ K := by
  have hb := firstLHS_hasFDerivAt_base z ρ σ (baseSeed z ρ σ)
  rw [← h0] at hb
  have hcomp := hb.comp_hasDerivAt 0 hd
  change HasDerivAt (fun τ => firstLHS z ρ σ (ψ τ).1 (ψ τ).2)
    (rightBlock (baseFirst z ρ σ) d.1) 0 at hcomp
  have he : (fun τ => firstLHS z ρ σ (ψ τ).1 (ψ τ).2) =ᶠ[𝓝 (0 : ℝ)]
      (fun τ => τ • firstOrderSource z K) := by
    filter_upwards [hroot] with τ hτ
    funext u i j
    rw [hτ.1]
    simp only [firstOrderSource, Pi.smul_apply, smul_eq_mul]
    ring
  have hs : HasDerivAt (fun τ : ℝ => τ • firstOrderSource z K) (firstOrderSource z K) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (firstOrderSource z K)
  have hlin := (hcomp.congr_of_eventuallyEq he.symm).unique hs
  have hinv := congrArg (rightBlock (inverseBlocks (baseFirst z ρ σ))) hlin
  rw [rightBlock_left_inverse _ (baseFirst_isUnit_det z ρ σ hz hvac hρ hσ)] at hinv
  exact hinv

/-- Existence and the actual first derivative are both discharged internally. -/
theorem exists_contDiffAt_root_with_firstOrderDt (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    ∃ ψ : ℝ → TailMatrix ι N × TailMatrix ι N,
      ψ 0 = (0, baseSeed z ρ σ) ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2) ∧
      ContDiffAt ℝ ∞ ψ 0 ∧
      HasDerivAt (fun τ => (ψ τ).1) (firstOrderDt z ρ σ K) 0 := by
  obtain ⟨ψ, h0, hr, hc⟩ := exists_contDiffAt_root z ρ σ K hz hvac hρ hσ
  have hd := (hc.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
  have hs := firstOrderDt_eq_of_family z ρ σ K hz hvac hρ hσ ψ _ h0 hr hd
  have hfst := (ContinuousLinearMap.fst ℝ (TailMatrix ι N) (TailMatrix ι N)).hasFDerivAt.comp_hasDerivAt 0 hd
  change HasDerivAt (fun τ => (ψ τ).1) (deriv ψ 0).1 0 at hfst
  rw [hs] at hfst
  exact ⟨ψ, h0, hr, hc, hfst⟩

/-- Exact first-order exterior DCF for the actual convolution-defined family.
Only a local BH-root germ is required; no DCF derivative is assumed. -/
theorem correlation_exterior_hasDerivAt_of_family (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N)
    (hroot : ∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2)
    (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    HasDerivAt (fun τ => correlation z ρ σ
      (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
      (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) i j r)
      (∑ u, K u i j * exp (-z u * (r - edgeHi σ i j)) / r) 0 := by
  let tail : ℝ := ∑ u, K u i j * exp (-z u * (r - edgeHi σ i j)) / r
  have hd : HasDerivAt (fun τ : ℝ => τ * tail) tail 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const tail
  apply hd.congr_of_eventuallyEq
  filter_upwards [hroot] with τ hτ
  rw [correlation_exterior_of_root z hz ρ σ (τ • K) (ψ τ).1 (ψ τ).2 hσ hτ i j r hr]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Audited local root family with its actual HS-dressed amplitude slope and
actual exterior DCF slope. Core FMSA DCF and matrix RDF/OZ remain separate. -/
theorem exists_contDiffAt_root_with_firstOrder_exterior (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    ∃ ψ : ℝ → TailMatrix ι N × TailMatrix ι N,
      ψ 0 = (0, baseSeed z ρ σ) ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2) ∧
      ContDiffAt ℝ ∞ ψ 0 ∧
      HasDerivAt (fun τ => (ψ τ).1) (firstOrderDt z ρ σ K) 0 ∧
      ∀ i j r, edgeHi σ i j < r →
        HasDerivAt (fun τ => correlation z ρ σ
          (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
          (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) i j r)
          (∑ u, K u i j * exp (-z u * (r - edgeHi σ i j)) / r) 0 := by
  obtain ⟨ψ, h0, hr, hc, hd⟩ := exists_contDiffAt_root_with_firstOrderDt z ρ σ K hz hvac hρ hσ
  exact ⟨ψ, h0, hr, hc, hd, fun i j r h =>
    correlation_exterior_hasDerivAt_of_family z hz ρ σ K (fun i => (hσ i).le) ψ hr i j r h⟩

end FMSA.ExactMSA.MultiTailMixture
