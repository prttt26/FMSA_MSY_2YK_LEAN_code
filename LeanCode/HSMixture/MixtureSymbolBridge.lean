/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.MixtureCoercivityReduction
import LeanCode.HSMixture.MixtureOzStar

/-!
# The real-space ⇄ Fourier DCF bridge for the coercivity symbol (toward MRS.8)

The corrected value route needs the Gram factorizations `hfac0`/`hfack`
(`matSymbolCoercive_of_gramFactors`): the OZ symbol quadratic form
`∑ᵢuᵢ² − ρ∑ᵢⱼ matRadialSymbol Φ k uᵢuⱼ` must equal a squared complex norm `∑ₗ|(B·u)ₗ|²`.  That
reduces to the **matrix identity** `ρ · matRadialSymbol Φ k = Cmix0(Q̂₀, i·k)` (the DCF Fourier
transform equals the Baxter-factorization DCF `Ĉ₀ = 1 − Q̂₀Q̂₀ᵀ`) — task **MRS.8**.

This file supplies the connective links that route the abstract coercivity symbol onto the
established Baxter machinery, and isolates the single irreducible analytic fact that remains:

* `matRadialSymbol_eq_radial_fourier` — DEFINITIONAL:
  `matRadialSymbol Φ k i j = radial_fourier (Φ i j) k`.  Lets the whole scalar `radial_fourier`
  theory (`shellKernel_cos_eq_radial_fourier`, the DCF transform lemmas) apply per entry.
* `matRadialSymbol_eq_shellKernel_cos` — each symbol entry is the Baxter shell-kernel cosine
  transform `2∫₀^σ shellKernel(Φᵢⱼ)·cos(kv) dv` (via the matrix `F[K]=Ĉ`
  `matShellKernel_cos_eq_radial_fourier`).  The entrypoint onto the Baxter-kernel side.

**What remains (the genuine MRS.8/Wertheim content, research-scale — NOT a transcription).**
Closing `hfack`/`hfac0` from here is the Fourier-space Baxter Wiener–Hopf factorization
`F[ρK] = I − Q̂₀(i·k)·Q̂₀(−i·k)ᵀ` — the shell kernel `K` (= the Baxter kernel of the mixture DCF)
matched to its WH factor `Q̂₀`.  It decomposes into two concrete sub-facts:
1. the radial-FT **convolution theorem** for the Baxter-factor products (`radial_fourier` of the
   self-convolution `qFwd ⋆ pMixEntry` = the product of the entry transforms), plus the assembly of
   the real-space DCF `cHSmixRaw = qFwd + pMixEntry − ∑ qpConv` into `1 − Q̂₀Q̂₀ᵀ`;
2. the **Hermitian reality** `Q̂₀(−i·k) = conj(Q̂₀(i·k))` (real Baxter coefficients on the imaginary
   axis), turning `vᵀ Q̂₀(i·k)Q̂₀(−i·k)ᵀ v` into the squared norm `∑ₗ|(Q̂₀(i·k)ᵀ v)ₗ|²`.
The determinant inputs are already in hand (`mixtureDet_pole_free_N` off-origin,
`det_Q0_mat_c_repr_origin_ne_zero` at it); only this transform identity is open, and it is the SAME
bridge for both the middle (`hfack`) and the origin (`hfac0`).

**Update (2026-08-19) — the gap is now narrowed to ONE real-space identification.**  Sub-fact 1's
Fourier END has landed at general `N`: `matDCFfullN_laplace` (`MixtureDCFAEInjective.lean`) proves
`𝓛(matDCFfullN)(i·k) = Cmix0(Q̂₀, i·k) = I − Q̂₀(i·k)Q̂₀(−i·k)ᵀ`, where `matDCFfullN` is the Baxter
reconstruction `ρgeo·q₀(v) + ρgeo·q₀ᵀ(−v) − (q₀⋆q₀)` (= `q + q̃ − q⋆q`).  Sub-fact 2 (Hermitian
reality) is proved: `Q0_mat_c_phys_neg_axis`.  So the SOLE remaining open piece is the **real-space
identification** `matDCFfullN(v) = ` the physical two-piece Lebowitz DCF `cMixDCFN(v)` on `v > 0`
(with `matDCFfullN` even), whence `𝓛(matDCFfullN)(i·k) = ρ·radial_fourier(cMixDCFN)(k)` bridges the
Baxter 1D transform to the coercivity symbol `matRadialSymbol Φ`.  That identity is "Baxter
reconstruction = ODE Lebowitz DCF", the MRS.8 companion of `shellForcing_eq_cMixDCFN` — genuine
Wertheim content, still unproved (grep: no `matDCFfullN`↔`cMixDCFN` theorem).  Everything downstream
(det ≠ 0, tail `matSymbol_tail_bound`, continuity `matDCFfullN_ae_continuous`, the coercivity
assembly `matSymbolCoercive_of_gramFactors`, and `matOzStar_unique`) is in hand.
-/

open MeasureTheory Set
namespace FMSA.MixtureOzStar
variable {N : ℕ}

/-- **The matrix radial symbol is the entrywise scalar radial Fourier transform.**  Definitional
bridge `matRadialSymbol Φ k i j = radial_fourier (Φ i j) k` — lets the scalar `radial_fourier`
theory apply to the coercivity symbol per entry. -/
theorem matRadialSymbol_eq_radial_fourier (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (k : ℝ)
    (i j : Fin N) :
    matRadialSymbol Phi k i j = FMSA.HardSphere.radial_fourier (Phi i j) k := rfl

/-- **The coercivity symbol equals the Baxter shell-kernel cosine transform, entrywise.**  Combines
the definitional `matRadialSymbol = radial_fourier` with the matrix `F[K]=Ĉ`
(`matShellKernel_cos_eq_radial_fourier`): each symbol entry is `2∫₀^σ shellKernel(Φᵢⱼ)·cos(kv) dv`.
Routes the coercivity symbol onto the Baxter-kernel side; the remaining step to `Cmix0` is the WH
factorization `F[ρK] = I − Q̂₀Q̂₀ᵀ` (see the module header). -/
theorem matRadialSymbol_eq_shellKernel_cos (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    {sigma : ℝ} (hsigma : 0 < sigma) (i j : Fin N)
    (hc_outer : ∀ s, sigma ≤ s → Phi i j s = 0)
    (hint : ∀ a b, IntervalIntegrable (fun s : ℝ => s * Phi i j s) MeasureTheory.volume a b)
    (hccore : ∀ v ∈ Set.Ioo (0 : ℝ) sigma, ContinuousAt (fun s : ℝ => s * Phi i j s) v)
    (hmeas : ∀ v ∈ Set.Ioo (0 : ℝ) sigma,
      StronglyMeasurableAtFilter (fun s : ℝ => s * Phi i j s) (nhds v))
    {k : ℝ} (hk : k ≠ 0) :
    matRadialSymbol Phi k i j
      = 2 * ∫ v in (0 : ℝ)..sigma,
          FMSA.HardSphere.shellKernel (Phi i j) sigma v * Real.cos (k * v) := by
  rw [matRadialSymbol_eq_radial_fourier,
    ← matShellKernel_cos_eq_radial_fourier Phi hsigma i j hc_outer hint hccore hmeas hk]

end FMSA.MixtureOzStar
