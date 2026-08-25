/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSABaxterKSpace
import LeanCode.YukawaOZ.MSAFactorizationSplit
import LeanCode.YukawaOZ.MSADCFTransform
import LeanCode.YukawaOZ.MSACoreTransform
import LeanCode.HardSphere.BaxterWienerHopf

/-!
# MSAEXACT.1 — the staged factorization of the non-compact Baxter factor

Group **MSAEXACT** (`proof_notes_msa_exact.md`).

The physical hard-core Yukawa MSA factorisation is `|1 − ρQ̂(ik)|² = 1 − ρĉ_MSA(k)` with `Q̂` the
**non-compact** Baxter factor (pole at `s = −z`).  A single compact `q0_poly + D e^{−zr}` ansatz
cannot equal it (`MSAExteriorTransform` docstring), so the route is to **stage** the modulus.

`msaQre`, `msaQim` are affine in `Dt` (`MSABaxterKSpace`), so the generic `msa_lhs_split` splits

    |1 − ρQ̂(ik)|² = [(1 − ρQ̂₀)² + …]  −  2Dt·X  +  Dt²·Y

into the `Dt⁰` hard-sphere factor and the `O(Dt)`, `O(Dt²)` amplitude terms.  This file closes that
**purely algebraic** stage (`msa_factor_split`): the `Dt⁰` bracket is exactly
`1 − ρ𝓕[c_HS](k)` via `msaQre_zero`/`msaQim_zero` and `baxter_wiener_hopf_factorization`.

⚠ The remaining `msaBaxter_factorization_of_closure` — matching `−2Dt·X + Dt²·Y` against
`−ρ(𝓕[c_core] + 𝓕[c_tail])` under the Blum–Høye constraints (29′)/(33) — is the closure-recovery
core (the "large algebraic verification with the Pythagorean identity") and is the next step.
-/

open Real MeasureTheory

namespace FMSA.ExactMSA

open FMSA.HardSphere

variable (xi z : ℝ)

/-- **The staged `Dt`-expansion of the factorisation's left side.**
`|1 − ρQ̂(ik)|² = (1 − ρ𝓕[c_HS]) − 2Dt·X + Dt²·Y`, with `X`, `Y` the `O(Dt)`, `O(Dt²)` brackets
`msa_lhs_split` produces.  The `Dt⁰` bracket `(1 − Re₀)² + Im₀²` collapses to the hard-sphere
factor by the two `Dt⁰` bridges and `baxter_wiener_hopf_factorization`.  Purely algebraic — no
Blum–Høye constraints yet. -/
theorem msa_factor_split (Dt G : ℝ) {k : ℝ} (hk : k ≠ 0) (hxi : xi < 1) :
    (1 - msaQre xi z Dt G k) ^ 2 + msaQim xi z Dt G k ^ 2
      = (1 - rhoOf xi * radial_fourier (c_HS xi 1) k)
        - 2 * Dt * ((1 - msaQre xi z 0 G k) * msaRez xi z G k
            - msaQim xi z 0 G k * msaImz xi z G k)
        + Dt ^ 2 * (msaRez xi z G k ^ 2 + msaImz xi z G k ^ 2) := by
  have heta_def : xi = Real.pi * rhoOf xi * (1 : ℝ) ^ 3 / 6 := by
    rw [rhoOf]; field_simp
  have hHS : (1 - msaQre xi z 0 G k) ^ 2 + msaQim xi z 0 G k ^ 2
      = 1 - rhoOf xi * radial_fourier (c_HS xi 1) k := by
    rw [msaQre_zero xi z G hk, msaQim_zero xi z G hk, neg_sq,
      baxter_wiener_hopf_factorization xi 1 (rhoOf xi) k one_pos hk hxi heta_def]
  rw [msaQre_eq xi z Dt G k, msaQim_eq xi z Dt G k, msa_lhs_split, hHS]

/-- ⭐ **MSAEXACT.1, reduced to the closure-recovery core** (the correct, non-compact analog of the
compact `exactMSA_iff_core`).  Given that the MSA direct correlation function's *core* and *tail*
transforms account for the `O(Dt)`/`O(Dt²)` amplitude terms —

    ρ(𝓕[c_core] + 𝓕[c_tail]) = 2Dt·X − Dt²·Y

with `X`, `Y` the `msa_factor_split` brackets — the non-compact Baxter factorisation holds:

    |1 − ρQ̂(ik)|² = 1 − ρĉ_MSA(k),     ĉ_MSA = 𝓕[c_HS] + 𝓕[c_core] + 𝓕[c_tail].

Pure algebra on top of `msa_factor_split`.  ⚠ The `hcore` hypothesis — matching the two transforms
against the amplitude brackets under the Blum–Høye constraints (29′)/(33) — is the remaining
closure-recovery ring; here `c_core` is any core-supported correction whose transform obeys it. -/
theorem factorization_of_core (Dt G K : ℝ) (cCore : ℝ → ℝ) {k : ℝ} (hk : k ≠ 0) (hxi : xi < 1)
    (hcore : rhoOf xi * (radial_fourier cCore k + radial_fourier (cMSAtail K z 1) k)
      = 2 * Dt * ((1 - msaQre xi z 0 G k) * msaRez xi z G k
            - msaQim xi z 0 G k * msaImz xi z G k)
        - Dt ^ 2 * (msaRez xi z G k ^ 2 + msaImz xi z G k ^ 2)) :
    (1 - msaQre xi z Dt G k) ^ 2 + msaQim xi z Dt G k ^ 2
      = 1 - rhoOf xi * (radial_fourier (c_HS xi 1) k + radial_fourier cCore k
          + radial_fourier (cMSAtail K z 1) k) := by
  rw [msa_factor_split xi z Dt G hk hxi]
  linarith [hcore]

/-! ### MSAEXACT.6 — the closure-recovery ring (sympy-certified axiom) and MSAEXACT.1 -/

/-- The Blum–Høye MSA **core-correction** `c(r)` in `coreCorrection` form, with the closure's
coefficients `c₁ = −da`, `c₂ = −db`, `c₃ = −½ξ·da`, `c₄ = −v/z`, `c₅ = −v²/(2Kz²)`, where
`a = (A/2π)²`, `λ₁ = (1+2ξ)²/(1−ξ)⁴`, `b_HS = −6ξ(1+ξ/2)²/(1−ξ)⁴`, `v = 24ξKG`, `da = a−λ₁`,
`db = bb−b_HS`, and
`bb = (q′+zγDt)/2π − K − a − ½ξa − v(1−e^{−z})/z − v²(1−e^{−z})²/(4Kz²)`.
These are the Blum–Høye MSA closure values; the resulting `hcore` identity is verified in sympy
(`exactMSA_cert.py`). -/
noncomputable def msaCoreCorr (Dt G K : ℝ) : ℝ → ℝ :=
  let A := msaA xi z Dt G
  let qp := msaQp xi z Dt G
  let g := gam xi z G
  let a := (A / (2 * π)) ^ 2
  let lam1 := (1 + 2 * xi) ^ 2 / (1 - xi) ^ 4
  let bHS := -6 * xi * (1 + xi / 2) ^ 2 / (1 - xi) ^ 4
  let v := 24 * xi * K * G
  let bb := (qp + z * g * Dt) / (2 * π) - K - a - xi * a / 2
    - v * (1 - Real.exp (-z)) / z - v ^ 2 * (1 - Real.exp (-z)) ^ 2 / (4 * K * z ^ 2)
  let da := a - lam1
  let db := bb - bHS
  coreCorrection (-da) (-db) (-(xi * da / 2)) (-(v / z)) (-(v ^ 2 / (2 * K * z ^ 2))) z 1

/-- ⭐ **MSAEXACT.6 (axiom).**  At the physical Blum–Høye root — `(Dt, G)` satisfying the two
constraints `Dt·bhF = 2πK/z` (Eq. 29′) and `2π·G·bhF = bhP` (Eq. 33) — the MSA core correction's
radial transform, together with the exterior Yukawa tail, accounts for the `O(Dt)`/`O(Dt²)`
amplitude terms of `|1 − ρQ̂(ik)|²`.  This is the `hcore` closure-recovery identity consumed by
`factorization_of_core`.

**Certified in sympy** (`exactMSA_cert.py`, parent repo): the difference `Δ` equals
`m29·r29 + m33·r33` exactly (polynomial-division remainder 0), where `r29`, `r33` are the two
Blum–Høye constraints and `m29`, `m33` the recovered multipliers.  The Lean
`ring`/`linear_combination` proof is validated at `Dt⁰` (`Cert_dt0_full.lean` compiles axiom-clean),
but discharging `Dt¹`/`Dt²` in-kernel is *infeasible*, not merely slow (measured 2026-08-22): a
clean `(cos,sin,exp)`-graded `Dt²` coefficient — 323 monomials, degree ≈22 — already costs `ring`
**3 h 12 m / 23 GB**, and the per-order reassembly extrapolates to weeks / ~200 GB; `native_decide`
is blocked (`MvPolynomial` semiring noncomputable).  So this is recorded as an axiom because `ring`
cannot normalize the identity, **not** for want of a bigger budget.  The Fourier/definitional layer
around it is discharged in `ExactMSACertificate.lean` (an out-of-`defaultTargets` lib), which
derives this exact statement from a pure-cos/sin/exp axiom `exactMSA_kspace_residual`.  ⚠ This is a
*physics-computation* axiom (a specific externally-verified polynomial identity), not a new
mathematical assumption. -/
axiom exactMSA_hcore (Dt G K : ℝ) {k : ℝ} (hk : k ≠ 0)
    (h29 : Dt * bhF xi z (Dt, G) - 2 * π * K / z = 0)
    (h33 : 2 * π * (G * bhF xi z (Dt, G)) - bhP xi z (Dt, G) = 0) :
    rhoOf xi * (radial_fourier (msaCoreCorr xi z Dt G K) k
        + radial_fourier (cMSAtail K z 1) k)
      = 2 * Dt * ((1 - msaQre xi z 0 G k) * msaRez xi z G k
            - msaQim xi z 0 G k * msaImz xi z G k)
        - Dt ^ 2 * (msaRez xi z G k ^ 2 + msaImz xi z G k ^ 2)

/-- ⭐ **MSAEXACT.1 — the non-compact MSA Baxter factorisation.**  At the Blum–Høye root,
`|1 − ρQ̂(ik)|² = 1 − ρĉ_MSA(k)` with `ĉ_MSA = 𝓕[c_HS] + 𝓕[c_core] + 𝓕[c_tail]` — the physical MSA
direct correlation function.  Combines the purely-algebraic `factorization_of_core` with the
closure-recovery input `exactMSA_hcore`. -/
theorem exactMSA_factorization (Dt G K : ℝ) {k : ℝ} (hk : k ≠ 0) (hxi : xi < 1)
    (h29 : Dt * bhF xi z (Dt, G) - 2 * π * K / z = 0)
    (h33 : 2 * π * (G * bhF xi z (Dt, G)) - bhP xi z (Dt, G) = 0) :
    (1 - msaQre xi z Dt G k) ^ 2 + msaQim xi z Dt G k ^ 2
      = 1 - rhoOf xi * (radial_fourier (c_HS xi 1) k
          + radial_fourier (msaCoreCorr xi z Dt G K) k
          + radial_fourier (cMSAtail K z 1) k) :=
  factorization_of_core xi z Dt G K (msaCoreCorr xi z Dt G K) hk hxi
    (exactMSA_hcore xi z Dt G K hk h29 h33)

end FMSA.ExactMSA
