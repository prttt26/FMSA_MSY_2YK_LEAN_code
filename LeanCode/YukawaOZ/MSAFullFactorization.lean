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

namespace FMSA.MSAExact

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
compact `msaexact1_iff_core`).  Given that the MSA direct correlation function's *core* and *tail*
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

end FMSA.MSAExact
