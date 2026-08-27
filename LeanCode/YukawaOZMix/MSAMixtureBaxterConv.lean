/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBreakpointScheme

/-!
# BRK.13 — the closure seam: real-space Baxter `Q`, its convolution core `c`, and `c = matCoreUneq`

Group **BRK** (`proof_notes_breakpoints_MSA.md`, §PENDING BRK.13).  This file discharges the *one*
link BRK could not close on its own — the "faithful-transcription task kept outside" flagged in
`MSAMixtureBreakpointScheme.lean`'s closure-scaffolding docstring: it defines the real-space Baxter
factor `Q_ab(r)` and the physical exact-MSA core

    c_ij(r) = ( −Q'_ij(r) + Σ_l ρ_l ∫ Q'_il(t+r) Q_jl(t) dt ) / (2π r)               (r > 0)

then the symbolic-`σ` identity `c = matCoreUneq` on the two open pieces of `(0, σ_ij)` — MSAEMIX.4
Stage 3 — closes BRK about the *physical* core: `c` is `ContDiffOn ℝ ⊤` on each side of its unique
interior breakpoint `|λ_ij|`, at every `K`-order.

## The identity is a THEOREM (BRK.16) — the former axiom is RETIRED

`c = matCoreUneq` is DERIVED in Lean, std-3, in `MSAMixtureBreakpointConvDirect.lean`
(`baxterConvCore_eq_matCoreUneq_proved`): the per-`l` convolution is computed explicitly (region
decomposition + `integral_canonical`/`integral_tailtail` + `gForm`-linearity), so NO sympy axiom is
needed.  (Earlier this file collapsed the seam to a grade-2 axiom on the — incorrect — premise that
grade 1 was "the same class as the ring-infeasible `MSAEXACT.6` hcore"; that infeasibility is the
k-space degree-22 ring, whereas the REAL-space convolution here is the tractable MML.8/MRS.5 class.)
This file now supplies only DEFINITIONS; the physical-core capstones live downstream and are std-3.

Transcription is faithful to the sympy `Qn`/`Qpn` (`msaemix_uneq_symconv.py`): with
`λ_ab = edgeLo σ a b = (σ_b − σ_a)/2`, `σ_ab = edgeHi σ a b = (σ_a + σ_b)/2`, poly argument
`x − λ_ab − σ_a`.  The convolution integrates the full support `∫_ℝ` (both factors vanish below
their support edge — which can be negative when `σ_l < σ_j` — decaying like `e^{−2zt}` above), as in
Stage 3's `convterm` and the numeric `gnum`.
-/

open MSAMixture MSAMixtureCoreUneq

namespace FMSA.ExactMSA.Breakpoint

variable {N : ℕ}

/-! ### The real-space Baxter factor `Q_ab` and its derivative -/

/-- Real-space Baxter factor `Q_ab(x)` (unequal σ), piecewise: `0` below the support edge
`λ_ab = edgeLo σ a b`, a quadratic-plus-exponential core on `[λ_ab, σ_ab]`, and a two-exponential
tail beyond `σ_ab = edgeHi σ a b`.  Faithful transcription of `Qn` (`msaemix_uneq_symconv.py`);
`A b` is the column-`b` Baxter amplitude, `qp/Wt/Ct` the pair amplitudes. -/
noncomputable def baxterQ (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (a b : Fin N) (x : ℝ) : ℝ :=
  if x < edgeLo σ a b then 0
  else if x ≤ edgeHi σ a b then
    qp a b * (x - edgeLo σ a b - σ a) + A b / 2 * (x - edgeLo σ a b - σ a) ^ 2
      + Wt a b * Real.exp (-z * (x - edgeLo σ a b)) + Ct a b
  else
    Wt a b * Real.exp (-z * (x - edgeLo σ a b)) + Ct a b * Real.exp (-z * (x - edgeHi σ a b))

/-- The derivative `Q'_ab(x)` of `baxterQ`, transcribed analytically from `Qpn`
(`msaemix_uneq_symconv.py`): `0` below `λ_ab`, `qp + A·(x−λ−σ_a) − z W e^{−z(x−λ)}` on the core, and
`−z W e^{−z(x−λ)} − z C e^{−z(x−σ_ab)}` on the tail. -/
noncomputable def baxterQ' (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (a b : Fin N) (x : ℝ) : ℝ :=
  if x < edgeLo σ a b then 0
  else if x ≤ edgeHi σ a b then
    qp a b + A b * (x - edgeLo σ a b - σ a) - z * Wt a b * Real.exp (-z * (x - edgeLo σ a b))
  else
    -z * Wt a b * Real.exp (-z * (x - edgeLo σ a b))
      - z * Ct a b * Real.exp (-z * (x - edgeHi σ a b))

/-! ### The physical exact-MSA core and its `K`-family -/

/-- ⭐ **The physical exact-MSA core**
`c_ij(r) = (−Q'_ij(r) + Σ_l ρ_l ∫ Q'_il(t+r) Q_jl(t) dt)/(2π r)` — the real-space Baxter convolution
whose closed form MSAEMIX.4 Stage 3 computes as `matCoreUneq`. -/
noncomputable def baxterConvCore (z : ℝ) (ρ σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) (r : ℝ) : ℝ :=
  (-baxterQ' z σ A qp Wt Ct i j r
      + ∑ l, ρ l * ∫ (t : ℝ), baxterQ' z σ A qp Wt Ct i l (t + r) * baxterQ z σ A qp Wt Ct j l t)
    / (2 * Real.pi * r)

/-- The `K`-family of the physical core: amplitudes carried as functions of the coupling `K` (the
diameters `σ` are `K`-free). -/
noncomputable def baxterConvCoreK (z : ℝ) (σ : Fin N → ℝ) (ρ A : ℝ → Fin N → ℝ)
    (qp Wt Ct : ℝ → Fin N → Fin N → ℝ) (i j : Fin N) : ℝ → ℝ → ℝ :=
  fun K r => baxterConvCore z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j r

/-! ### The Stage-3 convolution identity — now a PROVED THEOREM (not an axiom)

The identity `baxterConvCore = matCoreUneq` (BRK.16) is DERIVED in Lean, std-3, in
`MSAMixtureBreakpointConvDirect.lean` (`baxterConvCore_eq_matCoreUneq_proved`), together with the
physical-core capstones (`baxterConvCore_smooth_off_unique_breakpoint`,
`baxterConvCoreK_paramDeriv_contDiffOn_{inner,outer}`).  This file now supplies only the DEFINITIONS
(`baxterQ`, `baxterQ'`, `baxterConvCore`, `baxterConvCoreK`); the former sympy-backed seam axiom and
its consumers moved downstream and are retired. -/

end FMSA.ExactMSA.Breakpoint
