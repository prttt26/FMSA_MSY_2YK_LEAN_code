/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAEMixBreakpointScheme

/-!
# BRK.13 — the closure seam: real-space Baxter `Q`, its convolution core `c`, and `c = matCoreUneq`

Group **BRK** (`proof_notes_breakpoints_MSA.md`, §PENDING BRK.13).  This file discharges the *one*
link BRK could not close on its own — the "faithful-transcription task kept outside" flagged in
`MSAEMixBreakpointScheme.lean`'s closure-scaffolding docstring: it defines the real-space Baxter
factor `Q_ab(r)` and the physical exact-MSA core

    c_ij(r) = ( −Q'_ij(r) + Σ_l ρ_l ∫ Q'_il(t+r) Q_jl(t) dt ) / (2π r)               (r > 0)

then states MSAEMIX.4 Stage 3's symbolic-`σ` identity `c = matCoreUneq` on the two open pieces of
`(0, σ_ij)` as **one sympy-backed convolution-identity axiom** and feeds it into BRK's
hypothesis-parametrised lemmas.  With that seam supplied, the *physical* core inherits all of BRK's
smoothness/knot structure: `c` is `ContDiffOn ℝ ⊤` on each side of its unique interior breakpoint
`|λ_ij|`, at every `K`-order.

## Why an axiom (grade 2, the POLICY-conformant closure)

The identity `c = matCoreUneq` is MSAEMIX.4 Stage 3's region-split symbolic Baxter convolution,
validated to `1e-14` (`msaemix_uneq_symconv.py`, `symbolic_{inner,outer}.py`,
`verify_{inner,outer}.py`, parent repo; correct orientation `σ_i ≥ σ_j`, row = larger diameter).
Proving it in Lean (grade 1) is a piecewise-convolution integral identity of the same class as the
scalar MSAEXACT.6 hcore ring, which a dedicated attempt measured to be impractically large
(`project_msaexact6_ring_infeasible`).  So this file takes the documented grade-2 route: the seam is
collapsed to a single named numerical fact, exactly mirroring the k-space
`matMSAexactUnequalDiam_hcore` / `matMSAexactEqualDiam_kspace_residual` that the `hcore`
certificates carry.  Kept OUT of `defaultTargets` (own `[[lean_lib]]`, not imported by root) so a
normal `lake build` stays std-3; build on demand with `lake build MSAEMixBaxterConvCertificate`.

Transcription is faithful to the sympy `Qn`/`Qpn` (`msaemix_uneq_symconv.py`): with
`λ_ab = edgeLo σ a b = (σ_b − σ_a)/2`, `σ_ab = edgeHi σ a b = (σ_a + σ_b)/2`, poly argument
`x − λ_ab − σ_a`.  The convolution integrates the full support `∫_ℝ` (both factors vanish below
their support edge — which can be negative when `σ_l < σ_j` — decaying like `e^{−2zt}` above), as in
Stage 3's `convterm` and the numeric `gnum`.
-/

open MSAEMix MSAEMixCoreUneq

namespace FMSA.MSAExact.BRK

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

/-! ### The Stage-3 convolution identity (the sympy-backed seam axiom) -/

/-- ⭐ **BRK.13 seam — the Stage-3 convolution identity.**  In the orientation `σ_j ≤ σ_i` (row =
larger diameter), the physical Baxter-convolution core equals the closed form `matCoreUneq` on the
two open pieces of the core interval `(0, σ_ij)` (i.e. off the endpoints and the interior breakpoint
`|λ_ij|`).  This is MSAEMIX.4 Stage 3, validated to `1e-14` (`verify_{inner,outer}.py`); it is the
real-space analog of the k-space `matMSAexactUnequalDiam_hcore`, and the single input that closes
BRK about the physical core. -/
axiom baxterConvCore_eq_matCoreUneq (z : ℝ) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j : Fin N) (hori : σ j ≤ σ i) :
    Set.EqOn (baxterConvCore z ρ σ A qp Wt Ct i j)
      (fun r => matCoreUneq z ρ σ A qp Wt Ct i j r)
      (Set.Ioo 0 (lamA σ i j) ∪ Set.Ioo (lamA σ i j) (edgeHi σ i j))

/-! ### BRK closed about the physical core -/

/-- ⭐ **BRK closed (value level, physical core).**  With the Stage-3 seam supplied, the physical
exact-MSA core `baxterConvCore` is `ContDiffOn ℝ ⊤` on all of `(0, σ_ij)` except at the single
interior breakpoint `|λ_ij|`, which MSAEMIX.5 pins as the unique `σ_l`-free interior crossing. -/
theorem baxterConvCore_smooth_off_unique_breakpoint (z : ℝ) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j : Fin N)
    (hi : 0 < σ i) (hj : 0 < σ j) (hne : σ i ≠ σ j) (hori : σ j ≤ σ i) :
    lamA σ i j ∈ Set.Ioo (0 : ℝ) (edgeHi σ i j)
    ∧ ContDiffOn ℝ ⊤ (baxterConvCore z ρ σ A qp Wt Ct i j) (Set.Ioo 0 (lamA σ i j))
    ∧ ContDiffOn ℝ ⊤ (baxterConvCore z ρ σ A qp Wt Ct i j)
        (Set.Ioo (lamA σ i j) (edgeHi σ i j)) :=
  let hEq := baxterConvCore_eq_matCoreUneq z ρ σ A qp Wt Ct i j hori
  exactCore_smooth_off_unique_breakpoint_of_eqOn z ρ σ A qp Wt Ct i j
    (baxterConvCore z ρ σ A qp Wt Ct i j)
    (hEq.mono Set.subset_union_left) (hEq.mono Set.subset_union_right) hi hj hne

/-- ⭐ **BRK closed (all orders, inner piece, physical core).**  Every `K`-derivative of the physical
core `baxterConvCoreK` is `ContDiffOn ℝ ⊤` on `(0, |λ_ij|)`: the amplitudes are `ContDiff` in `K`,
and the Stage-3 identity carries BRK's abstract all-orders smoothness to the physical object. -/
theorem baxterConvCoreK_paramDeriv_contDiffOn_inner (z : ℝ) (σ : Fin N → ℝ) (ρ A : ℝ → Fin N → ℝ)
    (qp Wt Ct : ℝ → Fin N → Fin N → ℝ) (i j : Fin N)
    (hρ : ∀ l, ContDiff ℝ ⊤ (fun K => ρ K l)) (hA : ∀ l, ContDiff ℝ ⊤ (fun K => A K l))
    (hqp : ∀ a b, ContDiff ℝ ⊤ (fun K => qp K a b)) (hWt : ∀ a b, ContDiff ℝ ⊤ (fun K => Wt K a b))
    (hCt : ∀ a b, ContDiff ℝ ⊤ (fun K => Ct K a b)) (hori : σ j ≤ σ i) (n : ℕ) (K₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun r => iteratedDeriv n (fun K => baxterConvCoreK z σ ρ A qp Wt Ct i j K r) K₀)
      (Set.Ioo 0 (lamA σ i j)) := by
  refine (matCoreUneq_paramDeriv_contDiffOn_inner z σ ρ A qp Wt Ct i j hρ hA hqp hWt hCt n K₀).congr
    ?_
  intro r hr
  have hfun : (fun K => baxterConvCoreK z σ ρ A qp Wt Ct i j K r)
      = (fun K => matCoreUneq z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j r) := by
    funext K
    simpa [baxterConvCoreK] using
      baxterConvCore_eq_matCoreUneq z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j hori
        (Set.mem_union_left _ hr)
  rw [hfun]

/-- ⭐ **BRK closed (all orders, outer piece, physical core).**  Same as the inner piece, on
`(|λ_ij|, σ_ij)`. -/
theorem baxterConvCoreK_paramDeriv_contDiffOn_outer (z : ℝ) (σ : Fin N → ℝ) (ρ A : ℝ → Fin N → ℝ)
    (qp Wt Ct : ℝ → Fin N → Fin N → ℝ) (i j : Fin N)
    (hρ : ∀ l, ContDiff ℝ ⊤ (fun K => ρ K l)) (hA : ∀ l, ContDiff ℝ ⊤ (fun K => A K l))
    (hqp : ∀ a b, ContDiff ℝ ⊤ (fun K => qp K a b)) (hWt : ∀ a b, ContDiff ℝ ⊤ (fun K => Wt K a b))
    (hCt : ∀ a b, ContDiff ℝ ⊤ (fun K => Ct K a b)) (hori : σ j ≤ σ i) (n : ℕ) (K₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun r => iteratedDeriv n (fun K => baxterConvCoreK z σ ρ A qp Wt Ct i j K r) K₀)
      (Set.Ioo (lamA σ i j) (edgeHi σ i j)) := by
  refine (matCoreUneq_paramDeriv_contDiffOn_outer z σ ρ A qp Wt Ct i j hρ hA hqp hWt hCt n K₀).congr
    ?_
  intro r hr
  have hfun : (fun K => baxterConvCoreK z σ ρ A qp Wt Ct i j K r)
      = (fun K => matCoreUneq z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j r) := by
    funext K
    simpa [baxterConvCoreK] using
      baxterConvCore_eq_matCoreUneq z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j hori
        (Set.mem_union_right _ hr)
  rw [hfun]

end FMSA.MSAExact.BRK
