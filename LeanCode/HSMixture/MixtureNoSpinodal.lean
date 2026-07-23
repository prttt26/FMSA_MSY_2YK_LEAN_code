/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.Q0Complex

/-!
# Mixture no-spinodal — the multicomponent PY hard-sphere structure-factor axiom

The N-component generalisation of the single-component `pyhs_no_spinodal`
(`HardSphere/BaxterNoSpinodalEquiv.lean`, now a **THEOREM**): on the Fourier axis `s = ik` the
physical multicomponent Baxter matrix `Q̂₀` is nonsingular, i.e. the PY hard-sphere *mixture*
structure factor never diverges.

Positive *semi*-definiteness `S⁻¹ = Q̂†Q̂ ⪰ 0` is automatic from the Baxter factorization; the
content of the axiom is the strict statement, which is exactly `det Q̂ ≠ 0`.

**Pre-placed: no consumer yet.**  It is intended for the mixture track (Group `MRS` /
`MixtureInnerDCF`), and is declared ahead of that development in the same spirit as `MA.8`.
Because nothing imports it, the single-component results remain at **zero** physics axioms.
-/

namespace FMSA.MixtureNoSpinodal

/-- The **physical** complex multicomponent Baxter matrix `Q̂₀(s)` — the complex analogue of
`FMSA.MatrixQ0.Q0_mat_phys`.  `FMSA.Q0Complex.Q0_mat_c` takes `rho_geo`/`Qp`/`Qpp` as *free*
parameters; here they are the concrete Lebowitz/Baxter PY-mixture coefficients
(`rhoGeoPhys`, `Q0phys`, `Qppphys`), coerced to `ℂ`.  Fixing them is essential — see the axiom's
docstring. -/
noncomputable def Q0_mat_c_phys {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  FMSA.Q0Complex.Q0_mat_c s (fun i => (sigma i : ℂ))
    (fun i j => (FMSA.MatrixQ0.rhoGeoPhys rho i j : ℂ))
    (fun i j => (FMSA.MatrixQ0.Q0phys rho sigma i j : ℂ))
    (fun i j => (FMSA.MatrixQ0.Qppphys rho sigma i j : ℂ))

/-- **PY-HS mixture "no spinodal" — the project's only PHYSICS axiom (pre-placed, no consumer).**

On the Fourier axis `s = i·k` the physical multicomponent Baxter matrix is nonsingular:
`det Q̂₀(ik) ≠ 0` for every real `k ≠ 0`.  Equivalently, the PY hard-sphere *mixture* structure
factor never diverges: `S⁻¹ = Q̂†Q̂ ⪰ 0` is automatic from the Baxter factorization, and strict
positive-definiteness of `S⁻¹` is exactly `det Q̂ ≠ 0`.  This is the N-component generalisation of
the single-component `pyhs_no_spinodal`, which is now a **THEOREM**
(`HardSphere/BaxterNoSpinodalEquiv.lean`).

**`k ≠ 0` is required.**  `q0_entry_c` divides by `s²` and `s³`, so `s = 0` is Lean junk — exactly
the same exclusion the scalar statement carries.

**Physical coefficients are required — with free `Qp`/`Qpp` the statement is FALSE.**  The
hypotheses `hsigma`/`hrho`/`heta` constrain only `sigma`/`rho`; if `Qp`/`Qpp` were left free they
could be chosen adversarially.  Counterexample recorded in `MatrixQ0.lean`'s M.3 docstring
(`n = 2`, `σ₁ = σ₂ = 1`, `rho_geo ≡ 0.1` so `η ≈ 0.0105 ∈ (0,1)`, `Qpp ≡ 0`, `Qp ≈ −13.59`) gives
`Q0_mat = !![0.5, -0.5; -0.5, 0.5]`, `det = 0`, with every hypothesis satisfied.  This is precisely
why the axiom is stated through `Q0_mat_c_phys` (i.e. `rhoGeoPhys`/`Q0phys`/`Qppphys`) and **not**
through `Q0_mat_c` with free arguments.

**Numerical evidence (2026-07-19).**  `det Q0_mat_c_phys(ik)` was computed two independent ways —
directly from `q0_entry_c`'s `n × n` formula, and via the rank-2 reduction `det(I₂ − M)` — agreeing
to `2·10⁻¹⁵` across 300 mixtures × 4 `k`-values, `N = 1..4`.  Scans: 800 random mixtures
(`N = 2,3`, `η ≤ 0.55`, size ratio `≤ 6.7`) give `min_k |det| ≥ 0.517`; a harsher 250-trial run
(`η ∈ [0.40, 0.62]`, ratio up to 20, `N ≤ 4`) gives `min_k |det| ≥ 0.375`.  `|det|` never
approaches `0`.

**Why the scalar proof does not generalise** (the load-bearing justification for axiomatizing).
The single-component proof multiplies by `k³` to clear the `1/s²`, `1/s³` poles, leaving
`N(k) − D(k)·e^{−ikσ}` with a **single** exponential; then `|e^{−ikσ}| = 1` on the real axis turns
nonvanishing into the polynomial identity `‖N‖² − ‖D‖² = k⁶`.  For `N` species the determinant
carries about `(N² + 3N)/2` distinct exponentials `e^{−ikσᵢ}`, `e^{−ik(σᵢ+σⱼ)}`, and two natural
certificates were tested, both failing:
* term-wise dominance `|c₀| > Σ_{α ≠ 0} |c_α|` over the marks `tᵢ = e^{−ikσᵢ}` — positive for
  `N = 1` (it *is* the `k⁶` fact), but **negative in 300/300 trials for `N ≥ 2`, even at size
  ratio ≈ 1.00**; splitting one species into two identical halves leaves `det` unchanged yet flips
  the margin, so the failure is an artifact of discarding phase, not of the statement;
* spectral radius `ρ(M) < 1` — fails **even at `N = 1`** (77% of trials), because `M`'s entries have
  poles as `k → 0` while `det` stays bounded.

So a proof needs a genuine phase/winding argument — the same difficulty class as the math axiom
`baxter_no_open_lhp_pole_core` (MA.14).

**Specialisation — ✅ DONE 2026-07-19** (`MixtureNoSpinodalN1.lean`; was "optional follow-up, not
done").  At `n = 1` this reduces to the scalar `pyhs_no_spinodal` exactly:
`pyhs_mixture_no_spinodal_n1` is *this* statement at `Fin 1`, proved **without** this axiom and
axiom-clean (`#print axioms` = standard three only).  So the one-component slice is not merely
consistent with an established fact — it is **redundant**, and this axiom's content is entirely in
`n ≥ 2`.  Since nothing consumes this axiom, that bridge is the only mechanical check available on
its statement; it found no bug. -/
axiom pyhs_mixture_no_spinodal {N : ℕ} {sigma rho : Fin N → ℝ}
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (heta : FMSA.MatrixQ0.etaMix rho sigma < 1) {k : ℝ} (hk : k ≠ 0) :
    (Q0_mat_c_phys (Complex.I * (k : ℂ)) sigma rho).det ≠ 0

end FMSA.MixtureNoSpinodal
