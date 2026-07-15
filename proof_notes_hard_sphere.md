# Proof Notes: Hard-Sphere Structure

Detailed proof records for Groups 2, 3, and OZ — pure hard-sphere foundations.
See `todo_lean.md` for task status summary.

## Group 2 — Hard-Sphere Baxter Factor Identities

### Task 2.1 — φ₁, φ₂ auxiliary function formulas ([chsY] Appendix A, Eq. 49; [LN] Eq. 13)

**Statement (corrected):**
```
φ₁(R; s)  =  ∫₀^R r exp(−sr) dr          =  (1 − (1+sR) exp(−sR)) / s²
φ₂(R; s)  =  ∫₀^R (r²/2) exp(−sr) dr     =  (1 − (1+sR+s²R²/2) exp(−sR)) / s³
```
The pattern is `φ_n = [1 − exp(−sR) Σ_{k=0}^n (sR)^k/k!] / s^{n+1}`.

Note: the originally stated forms `(1−sR−exp(−sR))/s²` and `(1−sR+(sR)²/2−exp(−sR))/s³`
are incorrect; verified numerically at R=1, s=1.5 (φ₁ correct=0.197, wrong=−0.321).

**Antiderivatives (needed for FTC proof):**
```
F₁(r) = −(r/s + 1/s²) exp(−sr)             F₁'(r) = r exp(−sr)
F₂(r) = −(r²/(2s) + r/s² + 1/s³) exp(−sr)  F₂'(r) = (r²/2) exp(−sr)
```

**Lean:** Prove via `intervalIntegral.integral_eq_sub_of_hasDerivAt`
using `HasDerivAt F_n (integrand) r` for each antiderivative.

**Status:** ✓ complete — `LeanCode/HardSphere/BaxterFactor.lean`
  (`phi1_formula`, `phi2_formula`, `phi1_hasDerivAt`, `phi2_hasDerivAt`, `hasDerivAt_exp_neg_mul`)

  Key tactics used:
  - `HasDerivAt.exp` (chain rule for exp(-s·x))
  - `hasDerivAt_pow` (avoids the `id^2` instance mismatch from `.pow`)
  - `HasDerivAt.congr_deriv` (adjust derivative value after product rule)
  - `integral_eq_sub_of_hasDerivAt` (FTC; takes HasDerivAt proof + integrability, no ContinuousOn)

---

### Task 2.2 — det(s) positivity / non-vanishing ([LN] Eq. 16)

**Statement:** For a physically valid mixture (η < 1), `det(s) ≠ 0` for `s ≥ 0`, ensuring the
Baxter factor Q̂₀(s) is invertible.

**Why it matters:** The propagator `A_ij(t) = 2π(ρiρj)^{1/2} W_ij(t) / (Δ det(t))` ([LN] Eq. 17)
is only well-defined when `det ≠ 0`.

**Difficulty:** Requires showing a real-analytic function has no positive real zeros given
positivity constraints on ρ, σ.  Likely needs interval arithmetic or monotonicity argument.

**Status:** ✓ DONE — `Q0_ne_zero_at_yukawa` is now a **proved theorem** (was an axiom) in
  `LeanCode/HardSphere/BaxterFactor.lean`, for the physically needed case (η ∈ (0,1), z > 0
  real Yukawa pole). The imaginary-axis version `Q0_imaginary_axis_ne_zero` was already proved.

  **The stale "z0(eta) ≈ 3" counterexample note was wrong** for this concrete `D(z)` — numerics
  across a fine grid (η ∈ (0.001, 0.999), z ∈ (0, 2000)) show `D` is strictly increasing from
  `D(0) = 0`, hence strictly positive for all `z > 0`. That note described a different,
  not-yet-pinned-down function from before `D` was reduced to this concrete single-component form.

  **Proof (monotonicity via two nested derivative arguments, no axiom needed):**
  - `bigD2(z) := d²D/dz² = 6(1−η)²z + 12η(1−η)(1−exp(−z)) + 12η(1+η/2)·z·exp(−z)` is a sum of
    three manifestly nonnegative terms for `z ≥ 0, η ∈ (0,1)`, strictly positive for `z > 0`.
  - `strictMonoOn_of_hasDerivWithinAt_pos` on `bigD1 := dD/dz` (whose derivative is `bigD2`, `>0`
    on `(0,∞)`), combined with `bigD1(0) = 0`, gives `bigD1(z) > 0` for `z > 0`.
  - Same lemma again on `D` itself (derivative `bigD1`, `>0` on `(0,∞)`), combined with `D(0) = 0`,
    gives `D(z) > 0` for `z > 0`, hence `D(z) ≠ 0`.

---

## Group 3 — Wiener–Hopf Structure

### Task 3.1 — Consistency check B₁ + D₁ = T_U ([chsY] Eq. 28)

**Statement:** For the causal/anti-causal split of T_U(k):
```
1/(ik + z)  +  1/(−ik + z)  =  2z / (z² + k²)
```
This is the Fourier transform of `exp(−z|r|)` evaluated at k, confirming that B₁ and D₁
together reconstruct the full Yukawa kernel.

**Lean:** Uses `linear_combination k^2 * Complex.I_sq` (ring alone cannot evaluate `i²=-1`).

**Status:** ✓ complete — `LeanCode/HardSphere/Splitting.lean`

---

### Task 3.2 — Support of T_S on (−∞, R_ij] ([chsY] Proof 2)

**Statement:** `{S₁(k)}_ij`, the Fourier transform of `r c_ij^(1)(r) 1_{[0,R_ij]}`, is the
Fourier transform of a function supported on `(−∞, R_ij]`.

**Why it matters:** This is the key support statement that makes the Wiener–Hopf split
well-defined.  A Lean proof would confirm the sign of the phase exponent matters.

**Status:** ✓ DONE — proved in `LeanCode/HardSphere/Splitting.lean` (complete):
  - `innerCoreFun`: `Set.indicator (Set.Icc 0 R) (fun r => r * c r)` — inner-core function
    supported on `[0, R]` by indicator construction
  - `innerCore_support_subset_Iic`: `Function.support (innerCoreFun c R) ⊆ Set.Iic R`
    — proved via `split_ifs` on indicator; value outside [0,R] is 0 so not in support
  - `T_S_eq_fourier_of_innerCore`: FT integral over [0, R] equals full-line FT of `g_R`
    — proved via `integral_indicator` + `integral_Icc_eq_integral_Ioc`

---

## Group OZ — Ornstein-Zernike Structure and Reference RDF  *(prerequisites for F.5; pure HS)*

These tasks are self-contained pure hard-sphere results — no FMSA_GA_matrix_mix or specific Yukawa
perturbation form is required.  OZ.1–OZ.4 can be proved independently of Group 4 (FMSA_GA_matrix_mix).
Together they enable the contact-value approximation assessment in Task F.5.

### Task OZ.1 — PY closed-form DCF for hard-sphere reference

**Statement:** The Percus-Yevick direct correlation function for hard spheres (diameter σ,
packing fraction η) has the closed-form polynomial structure:
```
c_HS(r) = −(α₀ + α₁·r + α₃·r³)   for r < σ
c_HS(r) = 0                         for r ≥ σ
```
where `α₀, α₁, α₃` are explicit rational functions of η (the standard PY coefficients).

**In Lean:** Define `c_HS` with these coefficients and prove it satisfies the PY closure
`c_HS(r) = g_HS(r) − 1 − h_HS(r)·g_HS(r)` (linearised) and has support in `[0, σ]`.

**Status:** ✓ complete — `LeanCode/HardSphere/PYDCF.lean`
  (`py_α₀`, `py_α₁`, `py_α₃`, `c_HS`, `py_α₃_eq`, `c_HS_measurable`, `c_HS_integrableOn`; complete)

  Key results:
  - `py_α₃_eq` — `α₃(η) = (η/2)·α₀(η)` via `field_simp`
  - `c_HS_inner` / `c_HS_outer` — `@[simp]` evaluation lemmas
  - `c_HS_measurable` — piecewise measurability via `Measurable.ite`
  - `c_HS_integrableOn` — L¹ on [0,σ] via `Ico` exact-equality route + `congr_fun`

---

### Task OZ.2 — Real-space definition of g₀_HS via OZ fixed point

> **2026-07-15 — the whole Laplace-domain line in this task was DELETED.** The axioms
> `radial_laplace_conv` (`RadialLaplace.lean`) and `oz_laplace_oz_eq` (`PYOZ_GHS.lean`), and the
> theorems that only consumed them — `oz_laplace_oz_eq_of_core_closure` (`OZExteriorBridge.lean`)
> and `g0_HS_laplace_spec` (`PYOZ_GHS.lean`) — were removed. `radial_laplace_conv` was
> mathematically false (radial 3D convolution does not factor under the real Laplace transform);
> `oz_laplace_oz_eq`'s real-`s` product form is therefore not reliably provable and is most likely
> false as stated. None had live callers, so no true result was lost, and the axiom count dropped
> 5 → 3. The correct, live OZ-domain equation is the *sine*-transform OZ.6/OZ.7/OZ.9b
> (`RadialFourier.lean` / `OZFourierBridge.lean`). **What survives in this task:** the entire
> fixed-point framework (`oz_h`, `oz_fixed_pt_unique`, `oz_operator`, …) and the
> transform-independent Gap-A lemma `oz_h_satisfies_conv_ext` (`OZExteriorBridge.lean`), which OZ.7
> reuses verbatim. Everything below that mentions `oz_laplace_oz_eq` / `radial_laplace_conv` /
> `g0_HS_laplace_spec` is retained only as historical background about the now-deleted line.

**Statement:** The hard-sphere RDF `g₀_HS(r)` is the unique solution of the
Ornstein-Zernike integral equation with the PY hard-sphere boundary conditions:
1. `g₀_HS(r) = 0` for `r < σ` (hard-core exclusion)
2. OZ convolution: `h(r) = c_HS(r) + ρ · (c_HS *₃D h)(r)` where `h = g₀_HS − 1`
Since `c_HS(r) = 0` for `r ≥ σ` (Task OZ.1), this reduces on `r > σ` to the fixed-point
problem `h = T[h]` with the radially-reduced 1D OZ operator `T`.

**What was proved (`LeanCode/HardSphere/PYOZ_GHS.lean`):**
- `oz_forcing`: forcing term (core contribution h=−1 on (0,σ)) — definition
- `oz_linear_op`: linear exterior operator on h — definition
- `oz_operator`: full OZ operator `T` (if r<σ then −1 else forcing+linear) — definition
- `OzFixedPt`: predicate `T[h] = h` pointwise — definition
- `oz_operator_core`: `T[h](r) = −1` for `r < σ` — **proved** (from `if_pos`)
- `oz_fixed_pt_core`: fixed point has `h(r) = −1` for `r < σ` — **proved**
- `oz_fixed_pt_exterior`: fixed point satisfies OZ equation for `r ≥ σ` — **proved**
- `oz_fixed_pt_unique`: `∃! h:ℝ→ℝ, T[h]=h ∧ ContinuousOn h (Ici sigma) ∧ bounded` — **axiom**
  (2026: was BCF-scoped/globally-continuous, fixed — see "2026 (latest) update" below)
- `oz_h`: canonical total correlation function via `Classical.choose` — definition
- `oz_h_core`: `oz_h(r) = −1` for `r < σ` — **proved**
- `oz_h_ghs_core`: `1 + oz_h(r) = 0` for `r < σ` — **proved**
- `g0_HS_outer`: `fun r => 1 + oz_h eta sigma rho r` — **concrete definition** 
- `g0_HS`: piecewise definition (`if r < σ then 0 else g0_HS_outer r`) — **definition**
- `g0_HS_core`: `g0_HS(r) = 0` for `r < σ` — **proved** (`if_pos hr`)
- `g0_HS_outer_is_oz_fp`: `g₀_HS_outer − 1 = oz_h` is a fixed point — **proved** (from `oz_h_is_fp`)
- `g0_HS_outer_eq_oz_h`: `g₀_HS_outer = 1 + oz_h` — **proved** (`rfl`)
- `g0_HS_laplace_spec`: Laplace OZ characterization — **proved theorem** (stale note below
  corrected: this used to be listed as an axiom; it now rests on the two OZ.2b axioms
  `oz_laplace_oz_eq` + `radial_laplace_conv` instead, see 2026 update below)
- `g0_HS_contact_value`: PY contact value `(1+η/2)/(1−η)²` — **axiom** (Wertheim 1963)

**Net improvement (restructure):**
- `g0_HS_outer` : now a concrete def `1 + oz_h`
- `g0_HS_outer_is_oz_fp`:  **proved theorem**
- `g0_HS_outer_eq_oz_h`: **proved theorem** (`rfl`)
- Definitions/theorems for `g0_HS*` moved from `PYOZ.lean` to `PYOZ_GHS.lean`

**Uniqueness** of this fixed point is Task OZ.10 (general axiom) — the dilute-density case is
now solved as Task OZ.10-dilute; see both below.

**Prerequisites:** Task OZ.1 (`c_HS_integrableOn`); Task OZ.3 for `g0_HS_laplace_spec`

**Status:** ◑ mixed (`g0_HS_outer` as def; `g0_HS_core`, `g0_HS_outer_is_oz_fp`,
  `g0_HS_outer_eq_oz_h` all genuinely proved; `oz_fixed_pt_unique` still a separate open axiom;
  `g0_HS_laplace_spec` builds as a theorem but rests on `oz_laplace_oz_eq` + the now-**disproven**
  `radial_laplace_conv` — see the 2026-later update below — so its conclusion is not actually
  established despite compiling; `g0_HS_contact_value` axiom remaining)

**2026 update — Gap A of `oz_laplace_oz_eq` closed** in
`LeanCode/HardSphere/OZExteriorBridge.lean` (no `sorry`, no new axiom). The original axiom:
```lean
axiom oz_laplace_oz_eq {eta sigma rho s : ℝ} (hsigma : 0 < sigma) (hs : 0 < s)
    (hne : 1 - rho * C_HS_laplace eta sigma s ≠ 0) :
    (∫ r in Set.Ioi (0 : ℝ), r * oz_h eta sigma rho r * Real.exp (-s * r)) *
    (1 - rho * C_HS_laplace eta sigma s) = C_HS_laplace eta sigma s
```
(`PYOZ_GHS.lean:233-236`) bundled two independent gaps. **Gap A (r ≥ σ half + Laplace
factorization)** is now fully proved:
- `oz_forcing_add_linear_op_eq_radial3d_conv`: for any continuous `h` with `h = -1` on the
  core, `oz_forcing(r) + oz_linear_op(r)[h] = ρ · radial3d_conv c_HS h (r)` for all `r ≥ σ`
  (conditional on 2 routine `IntervalIntegrable` side-conditions, taken as explicit hypotheses
  in the same spirit as `radial_laplace_conv`'s own integrability hypotheses). Proved by
  splitting the convolution's inner integral at `σ`, using `h = -1` on the core (extended to
  the boundary point `σ` itself via `Set.EqOn.closure` + continuity, not just `hcore`'s open
  hypothesis) and `Set.uIcc`/`intervalIntegral` bookkeeping.
- `oz_h_satisfies_conv_ext`: specializes the above to `h := oz_h`, using the *public*
  `g0_HS_outer_is_oz_fp` + `g0_HS_outer_eq_oz_h` (to reconstruct `OzFixedPt` for `oz_h` without
  touching the *private* `oz_h_is_fp`), `oz_fixed_pt_exterior`, and `oz_h_core`. Result:
  **`oz_h(r) = c_HS(r) + ρ·radial3d_conv c_HS oz_h (r)` unconditionally for all `r ≥ σ`** — a
  genuinely new, real result, not just a plausibility argument.
- `oz_laplace_oz_eq_of_core_closure`: assembles the above with **Gap B (PY core closure,
  r < σ)** — still genuinely hard, not derivable from anything proved (`oz_operator_core` only
  *defines* `h=-1` on the core by fiat) — taken as an explicit hypothesis `hcore`, plus routine
  integrability hypotheses for invoking `radial_laplace_conv` (itself still a separate,
  unproved axiom — a pure Fubini identity, no physics). The conclusion is the *exact* original
  axiom's statement, now a proved theorem.

**Net result (at the time of the update above):** the axiom's content was split into three
clearly separated pieces instead of one opaque bundle: (a) machine-checked algebra
(`oz_forcing_add_linear_op_eq_radial3d_conv`, `oz_h_satisfies_conv_ext` — done), (b)
`radial_laplace_conv` (separate pure-math Fubini axiom, *believed* unproved-but-true at the
time), (c) `hcore` (Gap B, the one remaining genuinely hard physics hypothesis). This is the
same honest-remaining-gap pattern used for Task M.4 (`Q0DetRankTwo.lean`,
`proof_notes_yukawa_dcf.md`) — **but see the correction below: piece (b) turned out to be
false, not just unproved.**

**2026 (later) update — `radial_laplace_conv` is mathematically FALSE, not just unproved.**
While scoping an attempt to fully prove `radial_laplace_conv` via Mathlib's real Fubini
theorem (`MeasureTheory.integral_integral_swap`), a hand re-derivation of the claimed identity
did not close, which was then confirmed by two independent methods:

1. **Numerical check** of the axiom's literal claim `ℒ_r[f⊛₃Dg](s) = ℒ_r[f](s)·ℒ_r[g](s)`
   across several `(f,g,s)` triples (including `g` with compact support on `(0,σ)`, matching
   the actual `c_HS` use case): the `LHS/RHS` ratio ranges from ~12 to ~37, varying with the
   choice of `f,g` and not just `s` — ruling out a missing normalization constant as the
   explanation.
2. **Exact symbolic re-derivation:** correctly swapping the order of integration over the
   triangle-inequality region `{(r,t,s'): |r-t|≤s'≤r+t}` (symmetric in `r,t,s'`; integrate
   over `r` first) gives
   ```
   ℒ_r[f ⊛₃D g](s) = (2π/s) · [A(s) − ℒ_r[f](s)·ℒ_r[g](s)]
   ```
   where `A(s) = ∫∫ t·f(t)·s'·g(s')·e^{-s|t-s'|} dt ds'` — a bilateral Green's-function-kernel
   term that does not vanish or factor further. This corrected formula was checked to match
   the true LHS to 6 decimal places numerically. The original proof sketch's step
   `∫_{|s-t|}^{s+t} e^{-sr} dr` does integrate correctly to `(1/s)[e^{-s|s-t|}-e^{-s(s+t)}]`,
   but the sketch then silently dropped the first (`e^{-s|s-t|}`) term — that dropped term
   *is* the missing `A(s)` piece.

**Why this can't be patched by correcting the axiom's statement:** even the true `A(s)`-
including identity would not rescue `oz_laplace_oz_eq`, which specifically needs the clean
product form to combine algebraically with `oz_laplace_identity` (`PYOZ.lean`) into
`H̃(s)(1-ρC̃(s))=C̃(s)`. The genuinely correct OZ multiplicative structure lives in Fourier
space (`ĥ(k)=ĉ(k)+ρĉ(k)ĥ(k)`, real `k`, the standard textbook 3D OZ relation) or in Baxter's
Wiener–Hopf factorization (`1-ρĉ(k)=A(k)·Ā(k)`, needing half-plane analyticity) — neither
reduces to a one-sided real Laplace transform of `r·f(r)`. So the fix is a rearchitecture of
this transform choice, not a proof-effort problem. **Done** via the Fourier route — see
Task OZ.6/OZ.7 below.

**Practical effect on the pieces above:** (a) `oz_forcing_add_linear_op_eq_radial3d_conv` and
`oz_h_satisfies_conv_ext` are real-space results independent of the Laplace transform and
remain genuinely valid/useful. (b) `radial_laplace_conv` is now known false — downgraded from
"unproved axiom" to "disproven axiom" (see Task OZ.6 below for its replacement). (c)
`oz_laplace_oz_eq_of_core_closure` and `g0_HS_laplace_spec`, which both invoke
`radial_laplace_conv` to reach the Laplace-domain conclusion, compile but do not actually
establish their stated results — superseded by Task OZ.7's Fourier-domain analogue, itself
conditional only on Task OZ.9 (the PY core closure, `hcore` — same Gap B as here).

**2026 (latest) update — `oz_fixed_pt_unique` contradicted `g0_HS_contact_value`; fixed.**
While scoping a Banach-contraction proof of `oz_fixed_pt_unique` for small `eta` (dilute
regime — see Task OZ.10 groundwork below), an attempt to show `oz_operator` is a well-defined
continuous self-map on `BoundedContinuousFunction ℝ ℝ` (the axiom's then-codomain) surfaced a
real problem: `oz_linear_op h(σ)` genuinely depends on `h`'s exterior values near `σ` (linear,
non-degenerate — compare `h≡0` vs `h≡1`), so `oz_operator h` cannot be continuous at `r=σ` for
*arbitrary* `h`. Chasing this further exposed a **real, independently-existing contradiction**:

- `oz_fixed_pt_unique` claimed the fixed point lies in `BoundedContinuousFunction ℝ ℝ` —
  continuous on *all* of ℝ, including `r=σ`.
- `g0_HS_contact_value` claims `g0_HS(σ) = (1+η/2)/(1−η)² ≠ 0` (standard Wertheim PY contact
  value).
- Since `g0_HS(r)=0` for all `r<σ` (`g0_HS_core`, proved), global continuity of `oz_h` at `σ`
  forces `g0_HS(σ)=0` by the left limit — contradicting `g0_HS_contact_value` for every
  physical `η∈(0,1)`.

Verified concretely, not just argued: a scratch `example ... : False := by ...` combining only
`oz_h_continuous` (the old theorem), `oz_h_core`, `g0_HS_outer_eq_oz_h`, `g0_HS_core`, and
`g0_HS_contact_value` type-checked with `lake env lean`, zero errors, no `sorry`.

**Physically this makes sense**: PY hard-sphere `g(r)` genuinely has a jump discontinuity at
contact (`g=0` just inside `σ`, `g=(1+η/2)/(1−η)²` just outside — standard textbook fact).
`oz_fixed_pt_unique`'s restriction to *globally* continuous functions was simply the wrong
codomain; only the exterior `[σ,∞)` needs continuity (that's where the integral-equation
content lives — the core branch `r<σ` is pinned to the constant `-1` by `oz_operator`'s own
definition, automatically continuous there regardless of any jump at the seam).

**The fix** (`PYOZ_GHS.lean`, `OZExteriorBridge.lean`): changed the regularity requirement
from global continuity to `ContinuousOn h (Set.Ici sigma)`:
```lean
axiom oz_fixed_pt_unique (eta sigma rho : ℝ) (hsigma : 0 < sigma) :
    ∃! h : ℝ → ℝ, OzFixedPt eta sigma rho h ∧ ContinuousOn h (Set.Ici sigma) ∧
      ∃ C, ∀ r, |h r| ≤ C
```
(a plain `∃! h:ℝ→ℝ` with explicit regularity conjuncts, rather than bundling into a
`BoundedContinuousFunction` type — avoids inventing a subtype-domain bundle at the axiom
level; dropping regularity entirely would still admit non-measurable pathological fixed
points the operator definition alone can't exclude). `oz_h`'s definition and `oz_h_is_fp`
updated to unwrap the 3-way `∧` (`.1`/`.2.1`/`.2.2`) instead of a `BoundedContinuousFunction`
coercion. `oz_h_continuous : Continuous (oz_h ...)` is **retired** (was mathematically false
under the corrected axiom — `oz_h` genuinely jumps at `σ`) and replaced by
`oz_h_continuousOn_ext : ContinuousOn (oz_h eta sigma rho) (Set.Ici sigma)`.

This forced a real proof rewrite in `inner_integral_bridge` (`OZExteriorBridge.lean`, part of
Gap A), which used to derive `h(σ)=-1` via `Set.EqOn.closure` + global continuity (extending
`h=-1` from the open core `(0,σ)` to its closure) — this both no longer type-checks with only
`ContinuousOn h (Ici sigma)`, and mathematically *shouldn't* work anymore (`h(σ)` genuinely
isn't `-1`). Fixed by dropping the `h(σ)=-1` step entirely and using **open-interval (`uIoo`)
a.e.-congruence** instead, tolerating the single boundary point `s=σ` differing from the core
value: `IntervalIntegrable.congr_uIoo` and `intervalIntegral.integral_congr_uIoo`
(`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`), matched only on the open
interval where `hcore` directly applies. Same "modify a measure-zero point, use an
a.e./open-interval congruence lemma" family of technique as `radial_fourier_conv`'s indicator
handling (Task OZ.6) and `c_HS_abs_integral`'s `Ioo_ae_eq_Ioc` fix (below) — just the
`uIoo`-flavored variant. Verified: full project `lake build` green, no new `sorry`; the
original scratch contradiction file now fails to compile (`oz_h_continuous` no longer exists)
confirming the fix actually closes the hole, not just relabels it.

**Uniqueness of `oz_fixed_pt_unique` is Task OZ.10** (dilute case solved as Task OZ.10-dilute) —
see both below.

---

### Task OZ.10 — Uniqueness of the OZ fixed point (`oz_fixed_pt_unique`)

**Statement:** the axiom `oz_fixed_pt_unique` (`PYOZ_GHS.lean`, shown in full above, in Task
OZ.2's "2026 (latest) update"): `∃! h : ℝ → ℝ, OzFixedPt eta sigma rho h ∧
ContinuousOn h (Set.Ici sigma) ∧ ∃ C, ∀ r, |h r| ≤ C`. Prove this via Banach's fixed-point
theorem applied to `BoundedContinuousFunction {x:ℝ//sigma≤x} ℝ` (exterior-only — see Task OZ.2's
contradiction-and-fix story for why only exterior continuity is required); requires (1) showing
`oz_linear_op` is a bounded operator there, with `‖K‖_{op} ≤ 4π|ρ|·∫₀^σ t²|c_HS(t)| dt`, and
(2) `‖K‖_{op} < 1` for the contraction to apply — this second condition is where the two density
regimes below diverge.

**Groundwork (`PYDCF.lean`), used by both regimes:**
- `py_bracket_pos`/`c_HS_neg`: the inner-core bracket
  `alpha0+alpha1·x+alpha3·x^3 > 0` for `x∈[0,1]`, `eta∈(0,1)` (hence `c_HS eta sigma t < 0` on
  `(0,σ)`) — proved via a purely algebraic minimum-at-the-boundary argument: the identity
  `f(1)-f(x) = (1-x)·(alpha1+alpha3·(1+x+x²))` (`ring`), `f(1)=(1+η/2)/(1-η)²>0`
  (`py_f1_pos`), and `alpha1+3·alpha3 = 9η(η²-1)/(2(1-η)^4) < 0` (`py_a1_add_three_a3_neg`,
  using `alpha3≥0` and `1+x+x²≤3` on `[0,1]`) combine to give `f(x)≥f(1)>0`. Symbolically
  verified via `sympy` before formalizing.
- `c_HS_abs_integral`: closed form
  `∫₀^σ t²|c_HS(t)|dt = σ³·(alpha0/3+alpha1/4+alpha3/6)` — substitutes the sign fact to drop
  the absolute value (valid a.e., via `Ioo_ae_eq_Ioc` for the single point `t=σ`), then
  integrates the resulting cubic term-by-term via `integral_pow`. This turns the `‖K‖_{op}<1`
  contraction hypothesis into the clean polynomial inequality
  `24·eta·(py_a0 eta/3+py_a1 eta/4+py_a3 eta/6) < 1`, numerically `eta* ≈ 0.08806`.

**Small `eta` (dilute, `eta < eta* ≈ 0.088`): proved.** See Task OZ.10-dilute below for the full
six-piece Banach-contraction proof of `oz_fixed_pt_unique_dilute`.

**Middle/high density (`eta≈0.3–0.5` up to `eta<1`): TRUE, but same-core as the BAXTER line — not
the compact-operator Fredholm alternative (corrected 2026-07-15).** An earlier version of this note
said this case "needs the Fredholm alternative, likely absent from Mathlib." Both halves were wrong:

- **Mathlib *has* the compact-operator Fredholm alternative**
  (`Mathlib/Analysis/Normed/Operator/Compact/FredholmAlternative.lean`,
  `hasEigenvalue_or_mem_resolventSet`), but it **does not apply**, because `oz_linear_op` (`K`) is
  **not compact**: `c_HS` is compactly supported on `[0,σ]`, so `K`'s kernel has finite width `2σ`
  — `K` is a half-line **band / Wiener–Hopf operator**, tending to *multiplication by the constant
  `−24η·bracket`* as `r→∞` (`K[1](r) = (2π·ρ/r)∫₀^σ t·c_HS·2rt dt = 4π·ρ·∫₀^σ t²·c_HS dt =
  −24η·bracket`). A nonzero multiplication operator is not compact. That constant is exactly the
  dilute Banach constant `T_ext_K` — `K`'s **spectral radius** — so `24η·bracket<1` (η≲0.088) is the
  natural Banach/Neumann boundary, not a loose estimate. (Building OZ.10-dilute's Pieces 2–3 is
  consistent with this: those lemmas are continuity/boundedness, never compactness.)

- **The statement is TRUE unconditionally for hard spheres** (no phase transition): PY
  `1−ρ·ĉ(k)>0` for all `k`, all `eta∈(0,1)` (compressibility `(1−η)⁴/(1+2η)²>0`), so no spinodal /
  no resonance. `(I−K)` is invertible not because `‖K‖<1` (false past η≈0.088) but because
  `1 ∉ spectrum(K) = symbol range {ρ·ĉ(k)} ⊂ (−∞,1)` (real symbol, winding 0), for every
  `eta∈(0,1)`. (This supersedes the earlier speculative "`detQ`-zeros = spinodal" bridge.)

- **Proving it needs no general Wiener–Hopf / Toeplitz operator theory:** the symbol factorization
  `1−ρ·Ĉ = (1−ρ·Q̂(k))(1−ρ·Q̂(−k))` is *already* the **Baxter factorization** (Task BAXTER.3,
  `baxter_wiener_hopf_factorization`; `BaxterRealSpace.lean` gives the real-space form). What is
  missing is the explicit inverse/solution from it — `(I−K)=(I−K₊)(I−K₋)`, each one-sided factor
  Volterra (spectral radius 0) hence invertible ⇒ `(I−K)` invertible ⇒ existence+uniqueness — which
  is exactly Tasks BAXTER.12–13's `h_explicit`. So OZ.10 mid/high is **same-core as, and gated by,
  the BAXTER Wiener–Hopf line**; the missing piece is a concrete construction, not Mathlib-absent
  machinery.

**Status:** ◑ mixed — dilute case (Task OZ.10-dilute) ✓ DONE, no axiom, no sorry; mid/high density
TRUE but still axiomatic here, gated by the BAXTER line (Baxter factorization BAXTER.3 → BAXTER.12–13
explicit inverse), not by any missing Mathlib theory. K's non-compactness rules out the compact
Fredholm route.

---

### Task OZ.10-dilute — Banach proof of `oz_fixed_pt_unique_dilute` (dilute regime)

**`oz_fixed_pt_unique_dilute` DONE, no axiom, no sorry**
(`HardSphere/OzFixedPtDilute.lean`, new file — kept separate from `PYOZ_GHS.lean` since it
*imports* `PYOZ_GHS.lean`, so the theorem cannot live there without an import cycle). Full
statement:
```lean
theorem oz_fixed_pt_unique_dilute (eta sigma rho : ℝ) (hsigma : 0 < sigma)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_pos : 0 < eta) (heta1 : eta < 1)
    (hsmall : 24 * eta * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) < 1) :
    ∃! h : ℝ → ℝ, OzFixedPt eta sigma rho h ∧ ContinuousOn h (Set.Ici sigma) ∧
      ∃ C, ∀ r, |h r| ≤ C
```
One deliberate deviation from the original plan sketch: adds `heta1 : eta < 1`. `hsmall` alone
does *not* force it — e.g. `eta = 5` satisfies `24·eta·bracket < 1` too, since the bracket
(`py_a0/3+py_a1/4+py_a3/6`) goes negative for `eta` past ≈2 (checked numerically). `eta < 1` is
needed for `c_HS_neg`/`c_HS_abs_integral` (both used throughout) and is physically free (`eta`
is a packing fraction).

Six pieces, all in `HardSphere/OzFixedPtDilute.lean` unless noted:
1. **Exterior domain.** `ExtDom sigma := {x:ℝ//sigma≤x}`; `extendClamp` (clamps `r` to `σ`
   before evaluating — globally continuous, used inside the contraction argument) vs
   `extendCore` (`-1` below `σ`, the semantically correct extension, used only for the final
   glued `h*`). Both agree wherever `oz_linear_op` ever reads them (`extendClamp_eq_extendCore`)
   since its integration domain `[max(r-t,σ),r+t] ⊆ [σ,∞)` always — this is what avoids the
   core/exterior gluing trap that caused the "2026 (latest) update" contradiction above.
2. **`T_ext` continuity.** `oz_forcing_continuousOn`/`oz_linear_op_continuousOn` on
   `[σ,∞)`. The novel piece: `oz_linear_op`'s inner integral has *two* moving bounds
   (`max(r-t,σ)` and `r+t`); split via `integral_interval_sub_left` anchored at `σ` into two
   one-moving-bound integrals, each handled by
   `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`
   (`@[fun_prop]`-tagged). `c_HS`'s own jump at `t=σ` removed by swapping in the explicit
   polynomial (`c_HS_inner`) via `uIoo`/a.e. congruence (single point, same technique as the
   "2026 (latest)" fix above). Factored into a standalone `oz_inner_shell_continuous` (joint
   continuity in `(r,t)`) since Piece 3/4 need it too, sliced at fixed `r`.
3. **Boundedness.** `oz_forcing_bound`/`oz_linear_op_bound`: uniform-in-`r≥σ` bounds
   `2π|ρ|σ³·bracket` / `4π|ρ|·N·σ³·bracket` (for `h` bounded by `N`). Key estimate,
   `oz_inner_shell_bound`: `|∫ s in max(r-t,σ)..(r+t), s·h(s)| ≤ N·2rt` — *tight* (not a cruder
   `N·(r+t)·2t`), via the exact antiderivative `∫s ds=(b²-a²)/2` and `max(r-t,σ)²≥(r-t)²`
   (from `r-t≥0`, itself from `t≤σ≤r`). This tightness is what makes `oz_linear_op_bound`'s
   constant `4π|ρ|Nσ³bracket` match `hsmall`'s `24η·bracket` *exactly* after the `eta`
   substitution — no slack anywhere in the chain. `oz_forcing_bound` similarly reuses the
   `t²|c_HS(t)|` integrand (via a parallel tight estimate on `σ²-(r-t)²≤2σt`), letting both
   bounds reuse `c_HS_abs_integral` directly. New PYDCF.lean lemma `c_HS_abs_t2_integrableOn`
   (`t²|c_HS(t)|` interval-integrable on `[0,σ]`, via `Integrable.mul_bdd`) backs the
   `norm_integral_le_of_norm_le` calls in both bounds.
4. **Contraction estimate.** `T_ext_contracting`: `dist (T_ext h1)(T_ext h2) ≤ K·dist h1 h2`,
   `K:=4π|ρ|σ³·bracket`. `oz_forcing` cancels in the difference (`h`-independent); the
   remainder reduces to `oz_linear_op_bound` applied to `extendClamp h1 - extendClamp h2`, via
   a genuine linearity lemma `oz_linear_op_sub` (needs integrability of both summands
   individually, from `oz_linear_op_integrand_intervalIntegrable`, itself via
   `Integrable.mul_bdd` with a crude-but-sufficient constant bound — the *tight* `2rt` bound is
   only invoked for the final numeric estimate, not for integrability).
5. **Banach assembly.** `T_ext` packaged via `BoundedContinuousFunction.ofNormedAddCommGroup`
   (continuity + boundedness from pieces 2–3); `T_ext_K` (`K` as a plain real);
   `T_ext_contractingWith` bundles `K<1` (via `Real.toNNReal`/`Real.toNNReal_lt_iff_lt_coe`) +
   `LipschitzWith.of_dist_le_mul` into `ContractingWith`; `h_ext_star :=
   (T_ext_contractingWith ...).fixedPoint` (needs `[Nonempty][CompleteSpace]` on
   `ExtDom sigma →ᵇ ℝ`, both automatic instances).
6. **Translation.** `oz_linear_op_congr_on_ext`: `oz_linear_op` only reads its function
   argument on `[σ,∞)`, so it agrees for *any* two functions agreeing there — the general form
   of the Piece-1 fact, reused both for `h* := extendCore h_ext_star` satisfying `OzFixedPt`
   (`h_star_isFixedPt`) and, in the uniqueness direction, for showing an arbitrary candidate
   `h'`'s exterior restriction is *also* a `T_ext`-fixed-point (bundled into
   `ExtDom sigma →ᵇ ℝ` via the same `ofNormedAddCommGroup` constructor, using `h'`'s own
   `ContinuousOn`/bounded hypotheses), hence equals `h_ext_star` by
   `ContractingWith.fixedPoint_unique`; combined with `h'(r)=-1=h*(r)` for `r<σ` (forced by
   `oz_fixed_pt_core`/`extendCore_eq_of_lt`), `funext` + case split on `r<σ` closes uniqueness.
   The `eta<1`-free algebra step (`hrho_pos`, `T_ext_K eta sigma rho = 24·eta·bracket` exactly,
   via `heta_def`⟹`π·rho·σ³=6·eta`⟹`4π·rho·σ³=24·eta`) is where `hsmall` becomes `K<1`.

**Depends on:** Task OZ.10's groundwork (`c_HS_neg`, `c_HS_abs_integral`).

**Status:** ✓ DONE — genuine theorem, no axiom, no `sorry`. Middle/high density remains open;
see Task OZ.10 above.

---

### Task OZ.3 — PY reference RDF g₀_HS(r) via OZ Laplace inversion

**Statement:** Applying OZ to `c_HS` from Task OZ.1 gives the Laplace-domain relation:
```
Ĥ₀(s) = Ĉ_HS(s) / (1 − ρ · Ĉ_HS(s))
```
where `Ĉ_HS(s) = ∫₀^σ r · c_HS(r) · e^{−sr} dr` is a closed-form polynomial in `s`.
Partial-fraction decomposition then gives `g₀_HS(r)` as a sum of damped exponentials for `r > σ`.

**In Lean:** Prove the algebraic OZ identity in Laplace space; derive the partial-fraction
form of `Ĥ₀(s)` and state the real-space `g₀_HS(r)`.

**Prerequisites:** Task OZ.1

**Status:** ✓ DONE — `LeanCode/HardSphere/PYOZ.lean`:
- `phi4_formula`: ∫₀^σ r⁴·e^{−sr} dr closed form (complete)
- `C_HS_laplace` + `C_HS_laplace_formula`: Ĉ_HS(s) in terms of φ₁, 2φ₂, φ₄ (complete)
- `C_HS_laplace_eq_cHS`: poly form equals c_HS integral a.e. (complete)
- `S0`: structure factor 1/(1−ρĈ_HS)
- `oz_laplace_identity`: H₀ = Ĉ·S₀ (pure algebra, complete)
- `g0_HS`, `g0_HS_outer`, `g0_HS_core`: moved to `PYOZ_GHS.lean`; `g0_HS_outer` now concrete def `1 + oz_h` 
- `g0_HS_contact_value`: moved to `PYOZ_GHS.lean` — exact PY contact value `(1+η/2)/(1−η)²` (axiom)

**2026 update — target formula confirmed algebraically, but the proof is *not* independent
of Gap B.** `[LN]` (`pdf/lecture_notes_OZ_Yukawa.tex`) states the contact value directly
(Eq. `g0_contact`):
```
g0_ij(R_ij) = (1/(R_ij·Δ)) · (R_ij + π·R_i·R_j·ξ_2/(4Δ))
```
Comparing to `Q'_ij` (defined two sections earlier in `[LN]`, and **already formalized** as
`q_prime_py` in `BaxterRealSpace.lean` for Task `BAXTER.1`, `proof_notes_baxter.md`), this is
exactly `Q'_ij/(2π·R_ij)`.
**Now a proved theorem**, `g0_contact_formula_eq_q_prime` (`BaxterRealSpace.lean`, no sorry):
```lean
theorem g0_contact_formula_eq_q_prime (eta sigma : ℝ) (hsigma : 0 < sigma) (heta : eta < 1) :
    q_prime_py eta sigma / (2 * Real.pi * sigma) = (1 + eta / 2) / (1 - eta) ^ 2
```
— the axiom's target formula, via pure algebra (`field_simp`). **This match is real and
worth keeping on record**, but does **not** mean the axiom is easier to prove:
checked directly against `oz_linear_op`'s definition (`PYOZ_GHS.lean`) — evaluating the OZ
fixed-point equation at `r=σ` needs `∫_{s=σ}^{σ+t} s·oz_h(s) ds` for `t` ranging over `(0,σ)`,
i.e. `oz_h` over the *whole interval* `[σ,2σ)`, not just the point `oz_h(σ)`. So the boundary
evaluation is exactly as entangled with `oz_h`'s unknown exterior profile as Gap B's
full-interval closure is. The alternative (Laplace-asymptotic, `s→∞` in `Ĥ₀(s)=Ĉ_HS(s)S0(s)`,
the technique `[LN]` uses for its *first-order* contact value) doesn't shortcut this either —
it needs that Laplace relation to hold for the *actual* `oz_h`, which is exactly what the
blocked `oz_laplace_oz_eq`/Gap A+B chain (or OZ.7+OZ.8's bridge) already tries to establish.
`oz_h` is defined abstractly via `Classical.choose` of an axiomatized fixed point
(`oz_fixed_pt_unique`), so any concrete closed-form claim about it — at the boundary or any
interior point — needs the same abstract-to-concrete bridge. **Not yet attempted in Lean.**

**Relation to Gap B (Task OZ.9):** shares the same underlying physics — see the dedicated
Task OZ.9 section below for the full account, including: Gap B's direct numerical
verification and its resulting axiom `oz_core_closure` (Route A, now done); Baxter's second
relation (`r·h(r) = -Q'(r)/(2π) + ρ∫₀^σ Q(t)(r-t)h(|r-t|)dt`, also numerically verified) as
the alternative Route B that would additionally unlock `g0_HS_contact_value`, not yet taken
(needs an unverified `Q`-elimination bridge first).

---

### Task OZ.4 — Linearized OZ: Ĥ^(1)(s) = Ĉ^(1)(s) · S₀(s)

**Statement:** At first order in any Yukawa perturbation, the linearised OZ equation gives
the general algebraic identity in Laplace space:
```
Ĥ^(1)(s) = Ĉ^(1)(s) · S₀(s),      S₀(s) = 1 + ρ · Ĥ₀(s)
```
where `S₀(s)` is the HS structure factor from Task OZ.3.  This holds for **any** `Ĉ^(1)(s)`
— the specific FMSA_GA_matrix_mix closed form ([chsY] Eq. 41, Task 4.4) is **not** required here.

**In Lean:** Prove `Ĥ^(1) = Ĉ^(1) · S₀` from the linearized OZ convolution equation
(a pure algebraic identity given OZ.3).  Task 4.4 is **not** a prerequisite here;
substituting a specific `Ĉ^(1)` to obtain a closed-form `h^(1)(r)` is a later step
that builds on both OZ.4 and Task 4.4.

**Prerequisites:** Task OZ.3 only (Task 4.4 is NOT required)

**Status:** ✓ DONE — `oz_linearized_identity` in `LeanCode/HardSphere/PYOZ.lean` (complete).
Proved: given `H1 * (1 − ρ·Ĉ_HS(s)) = C1`, then `H1 = C1 * S0 η σ ρ s`.
Same 3-line algebra as `oz_laplace_identity`; `div_eq_iff` + `linarith`.

---

**Task OZ.5 (Baxter real-space convolution identity) has moved to `proof_notes_baxter.md`
Task `BAXTER.1`** — it's part of Group BAXTER's Baxter-Q-factor family, not the general OZ/PY
solution framework. `q0_poly`, `q_prime_py`, `q_doubleprime_py` (defined in
`LeanCode/HardSphere/BaxterRealSpace.lean`) and `baxter_factorization_inner` are the concrete
Lean artifacts; see `proof_notes_baxter.md` for the full writeup.

---

### Task OZ.6 — Radial sine/Fourier transform convolution theorem

**Statement:** the correct replacement for the disproven `radial_laplace_conv` (see the
2026-later update in Task OZ.2's write-up above). Define the radial sine transform
```
𝓕_r[f](k) = (4π/k) · ∫_0^∞ r·f(r)·sin(kr) dr
```
(the radial reduction of the genuine 3D Fourier transform). Then, unlike the one-sided real
Laplace transform, this *does* turn `radial3d_conv` into a clean product:
```
𝓕_r[f ⊛₃D g](k) = 𝓕_r[f](k) · 𝓕_r[g](k)
```
with **no extra term** — confirmed both symbolically and numerically (machine precision)
before writing any Lean.

**Why this succeeds where the Laplace attempt failed:** doing the same triangle-region
integration-order swap (over `{(r,t,s): |r-t|≤s≤r+t}`, integrate `r` first for fixed `(t,s)`),
the inner step is
```
∫_{|t-s|}^{t+s} sin(kr) dr = (2/k)·sin(kt)·sin(ks)
```
via the antiderivative `-cos(kr)/k` plus the product-to-sum identity
`cos(a-b) - cos(a+b) = 2 sin a sin b`. This is an *exact* factorization into a product of
`sin(kt)` and `sin(ks)` — the analogous Laplace-case step gives `e^{-s|t-s'|}` and
`e^{-s(t+s')}`, and only the second half of that difference matches the desired product; the
first half (`e^{-s|t-s'|}`) is exactly the extra, non-factoring term `A(s)` that made
`radial_laplace_conv` false. The sine kernel has no such leftover because `cos(a-b)-cos(a+b)`
resolves completely into the product `2 sin a sin b`.

**In Lean:** `LeanCode/HardSphere/RadialFourier.lean` (new file). Key pieces, all proved
(no `sorry`, no axiom):
- `radial_fourier` — the transform, defined exactly as above.
- `sin_triangle_integral` — the trig identity, via `intervalIntegral.integral_comp_mul_left`
  + `integral_sin` (`cos a - cos b` antiderivative) + `Real.cos_sub`/`Real.cos_add` unfolded
  by hand (no direct `Real.cos_sub_cos` lemma in this Mathlib snapshot; the 6-line derivation
  mirrors `Complex.cos_sub_cos`'s proof).
- `triangle_mem_iff` — the triangle-inequality region is symmetric under solving for any one
  of its three variables (`s ∈ Icc|r-t|(r+t) ↔ r ∈ Icc|t-s|(t+s)`), pure `abs_le`+`linarith`.
- `setIntegral_Icc_eq_setIntegral_Ioi_indicator` — bridges a bounded `Icc a b` set-integral
  (a≥0) to an indicator integral over `Set.Ioi 0`, needed since `radial3d_conv`'s inner
  integral is over `Icc`, but the Fubini swap needs everything on the same `(0,∞)`-restricted
  product measure; the `a=0` boundary case is handled via `MeasureTheory.ae_eq_set` (removing
  the single point `{0}` doesn't change a Lebesgue integral).
- `radial_fourier_conv` — the main theorem. Proof: (1) cancel `radial3d_conv`'s own `1/r`
  against the outer `r` weight; (2) convert the moving-bound `s`-integral to an indicator
  integral and fold the `t*f(t)` constant in via `integral_const_mul`, then apply
  `MeasureTheory.integral_integral` (nested → joint over `(t,s)`, per-`r`); (3) push `sin(kr)`
  into the `(t,s)`-integral and apply `MeasureTheory.integral_integral_swap` to swap `r`
  against the `(t,s)` pair as a whole; (4) evaluate the inner `r`-integral pointwise for each
  `(t,s) ∈ Ioi 0 ×ˢ Ioi 0` via `triangle_mem_iff` + `sin_triangle_integral` (converting between
  indicator/Icc/interval-integral forms along the way); (5) factor the resulting product
  integral via `MeasureTheory.integral_prod_mul` (unconditional — no integrability hypothesis
  needed, since it returns `0` on both sides when not integrable) and close with `ring`.

**Hypotheses:** `htsInt` (per-`r` joint integrability of `(t,s) ↦ t·f(t)·indicator(...)`) and
`hjoint` (the full triple joint integrability, needed for the `r ↔ (t,s)` swap) are taken as
explicit hypotheses, in the same spirit as `OZExteriorBridge.lean`'s own integrability
side-conditions — deriving them from plain marginal L¹ facts about `f,g` is a further,
orthogonal piece of work (the crude bound `|sin|≤1` alone is too lossy for `r`-integrability
over all of `(0,∞)` without support/decay information). No separate hypothesis on `f` or `g`
alone (e.g. an `hf`/`hg` pair analogous to `radial_laplace_conv`'s) is needed — checked by
building the theorem with such hypotheses first and finding they were unused by the actual
proof, then removing them.

**Status:** ✓ DONE — `LeanCode/HardSphere/RadialFourier.lean`, no sorry, no axiom.

---

### Task OZ.7 — Fourier-domain exterior OZ equation for `oz_h`

**Statement:** the mathematically correct counterpart of `oz_laplace_oz_eq_of_core_closure`
(`OZExteriorBridge.lean`), replacing its false `radial_laplace_conv` step with the proved
`radial_fourier_conv` (Task OZ.6):
```
radial_fourier (oz_h eta sigma rho) k · (1 - rho · radial_fourier (c_HS eta sigma) k)
  = radial_fourier (c_HS eta sigma) k
```
conditional only on Gap B (`hcore`, the PY core closure for `r<σ` — genuinely hard physics,
identical hypothesis to `oz_laplace_oz_eq_of_core_closure`'s, unrelated to the transform
choice) plus routine integrability side-conditions.

**In Lean:** `LeanCode/HardSphere/OZFourierBridge.lean` (new file), `theorem
oz_fourier_oz_eq_of_core_closure`. Proof structure directly mirrors
`oz_laplace_oz_eq_of_core_closure`:
1. `hpointwise` — combine Gap A (`oz_h_satisfies_conv_ext`, `OZExteriorBridge.lean`, reused
   verbatim/unchanged since it's a real-space result independent of the transform choice) with
   Gap B (`hcore`) to get the full pointwise 3D-OZ convolution equation for every `r > 0`.
2. `hsum`/`hfourier` — apply `radial_fourier` to both sides. Unlike the Laplace case,
   `radial_fourier` carries an explicit `4π/k` prefactor, so the linearity step first proves
   the identity at the level of the bare (unprefactored) integrals via
   `MeasureTheory.integral_add`, then multiplies through by `4π/k` via `ring` — a small but
   real deviation from the Laplace proof's structure, caught by a failed `rw` when first
   copying the Laplace pattern directly.
3. `radial_fourier_conv` factors the convolution transform (in place of the disproven
   `radial_laplace_conv`).
4. `linear_combination` closes the final rearrangement to the `H·(1-ρC)=C` form.

**Integrability hypotheses** (`hintB1`, `hintConv`) needed the explicit `sin(kr)` weight
(`Integrable (fun r => r * c_HS eta sigma r * Real.sin (k*r)) ...`), not just the bare
`r * c_HS eta sigma r` — an analogous correction to the `radial_fourier_conv` hf/hg situation,
but here the weighted form genuinely *is* needed (for `MeasureTheory.integral_add`'s
literal hypotheses), unlike OZ.6 where the unweighted marginal hypotheses turned out unused.
`hintB2` (for `oz_h`) was dropped entirely — not needed since `radial_fourier_conv`'s own
signature (after removing its unused `hf`/`hg`) has no marginal-integrability parameter to
supply it to.

**Status:** ✓ DONE — `LeanCode/HardSphere/OZFourierBridge.lean`, no sorry, no axiom, conditional
only on Gap B (same physics hypothesis as OZ.2b's `oz_laplace_oz_eq_of_core_closure`).

---

### Task OZ.8 — closed-form sine-transform of `c_HS` + bridge to `C_HS_laplace`/`S0`

**Statement.** Two things `OZFourierBridge.lean` left as abstract: (A) a closed-form for
`radial_fourier (c_HS eta sigma) k` (analogous to `C_HS_laplace_formula`), and (B) an explicit
correspondence between that closed form and `C_HS_laplace_formula` under `s ↦ -ik`, making the
Fourier-domain non-resonance condition (`1 - rho·radial_fourier (c_HS eta sigma) k`, implicit
in `oz_fourier_oz_eq_of_PY_core`) concretely comparable to the existing Laplace-domain
`S0`/`hne` condition (`1 - rho·C_HS_laplace eta sigma s ≠ 0`).

**Scoping decision (user-confirmed):** OZ.8 as originally titled bundled a third thing — using
this to derive `g0_HS_contact_value` — which is **not attempted**. That needs inverting the
closed-form-in-`k` Fourier-domain OZ solution back to real space (residue calculus / the
classical PY closed-form solution), a multi-session undertaking on the scale of the Baxter
Wiener–Hopf work (Task `BAXTER.3`) already flagged elsewhere as out of scope. Tracked separately
as Task `BAXTER.4` (`proof_notes_baxter.md`, Group BAXTER).

**In Lean:** `LeanCode/HardSphere/RadialFourierCHS.lean` (new file, no sorry, no axiom).

**Part A — `radial_fourier_c_HS_formula`.** Same technique as `C_HS_laplace_formula`
(`phi1/phi2/phi4_formula`'s `HasDerivAt`+FTC pattern), just for `sin` instead of `exp(-s·)`:
1. `radial_fourier_c_HS_eq_intervalIntegral` — reduces `radial_fourier`'s `Set.Ioi 0` integral
   to a finite `intervalIntegral` on `[0,sigma]`, via the same indicator-rewrite technique as
   `RadialFourier.lean`'s `setIntegral_Icc_eq_setIntegral_Ioi_indicator`, used in reverse
   (`c_HS` vanishes identically past `sigma`, not just a.e.).
2. `psi1_formula`/`psi2_formula`/`psi4_formula` — closed forms for `∫0^sigma r^n·sin(k·r) dr`,
   `n=1,2,4` (the powers appearing in `r·c_HS(r)`'s expansion). No Mathlib lemma exists for
   `∫x^n·sin(ax)dx` (checked), so each needed an explicit antiderivative verified via
   `HasDerivAt` — antiderivatives sourced from `sympy` before formalizing (residual check, not
   guessed). `psi4_formula`'s antiderivative (5 terms) was the most tedious single piece,
   mechanically identical to `phi4_formula`'s.
   - Recurring Lean 4 pitfall hit repeatedly here: `HasDerivAt.add`/`.sub`'s conclusion is
     stated as raw function subtraction/addition (`f - g`, via `Pi.instSub`), not the
     eta-expanded `fun x => f x - g x` — `exact`/`simpa` fail on the resulting (defeq but not
     syntactically matching) type. Fixed via `HasDerivAt.fun_add`/`.fun_sub` (the
     `@[to_fun]`-generated companions that DO state the eta-expanded conclusion directly),
     plus, for lingering associativity (`a*(b/c)` vs `a*b/c`) or `id x` vs `x` mismatches,
     `simp only [← mul_div_assoc, id_eq] at h` before the final `exact h`.
3. `radial_fourier_c_HS_formula` assembles (1)+(2), swapping `c_HS` for its explicit polynomial
   via `uIoo` congruence (tolerating the single differing point `r=sigma`, same technique as
   `C_HS_laplace_eq_cHS`).

**Part B — `radial_fourier_c_HS_eq_C_HS_laplace_expr`.** Deliberately *not* built via
Mathlib's analytic-continuation/identity-theorem machinery
(`Mathlib.Analysis.Analytic.Uniqueness`/`IsolatedZeros` — confirmed present, has the right
shape, but unneeded): since both closed forms already exist explicitly (Part A;
`C_HS_laplace_formula`), the bridge is a finite symbolic verification, not a general theorem.
`C_HS_laplace_expr (eta sigma : ℝ) (s : ℂ) : ℂ` is `C_HS_laplace_formula`'s RHS as a plain
algebraic expression (not an integral) with `s`/`Real.exp` promoted to `ℂ`/`Complex.exp`;
`C_HS_laplace_expr_ofReal` confirms it's a faithful complex lift (agrees after casting, for
real `s`) via `push_cast; ring`. The main theorem substitutes `s := -Complex.I*k`:
- `Complex.exp_ofReal_mul_I` converts the exponential term to `Real.cos+Real.sin·I` directly
  (no separate `Complex.ofReal_cos`/`_sin` bridging needed).
- `s^2,s^3,s^4,s^5` at `s=-Ik` reduce to clean real-or-purely-imaginary casts
  (`((-(k^2):ℝ):ℂ)`, `((k^3:ℝ):ℂ)*I`, `((k^4:ℝ):ℂ)`, `((-(k^5):ℝ):ℂ)*I`) via `linear_combination`
  against `Complex.I_sq`/`Complex.I_pow_four` — `push_cast; linear_combination c * Complex.I_sq`
  (or `I_pow_four`), verified in an isolated scratch file first (cheap, catches sign errors
  before touching the main proof).
- Taking `.im` of a sum of `N/(real-or-real·I)` terms: `Complex.div_ofReal_im`
  (`@[simp]`, already in Mathlib) handles the real-denominator term directly;
  the real·I-denominator terms need a small proved-from-scratch helper,
  `im_div_ofReal_mul_I (z)(r) : (z/((r:ℂ)*I)).im = -z.re/r`, via
  `z/((r:ℂ)*I) = z/(r:ℂ)/I = -(z/(r:ℂ)*I)` (`div_mul_eq_div_div`, `Complex.div_I`) then
  `Complex.div_ofReal_re`. (First attempt used the fully generic `Complex.inv_re`/`inv_im`
  formula via `normSq` on the *unreduced* `s^2,s^3,s^5` — technically correct but produced an
  enormous, untractable expression since it couldn't see that the denominators were secretly
  real/imaginary; substituting the clean forms *first* was the fix.)
- Final `.re`/`.im` decomposition of the resulting (still sizeable) expression via a `simp only`
  with the standard `Complex` arithmetic lemma set (`add_im/re`, `mul_im/re`, `sub_im/re`,
  `neg_im/re`, `ofReal_im/re`, `I_im/re`, `one_im/re`, `re_ofNat`/`im_ofNat`,
  `← Complex.ofReal_pow` to push casts through powers like `(sigma:ℂ)^3`) — an *unrestricted*
  `simp` was tried first and failed: it round-tripped `↑(Real.cos x)` back into `Complex.cos ↑x`
  via a competing `norm_cast`-tagged lemma, producing an unreducible mess. `simp only` with an
  explicit, curated list avoided this.
- Closed by `field_simp; ring` on the now-fully-real goal, confirming exact equality (ratio 1,
  no missing sign/factor — matching an independent `sympy` numeric check of the same
  correspondence done before writing any Lean).

**Status:** ✓ DONE (Parts A+B) — `LeanCode/HardSphere/RadialFourierCHS.lean`, no sorry, no
axiom. Part C (bridge to `g0_HS_contact_value`) as originally scoped (full residue inversion) —
see Task `BAXTER.4`, `proof_notes_baxter.md`; a narrower alternative route succeeded instead, see
Task `BAXTER.8`.

---

### Task OZ.9 — PY core closure (Gap B)

**Statement:** for `0 < r < σ`, the OZ convolution equation itself holds (not just the known
value `oz_h(r)=-1`):
```
oz_h(r) = c_HS(r) + ρ · radial3d_conv c_HS oz_h (r)
```
This is the "genuinely hard, unscaffolded physics input" (Wertheim 1963 / Baxter 1970's PY
closure) left after Gap A closed — previously an explicit hypothesis `hcore` on
`oz_laplace_oz_eq_of_core_closure`/`oz_fourier_oz_eq_of_core_closure`.

**Two possible routes:**
- **Route A (direct axiom) — taken.** State the closure equation itself as a named axiom,
  justified by direct numerical verification.
- **Route B (via Baxter's second relation) — not taken.** Would also unlock
  `g0_HS_contact_value`, but needs a from-primary-source re-derivation first — see
  `proof_notes_baxter.md` Task `BAXTER.2` (full `h(r)`, all `r`) and the narrower Task
  `BAXTER.5` (contact value only, since achieved via `BAXTER.6`–`8`), both built on Task
  `BAXTER.3`'s Wiener–Hopf factorization. Task `BAXTER.4` (full residue-calculus inversion of
  OZ.8's Fourier closed form) turned out **not** to be an independent route — it shares
  `BAXTER.2`/`5`'s same underlying analyticity question.

**Route A — numerical verification.** Solved the exact OZ+PY system from scratch,
independent of any Baxter `Q`-function machinery: the already-proved closed-form `c_HS(r)`
(`PYDCF.lean`) was numerically Fourier-transformed (`Ĉ(k)`, direct quadrature), `Ĥ(k) =
Ĉ(k)/(1-ρĈ(k))` formed by pure OZ algebra, then numerically inverse-transformed to get
ground-truth `h(r)` (sanity-checked: recovers `h(r)≈-1` inside the core; near-contact value
converges to the *known* analytic contact formula `(1+η/2)/(1-η)²-1` as truncation is
refined, at η=0.3 — an independent cross-check of `g0_HS_contact_value`'s target formula too).
Plugging this ground-truth `h(r)` directly into Gap B's closure equation:
```
c_HS(r) + ρ·radial3d_conv(c_HS,oz_h)(r) ≈ -1.01 to -1.02     (target: -1)
```
at `r=0.2, 0.5, 0.8` (η=0.3) — matching to within the numerical setup's known truncation
error, with **no** need to route through Baxter's `Q`-function at all. Verification script
not committed (scratchpad only); rerunnable from this description.

**In Lean:** `LeanCode/HardSphere/PYOZ_GHS.lean`:
```lean
axiom oz_core_closure {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      oz_h eta sigma rho r =
        c_HS eta sigma r + rho * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r
```
`heta_def`/`heta_lt` restrict to the physical PY regime the numerical check assumed (not
claimed for arbitrary unrelated `eta,sigma,rho` triples) — matches the honesty standard
`g0_HS_contact_value`'s axiom already uses. Proving this from Mathlib-available real analysis
(rather than assuming it) needs Baxter's Wiener–Hopf factorization — out of current scope.

`LeanCode/HardSphere/OZFourierBridge.lean`: `oz_fourier_oz_eq_of_PY_core` — direct
specialization of `oz_fourier_oz_eq_of_core_closure` (OZ.7) supplying `oz_core_closure` in
place of the externally-threaded `hcore`. The most complete, trustworthy result in the whole
`radial_laplace_conv`/`oz_laplace_oz_eq` lineage: Gap A (proved), the convolution theorem
(proved, no false-claim risk), and Gap B (`oz_core_closure`, numerically verified) are all
now accounted for by name — only routine integrability hypotheses remain open.
**Deliberately not built:** an analogous Laplace-domain wrapper around
`oz_laplace_oz_eq_of_core_closure` (`OZExteriorBridge.lean`) — that theorem internally invokes
the disproven `radial_laplace_conv`, so supplying `oz_core_closure` for its `hcore` argument
would not make its conclusion any more trustworthy; not worth building.

**Status:** ✓ DONE (Route A) — `oz_core_closure` axiom (`PYOZ_GHS.lean`) + corollary
`oz_fourier_oz_eq_of_PY_core` (`OZFourierBridge.lean`), no sorry. Route B / the Wiener–Hopf
factorization / the OZ.8 residue-calculus route turned out to be one underlying problem, not
three independent ones — `BAXTER.3` (the factorization) is DONE; `BAXTER.2`, `4`, `5` all build
on it. `BAXTER.5`-`8` (the jump-asymptotic sub-chain) succeeded and closed `g0_HS_contact_value`
(conditionally); `BAXTER.2`'s own full `h(r)` construction (needed to retire *this* axiom) is
still open — see `proof_notes_baxter.md`.

---

**Tasks OZ.11–OZ.17 (and their `OZ.13` sibling) have moved to `proof_notes_baxter.md`,
renumbered `BAXTER.2`–`BAXTER.8` (plus `BAXTER.4` for the old `OZ.13`)** — Baxter's
Wiener–Hopf factorization, the jump-asymptotic route to `g0_HS_contact_value`, and the
staged plan (`BAXTER.9`–`13`) for the full residue-series construction needed to retire
`oz_core_closure` itself. See `proof_notes_baxter.md`, Group BAXTER, for the full writeups.

---

### Task OZ.18 — Hard-sphere `λ_ij` kink in `c_HS` *(formerly B.19)*

*Moved here 2026-07-15 from the Yukawa breakpoint family (old **B.19**): this is an FMT
hard-sphere property, outside the Yukawa mediated chain. See
[proof_notes_breakpoints.md](proof_notes_breakpoints.md) (Group IB) for the mediated
breakpoints `r*`/`r**`.*

**Statement:** `c_HS,ij(r)` has a C⁰ slope kink at `λ_ij = |d_i − d_j|/2 = |R_i − R_j|` for unlike
pairs `i ≠ j`. `get_HS_FMT` clamps `r → |λ_ij|` for `r < |λ_ij|`, so `c_HS` is **constant** below
`λ_ij` and the White-Bear rational form above; the one-sided slopes differ (`0` vs `≠ 0`) ⇒
genuine C⁰ kink. This is the FMT realization of the Lebowitz two-piece PY structure.

**Proof (2026-07-15).** The kink is a property of the *clamp itself*, independent of the White-Bear
form, so it is isolated abstractly first:
`clampedBelow F λ r := if r < λ then F λ else F r` (mirrors the `if r < |λ_ij|: r = |λ_ij|` guard).
- `clampedBelow_continuousAt` — continuous at `λ` if `F` is (via `clampedBelow F λ = F ∘ (max · λ)`). **C⁰.**
- `clampedBelow_hasDerivWithinAt_Iic`/`_Ici` — the one-sided derivatives at `λ` are exactly `0`
  (constant on `Iic λ` by `EqOn` + `HasDerivWithinAt.congr`) and `F'(λ)` (`clampedBelow = F` on `Ici λ`).
- `clampedBelow_not_differentiableAt` — if `F'(λ) ≠ 0`, a two-sided derivative `L` would give
  `L = 0` on `Iic` and `L = F'(λ)` on `Ici` (`HasDerivWithinAt.derivWithin` + `uniqueDiffOn_Iic/Ici`),
  contradiction. **Genuine kink.**

Then `F` is instantiated with the faithful White-Bear core `cHS_core` (mirrors `get_HS_FMT`'s
`return -(χ₃·(π/6r)·V + χ₂·(π/r)·S + χ₁·Rterm/r + (χ₂₂−χ₁/4π)·Rprime + χ₀)`, with `χ₀…χ₃, χ₂₂` as
parameters). `cHS_core_eq_num` rewrites it as `−(polynomial)/r − χ₀` for `r ≠ 0`, giving
`cHS_core_differentiableAt` at any `r ≠ 0` (so at the cutoff of an unlike pair). `cHS_FMT :=
clampedBelow cHS_core |Rᵢ−Rⱼ|`; final theorems `cHS_FMT_continuousAt` (C⁰),
`cHS_FMT_hasDerivWithinAt_Iic`/`_Ici` (slopes `0` and `F'(λ)`), `cHS_FMT_not_differentiableAt`
(kink).

**Out of scope (numerical, faithful):** `F'(λ) ≠ 0` is *state-point-dependent* (the χ's are
functions of `η`/densities), so it is an explicit hypothesis `hslope`, not derived from `σ > 0` —
exactly as the strict-positivity half of Group IB stays numerical (`verify_stepwise_breakpoints.py`).

**Lean:** `HardSphere/CHSKink.lean` — identifiers task-ID-free (`clampedBelow`, `cHS_core`,
`cHS_FMT`, `cHS_FMT_continuousAt`, `cHS_FMT_not_differentiableAt`, …).
**Depends on:** none beyond `get_HS_FMT`'s two-piece definition; only Mathlib.
**Status:** ✓ DONE (2026-07-15), axiom-clean. Continuity + both one-sided slopes unconditional;
genuine-kink conclusion conditional on the numerical `F'(λ) ≠ 0`.
