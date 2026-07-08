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
- `oz_fixed_pt_unique`: `∃! h : BCF, T[↑h] = ↑h` — **axiom** (BCF-scoped; broad ℝ→ℝ version dropped — may be false)
- `oz_h`: canonical total correlation function via `Classical.choose` on BCF — definition
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

**Remaining work (OZ.2a):** Prove `oz_fixed_pt_unique` (BCF version) via Banach fixed-point theorem.
Requires: (1) show `oz_linear_op` is bounded on `BoundedContinuousFunction ℝ ℝ`
with `‖K‖_{op} ≤ 4π|ρ|·∫₀^σ t²|c_HS(t)| dt` < 1 for small ρ; (2) apply `ContractingWith.efixedPoint`.

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
`q_prime_py` in `BaxterRealSpace.lean` for Task OZ.5), this is exactly `Q'_ij/(2π·R_ij)`.
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

### Task OZ.5 — Baxter real-space convolution identity

**Statement (Wertheim 1963; Baxter 1970; [chsY] Eq. 46):**

For `r ∈ (0, σ)`, the PY hard-sphere DCF satisfies the real-space Wiener-Hopf identity:
```
2π·ρ·r·c_HS(r) = ∫_r^σ q0_poly(r'−r)·q0_poly'(r') dr' − q0_poly'(r)
```
where:
- `q0_poly(r) = α·(r−σ) + β·(r−σ)²/2` with `α = ρ·q_prime_py`, `β = ρ·q_doubleprime_py`
- `q0_poly'(r) = α + β·(r−σ)` is the derivative of q0_poly w.r.t. r
- `q0_poly = 2πρ·Q` where Q is the Wertheim Q-function for diameter σ

**Physical origin (Wertheim 1963):** The Wiener-Hopf factorization `1−ρĈ(s) = Q̂(s)Q̂(−s)` gives
the real-space identity `−r·c(r) = Q'(r) − 2πρ ∫_0^{σ-r} Q(t)·Q'(t+r) dt`. With Q = q0_poly/(2πρ)
and Q' = q0_poly'/(2πρ), multiplying by −2πρ and changing variables t → r'−r gives the Lean form.

**Numerical verification at η=0.4, σ=1, r=0.5, ρ=2.4/π:**

| Quantity | Value |
|---|---|
| 2πρ·r·c_HS(0.5) (LHS) | 2π·(2.4/π)·0.5·(−295/24) = −29.5 |
| q0_poly'(0.5) = α+β(r−σ) | 4 |
| ∫_r^σ q0_poly(r'−r)·q0_poly'(r') dr' | −25.5 (exact via antiderivative) |
| RHS = −25.5 − 4 | −29.5 ✓ |

**In Lean:** `baxter_factorization_inner` in `LeanCode/HardSphere/BaxterRealSpace.lean`:
```lean
theorem baxter_factorization_inner {eta sigma rho : ℝ}
    (hsigma : 0 < sigma) (_heta0 : 0 <= eta) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∀ r ∈ Set.Ioo 0 sigma,
    2 * Real.pi * rho * r * c_HS eta sigma r =
    (∫ r' in r..sigma, q0_poly eta sigma rho (r' - r) *
      (rho * q_prime_py eta sigma + rho * q_doubleprime_py eta * (r' - sigma))) -
    (rho * q_prime_py eta sigma + rho * q_doubleprime_py eta * (r - sigma))
```

**Proof approach (polynomial FTC + ring):**
1. Rewrite integral via `integral_congr`: substitute `q0_poly_inner` + `← hα_def`, `← hβ_def`.
2. Compute `∫_r^σ q0_poly(r'−r)·q0_poly'(r') dr'` via FTC on the 7-term degree-4 antiderivative:
   ```
   F(x) = α²/2·(x−σ−r)² + αβ/3·(x−σ)³ − αβr/2·(x−σ)² + αβ/6·(x−σ−r)³
         + β²/8·(x−σ)⁴ − β²r/3·(x−σ)³ + β²r²/4·(x−σ)²
   ```
3. Apply `HasDerivAt` chain (7 terms) + `integral_eq_sub_of_hasDerivAt`; F(σ) evaluates cleanly.
4. Substitute η = π·ρ·σ³/6; clear denominators with `field_simp [hsigma.ne', h1e]`; close by `ring`.

**Key Lean 4 patterns:**
- `HasDerivAt.congr_of_eventuallyEq` takes ONE explicit arg → `refine (hchain.congr_of_eventuallyEq ?_).congr_deriv ?_`
- `Filter.Eventually.of_forall` (not the deprecated `Filter.eventually_of_forall`)
- After `rw [q0_poly_inner ..., ← hα_def, ← hβ_def]`, the `integral_congr` goal closes automatically (no `ring` needed)

**Prerequisites:**
- `q0_poly_inner`, `c_HS_inner` (proved)
- `q_prime_py`, `q_doubleprime_py` (defined)
- `eta = pi*rho*sigma^3/6` (`heta_def`)

**Note on `hParseval` (Task F.4):** This is the **hard-sphere** Baxter identity.  Task F.4's
`hParseval` is a **Yukawa** Baxter identity: `∫_0^d b_ij(r)dr = K(1+A)²/z` where `b_ij(r)` is
the chsY inner-core function from [chsY] Eq. 41.  That requires a separate task using `I1`/`I2`
integrals and the MSA closure for `A`.

**Status:** ✓ PROVED — `LeanCode/HardSphere/BaxterRealSpace.lean`, no sorry.

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

**Not done here (Task OZ.8):** no closed-form sine-transform formula for `c_HS` is derived,
and no bridge back to `C_HS_laplace`/`S0`/`g0_HS_contact_value` is attempted — the conclusion
is stated directly in terms of `radial_fourier (c_HS eta sigma) k`, not a named closed form.
Bridging via analytic continuation `s ↔ -ik` (valid since `c_HS` has compact support, so its
Laplace transform is entire) is plausible future work, flagged but not started.

**Status:** ✓ DONE — `LeanCode/HardSphere/OZFourierBridge.lean`, no sorry, no axiom, conditional
only on Gap B (same physics hypothesis as OZ.2b's `oz_laplace_oz_eq_of_core_closure`).

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

**Two possible routes, both scoped this session:**
- **Route A (direct axiom) — taken.** State the closure equation itself as a named axiom,
  justified by direct numerical verification.
- **Route B (via Baxter's second relation) — scoped, not taken.** See below; would also
  unlock `g0_HS_contact_value`, but needs an unverified bridge step.

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

**Route B (not taken this pass) — Baxter's second relation.** Also numerically verified this
session (independently, before discovering Route A's more direct check):
```
r·h(r) = -Q'(r)/(2π) + ρ·∫₀^σ Q(t)·(r-t)·h(|r-t|) dt      for r > 0
```
where `Q(t) = q_prime_py·(t-σ) + q_doubleprime_py·(t-σ)²/2` for `0≤t≤σ` (0 outside) — the
same `Q` underlying `q0_poly`/OZ.5 (`q0_poly(t) = ρ·Q(t)`; this relation uses `Q` itself).
Verified at three `η` (0.1, 0.3, 0.45) against the same ground-truth `h(r)` solver, matching
to within ~0.3–5% (residual consistent with Fourier-inversion truncation). The *first*
reconstruction attempted (from general memory of Baxter 1970, not a primary source) was
structurally right but off by a factor of `2π`, caught by the same red-flag pattern that
disproved `radial_laplace_conv` — except here the LHS/RHS ratio was *constant* (~1/2π) across
every `r` tested rather than varying, indicating a normalization bug rather than a false
relation. This route would additionally unlock `g0_HS_contact_value` (specializing at `r=σ`)
and reproduce OZ.9a as a corollary rather than a direct axiom — more powerful and closer to
the classical derivation, but needs an extra **unverified** step: eliminating `Q` to connect
this relation back to the `c_HS`/`radial3d_conv` form Gap A/B are stated in. Not attempted;
flagged as a follow-on (`todo_lean.md` Task OZ.9-RouteB).

**Status:** ✓ DONE (Route A) — `oz_core_closure` axiom (`PYOZ_GHS.lean`) + corollary
`oz_fourier_oz_eq_of_PY_core` (`OZFourierBridge.lean`), no sorry. Route B scoped, not started.

---

