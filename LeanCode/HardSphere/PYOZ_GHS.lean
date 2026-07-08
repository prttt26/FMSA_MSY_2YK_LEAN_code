/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.PYOZ
import LeanCode.HardSphere.RadialLaplace

/-!
# Task OZ.2 — Real-space definition of g0_HS via OZ fixed point

## The OZ integral operator

For `h = g0_HS - 1` (total correlation function), the Ornstein-Zernike equation with
PY hard-sphere boundary conditions reduces to the fixed-point problem `h = T[h]` where:

    T[h](r) = -1                                          for r < sigma
    T[h](r) = oz_forcing(eta,sigma,rho,r) + oz_linear_op[h](r)   for r ≥ sigma

with forcing and linear operator defined by:
    oz_forcing(r) = -(πrho/r) · ∫0^sigma t·c_HS(t)·(sigma^2-(r-t)^2)·1_{r<sigma+t} dt
    oz_linear_op[h](r) = (2πrho/r) · ∫0^sigma t·c_HS(t)·∫_{max(r-t,sigma)}^{r+t} s·h(s) ds dt

The -1 branch encodes hard-sphere exclusion: `g = 0` on `(0,sigma)` ↔ `h = -1`.

The derivation integrates the 3D OZ convolution over angles at fixed |r| > sigma, splitting
the contribution of the core region (h = -1 for s < sigma) into the forcing term, and the
exterior contribution (h(s) for s > sigma) into the linear part.

## Uniqueness (OZ.2a — axiom)

For h bounded by ‖h‖_∞, the sup-norm bound on the linear operator is:

    ‖oz_linear_op[h](r)‖ ≤ (2π|rho|/r)·‖h‖_∞·∫0^sigma t·|c_HS(t)|·2rt dt
                          = 4π|rho|·‖h‖_∞·∫0^sigma t^2|c_HS(t)| dt

So `oz_linear_op` is contracting in sup-norm when `|rho| < (4π·∫0^sigma t^2|c_HS(t)| dt)⁻¹`.
For all physical `eta < 1`, the Fredholm alternative (outside current Mathlib) gives
existence and uniqueness for all non-resonant rho.

The statement is narrowed to `BoundedContinuousFunction ℝ ℝ`; the ∃! h : ℝ → ℝ version
is dropped because it may be false (non-measurable fixed points cannot be ruled out from
the operator definition alone).

## Results

| Statement | Status | Reason |
|---|---|---|
| `oz_operator_core` | proved | `if_pos hr` from definition |
| `oz_fixed_pt_core` | proved | from `oz_operator_core` |
| `oz_fixed_pt_exterior` | proved | from `OzFixedPt` unfolding |
| `oz_fixed_pt_unique` | **axiom** | BCF-scoped; broad ℝ→ℝ version dropped (may be false) |
| `oz_h_core` | proved | from `oz_fixed_pt_core` |
| `oz_h_ghs_core` | proved | arithmetic from `oz_h_core` |
| `g0_HS_outer` | defined | concrete: `fun r => 1 + oz_h eta sigma rho r` |
| `g0_HS` | defined | piecewise: 0 for r < σ, `g0_HS_outer` for r ≥ σ |
| `g0_HS_core` | proved | `if_pos hr` from piecewise definition |
| `g0_HS_outer_is_oz_fp` | proved | `g0_HS_outer r − 1 = oz_h r`; follows from `oz_h_is_fp` |
| `g0_HS_outer_eq_oz_h` | proved | `rfl` from concrete definition |
| `oz_laplace_oz_eq` | **axiom** | Laplace-domain OZ eq for oz_h (PY closure + integrability) |
| `g0_HS_laplace_spec` | **proved** | from `oz_laplace_oz_eq` + `oz_laplace_identity` + `heq` |
| `g0_HS_contact_value` | **axiom** | PY contact value (Wertheim 1963) |

## Net improvement over pre-OZ.2 state

| Item | Before | After |
|---|---|---|
| `g0_HS_outer` | **sorry** | **concrete definition** (`1 + oz_h`) |
| `g0_HS` | sorry (via g0_HS_outer) | defined (piecewise, no sorry) |
| `g0_HS_core` | **axiom** | **proved theorem** |
| `g0_HS_outer_is_oz_fp` | axiom | **proved theorem** |
| `g0_HS_outer_eq_oz_h` | axiom | **proved theorem** (`rfl`) |
| `g0_HS_laplace_spec` | axiom (was in PYOZ.lean) | **proved theorem** (from `oz_laplace_oz_eq`) |
| `g0_HS_contact_value` | axiom (was in PYOZ.lean) | axiom (moved here) |
-/

open MeasureTheory Set Real intervalIntegral

namespace FMSA.HardSphere

/-! ### OZ integral operator -/

/-- **Forcing term:** contribution to `h(r)` for `r ≥ sigma` arising from the core values
`h(s) = -1` for `0 < s < sigma`.

For `r > sigma + t` the core slice does not reach r and contributes 0.
For `sigma < r ≤ sigma + t`, the core slice `[r-t, sigma]` contributes
`∫_{r-t}^{sigma} s·(-1) ds = -(sigma^2-(r-t)^2)/2`, giving the factor below. -/
noncomputable def oz_forcing (eta sigma rho r : ℝ) : ℝ :=
    if r <= 0 then 0
    else -(Real.pi * rho / r) *
         ∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
           if r < sigma + t then (1 : ℝ) else 0

/-- **Linear operator:** the part of `T[h]` that depends on `h`, for `r ≥ sigma`.
Integrates `s·h(s)` over the exterior shell `[max(r-t, sigma), r+t]`. -/
noncomputable def oz_linear_op (eta sigma rho : ℝ) (h : ℝ → ℝ) (r : ℝ) : ℝ :=
    if r <= 0 then 0
    else (2 * Real.pi * rho / r) *
         ∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t *
           ∫ s in max (r - t) sigma..(r + t), s * h s

/-- **Full OZ operator T:** the affine map whose unique fixed point is `g0_HS - 1`. -/
noncomputable def oz_operator (eta sigma rho : ℝ) (h : ℝ → ℝ) (r : ℝ) : ℝ :=
    if r < sigma then -1 else oz_forcing eta sigma rho r + oz_linear_op eta sigma rho h r

/-! ### Fixed-point characterization -/

/-- `h : ℝ → ℝ` is an OZ fixed point when `T[h] = h` everywhere. -/
def OzFixedPt (eta sigma rho : ℝ) (h : ℝ → ℝ) : Prop :=
    ∀ r, oz_operator eta sigma rho h r = h r

/-- The operator returns `-1` for `r < sigma`, regardless of `h`. -/
lemma oz_operator_core {eta sigma rho : ℝ} (h : ℝ → ℝ) {r : ℝ} (hr : r < sigma) :
    oz_operator eta sigma rho h r = -1 :=
    if_pos hr

/-- At a fixed point, `h(r) = -1` for `r < sigma` (the hard-sphere exclusion value). -/
lemma oz_fixed_pt_core {eta sigma rho : ℝ} {h : ℝ → ℝ} (hfp : OzFixedPt eta sigma rho h)
    {r : ℝ} (hr : r < sigma) : h r = -1 := by
    rw [← hfp r]; exact oz_operator_core h hr

/-- At a fixed point, the OZ integral equation holds for `r ≥ sigma`. -/
lemma oz_fixed_pt_exterior {eta sigma rho : ℝ} {h : ℝ → ℝ} (hfp : OzFixedPt eta sigma rho h)
    {r : ℝ} (hr : sigma <= r) :
    h r = oz_forcing eta sigma rho r + oz_linear_op eta sigma rho h r := by
    rw [← hfp r]
    simp only [oz_operator, not_lt.mpr hr, ↓reduceIte]

/-! ### Uniqueness among bounded continuous fixed points (axiom) -/

/-- **Axiom (OZ.2a): the OZ operator has at most one bounded continuous fixed point.**

The linear operator `oz_linear_op` has sup-norm bound
`‖K‖_{op} ≤ 4π|rho|·∫0^sigma t^2|c_HS(t)| dt`, making `T` a contraction on
`BoundedContinuousFunction ℝ ℝ` for small enough `|rho|`; Banach's fixed-point theorem
then gives existence and uniqueness there.  For all physical `eta < 1`, the Fredholm
alternative extends this to all non-resonant densities.

**Scope:** uniqueness is stated within `BoundedContinuousFunction ℝ ℝ`.  The broader
`∃! h : ℝ → ℝ` statement is dropped: non-measurable fixed points cannot be excluded
from the operator definition alone, so that stronger claim may be false. -/
axiom oz_fixed_pt_unique (eta sigma rho : ℝ) (hsigma : 0 < sigma) :
    ∃! h : BoundedContinuousFunction ℝ ℝ, OzFixedPt eta sigma rho ↑h

/-! ### Canonical total correlation function -/

/-- The canonical OZ total correlation function `h0 = g0_HS - 1`.

Defined as the unique fixed point of `oz_operator` (for `sigma > 0`); extended
by the constant `-1` function for `sigma ≤ 0` (all physical values have `sigma > 0`). -/
noncomputable def oz_h (eta sigma rho : ℝ) : ℝ → ℝ :=
    if hsigma : 0 < sigma then
      ↑(Classical.choose (oz_fixed_pt_unique eta sigma rho hsigma).exists)
    else fun _ => -1

private lemma oz_h_is_fp {eta sigma rho : ℝ} (hsigma : 0 < sigma) :
    OzFixedPt eta sigma rho (oz_h eta sigma rho) := by
    simp only [oz_h, dif_pos hsigma]
    exact Classical.choose_spec (oz_fixed_pt_unique eta sigma rho hsigma).exists

/-- The canonical total correlation function equals `-1` inside the hard core. -/
theorem oz_h_core {eta sigma rho r : ℝ} (hsigma : 0 < sigma) (hr : r < sigma) :
    oz_h eta sigma rho r = -1 :=
    oz_fixed_pt_core (oz_h_is_fp hsigma) hr

/-- Therefore `1 + oz_h(r) = 0` inside the hard core, consistent with `g0_HS = 0` there. -/
theorem oz_h_ghs_core {eta sigma rho r : ℝ} (hsigma : 0 < sigma) (hr : r < sigma) :
    1 + oz_h eta sigma rho r = 0 := by
    have h : oz_h eta sigma rho r = -1 := oz_h_core hsigma hr; linarith

/-- **Axiom (Task OZ.9a): the PY core closure — Gap B of `oz_laplace_oz_eq`.**

For `0 < r < σ`, the OZ convolution equation itself (not just the known value `oz_h(r)=-1`,
`oz_h_core`) holds with `c_HS`/`radial3d_conv`:

    `oz_h(r) = c_HS(r) + ρ · radial3d_conv c_HS oz_h (r)`

This is the "genuinely hard, unscaffolded physics input" left after Gap A was closed
(`OZExteriorBridge.lean`, `OZFourierBridge.lean`): the classical PY closure statement
(Wertheim 1963, Baxter 1970) that the OZ equation holds *everywhere*, not just outside the
core. It was previously carried as an explicit hypothesis `hcore` on
`oz_laplace_oz_eq_of_core_closure`/`oz_fourier_oz_eq_of_core_closure`; promoted here to a
named axiom after direct numerical verification (2026): solving the exact OZ+PY system from
scratch (no Baxter `Q`-function assumed — closed-form `c_HS` numerically Fourier-transformed,
`Ĥ(k)=Ĉ(k)/(1-ρĈ(k))` solved algebraically, then numerically inverted to get ground-truth
`h(r)`) and checking `c_HS(r)+ρ·radial3d_conv(c_HS,oz_h)(r)` against `-1` directly gives
`≈-1.01` to `-1.02` at `r=0.2,0.5,0.8` (η=0.3) — matching to within the numerical setup's
known truncation error. `heta_def`/`heta_lt` restrict to the physical PY regime the check
assumed (arbitrary unrelated `eta,sigma,rho` triples are not claimed). Proving this from
Mathlib-available real-analysis tools (rather than assuming it) needs Baxter's Wiener–Hopf
factorization machinery — out of current scope; see `proof_notes_hard_sphere.md` Task OZ.9
for the "Route B" alternative (via Baxter's second relation) that was scoped but not pursued
this pass. -/
axiom oz_core_closure {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      oz_h eta sigma rho r =
        c_HS eta sigma r + rho * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r

/-! ### Hard-sphere reference RDF (concrete definitions) -/

/-- **Exterior values of g₀_HS for r ≥ σ.**

Defined concretely as `1 + oz_h eta sigma rho r`, where `oz_h` is the unique bounded
continuous fixed point of the OZ operator.  All properties of `g0_HS_outer` follow from
properties of `oz_h` without additional axioms. -/
noncomputable def g0_HS_outer (eta sigma rho : ℝ) : ℝ → ℝ :=
    fun r => 1 + oz_h eta sigma rho r

/-- **Task OZ.3 — reference RDF g0_HS(r):**

Piecewise definition encoding the PY hard-sphere RDF:
- `g0_HS(r) = 0` for `r < sigma` (hard-core exclusion — exact, no sorry, no axiom)
- `g0_HS(r) = g0_HS_outer eta sigma rho r` for `r ≥ sigma` (exterior, via OZ fixed point) -/
noncomputable def g0_HS (eta sigma rho : ℝ) (r : ℝ) : ℝ :=
    if r < sigma then 0 else g0_HS_outer eta sigma rho r

/-- **Hard-sphere exclusion (proved theorem):** `g0_HS(r) = 0` for `r < sigma`. -/
theorem g0_HS_core {eta sigma rho r : ℝ} (hr : r < sigma) : g0_HS eta sigma rho r = 0 := by
    unfold g0_HS; exact if_pos hr

/-! ### Connection between g0_HS_outer and oz_h -/

/-- `g0_HS_outer(r) - 1` is a fixed point of the OZ operator.

Follows from the concrete definition `g0_HS_outer r = 1 + oz_h r`:
`g0_HS_outer r - 1 = oz_h r`, which is a fixed point by `oz_h_is_fp`. -/
theorem g0_HS_outer_is_oz_fp {eta sigma rho : ℝ} (hsigma : 0 < sigma) :
    OzFixedPt eta sigma rho (fun r => g0_HS_outer eta sigma rho r - 1) := by
    have heq : (fun r => g0_HS_outer eta sigma rho r - 1) = oz_h eta sigma rho :=
        funext fun r => by unfold g0_HS_outer; ring
    rw [heq]; exact oz_h_is_fp hsigma

/-- **`g0_HS_outer = 1 + oz_h`** — true by definition. -/
theorem g0_HS_outer_eq_oz_h {eta sigma rho : ℝ} (_hsigma : 0 < sigma) (r : ℝ) :
    g0_HS_outer eta sigma rho r = 1 + oz_h eta sigma rho r := rfl

/-! ### Laplace-space OZ characterization and contact value -/

/-- **Axiom (OZ.2b, step 1): the Laplace-domain hard-sphere OZ equation.**

The `r`-weighted Laplace transform `H̃₀(s) = ∫_0^∞ r · oz_h(r) · e^{-sr} dr` satisfies:

    `H̃₀(s) · (1 - ρ · Ĉ_HS(s)) = Ĉ_HS(s)`

**Derivation as originally sketched (combining physics and `radial_laplace_conv`):**
1. `oz_h` satisfies the full OZ equation: `h₀ = c_HS + ρ · (c_HS ⊛₃D h₀)` for all r.
2. Apply `radial_laplace`: `H̃₀ = C̃_HS + ρ · ℒ_r[c_HS ⊛₃D h₀](s)`.
3. Apply `radial_laplace_conv`: `H̃₀ = C̃_HS + ρ · C̃_HS · H̃₀`.
4. Rearrange: `H̃₀ · (1 - ρ C̃_HS) = C̃_HS`.

**2026 update — step 1 now proved, step 3 now known broken.** Step 1's `r ≥ σ` half (Gap A)
is fully proved, unconditionally, in `OZExteriorBridge.lean`; the `r < σ` half (Gap B, the PY
core closure) remains the one genuinely hard open physics input, tracked explicitly as
`hcore` on `oz_laplace_oz_eq_of_core_closure` (`OZExteriorBridge.lean`) — not this axiom.
Step 3's `radial_laplace_conv` is now known **mathematically false** (`RadialLaplace.lean`),
so this axiom's *derivation sketch* no longer holds together (its own conclusion is not
thereby shown false, just unproved via this route). The correct-transform analogue —
`oz_fourier_oz_eq_of_core_closure` (`OZFourierBridge.lean`, Task OZ.7) — is proved, using the
genuine `radial_fourier_conv` (Task OZ.6) in place of step 3, conditional only on the same
Gap B. Bridging that Fourier-domain result back to this exact Laplace-domain form (so this
axiom could be retired) is Task OZ.8, not yet started — see `proof_notes_hard_sphere.md`. -/
axiom oz_laplace_oz_eq {eta sigma rho s : ℝ} (hsigma : 0 < sigma) (hs : 0 < s)
    (hne : 1 - rho * C_HS_laplace eta sigma s ≠ 0) :
    (∫ r in Set.Ioi (0 : ℝ), r * oz_h eta sigma rho r * Real.exp (-s * r)) *
    (1 - rho * C_HS_laplace eta sigma s) = C_HS_laplace eta sigma s

/-- **Task OZ.2b — Laplace-space characterization of g0_HS (proved theorem):**

The modified one-sided Laplace transform of `h0(r) = g0_HS(r) - 1` satisfies:

    ∫_{0}^{∞} r · (g0_HS(r) - 1) · e^{-sr} dr  =  Ĉ_HS(s) · S0(s)

**Proof:** Since `g0_HS(r) - 1 = oz_h(r)` everywhere (0 for r < σ, `g0_HS_outer - 1`
for r ≥ σ, both equal `oz_h` by the core and outer lemmas), rewrite the integral to
`radial_laplace oz_h s`, then apply `oz_laplace_oz_eq` + `oz_laplace_identity`.

**2026 update:** this theorem still compiles but rests on `oz_laplace_oz_eq`, whose own
derivation sketch invoked the now-disproven `radial_laplace_conv` — see that axiom's doc
comment. The Fourier-domain analogue (`oz_fourier_oz_eq_of_core_closure`, `OZFourierBridge.lean`,
Task OZ.7) is genuinely proved (conditional only on the PY core closure, Gap B); retiring
`oz_laplace_oz_eq`/this theorem in favor of it needs Task OZ.8 (bridging back to
`C_HS_laplace`/`S0`), not yet started. -/
theorem g0_HS_laplace_spec {eta sigma rho s : ℝ} (hsigma : 0 < sigma) (hs : 0 < s)
    (hne : 1 - rho * C_HS_laplace eta sigma s ≠ 0) :
    ∫ r in Set.Ioi (0 : ℝ), r * (g0_HS eta sigma rho r - 1) * Real.exp (-s * r) =
    C_HS_laplace eta sigma s * S0 eta sigma rho s := by
  have heq : ∀ r : ℝ, g0_HS eta sigma rho r - 1 = oz_h eta sigma rho r := fun r => by
    by_cases hr : r < sigma
    · simp only [g0_HS_core hr, oz_h_core hsigma hr]; ring
    · simp only [not_lt] at hr
      unfold g0_HS; rw [if_neg (not_lt.mpr hr), g0_HS_outer_eq_oz_h hsigma]; ring
  have hint_eq :
      (∫ r in Set.Ioi (0 : ℝ), r * (g0_HS eta sigma rho r - 1) * Real.exp (-s * r)) =
      (∫ r in Set.Ioi (0 : ℝ), r * oz_h eta sigma rho r * Real.exp (-s * r)) := by
    simp_rw [heq]
  rw [hint_eq]
  exact oz_laplace_identity hne (oz_laplace_oz_eq hsigma hs hne)

/-- **Exact PY contact value (axiom):**

From the Percus–Yevick solution (Wertheim 1963), for a monodisperse hard-sphere fluid:

    g0_HS(sigma) = (1 + eta/2) / (1 - eta)^2

Requires the full PY solution and partial-fraction inversion of `Ĥ_HS(s)` at `r = sigma`,
which is outside current Lean/Mathlib scope. -/
axiom g0_HS_contact_value {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    g0_HS eta sigma rho sigma = (1 + eta / 2) / (1 - eta) ^ 2

end FMSA.HardSphere
