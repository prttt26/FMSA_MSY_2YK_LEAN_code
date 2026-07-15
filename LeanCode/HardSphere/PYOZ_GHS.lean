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

## Uniqueness (OZ.10 — axiom)

For h bounded by ‖h‖_∞, the sup-norm bound on the linear operator is:

    ‖oz_linear_op[h](r)‖ ≤ (2π|rho|/r)·‖h‖_∞·∫0^sigma t·|c_HS(t)|·2rt dt
                          = 4π|rho|·‖h‖_∞·∫0^sigma t^2|c_HS(t)| dt

So `oz_linear_op` is contracting in sup-norm when `|rho| < (4π·∫0^sigma t^2|c_HS(t)| dt)⁻¹`.
For all physical `eta < 1`, the Fredholm alternative (outside current Mathlib) gives
existence and uniqueness for all non-resonant rho.

**2026 correction:** this used to be stated with the fixed point bundled into
`BoundedContinuousFunction ℝ ℝ`, i.e. continuous on *all* of ℝ including at `r = σ`. That
was wrong: `g0_HS_contact_value` correctly encodes the standard PY fact that hard-sphere
`g(r)` has a jump discontinuity at contact (`g0_HS(σ) = (1+η/2)/(1-η)² ≠ 0`, while
`g0_HS(r) = 0` for all `r < σ`), so no continuous-at-σ fixed point can exist — the old
statement and `g0_HS_contact_value` were directly contradictory (verified by deriving
`False` from the two). The regularity requirement is now `ContinuousOn h (Set.Ici sigma)`
only (continuity on the exterior `[σ,∞)`, where the integral-equation content lives); the
core branch `r < σ` is already pinned to the constant `-1` by `oz_operator`'s own
definition and needs no separate continuity assumption. The `∃! h : ℝ → ℝ` version (with
these two regularity conjuncts attached explicitly, rather than a bundled
`BoundedContinuousFunction` type) is kept — dropping regularity entirely would still admit
non-measurable pathological fixed points that the operator definition alone cannot exclude.

## Results

| Statement | Status | Reason |
|---|---|---|
| `oz_operator_core` | proved | `if_pos hr` from definition |
| `oz_fixed_pt_core` | proved | from `oz_operator_core` |
| `oz_fixed_pt_exterior` | proved | from `OzFixedPt` unfolding |
| `oz_fixed_pt_unique` | **axiom** | scoped to `ContinuousOn (Ici sigma)` + bounded (2026 fix) |
| `oz_h_core` | proved | from `oz_fixed_pt_core` |
| `oz_h_ghs_core` | proved | arithmetic from `oz_h_core` |
| `g0_HS_outer` | defined | concrete: `fun r => 1 + oz_h eta sigma rho r` |
| `g0_HS` | defined | piecewise: 0 for r < σ, `g0_HS_outer` for r ≥ σ |
| `g0_HS_core` | proved | `if_pos hr` from piecewise definition |
| `g0_HS_outer_is_oz_fp` | proved | `g0_HS_outer r − 1 = oz_h r`; follows from `oz_h_is_fp` |
| `g0_HS_outer_eq_oz_h` | proved | `rfl` from concrete definition |
| `oz_laplace_oz_eq` | **deleted 2026-07-15** | Laplace dead-end (used the false `radial_laplace_conv`); correct form is the sine-transform OZ.7 |
| `g0_HS_laplace_spec` | **deleted 2026-07-15** | only consumed `oz_laplace_oz_eq`; no live callers |
| `g0_HS_contact_value` | **theorem** (moved to `JumpAsymptotic.lean`) | PY contact value; now derived via BAXTER.8 + the `oz_h_exterior_regularity` axiom |

## Net improvement over pre-OZ.2 state

| Item | Before | After |
|---|---|---|
| `g0_HS_outer` | **sorry** | **concrete definition** (`1 + oz_h`) |
| `g0_HS` | sorry (via g0_HS_outer) | defined (piecewise, no sorry) |
| `g0_HS_core` | **axiom** | **proved theorem** |
| `g0_HS_outer_is_oz_fp` | axiom | **proved theorem** |
| `g0_HS_outer_eq_oz_h` | axiom | **proved theorem** (`rfl`) |
| `g0_HS_laplace_spec` | axiom (was in PYOZ.lean) | **deleted 2026-07-15** (Laplace dead-end) |
| `g0_HS_contact_value` | axiom (was in PYOZ.lean) | **theorem** in `JumpAsymptotic.lean` (BAXTER.8) |
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

/-- **Axiom (OZ.10): the OZ operator has at most one bounded fixed point that is continuous
on the exterior `[σ,∞)`.**

**2026 correction (read this first):** this axiom used to bundle the fixed point into
`BoundedContinuousFunction ℝ ℝ` — i.e. claim continuity on *all* of ℝ, including at `r = σ`.
That was actually **wrong**, not just imprecise: `g0_HS_contact_value` correctly states the
standard PY fact that hard-sphere `g(r)` has a jump discontinuity at contact
(`g0_HS(σ) = (1+η/2)/(1-η)² ≠ 0` for physical `η`, while `g0_HS(r) = 0` for every `r < σ`,
`g0_HS_core`), so continuity of `oz_h` at `σ` would force `g0_HS(σ) = 0` by the left limit —
directly contradicting `g0_HS_contact_value`. This was verified concretely: the two axioms
combined with `oz_h_core`/`g0_HS_outer_eq_oz_h`/the old `oz_h_continuous` type-check into a
complete proof of `False`. The fix: regularity is now `ContinuousOn h (Set.Ici sigma)` (the
exterior only — where the genuine integral-equation content lives) instead of global
continuity. The core branch `r < σ` needs no separate continuity hypothesis: `oz_operator`
pins it to the constant `-1` by definition (`oz_operator_core`), which is trivially
continuous on its own domain, jump at `σ` and all.

The linear operator `oz_linear_op` has sup-norm bound
`‖K‖_{op} ≤ 4π|rho|·∫0^sigma t^2|c_HS(t)| dt`, making `T` a contraction on
`BoundedContinuousFunction {x : ℝ // sigma ≤ x} ℝ` (exterior functions only — no gluing
needed inside the contraction argument itself, since `oz_linear_op` only ever reads exterior
values) for small enough `|rho|`; Banach's fixed-point theorem then gives existence and
uniqueness there, which packages into the `∃! h : ℝ → ℝ` shape below by gluing with the
forced core value `-1`. For all physical `eta < 1` uniqueness still holds — hard spheres have no
spinodal — but proving it beyond the dilute regime needs Wiener–Hopf machinery, **not** the
compact-operator Fredholm alternative (`K` is not compact); see the mid/high-density bullet below.

**2026 update — split by density regime, one piece now proved:**

- **Small `eta` (dilute, `eta < eta* ≈ 0.088`): proved**, as `oz_fixed_pt_unique_dilute` in
  `HardSphere/OzFixedPtDilute.lean` (a *separate* file, not this one — that file imports this
  one for `oz_forcing`/`oz_linear_op`/`OzFixedPt`, so the theorem can't live here too without
  an import cycle). Genuine theorem, no axiom, no `sorry`; its hypotheses restrict this axiom's
  `∃! h : ℝ → ℝ` statement by `heta_def : eta = π·ρ·σ³/6`, `heta_pos : 0 < eta`,
  `heta1 : eta < 1` (a necessary addition — `hsmall` alone doesn't force `eta < 1`, since the
  bracket below goes negative for `eta` past ≈2, and `c_HS_neg`/`c_HS_abs_integral` both need
  it; physically free since `eta` is a packing fraction), and
  `hsmall : 24·eta·(py_a0 eta/3+py_a1 eta/4+py_a3 eta/6) < 1`. Since `eta = π·ρ·σ³/6`, "small
  `|ρ|`" (fixed `σ`) is exactly "small `eta`"; with `c_HS` closed-form in `eta`, the
  contraction bound reduces to a concrete, σ-independent polynomial threshold in `eta` alone
  (numerically verified, then proved), via Mathlib's `ContractingWith`/Banach fixed-point
  theorem (`Mathlib/Topology/MetricSpace/Contracting.lean`) applied to
  `BoundedContinuousFunction {x : ℝ // sigma ≤ x} ℝ` (`CompleteSpace`+`Nonempty` instances and
  `dist f g = ⨆x,|f x-g x|` all already match the sup-norm argument sketched above). See
  `proof_notes_hard_sphere.md` (Task OZ.10-dilute) for the full six-piece proof writeup.

- **Middle/high density (`eta≈0.3–0.5`, up to `eta<1`): TRUE, and proving it in Lean is
  same-core as the BAXTER line — not the compact-operator Fredholm alternative.**

  *Why the naive "just use Fredholm" route fails.* Mathlib **does** have the compact-operator
  Fredholm alternative (`Mathlib/Analysis/Normed/Operator/Compact/FredholmAlternative.lean`,
  `hasEigenvalue_or_mem_resolventSet`) — an earlier version of this comment wrongly called it
  "thin or absent." But it **does not apply**: `oz_linear_op` (`K`) is **not compact**. `c_HS` is
  compactly supported on `[0,σ]`, so `K`'s kernel has finite width `2σ` — `K` is a half-line
  **band / Wiener–Hopf operator**, with large-`r` asymptotics `K[1](r) = (2π·ρ/r)·∫₀^σ
  t·c_HS(t)·2rt dt = 4π·ρ·∫₀^σ t²·c_HS(t) dt = −24η·bracket` (a constant): `K` tends to
  *multiplication by the constant `−24η·bracket`* as `r→∞`, and a nonzero multiplication operator
  is not compact. That constant is exactly the dilute Banach constant `T_ext_K`
  (`OzFixedPtDilute.lean`) — it is `K`'s **spectral radius** — so `24η·bracket < 1` (η ≲ 0.088) is
  the natural Banach/Neumann boundary (spectral radius < 1), not a loose estimate.

  *Why the statement is nonetheless TRUE for every `eta < 1`.* Hard spheres have **no phase
  transition**: PY `1 − ρ·ĉ(k) > 0` for all `k` and all `eta ∈ (0,1)` (compressibility
  `(1−η)⁴/(1+2η)² > 0`), so there is no spinodal / no resonance. `(I−K)` is invertible not because
  `‖K‖ < 1` (false past η≈0.088) but because `1 ∉ spectrum(K) = symbol range {ρ·ĉ(k)} ⊂ (−∞,1)`
  (the symbol is real, winding number 0). So existence+uniqueness holds unconditionally on
  `eta ∈ (0,1)`.

  *What the Lean proof actually needs — and does NOT need.* It does **not** need general
  Wiener–Hopf / Toeplitz operator theory: the symbol factorization
  `1 − ρ·Ĉ = (1 − ρ·Q̂(k))·(1 − ρ·Q̂(−k))` is already done concretely as the **Baxter
  factorization** (Task BAXTER.3, `baxter_wiener_hopf_factorization`; `BaxterRealSpace.lean` gives
  the real-space form). What remains is the explicit inverse/solution from that factorization —
  `(I−K) = (I−K₊)(I−K₋)`, each one-sided factor Volterra (spectral radius 0) hence invertible, so
  `(I−K)` is invertible ⇒ existence+uniqueness — which is exactly the `h_explicit` construction of
  Tasks BAXTER.12–13. So this axiom is **same-core as, and gated by, the BAXTER Wiener–Hopf line**;
  it is not an independent target, and the missing piece is a concrete construction, not
  Mathlib-absent machinery. (This supersedes the earlier speculative "`detQ`-zeros = spinodal"
  bridge: the clean statement is simply that hard spheres have no spinodal, the symbol never
  vanishes, and the Baxter factorization already supplies what is needed to invert `(I−K)`.)

**Scope:** stated as a plain `∃! h : ℝ → ℝ`, but with `ContinuousOn h (Set.Ici sigma)` and
boundedness attached as explicit conjuncts (rather than bundled into a
`BoundedContinuousFunction` type) — dropping regularity entirely would still admit
non-measurable pathological fixed points that the operator definition alone cannot exclude. -/
axiom oz_fixed_pt_unique (eta sigma rho : ℝ) (hsigma : 0 < sigma) :
    ∃! h : ℝ → ℝ, OzFixedPt eta sigma rho h ∧ ContinuousOn h (Set.Ici sigma) ∧
      ∃ C, ∀ r, |h r| ≤ C

/-! ### Canonical total correlation function -/

/-- The canonical OZ total correlation function `h0 = g0_HS - 1`.

Defined as the unique fixed point of `oz_operator` (for `sigma > 0`); extended
by the constant `-1` function for `sigma ≤ 0` (all physical values have `sigma > 0`). -/
noncomputable def oz_h (eta sigma rho : ℝ) : ℝ → ℝ :=
    if hsigma : 0 < sigma then
      Classical.choose (oz_fixed_pt_unique eta sigma rho hsigma).exists
    else fun _ => -1

private lemma oz_h_is_fp {eta sigma rho : ℝ} (hsigma : 0 < sigma) :
    OzFixedPt eta sigma rho (oz_h eta sigma rho) := by
    simp only [oz_h, dif_pos hsigma]
    exact (Classical.choose_spec (oz_fixed_pt_unique eta sigma rho hsigma).exists).1

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
for the "Route B" alternative (via Baxter's second relation), staged and tracked as Group
BAXTER's Task `BAXTER.2` (`proof_notes_baxter.md`) — scoped, not yet pursued to completion. -/
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

/-! ### Retired: Laplace-domain OZ characterization (`oz_laplace_oz_eq`, `g0_HS_laplace_spec`)

An axiom `oz_laplace_oz_eq` (`H̃₀·(1-ρĈ) = Ĉ`, the Laplace-domain OZ equation) and a theorem
`g0_HS_laplace_spec` (`∫ r·(g0_HS-1)·e^{-sr} = Ĉ·S₀`, proved from it via `oz_laplace_identity`)
used to live here. Both were **deleted** (2026-07-15). The only route to `oz_laplace_oz_eq` on the
real Laplace axis is a convolution factorization — exactly the axiom `radial_laplace_conv`, now
known **mathematically false** (the radial 3D convolution does not factor under the real Laplace
transform). So the Laplace-domain product form is not reliably provable and is most likely false
as stated in `s`; the correct, proved, live OZ-domain equation is the *sine*-transform
`oz_fourier_oz_eq_of_core_closure` / `oz_fourier_oz_eq_of_PY_core` (`OZFourierBridge.lean`, Tasks
OZ.7/OZ.9b). Neither deleted result had any live caller. The generic algebra identity
`oz_laplace_identity` (`PYOZ.lean`) that `g0_HS_laplace_spec` used is itself correct and is kept.
See `proof_notes_hard_sphere.md`. -/

/-! ### Exact PY contact value — now a theorem (Task OZ.3), see `JumpAsymptotic.lean`

`g0_HS_contact_value : g0_HS eta sigma rho sigma = (1 + eta/2) / (1 - eta)^2` used to be a bare
physical axiom here (the Percus–Yevick / Wertheim 1963 monodisperse hard-sphere contact value).
It is **no longer axiomatized**: Task BAXTER.8 (`g0_HS_contact_value_of_oz_h_regularity`,
`JumpAsymptotic.lean`) derives exactly this value from the jump-asymptotic lemma (BAXTER.6) + the
closed-form `Ĥ(k)` asymptotic (BAXTER.7) + the algebraic OZ identity (OZ.9b), conditional only on
`oz_h`'s exterior analytic regularity/decay/integrability. Those conditions are packaged as the
single named axiom `oz_h_exterior_regularity` (`JumpAsymptotic.lean`), from which the unconditional
theorem `g0_HS_contact_value` is proved. Net effect: the specific physical *number* is no longer
assumed — it follows from Fourier analysis; the only remaining assumption is that the OZ exterior
solution is as analytically well-behaved as physically expected. This file no longer declares the
name (it now lives, still in namespace `FMSA.HardSphere`, in `JumpAsymptotic.lean`). -/

end FMSA.HardSphere
