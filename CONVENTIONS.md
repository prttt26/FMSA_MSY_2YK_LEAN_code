# Coding Conventions

## Directory layering — a strict one-way import order

Source directories under `LeanCode/` are ordered by how *specific* their physics is, and imports
may only ever point **leftward**:

```
Analysis/  ←  HardSphere/  ←  HSMixture/  ←  YukawaDCF/
 general      single-        N-component     Yukawa-tail
 math         component HS    HS mixture     coupled
```

*(`FMSAPoly/`, `FreeEnergy/` and the other application directories sit to the right of all four.)*

**Enforce mechanically** — each of these must print nothing:

```
grep -rn "^import LeanCode.YukawaDCF" LeanCode/HSMixture/ LeanCode/HardSphere/ LeanCode/Analysis/
grep -rn "^import LeanCode.HSMixture"  LeanCode/HardSphere/ LeanCode/Analysis/
grep -rn "^import LeanCode.HardSphere" LeanCode/Analysis/
```

**Why it matters.** `Analysis/` is the home of Group MA — the general-purpose, project-independent
Mathlib vocabulary. Its value is that it is *citable without buying into the physics*; a single
back-edge would destroy that. The same reasoning cascades: `HSMixture/` results must hold for a hard
sphere mixture with no Yukawa tail attached.

**Classifying a file — do not trust its name.** Established traps, all real:

* Grep `Fin [A-Za-z]+ → (ℝ|ℂ)`, never `Fin n` alone. Species binders are `N` by the rule below, but
  the narrow pattern once misfiled the entire FMT cluster as single-component, and the general
  pattern keeps working if a stray binder slips in.
* ⚠ **`Fin _ → ℝ` alone does NOT mean "species"** — it is equally the *Yukawa tail* index
  (`A z : Fin n → ℝ` = amplitudes and decay rates, in `FMSAPoly/`, `FreeEnergy/`,
  `ContactMatching`, `YukawaInnerCore`, …). Decide by **what is indexed**: `sigma`/`rho`/`d`
  (diameters, densities) ⇒ species; `A`/`z`/`K`/`Amp` ⇒ tails.
* A `Mixture*` prefix proves nothing. `MixtureHSCounting` is abstract complex analysis
  (`f : ℂ → ℂ`), `MixtureLaurent` is generic Taylor calculus — both mostly belong in `Analysis/`.
  Conversely `SingleCompReduction` is genuinely scalar despite having lived in `YukawaDCF/`.
* Unlike radii `Ri ≠ Rj` is a **mixture-only** concept; a file assuming it is not scalar.
* The `Mix N M` structure is **not** pure hard sphere — its `zp`/`cb` fields carry Yukawa pole
  residues, so every `Mix`-based file belongs in `YukawaDCF/`. The pure-HS parameter pack is
  `MixParams` (`sig0`/`sig1`/`rr`/`Qp`/`Qpp` only).

A file that straddles the boundary should be **split**, not filed by majority vote: the general half
moves left (precedents: `BanachPoleFamily`, `radialShell_bounded_injective`, `MatrixIdentity`).

## Index binders: `N` is the number of species

For a multicomponent (mixture) statement, the number of species is bound as **`N`**, and the
species index type is `Fin N`:

```lean
noncomputable def etaMix {N : ℕ} (rho sigma : Fin N → ℝ) : ℝ := …
theorem pyhs_mixture_no_spinodal {N : ℕ} {sigma rho : Fin N → ℝ} … 
```

Normalised across the library on 2026-07-19 (`n`/`M` → `N` in `MatrixQ0`, `Q0Complex`,
`Q0DetRankTwo`, `Q0DetLimit`, `MixtureNoSpinodal`, `MixtureHSZeros`, `MixtureRealSpace`,
`SpectralAmplitude`, `CHSKinkWB`; `WhiteBearFMT`, `BijReduction` and `Mix` already conformed).

**The other two letters are reserved, and the distinction is load-bearing:**

| binder | counts | example |
|--------|--------|---------|
| `N` | **species** | `sigma rho : Fin N → ℝ`, `Mix N M`'s first index |
| `M` | **poles** — Yukawa poles per residue expansion | `Mix N M`'s `zp cb : Fin N → Fin N → Fin M → ℝ` |
| `n` | anything else, unindexed: a pole/branch number, an iteration count, a chord index, a Taylor order | `baxterPhi … (n : ℕ)`, `volterra_integral_sub_pow … (n : ℕ)` |

**Why this matters, concretely.** `CHSKinkWB` once bound species as `M` — the same letter that means
*pole count* in `Mix N M`. Nothing broke and nothing could: binder names are implicit, so the type
checker is indifferent and a reader is the only thing that notices. Keep `M` for poles.

⚠ **A bare `(n : ℕ)` is usually correct and must not be renamed** — most `n`s in the library count
poles, iterations or Taylor orders, not species. Rename only a binder that actually indexes
`sigma`/`rho`/`d`.

⚠ **`lake build` does not validate this rename.** Renaming a bound variable is alpha-equivalent, so
a *local* `n` wrongly swept into `N` still compiles. After any such rename, grep the touched files
for `∀ N`, `intro N`, `fun N`, `induction N` — a species count is never introduced that way.

## Identifier naming: content-descriptive, never group- or task-coded

Lean **identifier names** (theorems, lemmas, `def`s, namespaces) and **file names** must describe
the mathematical *content*, never the organizational group letter or task number.  Do **not** prefix
a theorem with its task ID (`b5_degree_bound`, `mml3_…`) or name a file after a group (`B5MixturePoly.lean`,
`PathB`).  Name by what the object *is* (`q0_entry_degree_bound`, `MixturePolyCoeffs.lean`).

**Why:** group membership and task IDs live only in the docs (`proof_notes_*.md`, `todo_lean.md`).
Code named by content stays correct when a task is re-grouped, a group is renamed, or a group is
split across files — none of which should force a Lean rename.  (Legacy `b<N>_`/`FMSA.PathB` names
from the old flat numbering were cleaned up on 2026-07-17: Group B → Group GAP, files
`B4OriginBC`/`B5MixturePoly` → `InnerOriginBC`/`MixturePolyCoeffs`, theorems `b4_*`–`b10_*` →
content names.)  Docstrings may cite the task ID (`**Task GAP.5**`) for cross-reference; the
*identifier* may not.

## Identifier naming: ASCII-only

All Lean **identifier names** (variables, hypotheses, theorem names, local defs) must use
ASCII characters only.  Do not introduce new Unicode identifier names.

### Greek letter mapping

| Unicode | ASCII |
|---------|-------|
| `α` | `alpha` |
| `β` | `beta` |
| `γ` | `gamma` |
| `δ` | `delta` |
| `ε` | `epsilon` |
| `η` | `eta` |
| `θ` | `theta` |
| `λ` | `lam` or `lambda` |
| `μ` | `mu` |
| `ξ` | `xi` |
| `π` | `pi` |
| `ρ` | `rho` |
| `σ` | `sigma` |
| `φ` | `phi` |
| `χ` | `chi` |
| `ω` | `omega` |
| `ℓ` | `ell` |

### Subscript / superscript in identifier names

Use plain letter or digit suffixes, no Unicode sub/superscripts:

- `x₀` → `x0`, `x₁` → `x1`, `xₘ` → `xm`, `xᵢ` → `xi`
- Never use `ᶻ`, `ⱼ`, `ₖ`, `ᵃ`, `ᵉ`, `ᵐ`, `ᵛ`, etc. in identifiers

### Exceptions — Mathlib named arguments

These names belong to Mathlib's API and **cannot** be renamed:

- `(α := ℝ)` — type universe argument in `atTop`, etc.
- `(μ := volume)` — measure argument
- `(𝕜 := ℝ)` — field argument in `hasDerivAt_pow`, etc.
- `inv_mul_cancel₀` — Mathlib lemma name (subscript `₀` is part of the name)

---

## Comparison operators in code

Use ASCII comparison operators in proof terms and tactic goals:

| Unicode | ASCII (use this) |
|---------|-----------------|
| `≤` | `<=` |
| `≥` | `>=` |
| `≠` | keep as `≠` (no ASCII alternative for `Prop`-level `Ne`) |

Note: `!=` in Lean 4 means `BEq.bne` (Bool-valued), not `Ne` (Prop-valued).  Do not use
`!=` as a substitute for `≠`.

---

## Set complement in code

Use `Set.compl` instead of the `ᶜ` postfix notation (which is too small to read reliably):

```lean
-- Instead of:   nhdsWithin 0 {0}ᶜ
-- Write:        nhdsWithin 0 (Set.compl {0})
```

---

## Lean / Mathlib syntax and type names (keep as Unicode)

The following Unicode symbols are **Lean 4 / Mathlib built-in notation** and must remain as-is
in code:

| Symbol | Meaning |
|--------|---------|
| `ℝ`, `ℂ`, `ℕ` | type names (Real, Complex, Nat) |
| `𝓝` | neighborhood filter |
| `𝕜` | field typeclass variable |
| `→`, `←`, `↑`, `↔` | function type, rw direction, coercion, iff |
| `∀`, `∃` | quantifiers |
| `∈`, `⊆`, `∪`, `∧`, `¬` | set/logic connectives |
| `∑`, `∫` | sum and integral notation |
| `⟨⟩` | anonymous constructor |
| `•` | scalar multiplication |
| `⁻¹` | inverse (group / matrix) |
| `‖·‖` | norm |

---

## Docstrings and comments

- Replace `−` (U+2212 MINUS SIGN) with `-` (ASCII hyphen-minus).
- For subscripts, use `_` prefix when needed for clarity: `sigma_j`, `A_k`, `z_k`.
- For superscripts, use `^` prefix: `e^z`, `e^(-z)`, `x^2`.
- Math variable names with hats (`Ĝ`, `Ĉ`, `Â`) are acceptable in docstrings as they
  denote physics objects (Fourier-space propagators, DCF).
- Greek letters (`π`, `φ`, `λ`, etc.) are acceptable in docstrings as mathematical notation.
- `≤`, `≥` remain as Unicode in docstrings (math notation); they are replaced by `<=`, `>=`
  only in actual code.
