# Coding Conventions

## Directory layering — a strict one-way import order

Source directories under `LeanCode/` are ordered by how *specific* their physics is, and imports
may only ever point **leftward** (restructured 2026-08-06):

```
Analysis/   ─┐  general math (Group MA)          two BASES — import nothing project-local
FMSAPoly/   ─┘  FMSA polynomial inner core
HardSphere/     ← Analysis                       single-component HS (the PY-HS solution)
HSMixture/      ← Analysis, HardSphere           N-component PURE hard-sphere mixture
YukawaOZ/       ← Analysis, HardSphere, HSMixture, FMSAPoly    single-component Yukawa OZ (c AND h)
YukawaOZMix/    ← … + YukawaOZ                   N-component Yukawa mixture OZ
FreeEnergy/     ← FMSAPoly, YukawaOZ*            application sink (free-energy integrals)
Closures/       ← Analysis, HardSphere, YukawaOZ*    non-FMSA closures (PY/PYE/HNCB/MSA), sink
```

* **`Analysis/` and `FMSAPoly/` are both bases** — each imports nothing from another `LeanCode/`
  directory. (`FMSAPoly/` is FMSA-specific but foundational: it is imported *by* `YukawaOZ*/` and
  `FreeEnergy/`, never the reverse — it is **not** "to the right of everything".)
* **`YukawaDCF/` was split** into `YukawaOZ/` (single-component + generic-scalar base) and
  `YukawaOZMix/` (N-component mixture), and renamed off "DCF" (the folder carries RDF/`Ĥ₁`/`g`/`h`
  and closures too). The single→mixture cut is one-way: `YukawaOZMix/` builds on `YukawaOZ/`.
* **Policy: pure hard-sphere mixture content lives in `HSMixture/`** — a file with no Yukawa tail
  (species diameters/densities `Fin N → ℝ`, the Baxter `Q̂₀` matrix, its determinant/shell moments)
  belongs there even if only Yukawa code consumes it. (This is why `AppendixWDet`/`ArcAmplitudeBound`
  moved down from the Yukawa layer.)

**Enforce mechanically** — each of these must print nothing (`YukawaOZ` matches `YukawaOZMix` too):

```
grep -rn "^import LeanCode.\(HardSphere\|HSMixture\|YukawaOZ\|FreeEnergy\|Closures\)" LeanCode/Analysis/ LeanCode/FMSAPoly/
grep -rn "^import LeanCode.\(HSMixture\|YukawaOZ\|FreeEnergy\|Closures\)" LeanCode/HardSphere/
grep -rn "^import LeanCode.\(YukawaOZ\|FreeEnergy\|Closures\)" LeanCode/HSMixture/
grep -rn "^import LeanCode.YukawaOZMix" LeanCode/YukawaOZ/
```

**Why it matters.** `Analysis/` is the home of Group MA — the general-purpose, project-independent
Mathlib vocabulary. Its value is that it is *citable without buying into the physics*; a single
back-edge would destroy that. The same reasoning cascades: `HSMixture/` results must hold for a hard
sphere mixture with no Yukawa tail attached.

**⚠ Run the greps — the invariant has been broken twice and re-repaired.** (1) 2026-07-31:
`HSMixture/MixtureRDFUniqueness.lean` → `YukawaOZMix/MixtureRDFStructureFactor.lean` (commit `c8efdc4`).
(2) 2026-08-06: two `HSMixture/ → YukawaDCF/` back-edges (`Q0ComplexDetMatch → AppendixWDet`,
`MixtureRowSum → WHSupports`, commit `1dfae2a`), fixed in the restructure by moving `AppendixWDet`/
`ArcAmplitudeBound` **down** to `HSMixture/` (pure-HS content) and `MixtureRowSum` **up** to the
Yukawa layer (`Mix`-based). All greps now print nothing again.

The instructive part is **how small the offending dependency was**: of the 26 declarations in that
`YukawaDCF/` file, exactly **one** was used, and it was
`T₀ = Qp·Qmᵀ ⇒ det T₀ = det Qp · det Qm` — two Mathlib rewrites, no Baxter, Yukawa or mixture content
at all. The generic core is now `Analysis/MatrixIdentity.det_mul_transpose` and both sides cite it.

**The lesson for the next back-edge:** a violation usually does *not* mean the importing file is
misfiled. Check first *which names* it actually uses (`for d in <decls of the target>; do grep -q
"\b$d\b" <importer>; done`). If the answer is a handful of generic lemmas, the fix is to push those
**down** to `Analysis/`, not to move the whole file **up** — moving the file up would have dragged an
`HSMixture/` result into `YukawaDCF/` and quietly asserted that matrix OZ★ uniqueness needs a Yukawa
tail, which is false. Verify afterwards that `#print axioms` on the affected capstones is unchanged
(here `matOzStar_unique` still carries exactly `FMSA.matRadialShell_bounded_injective`).

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
  residues, so every `Mix`-based file belongs in the Yukawa **mixture** layer `YukawaOZMix/`. The pure-HS parameter pack is
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
the mathematical *content*, never a task number or a **content-unrelated group tag**.  Do **not** put
a task ID in a name (`b5_degree_bound`, `mml3_…`, `msaexact6_hcore`, `matMSAemix1_…`) or an opaque
group acronym / mash (`FMSA.MRS`, `…BRK`, `MSAEMix`, `matEMIX…`).  Name by what the object *is*
(`q0_entry_degree_bound`, `MixturePolyCoeffs.lean`).  A token that also happens to be a group's name is
fine **iff it describes the content** — keep `MSA` (mean-spherical), `exact`, `mixture`, `Baxter`,
`pole`, `Yukawa`, `HS`; drop the bookkeeping wrapper (`MSAEXACT`→`ExactMSA`, `MSAEMIX`→`MSAMixture`,
`BRK`→`Breakpoint`, `MRS`→`MixtureBaxterCore`).

**Why:** group membership and task IDs live only in the docs (`proof_notes_*.md`, `todo_lean.md`).
Code named by content stays correct when a task is re-grouped, a group is renamed, or a group is
split across files — none of which should force a Lean rename.  (Legacy `b<N>_`/`FMSA.PathB` names
from the old flat numbering were cleaned up on 2026-07-17: Group B → Group GAP, files
`B4OriginBC`/`B5MixturePoly` → `InnerOriginBC`/`MixturePolyCoeffs`, theorems `b4_*`–`b10_*` →
content names.  A second pass on 2026-08-25 stripped the residual MSA-layer tags: `msaexact*` + task#s
→ `exactMSA*`, `MSAEMix*`/`matMSAemix1`/`matEMIX…` → `MSAMixture*`/`matMSAmixture`/`matMixtureFactorization`,
namespaces `FMSA.MSAExact.BRK`→`FMSA.ExactMSA.Breakpoint` and `FMSA.MRS`→`FMSA.MixtureBaxterCore`, with 13
files renamed to match — pure rename, `lake build LeanCode` green and unchanged.)  Docstrings may cite the
task ID (`**Task GAP.5**`, `MSAEMIX.4`) for cross-reference; the *identifier* may not.

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

### Physics-identifier normalization (2026-08-17) — same quantity, one ASCII name

The physics identifiers were normalized to ASCII in **code** (docstrings keep Greek math
notation): `σ→sigma`, `ρ→rho`, `η→eta`, `ξ→xi`, `χ→chi` (incl. the `FMSA.HSMix` fields
`σ/ρ/hσ` → `sigma/rho/hsigma`). This removed a "same quantity, two names" split (diameter was
both `sigma` and `σ`; packing fraction both `eta` and `η`).

**⚠ The scalar-vs-function collision.** In the equal-diameter mixture theorems the *scalar*
common diameter and the *per-species* diameter function were DISTINCT variables that a blind
`σ→sigma` would merge (`sigma n = sigma` is ill-typed). They must keep distinct names: the
function/`HSMix` field is `sigma`/`rho`; the **scalar** equal-diameter/density value is
**`sigC`/`rhoC`** (see `MixtureDCFAEInjective`, `Q0DetLimit`, …). Do not rename a scalar
`sigC : ℝ` to `sigma` — it shadows the diameter function.

Deliberately **left Greek** (not physics-inconsistent): Mathlib idioms `α`/`β`/`γ` (type
variables), `μ` (measures), `λ`/`π` (Lean notation); and **narrow-scope proof temporaries**
(`ε`/`δ` in ε-δ arguments, integration variables `τ`, `set α := …`/`set β := …` local Baxter
coefficients, count binders `κ`, generic function binders `φ`). These are single-scope and
carry no cross-file ASCII twin, so renaming would only hurt readability or break Mathlib idiom.

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
