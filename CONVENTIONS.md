# Coding Conventions

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
