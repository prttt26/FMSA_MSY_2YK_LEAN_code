# FMSA Yukawa Mixture Theory — Lean 4 Proofs

Lean 4 + Mathlib formalization of the First-order Mean Spherical Approximation (FMSA) for
fluids with Yukawa interaction tails, covering both the hard-sphere Yukawa (HSY) and
two-Yukawa-tail (2YK) cases.

## Project organization — four content tracks

The development is organized around four logical tracks. Each *claim* track carries a scope + axiom
gate `.lean` file (a `#guard_msgs`-checked ledger of what it proves and its exact axiom footprint —
the build fails if either drifts) and a task-status file; the **Foundations** track is depended-upon
by all three claim tracks and therefore has no gate file of its own.

| Track | What it is | Task status | Scope gate | Dominant `LeanCode/` layers |
|---|---|---|---|---|
| **Foundations** (非闭包依赖基础) | HS / OZ / Baxter / Wiener–Hopf / thermodynamics infrastructure, independent of *which* closure | [todo_foundations.md](todo_foundations.md) | — (depended-upon) | L0 `Analysis/`, `FMSAPoly/` · L1 `HardSphere/` · L2 `HSMixture/` · `FreeEnergy/` |
| **FMSA** | the FMSA-DP first-order DCF/RDF construction | [todo_fmsa.md](todo_fmsa.md) | [FMSAProject.lean](LeanCode/FMSAProject.lean) | L3 `YukawaOZ/` · L4 `YukawaOZMix/` |
| **Exact MSA** (+ FMSA↔Exact-MSA bridge) | Waisman/Blum–Høye/Ginoza exact closed form; the FOEQ / MSAFAM / leg-3 bridge; the BRK mixture core (axiom-free) | [todo_exact_msa.md](todo_exact_msa.md) | [ExactMSAProject.lean](LeanCode/ExactMSAProject.lean) | L3/L4 + L5 `Closures/` |
| **Other closures** (其他闭包) | PYE (`pullback_passes=0` ≡ first-order PY); HNCB | [todo_closures_other.md](todo_closures_other.md) | [ClosuresProject.lean](LeanCode/ClosuresProject.lean) | L5 `Closures/` |

`todo_lean.md` remains the thin top-level index (layer map + project-wide axiom/sorry ledger +
category index → the four task files above). Detailed per-group proof records live in the
`proof_notes_*.md` cluster (see the Structure section).

## What this repository proves

The proofs are organized around the derivation of the direct correlation function (DCF)
and radial distribution function (RDF) for multi-component Yukawa mixtures via the
Ornstein-Zernike (OZ) equation and Baxter factorization.

### Hard-sphere foundations
- Percus-Yevick (PY) closed-form DCF for hard spheres
- Hard-sphere Baxter factor Q₀(s), its non-vanishing at Yukawa poles, and the Baxter
  Wiener–Hopf factorization of 1 − ρĈ_HS (Group BAXTER)
- Complex-analytic construction of the Baxter Q-factor's poles/residues — residue at a simple
  pole, Jordan's lemma, contour deformation, Banach pole-family (Group POLE, `Analysis/`)
- Wiener-Hopf splitting (B₁ + D₁ = T_U identity; support of T_S)
- OZ fixed-point existence for g₀_HS and its closed-form assembly into `OzFixedPt` (Group OZFIX)
- Contact value g₀_HS(σ) = (1+η/2)/(1−η)² via the jump-asymptotic route (Group CONTACT)
- Multi-component Baxter Q̂₀ matrix identity and det(Q̂₀) > 0 positivity (Group M)
- Baxter real-space convolution identity

### Yukawa DCF derivation
- Closed-form I₁/I₂ integral identities and their vanishing at ℓ=0
- Single-component reduction: b_ij N=1 collapse; g + a·exp(−z) = 1 identity
- FMSA_GA_matrix_mix algebraic foundation: Q̂₀ = P̂ + Ê·exp(−z·σ_min) decomposition,
  G/A matrix coefficients, degree-≤4 inner-core polynomial, origin BC automatic satisfaction
- Inner-core mediated breakpoints: mediated ≡ 0 below r* = R[a,b]+R[i,a], its C² onset and
  the second knot r** (Group IB)
- First-order Yukawa RDF/DCF via Wiener–Hopf: the spectral amplitude carrying the Yukawa-pole
  residue is the doubly-propagated Q̂₀⁻¹·K·Q̂₀⁻ᵀ, not the singly-propagated K·G (Group Y1)
- N=1 consistency: corrected formula reduces exactly to FMSA_pure; inner/outer matching at contact

### Multi-component mixture inner core (Wiener–Hopf)
- N=2 mixture Mittag-Leffler inner-core expansion (Group MML)
- Infinitude of the mixture det(Q̂₀) HS-pole zero family (Group MZERO)
- Mixture inner-core polynomial coefficients (Group MPOLY)

### Formula failure analysis
- Algebraic disproof of (1+A)² = 1−g² — root cause of the FMSA_chsY spike for HSY (Group chsY)
- FMSA_poly failure: origin constraint, degree-independent impossibility of approximating a
  growing exponential (P.3), two-endpoint bound, exponential-basis completeness (Group P)
- FMSA_GA_matrix_mix's own inner formula is ill-conditioned for unlike pairs at large σ-ratio:
  the two-exp base K·exp(z·R) diverges and no bounded additive HS-pole correction cancels it,
  with structural root cause G₀₁ → 0 (Group GA)

### Free energy integrals
- Outer-core and inner-core energy integrals; LJ integral identity
- Free energy convergence for FMSA_GA_matrix_mix and LJ/FMSA_poly routes; exact vs LJ comparison
- White-Bear FMT / BMCSL mixture thermodynamic consistency (Group FW)

## Physical setting

**HSY (hard-sphere Yukawa):** one Yukawa tail `−(K/r)·exp(−z·r)` added to a hard-sphere
potential. Standard model for colloidal suspensions and electrolyte solutions.

**2YK (two Yukawa tails):** two competing Yukawa terms — a short-range repulsive tail
(z₁ ≈ 14) and a longer-range attractive tail (z₂ ≈ 2.96) — without a hard core. Best method for approximating LJ potential.
Models soft-repulsion fluids; the large z₁ makes inner-core polynomial approximations
fail (exp(14) ≈ 10⁶), motivating the G/A matrix approach proved here.

## Structure

```
LeanCode/                         (layering + policy: see CONVENTIONS.md; restructured 2026-08-06)
  Analysis/      — general complex/functional-analysis infrastructure (Group MA): residues, Jordan's
                   lemma, contour deformation, Banach pole-family, Wiener–Hopf, Volterra   [base]
  FMSAPoly/      — FMSA polynomial inner core + formula-failure analysis (Groups chsY, P)  [base]
  HardSphere/    — single-component HS: PY DCF, Baxter factor + Wiener–Hopf, OZ fixed point, poles
  HSMixture/     — N-component PURE hard-sphere mixture: Baxter Q̂₀ matrix, det pole-freeness,
                   no-spinodal, White-Bear FMT, mixture RDF
  YukawaOZ/      — single-component Yukawa OZ: I₁/I₂ integrals, single-comp reduction, MSA outer DCF,
                   inner-core, causal projection, contact matching  (+ the generic-scalar base)
  YukawaOZMix/   — N-component Yukawa mixture OZ: real-space Baxter route, mixture DCF/RDF, ML series,
                   Wiener–Hopf spectral amplitude, residues
  FreeEnergy/    — sum rule, energy integrals, convergence  [sink]
  Closures/      — non-FMSA closures (PY/PYE/HNCB/MSA): ClosureExpansions + DPClosureMap  [sink]

Proof records — one file per related group cluster (see the todo_lean.md header for the
authoritative group↔file map):
  proof_notes_hard_sphere.md — Groups 2, 3, OZ
  proof_notes_baxter.md      — Group BAXTER (Baxter Q-factor + Wiener–Hopf factorization)
  proof_notes_contact.md     — Group CONTACT (g₀_HS contact value, jump-asymptotic route)
  proof_notes_pole.md        — Group POLE (complex-analytic Baxter pole/residue construction)
  proof_notes_ozfix.md       — Group OZFIX (h_explicit → OzFixedPt assembly)
  proof_notes_matrix_q0.md   — Group M (multi-component Q̂₀ matrix identity, det positivity)
  proof_notes_yukawa_dcf.md  — Groups 1, 4, GAP, C, 5
  proof_notes_breakpoints.md — Group IB (inner-core mediated breakpoints)
  proof_notes_yukawa_wh.md   — Group Y1 (first-order Yukawa RDF via Wiener–Hopf; general foundation)
  proof_notes_mixture_rdf.md — Groups MML, MZERO (N=2 mixture inner RDF h₁: Mittag-Leffler HS-pole series + det zero family)
  proof_notes_mixture_dcf.md — Groups MRS, MPOLY (N=2 mixture inner DCF: real-space Baxter finite closed form)
  proof_notes_failures.md    — Groups chsY, P, GA (method-failure analysis)
  proof_notes_free_energy.md — Groups F, FW (free energy; White-Bear FMT/BMCSL)

Scope + axiom gates — one #guard_msgs-checked ledger per claim track (see "four content tracks"):
  LeanCode/FMSAProject.lean     — FMSA-DP first-order construction (the paper's chain)
  LeanCode/ExactMSAProject.lean — exact MSA closed form + FMSA↔ExactMSA bridge (FOEQ/MSAFAM/BRK)
  LeanCode/ClosuresProject.lean — PYE / HNCB (the non-FMSA, non-exact-MSA closures)

Reference:
  todo_lean.md          — thin top-level index: layer map, project-wide axiom/sorry ledger, category index
  todo_foundations.md   — task status: Foundations track (非闭包依赖基础)
  todo_fmsa.md          — task status: FMSA track
  todo_exact_msa.md     — task status: Exact MSA (+ FMSA↔ExactMSA bridge) track
  todo_closures_other.md— task status: Other closures track (PYE / HNCB)
  MATH_AXIOMS.md — registry of named mathematical axioms used across the proofs
  CONVENTIONS.md — naming and notation conventions
  to_python.md   — Lean results → Python implications (analysis-session handoff notes)
```

## Dependencies

- [Lean 4](https://leanprover.github.io/)
- [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/)

See `lean-toolchain` for the exact Lean version and `lakefile.toml` for the Mathlib pin.

