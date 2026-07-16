# FMSA Yukawa Mixture Theory — Lean 4 Proofs

Lean 4 + Mathlib formalization of the First-order Mean Spherical Approximation (FMSA) for
fluids with Yukawa interaction tails, covering both the hard-sphere Yukawa (HSY) and
two-Yukawa-tail (2YK) cases.

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
LeanCode/
  HardSphere/    — PY DCF, Baxter factor + Wiener–Hopf factorization, OZ equation,
                   Wiener–Hopf splitting, det(Q̂₀) positivity, White-Bear FMT (HS only)
  YukawaDCF/     — I₁/I₂ integrals, G/A matrix, single-component reduction, inner-core
                   mediated breakpoints, Wiener–Hopf spectral amplitude, N=2 mixture inner
                   core, contact matching
  FMSAPoly/      — Formula failure analysis (Groups chsY, P): (1+A)²≠1−g² disproof,
                   polynomial-approximation impossibility
  FreeEnergy/    — Sum rule, energy integrals, convergence
  Analysis/      — Complex-analysis infrastructure (residue at a simple pole, Jordan's lemma,
                   contour deformation, Banach pole-family) supporting the Baxter pole route

Proof records — one file per related group cluster (see the todo_lean.md header for the
authoritative group↔file map):
  proof_notes_hard_sphere.md — Groups 2, 3, OZ
  proof_notes_baxter.md      — Group BAXTER (Baxter Q-factor + Wiener–Hopf factorization)
  proof_notes_contact.md     — Group CONTACT (g₀_HS contact value, jump-asymptotic route)
  proof_notes_pole.md        — Group POLE (complex-analytic Baxter pole/residue construction)
  proof_notes_ozfix.md       — Group OZFIX (h_explicit → OzFixedPt assembly)
  proof_notes_matrix_q0.md   — Group M (multi-component Q̂₀ matrix identity, det positivity)
  proof_notes_yukawa_dcf.md  — Groups 1, 4, B, C, 5
  proof_notes_breakpoints.md — Group IB (inner-core mediated breakpoints)
  proof_notes_yukawa_wh.md   — Groups Y1, MML, MZERO, MPOLY (Wiener–Hopf; N=2 mixture Mittag-Leffler)
  proof_notes_failures.md    — Groups chsY, P, GA (method-failure analysis)
  proof_notes_free_energy.md — Groups F, FW (free energy; White-Bear FMT/BMCSL)

Reference:
  todo_lean.md   — task status index (open sorries, axioms, completed/started tasks)
  MATH_AXIOMS.md — registry of named mathematical axioms used across the proofs
  CONVENTIONS.md — naming and notation conventions
  to_python.md   — Lean results → Python implications (analysis-session handoff notes)
```

## Dependencies

- [Lean 4](https://leanprover.github.io/)
- [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/)

See `lean-toolchain` for the exact Lean version and `lakefile.toml` for the Mathlib pin.

