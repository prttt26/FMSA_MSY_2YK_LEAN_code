# FMSA Yukawa Mixture Theory — Lean 4 Proofs

Lean 4 + Mathlib formalization of the First-order Mean Spherical Approximation (FMSA) for
fluids with Yukawa interaction tails, covering both the hard-sphere Yukawa (HSY) and
two-Yukawa-tail (2YK) cases.

## What this repository proves

The proofs are organized around the derivation of the direct correlation function (DCF)
for multi-component Yukawa mixtures via the Ornstein-Zernike (OZ) equation and Baxter
factorization.

### Hard-sphere foundations
- Percus-Yevick (PY) closed-form DCF for hard spheres
- Hard-sphere Baxter factor Q₀(s) and its non-vanishing at Yukawa poles
- Wiener-Hopf splitting (B₁ + D₁ = T_U identity; support of T_S)
- OZ fixed-point existence for g₀_HS; contact value g₀_HS(σ) = (1+η/2)/(1−η)²
- Baxter real-space convolution identity

### Yukawa DCF derivation
- Closed-form I₁/I₂ integral identities (FMSA_69 Eq. 38–39) and their vanishing at ℓ=0
- Single-component reduction: b_ij N=1 collapse; g + a·exp(−z) = 1 identity
- Multi-component Baxter identity Ĝ + Â·exp(−z·σ_min) = I and N=1 limits
- FMSA_GA_matrix_mix algebraic foundation: Q̂₀ = P̂ + Ê·exp(−z·σ_min) decomposition,
  G/A matrix coefficients, origin BC automatic satisfaction
- N=1 consistency: corrected formula reduces exactly to FMSA_pure (single-component MSA)
- Inner/outer DCF matching at contact r = R_ij for 2YK

### Formula failure analysis
- Algebraic disproof of (1+A)² = 1−g² — root cause of the FMSA_chsY spike for HSY
- FMSA_poly failure analysis: origin constraint, polynomial approximation impossibility
  for growing exponentials (P.3), two-endpoint bound, exponential basis completeness

### Free energy integrals
- Outer-core and inner-core energy integrals; LJ integral identity
- Free energy convergence for FMSA_GA_matrix_mix and LJ/FMSA_poly routes
- FMSA_GA_matrix_mix exact vs LJ free energy comparison

## Physical setting

**HSY (hard-sphere Yukawa):** one Yukawa tail `−(K/r)·exp(−z·r)` added to a hard-sphere
potential. Standard model for colloidal suspensions and electrolyte solutions.

**2YK (two Yukawa tails):** two competing Yukawa terms — a short-range repulsive tail
(z₁ ≈ 14) and a longer-range attractive tail (z₂ ≈ 2.96) — without a hard core.
Models soft-repulsion fluids; the large z₁ makes inner-core polynomial approximations
fail (exp(14) ≈ 10⁶), motivating the G/A matrix approach proved here.

## Structure

```
LeanCode/
  HardSphere/      — PY DCF, Baxter factor, OZ equation, Wiener-Hopf
  FMSAPoly/        — I₁/I₂ integrals, G/A matrix, single-component reduction
  WienerHopf/      — Splitting identities
  FreeEnergy/      — Sum rule, energy integrals, convergence
  Integrals/       — Supporting integral lemmas
proof_notes_hard_sphere.md    — Proof records for Groups 2, 3, OZ
proof_notes_yukawa_dcf.md     — Proof records for Groups 1, 4, M, B, C, 5
proof_notes_failures.md       — Proof records for Groups chsY, P (formula failure analysis)
proof_notes_free_energy.md    — Proof records for Group F
todo_lean.md                  — Task status index (open sorries, axioms, completed tasks)
```

## Dependencies

- [Lean 4](https://leanprover.github.io/)
- [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/)

See `lean-toolchain` for the exact Lean version and `lakefile.toml` for the Mathlib pin.

## References

- `pdf/FMSA_chsY.pdf` — Analytical multi-species MSA solution (Blum et al.)
- `pdf/lecture_notes_OZ_Yukawa_poly.pdf` — OZ equation, Yukawa DCF, polynomial inner-core approach
