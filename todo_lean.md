# Lean Proof Tasks: FMSA Yukawa Mixture Theory

This file is the **status index** for all Lean 4 + Mathlib proofs in `LeanCode/`.
Detailed proof records (statements, proof sketches, pitfalls, Lean API notes) are in:

- [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) — Groups 2, 3, OZ (pure HS foundations)
- [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) — Groups 1, 4, M, B, C, 5 (Yukawa DCF derivation)
- [proof_notes_failures.md](proof_notes_failures.md) — Groups chsY, P (formula failure analysis)
- [proof_notes_free_energy.md](proof_notes_free_energy.md) — Group F (free energy integrals)

**Source markers:**
- **[chsY]** — `pdf/FMSA_chsY.pdf` (analytical multi-species MSA solution)
- **[LN]** — `pdf/lecture_notes_OZ_Yukawa_poly.pdf`

---

## Open / Unfinished Items

### Sorries — actual `sorry` proof terms in source files

| Sorry | File | Task | What remains |
|-------|------|------|--------------|
| `compressibility_sum_rule` (under `hParseval`) | `FreeEnergy/SumRule.lean` | F.4 | `hParseval` is UNSATISFIABLE for FMSA parameters: `(1+A)²` from `b_n1_baxter_formula` depends on `(η,z)` but NOT `d`, while `hParseval` forces `(1+A)² = (zd+1)/(zd+1+z−exp(zd))` which depends on `d`. Numerically: η=0.3, z=1, d=1 gives FMSA 0.153 vs required 7.10. The theorem conflates 3D Fourier (r² weight) with 1D Laplace (no r² weight). Needs reformulation. |

### Axioms — `axiom` declarations assumed without proof

| Axiom | File | Task | Physical meaning / proof path |
|-------|------|------|-------------------------------|
| `Q0_ne_zero_at_yukawa` | `HardSphere/BaxterFactor.lean:326` | 2.2 | Q₀(z) ≠ 0 for z > 0, η ∈ (0,1); needs analytic bound |
| `Q0_mat_isUnit_det` | `FMSAPoly/MatrixQ0.lean:129` | M.3 | Multi-component Q̂₀ invertible; multi-component analog of 2.2 |
| `oz_fixed_pt_unique` | `HardSphere/PYOZ_GHS.lean:145` | OZ.2a | OZ fixed point unique in `BoundedContinuousFunction`; needs Banach contraction estimate |
| `radial_laplace_conv` | `HardSphere/RadialLaplace.lean` | OZ.2b (math) | F̃[f⊛₃Dg]=F̃[f]·F̃[g]; pure Fubini + change of variables; outside Mathlib scope |
| `oz_laplace_oz_eq` | `HardSphere/PYOZ_GHS.lean` | OZ.2b (physics) | oz_h satisfies Laplace-domain OZ eq; needs PY closure for r<σ + integrability for Fubini |
| `g0_HS_contact_value` | `HardSphere/PYOZ_GHS.lean` | OZ.3 | g₀_HS(σ) = (1+η/2)/(1−η)²; needs PY partial-fraction inversion |
### Open tasks — not yet started

*(none currently)*

*(Tasks D.1–D.4 removed — no longer valid after FMSA_GA_matrix_mix redesign; see [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) Group D note.)*

---

## Task Status

### Group 1 — Closed-Form Integral Identities *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 1.1 | I₁ antiderivative | ✓ DONE | `FMSAPoly/I1I2Integrals.lean` |
| 1.2 | I₂ antiderivative | ✓ DONE | `FMSAPoly/I1I2Integrals.lean` |
| 1.3 | I₁/I₂ vanish at ℓ=0 | ✓ DONE | `FMSAPoly/I1I2Integrals.lean` |

### Group 2 — Hard-Sphere Baxter Factor *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 2.1 | φ₁, φ₂ auxiliary formulas | ✓ DONE | `HardSphere/BaxterFactor.lean` |
| 2.2 | det(s) non-vanishing | ☐ axiom | `HardSphere/BaxterFactor.lean` |

### Group 3 — Wiener–Hopf Structure *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 3.1 | B₁+D₁ = T_U identity | ✓ DONE | `WienerHopf/Splitting.lean` |
| 3.2 | Support of T_S on (−∞, R_ij] | ✓ DONE | `WienerHopf/Splitting.lean` |

### Group chsY — FMSA_chsY Formula Failure *(failures)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 4.3 | (1+A)² ≠ 1−g² — root cause of HSY spike | ✓ RESOLVED | `FMSAPoly/OriginCheck.lean` |

### Group 4 — Single-Component Reduction *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 4.1 | b_ij N=1 collapse formula | ✓ DONE | `FMSAPoly/BijReduction.lean` |
| 4.2 | g + a·exp(−z) = 1 | ✓ DONE | `FMSAPoly/SingleCompIdentity.lean` |
| 4.4 | Full N=1 reduction Eq.41→42 | ✓ DONE | `FMSAPoly/SingleCompReduction.lean` |

### Group M — Multi-Component Baxter Identity *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| M.1 | Abstract matrix identity Ĝ+Â·c=I | ✓ DONE | `FMSAPoly/MatrixIdentity.lean` |
| M.2 | N=1 limit: Ĝ₀₀=g, Â₀₀=a | ✓ DONE | `FMSAPoly/MatrixN1.lean` |
| M.3 | det(Q̂₀) ≠ 0 multi-component | ✓ DONE (axiom) | `FMSAPoly/MatrixQ0.lean` |

### Group B — FMSA_GA_matrix_mix Algebraic Foundation *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| B.1 | Shifted-exponent integral | ✓ DONE | `HardSphere/BaxterFactor.lean` |
| B.2 | Concrete Q̂₀=P̂+Ê·exp(−z·σ_min) | ✓ DONE | `FMSAPoly/QhatDecomposition.lean` |
| B.3 | Coefficient algebra (1−g²)−a²c²=2acg | ✓ DONE | `FMSAPoly/SingleCompIdentity.lean` |
| B.4 | Origin BC automatic for FMSA_GA_matrix_mix | ✓ DONE | `FMSAPoly/B4OriginBC.lean` |

### Group C — FMSA_GA_matrix_mix Consistency *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| C.1 | N=1: corrected formula = FMSA_pure | ✓ DONE | `FMSAPoly/SingleCompReduction.lean` |

### Group P — FMSA_poly Failure Analysis *(failures)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| P.1 | E_ij is sum of decaying exponentials | ✓ DONE | `FMSAPoly/EijStructure.lean` |
| P.2 | Origin constraint p₀=−E_ij(0) | ✓ DONE | `FMSAPoly/OriginConstraint.lean` |
| P.3 | No polynomial approximates exp(+z·(R−r)) under normalisation | ✓ DONE | `FMSAPoly/PolyApproxFails.lean` |
| P.4 | E_ij contact value matches outer-core MSA | ✓ DONE | `FMSAPoly/ContactValue.lean` |
| P.C1 | Corollary: normalisation forces large error | ✓ DONE | `FMSAPoly/PolyApproxCorollary.lean` |
| P.C2 | Two-endpoint bound | ✓ DONE | `FMSAPoly/PolyApproxFails.lean` |
| P.B1 | Exponential basis: 2×2 system always solvable | ✓ DONE | `FMSAPoly/ExpBasis.lean` |
| P.B2 | Exponential basis: zero endpoint errors | ✓ DONE | `FMSAPoly/ExpBasis.lean` |

### Group OZ — Ornstein-Zernike Structure *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| OZ.1 | PY closed-form DCF for hard spheres | ✓ DONE | `HardSphere/PYDCF.lean` |
| OZ.2 | g₀_HS via OZ fixed point | ✓ DONE (2 axioms remain: `oz_laplace_oz_eq`, `oz_fixed_pt_unique`) | `HardSphere/PYOZ_GHS.lean` |
| OZ.3 | g₀_HS via OZ Laplace inversion | ✓ DONE (axiom remains) | `HardSphere/PYOZ.lean` |
| OZ.4 | Linearised OZ: Ĥ¹=Ĉ¹·S₀ | ✓ DONE | `HardSphere/PYOZ.lean` |
| OZ.5 | Baxter real-space convolution identity | ✓ DONE | `HardSphere/BaxterRealSpace.lean` |

### Group F — Free Energy Integrals *(free_energy)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| F.1 | Outer-core free energy integral | ✓ DONE | `FreeEnergy/OuterIntegral.lean` |
| F.2a | Inner-core energy integral (E_ij part) | ✓ DONE | `FreeEnergy/InnerIntegral.lean` |
| F.2b | LJ inner-core integral identity | ✓ DONE | `FreeEnergy/LJIntegral.lean` |
| F.3a | Free energy convergence (FMSA_GA_matrix_mix route) | ✓ DONE | `FreeEnergy/Convergence.lean` |
| F.3b | Free energy convergence (LJ/FMSA_poly route) | ✓ DONE | `FreeEnergy/Convergence.lean` |
| F.4 | Compressibility sum rule | ☐ sorry (mis-stated) | `FreeEnergy/SumRule.lean` |
| F.5 | Contact-value approximation error | ✓ DONE | `FreeEnergy/ContactError.lean` |
| F.6 | FMSA_GA_matrix_mix exact vs LJ free energy comparison | ✓ DONE | `FreeEnergy/SumRule.lean` |

### Group 5 — Matching at Contact *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 5.1 | Inner/outer matching at r=R_ij (2YK only) | ✓ DONE | `FreeEnergy/ContactMatching.lean` |

### Group D — Pure-Limit Equivalence

~~Tasks D.1–D.4 deleted.~~ Written for the old scalar Path B approach; no longer valid after
FMSA_GA_matrix_mix redesign (full G/A matrix, mediated terms). Pure-limit N=1 reduction is covered
by **C.1** (✓ DONE). See [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) if a new Group D is needed.
