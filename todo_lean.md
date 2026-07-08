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

### Axioms — `axiom` declarations assumed without proof

| Axiom | File | Task | Physical meaning / proof path |
|-------|------|------|-------------------------------|
| `oz_fixed_pt_unique` | `HardSphere/PYOZ_GHS.lean:145` | OZ.2a | OZ fixed point unique in `BoundedContinuousFunction`; needs Banach contraction estimate |
| `oz_core_closure` & `g0_HS_contact_value` | `HardSphere/PYOZ_GHS.lean` | OZ.9a / OZ.3 | PY core closure (Gap B) and the PY contact value — two independent claims, both from Baxter/Wertheim theory, both numerically verified (2026) but not proved from Mathlib real-analysis alone (needs Baxter's Wiener–Hopf factorization). Kept as separate axioms (not merged) since they're logically independent; see [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.9 for full detail on both, including Route A (taken, closed OZ.9) vs Route B (would retire both via one relation, not attempted). |

*(`radial_laplace_conv` and `oz_laplace_oz_eq` are still `axiom` declarations but are superseded dead ends
 — see OZ.2/OZ.6/OZ.7 for the history.)*

### Open tasks — not yet started

| Task | Title | Depends on | Notes |
|------|-------|-----------|-------|
| M.4 | Unconditional `det(Q0_mat_phys) ≠ 0` for all `z > 0` | M.3 | Rank-2 reduction formalized (see `YukawaDCF/Q0DetRankTwo.lean`, details in [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md)). Remaining: one scalar inequality `(1-M₀₀)(1-M₁₁) ≠ M₀₁·M₁₀` (`M := Vmat*Umat`), taken as an explicit hypothesis on `Q0_mat_phys_isUnit_det_of_two_by_two` — not closed unconditionally, robust numerically. |
| OZ.8 | Closed-form sine-transform formula for `c_HS` (analogous to `C_HS_laplace_formula`) + bridge back to `C_HS_laplace`/`S0`/`g0_HS_contact_value` via analytic continuation `s ↔ -ik` | OZ.6, OZ.7 | Not started, needs its own scoping pass. `c_HS` has compact support on `(0,σ)`, so its Laplace transform `C_HS_laplace` is entire — restricting it to the imaginary axis should give `radial_fourier (c_HS eta sigma) k` directly, avoiding a from-scratch sine-transform derivation. Plausible, probably comparable effort to the existing `phi4_formula`-style calculus, but distinct work from OZ.6/OZ.7. |
| OZ.9-RouteB | Baxter's `h`-via-`Q` relation → `g0_HS_contact_value` (and re-derive OZ.9 as a corollary instead of a direct axiom) | OZ.9 | Baxter's second relation is numerically verified (`r·h(r) = -Q'(r)/(2π) + ρ∫₀^σ Q(t)(r-t)h(\|r-t\|)dt`, three `η` values) but the Q-elimination bridge connecting it back to `c_HS`/`radial3d_conv` form has **not** been verified as straightforward — needs its own numerical check before any Lean work. Not started; larger, less scoped than OZ.9's direct-axiom route (Route A, already taken). See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.9. |
| FW.1 | FMT species symmetry: `betaf_hs(N, ρ/N each, d)` = `betaf_hs(1, ρ, d)` when all dᵢ=d | — | Algebraic identity: when all diameters equal, FMT n-functionals n₀=Σρᵢ, n₁=(d/2)Σρᵢ, n₂=πd²Σρᵢ, n₃=(π/6)d³Σρᵢ depend only on total density → White-Bear formula collapses to single-component form. Supports W-C.3 and W-C.4 (numerical verification in `todo_numerical.md`). Likely `simp`/`ring` with the FMT functional unfolded. No Mathlib obstruction. |
| FW.2 | MCSL mixture contact value: g⁰_ij(R_ij) = BMCSL formula for all N | `g0_HS_contact_value` (open axiom) | Mixture generalisation of `g0_HS_contact_value` (`HardSphere/PYOZ_GHS.lean`). Formula: `1/vac + 3ζ₂·dᵢdⱼ/(dᵢ+dⱼ)/vac² + 2ζ₂²·(dᵢdⱼ/(dᵢ+dⱼ))²/vac³`. Needed for W-C.2 (virial-FMT consistency). Same obstruction as `g0_HS_contact_value`. |

*(Tasks D.1–D.4 removed — no longer valid after FMSA_GA_matrix_mix redesign; see [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) Group D note.)*

---

## Task Status

### Group 1 — Closed-Form Integral Identities *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 1.1 | I₁ antiderivative | ✓ DONE | `YukawaDCF/I1I2Integrals.lean` |
| 1.2 | I₂ antiderivative | ✓ DONE | `YukawaDCF/I1I2Integrals.lean` |
| 1.3 | I₁/I₂ vanish at ℓ=0 | ✓ DONE | `YukawaDCF/I1I2Integrals.lean` |

### Group 2 — Hard-Sphere Baxter Factor *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 2.1 | φ₁, φ₂ auxiliary formulas | ✓ DONE | `HardSphere/BaxterFactor.lean` |
| 2.2 | det(s) non-vanishing | ✓ DONE | `HardSphere/BaxterFactor.lean` |

### Group 3 — Wiener–Hopf Structure *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 3.1 | B₁+D₁ = T_U identity | ✓ DONE | `HardSphere/Splitting.lean` |
| 3.2 | Support of T_S on (−∞, R_ij] | ✓ DONE | `HardSphere/Splitting.lean` |

### Group chsY — FMSA_chsY Formula Failure *(failures)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 4.3 | (1+A)² ≠ 1−g² — root cause of HSY spike | ✓ RESOLVED | `FMSAPoly/OriginCheck.lean` |

### Group 4 — Single-Component Reduction *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 4.1 | b_ij N=1 collapse formula | ✓ DONE | `YukawaDCF/BijReduction.lean` |
| 4.2 | g + a·exp(−z) = 1 | ✓ DONE | `YukawaDCF/SingleCompIdentity.lean` |
| 4.4 | Full N=1 reduction Eq.41→42 | ✓ DONE | `YukawaDCF/SingleCompReduction.lean` |

### Group M — Multi-Component Baxter Identity *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| M.1 | Abstract matrix identity Ĝ+Â·c=I | ✓ DONE | `YukawaDCF/MatrixIdentity.lean` |
| M.2 | N=1 limit: Ĝ₀₀=g, Â₀₀=a | ✓ DONE | `YukawaDCF/MatrixN1.lean` |
| M.3 | det(Q̂₀) ≠ 0 multi-component | ◑ conditional (old axiom disproved; see M.4) | `YukawaDCF/MatrixQ0.lean`, `YukawaDCF/Q0DetRankTwo.lean` |

### Group B — FMSA_GA_matrix_mix Algebraic Foundation and Polynomial Determination *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| B.1 | Shifted-exponent integral | ✓ DONE | `HardSphere/BaxterFactor.lean` |
| B.2 | Concrete Q̂₀=P̂+Ê·exp(−z·σ_min) | ✓ DONE | `YukawaDCF/QhatDecomposition.lean` |
| B.3 | Coefficient algebra (1−g²)−a²c²=2acg | ✓ DONE | `YukawaDCF/SingleCompIdentity.lean` |
| B.4 | Origin BC automatic for FMSA_GA_matrix_mix | ✓ DONE | `YukawaDCF/B4OriginBC.lean` |
| B.5 | Degree bound exisr: deg P_{ij} ≤ 4 (no r^n for n≥N with N=4) | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.6 | Origin uniqueness: only A_{ij}=−E_{ij}(0) forced at r=0 | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.7 | No contact BC: B,C,D,E^{(4)} not fixed by r=R_{ij} | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.8 | Laurent extraction: all five coefficients from R_{ij}(s) at s=0 | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.9 | D_{ij} generically nonzero for unlike pairs | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.10 | Exact degree: natDegree P_{ij} = 4 | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |

### Group C — FMSA_GA_matrix_mix Consistency *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| C.1 | N=1: corrected formula = FMSA_pure | ✓ DONE | `YukawaDCF/SingleCompReduction.lean` |

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
| OZ.2 | g₀_HS via OZ fixed point | ◑ superseded, see [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) | `HardSphere/PYOZ_GHS.lean` |
| OZ.2b | Gap A (r≥σ half of `oz_laplace_oz_eq`) | ◑ superseded by OZ.7, see [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) | `HardSphere/OZExteriorBridge.lean` |
| OZ.3 | g₀_HS via OZ Laplace inversion | ◑ conditional on OZ.2 + `g0_HS_contact_value` axiom | `HardSphere/PYOZ.lean` |
| OZ.4 | Linearised OZ: Ĥ¹=Ĉ¹·S₀ | ✓ DONE | `HardSphere/PYOZ.lean` |
| OZ.5 | Baxter real-space convolution identity | ✓ DONE | `HardSphere/BaxterRealSpace.lean` |
| OZ.6 | Radial sine/Fourier transform convolution theorem — correct replacement for the disproven `radial_laplace_conv` | ✓ DONE, no axiom | `HardSphere/RadialFourier.lean` |
| OZ.7 | Fourier-domain exterior OZ equation (Gap A ∪ Gap B, correct-transform counterpart of `oz_laplace_oz_eq_of_core_closure`) | ✓ DONE, conditional only on OZ.9 (`hcore`) | `HardSphere/OZFourierBridge.lean` |
| OZ.8 | Closed-form sine-transform formula for `c_HS` + bridge back to `C_HS_laplace`/`S0`/`g0_HS_contact_value` via analytic continuation `s↔-ik` | ☐ not started, needs its own scoping pass | — |
| OZ.9a | PY core closure (Gap B) for `r < σ` — promoted to a named, numerically-verified axiom | ✓ DONE (axiom `oz_core_closure`, Route A; not proved from Mathlib real-analysis — needs Baxter Wiener–Hopf, out of scope) | `HardSphere/PYOZ_GHS.lean` |
| OZ.9b | `oz_fourier_oz_eq_of_PY_core`: OZ.7 specialized to consume `oz_core_closure` instead of an externally-supplied `hcore` — most complete/trustworthy result in the whole OZ chain (Gap A + convolution theorem + Gap B all proved/axiomatized by name, only routine integrability hypotheses remain) | ✓ DONE | `HardSphere/OZFourierBridge.lean` |

### Group F — Free Energy Integrals *(free_energy)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| F.1 | Outer-core free energy integral | ✓ DONE | `FreeEnergy/OuterIntegral.lean` |
| F.2a | Inner-core energy integral (E_ij part) | ✓ DONE | `FreeEnergy/InnerIntegral.lean` |
| F.2b | LJ inner-core integral identity | ✓ DONE | `FreeEnergy/LJIntegral.lean` |
| F.3a | Free energy convergence (FMSA_GA_matrix_mix route) | ✓ DONE | `FreeEnergy/Convergence.lean` |
| F.3b | Free energy convergence (LJ/FMSA_poly route) | ✓ DONE | `FreeEnergy/Convergence.lean` |
| F.4 | Compressibility sum rule | ✗ deleted | — |
| F.5 | Contact-value approximation error | ✓ DONE | `FreeEnergy/ContactError.lean` |
| F.6 | FMSA_GA_matrix_mix exact vs LJ free energy comparison | ✓ DONE | `FreeEnergy/SumRule.lean` |

**F.4 deletion note:** The compressibility sum rule `∂(βP)/∂ρ = 1−ρĉ(0)` mixes the energy-route
free energy (what FMSA computes: `∫ u g₀ r² dr`) with the compressibility-route DCF (`ĉ(0)` from
integrating c(r)). For any first-order approximate theory these two routes give different numbers —
the gap measures route inconsistency, not model quality. Verifying route inconsistency numerically
is not a useful model check. Deleted.

### Group 5 — Matching at Contact *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 5.1 | Inner/outer matching at r=R_ij (2YK only) | ✓ structural (I1/I2=0) / **⊥ physical claim disproved** | `YukawaDCF/ContactMatching.lean` |

**5.1 disproof note:** The Lean proof establishes only that `I1(0) = I2(0) = 0` (integral over an
empty interval — trivially true) and `eij(R,R) = ΣA_k`. It explicitly states in a comment that
full DCF continuity additionally requires the MSA closure condition `K = A_k` at each Yukawa
pole, which is NOT proved and does NOT hold.

Numerical evidence from `FMSA_pure` (verify_pure.py V.1): the first-order c₁ gap at r = d_bh is
~1.1–1.7 across liquid-range state points, far from the ~1e-6 numerical-precision level.  The
total-c gap is smaller (~0.02–0.7) only because the FMT c₀ accidentally partially compensates.
Since the pure-fluid limit is the simplest case, the same discontinuity must appear in mixtures.
The intended physical matching property (DCF continuity at contact for the 2YK FMSA) is false.

### Group D — Pure-Limit Equivalence

~~Tasks D.1–D.4 deleted.~~ Written for the old scalar Path B approach; no longer valid after
FMSA_GA_matrix_mix redesign (full G/A matrix, mediated terms). Pure-limit N=1 reduction is covered
by **C.1** (✓ DONE). See [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) if a new Group D is needed.

---

*Numerical verification tasks (Groups V and W) are in `../todo/todo_numerical.md`.*
