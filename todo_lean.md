# Lean Proof Tasks: FMSA Yukawa Mixture Theory

This file is the **status index** for all Lean 4 + Mathlib proofs in `LeanCode/`.
Detailed proof records (statements, proof sketches, pitfalls, Lean API notes) are in:

- [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) — Groups 2, 3, OZ (pure HS foundations)
- [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) — Groups 1, 4, M, B, C, 5 (Yukawa DCF derivation)
- [proof_notes_failures.md](proof_notes_failures.md) — Groups chsY, P (formula failure analysis)
- [proof_notes_free_energy.md](proof_notes_free_energy.md) — Groups F, FW (free energy integrals; White-Bear FMT/BMCSL)

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
| `oz_fixed_pt_unique` | `HardSphere/PYOZ_GHS.lean` | OZ.10 | OZ fixed point uniqueness. Dilute case (`eta<1`, `24·eta·bracket<1`) now a real theorem, `oz_fixed_pt_unique_dilute` (`HardSphere/OzFixedPtDilute.lean`, no axiom); this axiom now covers only mid/high density (needs Fredholm alternative). See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.10. |
| `oz_core_closure` & `g0_HS_contact_value` | `HardSphere/PYOZ_GHS.lean` | OZ.9a / OZ.3 | PY core closure and PY contact value (Baxter/Wertheim). See Numerically verified section below. |

*(`radial_laplace_conv` and `oz_laplace_oz_eq` are still `axiom` declarations but are superseded dead ends
 — see OZ.2/OZ.6/OZ.7 for the history.)*

### Numerically verified — not proved in Lean

| Claim | File | Task | What's verified / what's missing |
|-------|------|------|-----------------------------------|
| PY core closure & PY contact value | `HardSphere/PYOZ_GHS.lean` (axioms `oz_core_closure`, `g0_HS_contact_value`) | OZ.9a / OZ.3 | Baxter/Wertheim results; numerically verified across state points, needs Baxter's Wiener–Hopf factorization for a Lean proof. See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.9. |
| `(1-M₀₀)(1-M₁₁) ≠ M₀₁·M₁₀` (`M := Vmat·Umat`) | `YukawaDCF/MatrixQ0.lean`, explicit hypothesis on `Q0_mat_phys_isUnit_det_of_two_by_two` | M.4 | Rank-2 reduction (M.4) leaves this one scalar inequality; robust numerically across tested parameters, not proved unconditionally. Blocks M.3's unconditional `det(Q̂₀)≠0`. See [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) Task M.4. |
| `D_ij ≠ 0` for unlike pairs | `YukawaDCF/B5MixturePoly.lean` (theorem `b9_d_ij_nonzero_example`) | B.9 | Confirmed numerically: `verify_oz_solver.py` Check 4 gives `D_01 = -3295.03` for the canonical binary HSY state point (σ=[1.0,1.2], ρ*=0.5, T*=1.5) — clearly nonzero. The Lean theorem only proves existence of valid unlike-pair parameters, not `D≠0` for them; the actual inequality is unproved. See [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) Task B.9. |

### Open tasks — not yet started

| Task | Title | Depends on | Notes |
|------|-------|-----------|-------|
| B.11 | Inner DCF decomposition: `mediated_ij(r)=0` for r<σ_min; P_ij is single polynomial on (0,R_ij) | B.5, 1.3 | Three sub-tasks with sorry in `YukawaDCF/B11InnerDecomp.lean`. Single polynomial confirmed for σ-ratio ≤ 3 (factor-of-3 threshold: alpha_0=(σ_j−3σ_b)/2; our binary ratio=2 < 3 → mediated=0 everywhere). σ-ratio > 3 Term IV (double convolution) breakpoint structure pending further research (B.11.4). |
| OZ.9-RouteB | Derive `g0_HS_contact_value` from Baxter's `h`-via-`Q` relation (alternative to OZ.9's direct axiom) | OZ.9 | Not started; Q-elimination bridge back to `c_HS` unverified. See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.9. |
| OZ.8-partB | Derive `g0_HS_contact_value` from OZ.8's Fourier-domain closed form | OZ.8 | Not started; needs Fourier inversion of the closed-form-in-`k` OZ solution (residue calculus), comparable in scale to the Baxter Wiener–Hopf work. See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.8. |

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
| M.4 | Unconditional `det(Q0_mat_phys) ≠ 0` for all `z > 0` | ◑ conditional — rank-2 reduction done; one scalar inequality left as explicit hypothesis, robust numerically but not proved unconditionally; see Numerically verified section | `YukawaDCF/MatrixQ0.lean` |

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
| B.9 | D_{ij} generically nonzero for unlike pairs | ◑ weakened — numerically confirmed, not proved; see Numerically verified section | `YukawaDCF/B5MixturePoly.lean` |
| B.10 | Exact degree: natDegree P_{ij} = 4 | ✓ DONE | `YukawaDCF/B5MixturePoly.lean` |
| B.11 | Inner DCF decomposition: domain of P_ij, mediated vanishing for r < σ_min | ☐ sorry | `YukawaDCF/B11InnerDecomp.lean` |

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
| OZ.8 | Closed-form sine-transform formula for `c_HS` + bridge to `C_HS_laplace`/`S0` via `s↔-ik` | ✓ DONE (Parts A+B), no axiom/sorry. Bridge to `g0_HS_contact_value` not attempted — see OZ.8-partB | `HardSphere/RadialFourierCHS.lean` |
| OZ.9a | PY core closure (Gap B) for `r < σ` — promoted to a named, numerically-verified axiom | ✓ DONE (axiom `oz_core_closure`, Route A; not proved from Mathlib real-analysis — needs Baxter Wiener–Hopf, out of scope) | `HardSphere/PYOZ_GHS.lean` |
| OZ.9b | `oz_fourier_oz_eq_of_PY_core`: OZ.7 specialized to consume `oz_core_closure` instead of an externally-supplied `hcore` — most complete/trustworthy result in the whole OZ chain (Gap A + convolution theorem + Gap B all proved/axiomatized by name, only routine integrability hypotheses remain) | ✓ DONE | `HardSphere/OZFourierBridge.lean` |
| OZ.9-RouteB | Derive `g0_HS_contact_value` from Baxter's `h`-via-`Q` relation (alternative to OZ.9's direct axiom) | ☐ not started — Q-elimination bridge back to `c_HS` unverified | — |
| OZ.8-partB | Derive `g0_HS_contact_value` from OZ.8's Fourier-domain closed form | ☐ not started — needs Fourier inversion of the closed-form-in-`k` OZ solution (residue calculus), comparable in scale to the Baxter Wiener–Hopf work | — |
| OZ.10 | Uniqueness of the OZ fixed point (`oz_fixed_pt_unique`) | ◑ axiom — dilute case proved (OZ.10-dilute); middle/high density still needs Fredholm alternative, likely absent from Mathlib | `HardSphere/PYOZ_GHS.lean` |
| OZ.10-dilute | Dilute-regime (`eta<1`, `24·eta·bracket<1`, i.e. `eta≲0.088`) Banach existence/uniqueness for `oz_fixed_pt_unique`, exterior-only | ✓ DONE — `oz_fixed_pt_unique_dilute`, genuine theorem, no axiom/sorry. Middle/high density (`eta≈0.3–0.5`) still needs Fredholm alternative, not attempted — see [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.10-dilute. | `HardSphere/OzFixedPtDilute.lean` (+ `c_HS_abs_t2_integrableOn` in `HardSphere/PYDCF.lean`) |

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

### Group FW — White-Bear FMT / BMCSL Mixture Thermodynamics *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| FW.1 | FMT species symmetry: `betaf_hs` depends on `rho` only through `∑ᵢρᵢ` when all diameters equal | ✓ DONE, no axiom (`betaf_hs_species_symmetry`) | `HardSphere/WhiteBearFMT.lean` |
| FW.2 | BMCSL/White-Bear thermodynamic consistency: virial pressure (from `g0_bmcsl`) = FMT scaled pressure (from `betaf_hs`) | ✓ DONE, no axiom (`bmcsl_virial_eq_fmt_pressure`) | `HardSphere/WhiteBearFMT.lean` |

**2026 note — corrected framing, then proved.** An earlier round of this file claimed FW.2
faced "the same obstruction as `g0_HS_contact_value`" (Baxter Wiener–Hopf). That was wrong —
`g0_bmcsl` reduces at N=1 to the Carnahan-Starling value `(1-η/2)/(1-η)³`, not the PY value
`(1+η/2)/(1-η)²` that `g0_HS_contact_value` axiomatizes, and is *used as a definition* in this
codebase (no independently-computed multi-species PY/Baxter solution exists to compare it
against). The real open content was the thermodynamic consistency identity numerically checked
by `verify_wc.py`'s `wc2()` — proved exactly (not axiomatized) via `bmcsl_virial_eq_fmt_pressure`,
assembled from a `HasDerivAt` chain along the density-scaling ray (`wbPhi_ray_pressure_eq`) and
a `Finset` double-sum moment reduction (`g0_bmcsl_virial_sum_eq`). See
[proof_notes_free_energy.md](proof_notes_free_energy.md) for the full derivation.

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
