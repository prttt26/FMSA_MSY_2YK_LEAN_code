# MSA_and_1st_Truncation — task status

Condensed on 2026-10-22 from the workspace files `todo_lean.md`, `todo_foundations.md`,
`todo_fmsa.md`, `todo_exact_msa.md` and `to_python.md`. Completed groups are reduced to
one line each; open and partial items are kept. The full pre-condensation text is in
this repository's history: `git show c95cad3:todo_lean.md` (likewise for the other four
file names). Detailed proof records are in `proof_notes/`; the math-axiom registry is
`proof_notes/MATH_AXIOMS.md`. Paper-specific obligations (F1–F6) are tracked in the
paper repository's `md/FORMALIZATION_TODO.md`; their Lean scope is in
`formalization/README.md`.

Directory layering and naming rules: `CONVENTIONS.md`.

Verification: `lake build` and `python3 formalization/check.py`. Re-derive any count
below from the source, not from this file.

## Axiom and sorry ledger (re-derived 2026-10-22)

`grep -rn "^axiom [a-zA-Z_]" LeanCode --include=*.lean` gives 11 hits; three are prose
lines (`PYOZ_GHS.lean`, `HalfDiskArgumentPrinciple.lean`, `MixturePoleExhaustion.lean`).
No `sorry` in the package. `FMSAPaper/` uses only the standard three axioms.

| Kind | Axiom | File | Status |
|---|---|---|---|
| math MA.1 | `circleIntegral_eq_sum_of_small_circles` | `Analysis/ContourDeformation.lean` | live; Mathlib has no winding number / residue theorem |
| math MA.1 | `halfDiskBoundary_eq_sum_of_small_circles` | `Analysis/ContourDeformation.lean` | live; same gap |
| math MA.7 | `sokhotski_plemelj_upper` | `Analysis/SokhotskiPlemelj.lean` | live, **no consumer** (deletion candidate) |
| math MA.13 | `wiener_causal_resolvent` | `Analysis/WienerRenewal.lean` | live; Wiener 1/f for the causal L¹ algebra |
| math MA.14 | `zeroFree_lowerHalfPlane_of_homotopy` | `Analysis/ZeroCountHomotopy.lean` | live; parametric argument principle |
| math MA.15 | `radialShell_bounded_injective` | `Analysis/RadialWienerHopf.lean` | live; L∞ Wiener–Hopf injectivity |
| math MA.15 (matrix) | `matRadialShell_bounded_injective` | `Analysis/MatrixRadialWienerHopf.lean` | live; matrix analog |
| physics | `pyhs_mixture_no_spinodal` | `HSMixture/MixtureNoSpinodal.lean` | live; consumed by the unequal-σ mixture RDF uniqueness capstone; redundant at N=1 |

Retired (now theorems): the six SymPy-certified computation axioms (`exactMSA_hcore`,
`exactMSA_kspace_residual`, `matExactMSAEqualDiam_hcore`,
`matExactMSAEqualDiam_kspace_residual`, `matExactMSAUnequalDiam_hcore`,
`matHSexactUnequalDiam_kspace`; 2026-10-09 legacy migration, see
`proof_notes_msa_exact.md`), MA.8, OZ.10, OZ.20 `pyhs_no_spinodal`, `oz_core_closure`,
`oz_h_exterior_regularity`, 6h/7a/7b, `Q0_moment_det_pos`, `baxter_no_open_lhp_pole_core`.

Before re-checking a "Mathlib gap" justification, re-verify it against the pinned Mathlib;
gap claims go stale (MA.8 was retired that way).

## Open and partial items

| Item | Track | State | Notes |
|---|---|---|---|
| Instability before fold | exact MSA / paper | paper proof + numerics | Any hard-core mixture, any tails, any instability mode: along the branch from τ=0 no fold occurs before the first τ at which det(I−C(k)) = 0 for some real k (Parseval on disjoint supports of δc, δh + canonical Wiener–Hopf uniqueness). Pointwise I−C(k) ≻ 0 is NOT sufficient: the A<0 continuation keeps it and does fold, but there the factor is non-canonical and the BH root is no longer an OZ solution. Record: `proof_notes_msa_exact.md` §8c; numerics `results/instability_before_fold/` (11 folds, density and composition modes; the k≠0 mode is untested). Open: strictness at the instability itself; the bridge BH residual ↔ OZ problem in Lean; Lean statement. |
| Single-tail spinodal before fold | paper | open (reduced) | Follows from the row above once the first instability of one attractive tail is shown to be at k = 0 (no k≠0 zero of F(ik) before A = 0). The 10⁴-point grid of `A(fold) < 0` is the only evidence so far. |
| Multi-tail fold binding | paper | open | 2YK: radius = fold numerically; no proof (no 1D reduction). Competing tails: complex branch points bind (F5). |
| F5, F6 | paper | certified (interval arithmetic) | Computer-assisted proofs in `formalization/certificates/`, not Lean. SI wording pending in the paper session. |
| MA axioms above | foundation | live | Retirement only if Mathlib gains the machinery or a narrower statement is found. MA.7 can be deleted if it stays consumer-less. |
| OZ.3 layer (3) | foundation | do-not-attempt boundary | Full damped-exponential `g₀_HS(r)` via `oz_h_eq_spliced_h_explicit` needs `hcollapse` (circular, OZFIX.14) and `hcont_sigma` (false as stated, OZFIX.7). Contact value and Laplace identity are proved. |
| POLE.10 | foundation | open | Pole-family exhaustion (all UHP zeros, injective, non-degenerate mirror pairing). Only needed for the residue-series `hcollapse` routes. |
| OZFIX.9, .10, .12, .13, .17, .18 | foundation | parked / partial | Residue-series route to `OzFixedPt`. Done: OZFIX.11 (`r ≥ 2σ`), OZ★ route OZFIX.15–22 (retired `oz_core_closure`), core form of OZFIX.18. Open: Route A (OZFIX.9), arc vanishing (OZFIX.10), `σ<r<2σ` assembly (OZFIX.12), endpoint wiring (OZFIX.13), 1D/3D transform obstacle (OZFIX.17). No capstone depends on these. |
| BAXTER.2, CONTACT.1 | foundation | parked | Absorbed into the POLE/OZFIX route. |
| MSAEXACT.3 | exact MSA | core done | Unique physical root below a coupling threshold; threshold `βK≈3` measured, not proved. |
| FOEQ.5 (general N), MSAFAM.5–.7 | exact MSA | re-audit | Their stated blockers (MSAEXACT.6, MSAEMIX.6) are now proved; status not re-audited after the 2026-10-09 retirement. |
| MSAMULTI automatic mixture certificate | exact MSA | open | General positive-density canonical nonzero-coupling branch, automatic finite Wronskian certificate in the general positive-density case; see the late sections of `proof_notes_msa_exact.md`. |
| MPhase 1 remainder (leg-3-mix) | exact MSA | deferred | `s=z` value, `T_n` moments, complex-`s` lift; do when consumed. |
| MRS.8 | FMSA | deferred | Identify `Ĉ₀ = I − Q̂₀(k)Q̂₀ᵀ(−k)` with the physical mixture HS DCF transform; off the critical path. |
| MRS.2, MRS.4 | FMSA | backbone / core done | Remaining physical-route wiring; the finite closed form (MRS.5) does not depend on it. |
| GAP.8 | FMSA | vacuous | `poly_coeff_from_laurent` asserts only that five reals exist; its target `P_ij` was falsified for unlike pairs (MPOLY.4/.5), so it stays a recorded vacuity. |

## Future plans

| Item | Track | Goal | Notes |
|---|---|---|---|
| Exact convergence condition | paper | State exactly when the HS-reference coupling series converges at a given state: the radius `R_c` as the distance to the nearest singularity of the physical branch in the complex τ plane, characterised in terms of the BH system (real fold, complex branch point, or other), not only bounded. | Known: `R_c ≤` fold (F2), `R_c =` fold for one tail (1.0.11), `R_c <` fold for competing tails via complex branch points (F5). Missing: the general characterisation and a decidable criterion. |
| Tail conditions for radius = fold | paper | Identify, and prove, the conditions on the tails (signs, rates, amplitudes, mixtures) under which the convergence boundary coincides exactly with the real fold. | Sufficient so far: one species, one attractive tail (Pringsheim via all-order coefficient signs). Counter-class: competing tails (F5). Candidate: tails for which all Taylor coefficients of the branch are nonnegative (Pringsheim then puts the nearest singularity on the positive real axis). |

## Completed groups (one line each)

| Group | Track | Content | Main files | Notes |
|---|---|---|---|---|
| MA (.2–.6, .8–.12, .16) | foundation | Mittag-Leffler, one-pole Fourier kernel, van der Corput, Jensen counting, radial Fourier inversion, Volterra, argument principle, positive-symbol Wiener–Hopf, Leibniz with variable limit; MA.8 retired by Mathlib's Poincaré lemma | `Analysis/` | MATH_AXIOMS.md |
| 2, 3 | foundation | HS Baxter factor identities; `B₁+D₁=T_U`, support of `T_S` | `HardSphere/BaxterFactor`, `YukawaOZ/Splitting` | hard_sphere |
| M (.1–.11) | foundation | Multi-component `Q̂₀`: identity, N=1 limit, `det ≥ 1` unconditional, rank-two reduction | `HSMixture/MatrixQ0`, `Q0DetRankTwo` | matrix_q0 |
| OZ (.1, .2b, .4, .6–.10, .18, .19) | foundation | PY DCF, exterior OZ, radial convolution theorem, sine-transform closed form, OZ fixed-point uniqueness (math axioms only), dilute Banach, `λ_ij` kink and inner flatness | `HardSphere/`, `HSMixture/CHSFlatInner` | hard_sphere |
| BAXTER.1, .3 | foundation | Real-space Baxter identity; Wiener–Hopf factorization | `HardSphere/BaxterRealSpace`, `BaxterWienerHopf` | baxter |
| CONTACT.2–.5 | foundation | `g₀_HS(σ) = (1+η/2)/(1−η)²` via jump asymptotics, now a theorem | `HardSphere/JumpAsymptotic` | contact |
| POLE.1, .3–.9 | foundation | Entire `Q̂`, unconditional infinite pole family, residues, magnitude bound, chord family | `HardSphere/Baxter{Zeros,Poles,Residue,PoleFamilyConcrete,ChordFamily}` | pole |
| OZFIX.1–.5, .7, .8, .11, .14–.16, .19–.22, .24 | foundation | Termwise machinery, `r≥2σ` collapse, circularity proof, OZ★ real-space route, retirement of `oz_core_closure` | `HardSphere/` | ozfix |
| MIXCHS.1–.7-N | foundation | Mixture `c_HS` seed and value routes, all diameter cases | `HSMixture/`, `YukawaOZMix/MixtureBaxterODE*` | hs_mixture |
| F, FW | foundation | Free-energy integrals and convergence; White-Bear FMT/BMCSL consistency (F.4 deleted as a route-inconsistency measure) | `FreeEnergy/`, `HSMixture/WhiteBearFMT` | free_energy |
| 1, 4, 5, C, GAP (.4–.7, .10) | FMSA | I₁/I₂ integrals, N=1 reduction, contact matching (structural only; physical claim disproved), origin BC, degree ≤ 4 (GAP.9 falsified: `D_ij ≡ 0`) | `YukawaOZ/`, `YukawaOZMix/MixturePolyCoeffs` | yukawa_dcf |
| IB.1–.9 | FMSA | Mediated breakpoints; first-order DCF knot set `{λ_ij}` | `YukawaOZMix/InnerDecomp`, `MixtureConvolution` | breakpoints |
| Y1.1–.7 | FMSA | Wiener–Hopf first-order RDF/DCF, doubly propagated amplitude `Q̂₀⁻¹ K Q̂₀⁻ᵀ`, all axiom-clean | `YukawaOZMix/SpectralAmplitude`, `YukawaWienerHopf` | yukawa_wh |
| MML (.1, .2, .4–.13, .16) | FMSA | Mittag-Leffler RDF; MML.8 closed by the value route `matOzStar_unequalDiam_unique_uncond`; literal pole-series collapse provably blocked; MML.14 superseded | `YukawaOZMix/MixtureRDF*` | mixture_rdf |
| MZERO.1–.12 | FMSA | Infinitely many `det Q̂₀` zeros (two routes), physical instantiation; RDF-only | `HSMixture/MixtureChordFamily`, `MixtureZerosPhys` | mixture_rdf |
| MRS.3, .5–.7, .9 | FMSA | (★) `Ĉ₁ = Q̂₀(−k)B₁Q̂₀ᵀ(−k)`; finite closed form, general N, axiom-free | `YukawaOZMix/Mixture{RealSpace,ClosedForm,DCFSmooth}` | mixture_dcf |
| MPOLY.1–.3 | FMSA | Order-4 Taylor calculus survives; MPOLY.4/.5 not completable (premise falsified) | `Analysis/Taylor4Calculus` | mixture_dcf |
| chsY, P, GA.1–.3 | FMSA | Method-failure analyses (GA.4 retired) | `FMSAPoly/` | failures |
| General-N det, L² matrix WH | FMSA | `mixtureDet_pole_free_N` for all N; matrix Plancherel Wiener–Hopf | `HSMixture/MixtureDetGeneralN`, `Analysis/MatrixWienerHopf` | mixture_rdf |
| MSAEXACT.1, .2, .4–.6 | exact MSA | Scalar exact MSA factorization, elimination, PY anchor, FMSA = first-order MSA; `hcore` now a theorem | `YukawaOZ/MSA*` | msa_exact |
| MSAEMIX.0–.7 | exact MSA | Mixture positivity, factorization (both diameters), Fin 1 reduction, root selection, breakpoints, `C^∞` BH root at K=0 (both diameters, unconditional) | `YukawaOZMix/MSAMixture*` | msa_exact |
| BRK | exact MSA | All-order mixture core knot structure; `baxterConvCore = matCoreUneq` axiom-free | `YukawaOZMix/MSAMixtureBreakpoint*` | breakpoints_MSA |
| FOEQ.1–.4, .6–.9; FOEQ.5 at N=1 | exact MSA | The two definitions of "first order" agree at every order | `Closures/FirstOrderEquivalence`, `MSASolutionFamily` | Other_Closures `proof_notes_closures.md` |
| leg-3, leg-3-mix (MPhase 1–9) | exact MSA | Blum–Høye (29)/(33) derived from OZ/Baxter primitives, scalar and all unequal σ | `YukawaOZ/MSABlumHoyeDerivation`, `MSAGSideOZ`, `YukawaOZMix/MixtureBlumHoyeDerivation` | leg3_* |
| MSAMULTI, MSABSource | exact MSA | Arbitrary finite Yukawa tails, finite source hierarchy, nonlinear reconstruction | `YukawaOZMix/MSAMultiTail*`, `MultiTailMSAProject.lean` | msa_exact |
| Single-tail fold binds (1.0.11) | paper | One species, one attractive tail: all coefficients nonnegative, radius = explicit fold, no hypothesis | `FMSAPaper/SingleTail*`, `QuarticBranch`, `AbsolutelyMonotone` | formalization/README.md |
| FMSAPaper F1–F4 | paper | All-order finite closed form incl. weak identity; radius ≤ fold; convergence ⇒ real branch; conditional Pringsheim equality | `FMSAPaper/` | formalization/README.md |

PYE and HNCB (other closures) are tracked in the separate Other_Closures project.

## Consequences for the Python code (condensed from `to_python.md`)

- The exact single-tail Yukawa-pole residue of the first-order amplitude is the doubly
  propagated `[Q̂₀⁻¹ K Q̂₀⁻ᵀ]_ij` (Y1.5/Y1.6), not `K·G`; `K·G·exp` in the old
  `get_c1_inner` was only a leading-order approximation.
- `det Q̂₀(z) ≥ 1` for all physical `z > 0` (M.4/M.8), so `np.linalg.inv(Q0)` on the
  positive real axis needs no regularization.
- The origin constraint `p₀ = −E_ij(0)` (Y1.7, MML.7) is exact; with the shifted basis
  `exp(−z r) − 1` it is automatic.
- Additive HS-pole corrections cannot cancel the unlike-pair `K·exp(zR)` growth (GA.1,
  GA.3); off-diagonal `G₀₁` decays exponentially (GA.2).
- The open "B_k for the doubly propagated base" question in `to_python.md` is moot: the
  inner DCF has no HS poles (MRS.3) and MML.8 is closed by the value route.
