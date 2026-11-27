# MSA_and_1st_Truncation

Lean 4 formalization accompanying R. Pan and J. Wu, *Analytical direct correlation functions for
hard-core Yukawa mixtures in the first-order mean spherical approximation*.

The subject is the mean spherical approximation (MSA) of additive hard-core multi-Yukawa mixtures and its
first truncation in the coupling (FMSA): why the first-order mixture direct correlation function (DCF) has a
finite closed form in real space, how it relates to the exact Blum–Høye solution, and what holds at higher
coupling orders. The numerical implementation and the data of the paper are in a separate repository,
<https://github.com/prttt26/fmsa_mixture>.

## What is verified

No `sorry`. Each statement holds under the hypotheses written in its declaration; the names below are in
namespace `FMSA`, except those in the top-level namespace `MSAMixture`.

| result | declarations |
|---|---|
| first-order PY and MSA closures are derivatives at zero coupling; the solution map is linear in the closure data | `FirstOrderClosure.py_first_order_outer`, `FirstOrderClosure.msa_first_order_outer`, `FirstOrderClosure.dpDCFLinear` |
| first coupling derivative of the Ornstein–Zernike product | `FirstOrderEquivalence.oz_deriv_eq_firstOrderLine` |
| the inverse Baxter factors cancel in the first-order DCF; the result has no hard-sphere poles | `MixtureBaxterCore.star_of_first_order_oz`, `.star_of_oz1_baxter`, `.star_entry_differentiableAt` |
| the hard-sphere determinant of the mixture has infinitely many zeros | `MixtureHSPoles.detC_zeros_infinite_phys` |
| the first-order RDF carries the inverse Baxter factors twice | `MixtureRDF.oz1_H1_eq` |
| finite real-space closed form, any number of species, no residual integral | `MixtureDCFSmooth.pbpConvG_eq`, `MixtureConvolution.pbp_edge_eq` |
| core breakpoints are contained in {λ_ij} | `MixtureConvolution.pbp_breakpoints_subset`, `MSAMixture.interior_breakpoint_eq_absLam`, `ExactMSA.Breakpoint.baxterConvCore_smooth_off_unique_breakpoint` |
| the reflected parity partners of the RDF are removed exactly by the causal projection | `ReflectedSupports.parity_partners_causal_projection_zero` |
| the first variation of the local Blum–Høye family equals the first-order construction, in real and Fourier space | `ExactMSA.MultiTailMixture.linearizedCorrelation_eq_dpCorrelation_ordered`, `.linearizedSpectralC_eq_all_pairs_ordered_radial` |
| first-order RDF, **under a decay condition** on its Volterra solution | `ExactMSA.MultiTailMixture.firstOrderMixtureRDF_certificate` |
| nonlinear reconstruction of a supplied Blum–Høye root, **under a weighted decay budget** | `ExactMSA.MultiTailMixture.nonlinearMixtureRDF_core_moments_decay_certificate`, `.nonlinearHS_actual_joint_certificate` |
| every coupling order: homogeneous coefficients, a fixed spatial basis, weak real-space relations, exterior tails | `Paper.ActualStrengthJets.actual_jets_homogeneous_polynomial`, `Paper.ActualBaxterJets.factor_jet_basis`, `Paper.BaxterWeakCauchy.fullPrimitive_weak_cauchy`, `Paper.ActualRadialWeakJets.normalized_local_root_weak_cauchy`, `Paper.PhysicalExteriorJets.exterior_jet` |
| the coupling series cannot converge beyond the fold; conditions for radius equal to fold | `Paper.FoldRadius.actual_radius_le_fold`, `.actual_nonconvergence_beyond_fold`, `Paper.TaylorRoot.exists_physical_taylor_convergence_theorem`, `Paper.SingleTailRadius.single_tail_radius_eq_fold` |
| pure fluid with positive tails: the Taylor radius is the fold coupling (library `MSAConvergence`) | `Convergence.PureFluidFoldTheorem.taylor_radius_is_fold` |

The paper's Supplementary Material gives the correspondence between its equations and these declarations.

## What is not verified

The Lean kernel checks proofs; it does not check that a statement matches the mathematics of a paper, and
nothing here concerns the physical accuracy of the closure, of the first-order truncation, of the
Lennard-Jones mapping or of any simulation or numerical result. Global existence and continuation of the
physical root, decay of the nonlinear solution at all states, non-negativity of g(r), consistency of
thermodynamic routes and coexistence accuracy are outside the statements. No general convergence boundary
is claimed for mixtures.

## Assumptions

Eight axioms beyond Lean's `propext`, `Classical.choice` and `Quot.sound`. Seven are statements of classical
analysis not available in the pinned Mathlib; one is physical. The exact dependencies of a theorem are given
by `#print axioms`, and the paper-level collection `FMSAPaper` uses the three standard axioms only.

| axiom | content |
|---|---|
| `circleIntegral_eq_sum_of_small_circles`, `halfDiskBoundary_eq_sum_of_small_circles` | contour deformation (residue sums) |
| `zeroFree_lowerHalfPlane_of_homotopy` | Rouché/Hurwitz homotopy: zero-freeness in a half-plane |
| `sokhotski_plemelj_upper` | boundary values of the Cauchy integral (Wiener–Hopf splitting) |
| `wiener_causal_resolvent` | integrable resolvent of a causal convolution equation |
| `radialShell_bounded_injective`, `matRadialShell_bounded_injective` | uniqueness of bounded exterior OZ solutions, scalar and matrix |
| `pyhs_mixture_no_spinodal` (**physical**) | the Percus–Yevick hard-sphere mixture factor is non-degenerate, det Q̂₀(k) ≠ 0 for real k ≠ 0, η < 1 |

Registry and history: `proof_notes/MATH_AXIOMS.md`.

## Layout

| path | content |
|---|---|
| `LeanCode/` | foundation: hard spheres, Ornstein–Zernike and Baxter factorization, one-component and mixture Yukawa solutions, closures, analysis tools |
| `FMSAPaper/` | theorems collected for the paper (all-order structure, Taylor radius, RDF), each with an axiom guard |
| `MSAConvergence/` | convergence of the coupling series; **not** a default build target |
| `formalization/` | audits (`audit_foundation.py`, `check.py`), certificates and validation records |
| `scripts/`, `results/` | numerical and SymPy checks behind some theorems, and their recorded outputs; evidence, not proof premises |
| `proof_notes/`, `TODO.md` | working notes and open items |
| `CHANGELOG.md` | per-version history |

Module names `LeanCode.*` and declaration names `FMSA.*` are stable.

## Build and check

Lean toolchain v4.31.0 (`lean-toolchain`); Mathlib `v4.31.0`, revision `fabf563a7c95`.

`lakefile.toml` sets `packagesDir = "../.lake/packages"`, so clone into an otherwise empty parent directory
(dependencies are placed in a `.lake/` directory next to the clone). Then

```bash
lake exe cache get
lake build                                   # LeanCode and FMSAPaper
python3 formalization/audit_foundation.py    # source and configuration hashes against release-manifest.json
python3 formalization/check.py               # paper modules, axiom guards, then the convergence library
```

A full build needs about 24 GB of RAM plus swap:
`LeanCode/YukawaOZ/ExactMSASparseDt2.lean` peaks at about 21 GB; building it on its own first
(`lake build LeanCode.YukawaOZ.ExactMSASparseDt2`) helps. `check.py` also builds `MSAConvergence`, one
process at a time under a 30 GB cap; `--skip-convergence` omits it.

Some scripts in `scripts/` import Python modules from the authors' research repository and run only there.
Lean inputs stored under `results/` use the suffix `.lean.txt` so that they are outside the hashed sources.

## Authorship of the formalization

The formal statements were written partly by hand and partly with Claude Code; the proofs were written with
Claude Code and Codex and are checked by the Lean kernel. The correspondence between statements and the
paper is the authors' responsibility.

## License

Apache License 2.0, see [`LICENSE`](LICENSE).
