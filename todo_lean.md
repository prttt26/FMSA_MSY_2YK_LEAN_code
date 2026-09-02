# Lean Proof Tasks: FMSA Yukawa Mixture Theory

This file is the **status index** for all Lean 4 + Mathlib proofs in `LeanCode/`.

> **⚠ Directory restructure (2026-08-06).** The layering was cleaned up (see `CONVENTIONS.md`):
> `Analysis/` + `FMSAPoly/` are the two bases; then `HardSphere/ → HSMixture/ → YukawaOZ/ →
> YukawaOZMix/`, with sinks `FreeEnergy/` and `Closures/`. Concretely: **`YukawaDCF/` was split and
> renamed** into `YukawaOZ/` (single-component + generic-scalar base, 11 files) and `YukawaOZMix/`
> (N-component mixture, 24 files) — "DCF" dropped since the layer also carries RDF/`g`/`h`/closures.
> **New `Closures/`** holds the non-FMSA closures (`FirstOrderClosures` split into
> `ClosureExpansions` + `DPClosureMap`). Reverse-reference back-edges fixed by moving `AppendixWDet`/
> `ArcAmplitudeBound` **down** to `HSMixture/` and `MixtureRowSum` **up** to `YukawaOZMix/`. Group
> names are directory-independent, so the tables below are unchanged; only *file paths* in prose that
> say `YukawaDCF/…` should be read as `YukawaOZ*/…`.

> **⚠ Layer/namespace coherence refactor (2026-08-17).** Every declaration now sits in its
> content-correct layer, and **each namespace lives in exactly one layer** (verified: no
> `namespace FMSA.X` is declared across >1 directory-layer). Relocations: `Splitting.lean`
> (Yukawa-kernel algebra `B₁+D₁=T_U`, not HS) `HardSphere/ → YukawaOZ/`; the four mixture-RDF files
> `MixtureYukawa{ContourTerm,Residue,Transform}` + `YukawaArcBound` `YukawaOZ/ → YukawaOZMix/`
> (single → mixture). Pure-math lemmas re-homed to `FMSA.Analysis`. Namespace splits (higher-layer
> decls → new ns; lower layer keeps the old name): new **L4** `FMSA.MixtureBaxter` (the mixture
> Baxter/OZ★ DCF-value route — 9 files, was `FMSA.MixtureOzStar`/`FMSA.HSMix`), `FMSA.MixtureMLSeries`
> (was L4 `FMSA.MixtureHSPoles`), `FMSA.MixtureYukawaWH` (was L4 `FMSA.YukawaWH`), `FMSA.MixtureRDFContact`
> (was L4 `FMSA.MatrixQ0`), `FMSA.MixtureHSDCF` (`RadialFourierQFwd` psi3 block, was `FMSA.HardSphere`);
> new **L2** `FMSA.MixtureArcBound` (was L2 `FMSA.MixtureRDF`), `FMSA.WhiteBear` (was L2 `FMSA.HardSphere`);
> **L3** `FMSA.InnerOriginBC` (was L4-shared `FMSA.MixturePoly`). See memory `project_layer_refactor`.

### Layer map — directory · namespaces · proof_notes · task groups

| Layer | Directory | Primary namespaces | proof_notes | Groups (dominant) |
|---|---|---|---|---|
| **L0** pure math | `Analysis/`, `FMSAPoly/` | `FMSA.Analysis`, `FMSA.<perfile>` | (MATH_AXIOMS.md) | MA |
| **L1** HS · single | `HardSphere/` | `FMSA.HardSphere` | hard_sphere, baxter, pole, ozfix, contact | 2, OZ, BAXTER, POLE, OZFIX, CONTACT |
| **L2** HS · mixture | `HSMixture/` | `FMSA.MixtureOzStar`, `MixtureHSPoles`, `MatrixQ0`, `HSMix`, `MixtureArcBound`, `WhiteBear` | matrix_q0, hs_mixture, mixture_rdf(MZERO), free_energy(FW) | M, MZERO, MIXCHS, FW |
| **L3** Yukawa · single | `YukawaOZ/` | `FMSA.YukawaWH`, `ExactMSA`, `InnerOriginBC` | yukawa_dcf, yukawa_wh(Grp 3), msa_exact | 1, 3, 4, 5, GAP, C, MSAEXACT |
| **L4** Yukawa · mixture | `YukawaOZMix/` | `FMSA.MixtureBaxter`, `MixtureRDF`, `MRS`, `MML`, `MixtureMLSeries`, `MixtureYukawaWH`, `MixtureHSDCF` | mixture_dcf, mixture_rdf, breakpoints | Y1, MML, MRS, MPOLY, MIXCHS(value), IB |
| **L5** applications | `FreeEnergy/`, `Closures/` | `FMSA.FreeEnergy`, `FirstOrderClosure`, `FirstOrderEquivalence`, `MSASolutionFamily` | closures, free_energy | FOEQ, PYE, HNCB, MSAFAM, F |
| *cross-cutting* | (method-failure analysis) | — | failures | chsY, P, GA |

Groups whose derivation legitimately touches two layers (e.g. **Y1**/WH: single-component base in
L3 `FMSA.YukawaWH` + matrix mixture form in L4 `FMSA.MixtureYukawaWH`; **MIXCHS**: HS-mixture `c_HS`
in L2 + Baxter-WH value route in L4) are listed under their *capstone* layer.

Detailed proof records (statements, proof sketches, pitfalls, Lean API notes) are in:

- [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) — Groups 2, 3, OZ (pure HS foundations)
- [proof_notes_baxter.md](proof_notes_baxter.md) — Group BAXTER (Baxter Q-factor + Wiener–Hopf route to the PY closed form)
- [proof_notes_matrix_q0.md](proof_notes_matrix_q0.md) — Group M (multi-component HS Baxter Q̂₀ matrix identity, rank-2 det reduction, det-positivity monotonicity M.5–M.8)
- [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) — Groups 1, 4, GAP, C, 5 (Yukawa DCF derivation)
- [proof_notes_breakpoints.md](proof_notes_breakpoints.md) — Group IB (inner-core mediated breakpoints)
- [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) — Group Y1 (first-order Yukawa RDF via Wiener–Hopf; the general foundation)
- [proof_notes_mixture_rdf.md](proof_notes_mixture_rdf.md) — Groups MML, MZERO (the N=2 mixture inner **RDF** `h₁` Mittag-Leffler HS-pole series + `det(Q̂₀)` zero family)
- [proof_notes_mixture_dcf.md](proof_notes_mixture_dcf.md) — Groups MRS, MPOLY (the N=2 mixture inner **DCF** as a finite closed form: real-space Baxter route + polynomial coefficients)
- [proof_notes_failures.md](proof_notes_failures.md) — Groups chsY, P, GA (method-failure analysis)
- [proof_notes_closures.md](proof_notes_closures.md) — Groups PYE, HNCB, **FOEQ**, **MSAFAM** (first-order PY / HNCB closures of the YK-tail FMSA-DP construction; **what "first order" means at all**; and **removing the hypothesis it is conditional on**)
- [proof_notes_msa_exact.md](proof_notes_msa_exact.md) — Groups MSAEXACT, MSAEMIX (the **exact** MSA closed form, Waisman / Blum–Høye / Ginoza: single component, then mixture)
- [proof_notes_free_energy.md](proof_notes_free_energy.md) — Groups F, FW (free energy integrals; White-Bear FMT/BMCSL)

**Source markers:**
- **[chsY]** — `pdf/FMSA_chsY.pdf` (analytical multi-species MSA solution)
- **[LN]** — `pdf/lecture_notes_OZ_Yukawa_poly.pdf`

---

## Open / Unfinished Items

*One line per item; details live in the linked `proof_notes_*.md`.*

### Sorries — actual `sorry` proof terms in source files

*(none)*

### Axioms — `axiom` declarations assumed without proof

**Math axioms (7)** — general-analysis facts, not physics-closure assumptions
(registry [MATH_AXIOMS.md](MATH_AXIOMS.md)). They split cleanly by Lean home, and the split is
**mechanically checkable** — both axiom tables on this page must stay in sync with

```
grep -rn "^axiom [a-zA-Z_]" LeanCode/ --include=*.lean | sed 's|LeanCode/\([A-Za-z]*\)/.*|\1|' | sort | uniq -c
```

⚠ **That grep spans math, physics *and* symbolic-computation axioms — it is the count for ALL axiom
tables on this page, not one alone.**
As of 2026-09-01 it returns **17 raw hits = 3 false + 14 real**:
3 false positives (prose lines that happen to begin `axiom `, in `PYOZ_GHS.lean`,
`HalfDiskArgumentPrinciple.lean`, and `YukawaOZMix/MixturePoleExhaustion.lean`) and 14 real axioms —
**7 math + 1 physics + 6 sympy-computation**. So the bucket counts are
**`Analysis` 7 (math) + `HardSphere` 0 + `HSMixture` 1 (physics) + `YukawaOZ` 2 + `YukawaOZMix` 4** —
the 1 HSMixture being `pyhs_mixture_no_spinodal` (physics), and the `YukawaOZ` 2 + `YukawaOZMix` 4
being the sympy-certified `exactMSA_hcore` / `exactMSA_kspace_residual` / `matExactMSAEqualDiam_hcore` /
`matExactMSAEqualDiam_kspace_residual` / `matExactMSAUnequalDiam_hcore` / `matHSexactUnequalDiam_kspace`
identities (the *Symbolic-computation axioms* table below).  The 7th math axiom (Analysis) is
`matRadialShell_bounded_injective` (`Analysis/MatrixRadialWienerHopf.lean`, MML.8 value route,
committed + **abstracted to `Analysis/` in raw-integral form 2026-07-30**: the matrix analog of the
scalar `radialShell_bounded_injective`, arbitrary matrix kernel; `MixtureRDFUniqueness.lean` re-exposes
it as a theorem via definitional bridges → `matOzStar_unique`). The 7 math axioms:

* **`Analysis/` (6)** — general-purpose, project-independent Mathlib vocabulary: MA.1 (×2), MA.7,
  MA.13 (`wiener_causal_resolvent`), `radialShell_bounded_injective` (OZ.10, **abstracted to an arbitrary kernel `C` and
  migrated here 2026-07-19**), and `zeroFree_lowerHalfPlane_of_homotopy` (**MA.14, abstracted +
  migrated here 2026-07-21** when `baxter_no_open_lhp_pole_core` was retired — see below).
* **`HardSphere/` (0)** — ✅ **`HardSphere/` now contains no domain-referencing axiom at all.** The
  last one, `MA.14 baxter_no_open_lhp_pole_core`, was **RETIRED to a theorem 2026-07-21** via the
  `η`-homotopy of the open-lower-half-plane zero count (`BaxterLowerHalfPlane.lean`), leaving only the
  abstract `zeroFree_lowerHalfPlane_of_homotopy` in `Analysis/`. The whole OZ exterior-regularity
  cluster (6h, 6j, 7a, 7b) was already axiom-free.

⚠ **Count history.** This header read `9` while the table listed `10` rows — the 7a/7b split of
`ozExterior_smooth_deriv` was never added to it. Reconciled 2026-07-19: `10 → 9` by retiring 6h, then
**`9 → 8` by retiring 7a `ozExterior_smooth_repr`, then `8 → 7` by retiring 7b
`ozExterior_deriv_integrable`** (`OZFIX.25`: both proved via (★DIFF), the differentiated renewal
equation; 7b's three summands via compact support, the proven `ψ ∈ L¹`, and Mathlib's Young). Then
**`7 → 6` by retiring MA.8 `contourIntegral_eq_of_homotopic_loops` 2026-07-24** — its "Mathlib lacks
homotopy/winding machinery" gap **closed** upstream (Mathlib `v4.31.0` gained the Poincaré lemma for
`1`-forms, `CurveIntegral/Poincare.lean`); the content is now the axiom-free bundled `C²` theorems in
`Analysis/ContourHomotopy.lean`. **Re-derive the count from the `grep` above, not from this
header.**

The **exterior OZ integrability cluster (6g/6h/6j) is now entirely axiom-free**: 6g was proved from
the start, clause 6j (`ozExterior_conv_sin_integrable`) was DERIVED from 6h (2026-07-19), and 6h
(`ozExterior_triple_shell_sin_integrable`) was **RETIRED to a theorem 2026-07-19** (`OZFIX.24`) — it
had been axiomatized on an **effort** argument ("formalizing the triple `lintegral` chain is
substantial"), not a gap argument, which put it in tension with Group MA admissibility rule (c).
Proving it — rather than abstracting a side condition — was the right call, as with MA.10/11/12.
**Triage heuristic for the remaining 6: an axiom whose docstring justifies itself by effort *and*
supplies its own proof sketch is a retirement target; one that cites a genuine Mathlib gap (no Wiener
algebra, no winding number, no P.V. API, no L∞ Plancherel) is not.** ⚠ **Gap justifications go stale —
re-verify against the *current* Mathlib, not the docstring's date.** Recon 2026-07-24 (`Explore` sweep
of `.lake/packages/mathlib`, `v4.31.0`) **re-confirmed the gaps for MA.1, MA.7, MA.13, MA.14, MA.15
are still real** (no winding number, argument principle, Rouché, residue theorem, Hurwitz, Wiener
algebra, or P.V./Hilbert transform), but found **MA.8's gap had closed** (new `CurveIntegral/Poincare.lean`)
⇒ MA.8 retired. Cauchy higher-derivative formulas are also present now (no MA-axiom uses them);
`meromorphicOrderAt`/`divisor` exist but are **not** linked to any contour integral (so the
argument-principle gap that MA.14 rests on stands).

| Task | Axiom | File | Meaning / proof path |
|------|-------|------|----------------------|
| MA.1 | `circleIntegral_eq_sum_of_small_circles` | `Analysis/ContourDeformation.lean` | Keyhole/slit contour deformation: a big circle's integral = the sum over finitely many disjoint off-center hole circles. Mathlib has no winding number / residue theorem. Powers the genuine theorem `circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles` and MA.11. See [MATH_AXIOMS.md](MATH_AXIOMS.md). |
| MA.1 | `halfDiskBoundary_eq_sum_of_small_circles` | `Analysis/ContourDeformation.lean` | Same deformation for the **upper half-disk** boundary (`[−R,R]` + arc) — the shape Fourier inversion closes; provably not reducible to the circle axiom. Powers `halfDiskArgumentPrinciple_sum`. See [MATH_AXIOMS.md](MATH_AXIOMS.md). |
| MA.7 | `sokhotski_plemelj_upper` | `Analysis/SokhotskiPlemelj.lean` | Sokhotski–Plemelj upper boundary value, integrated form (P.V. existence taken as a hypothesis, so no distribution theory). Mathlib has no Hilbert-transform / P.V. API. **No consumer yet.** See [MATH_AXIOMS.md](MATH_AXIOMS.md). |
| MA.13 | `wiener_causal_resolvent` | `Analysis/WienerRenewal.lean` | **Wiener's `1/f` theorem** for the causal `L¹` convolution algebra `ℂ·δ ⊕ L¹(0,∞)` (maximal ideal space = closed RHP, Gelfand transform = Laplace transform): symbol `1−q̂` nonvanishing there ⇒ causal resolvent `R ∈ L¹`, `R = q + q ⋆ R`. **Reshaped 2026-07-21** from the former bespoke `volterra_renewal_tendsto_zero`, which is **now a THEOREM** proved from this: resolvent formula (Fubini) + `MA.10` uniqueness + moving-window `L¹` tail (decay) + Young (integrability). Irreducible: `‖q‖₁ > 1` in the physical regime so the Neumann series diverges; Mathlib has no Wiener algebra / Laplace transform / Paley–Wiener / Hardy spaces (re-verified 2026-07-21). See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.13 and `proof_notes_pole.md` POLE.11 decay half. |
| MA.14 | `zeroFree_lowerHalfPlane_of_homotopy` | `Analysis/ZeroCountHomotopy.lean` | **Homotopy invariance of the open-lower-half-plane zero count** (argument principle / Hurwitz): a jointly-continuous family of entire functions `H t`, with all closed-LHP zeros inside `‖z‖<R` and never vanishing on the real axis, keeps its open-LHP zero-freeness from `t=a` to `t=b`. Fully general (no Baxter/Yukawa), abstracted here 2026-07-21. Mathlib has **neither Rouché nor the parametric argument principle**. **Retired the former domain axiom `baxter_no_open_lhp_pole_core`**, which is now a THEOREM (`BaxterHermiteBiehler.lean`) proved by the `η`-homotopy `Qhat_complex_ne_one_of_im_neg` (`BaxterLowerHalfPlane.lean`). See [MATH_AXIOMS.md](MATH_AXIOMS.md) and `proof_notes_pole.md` POLE.11-general. |
| MA.15 | `radialShell_bounded_injective` | `Analysis/RadialWienerHopf.lean` | **L∞ Wiener–Hopf injectivity** for a radial shell operator with an *arbitrary* kernel `C` supported in `[0,σ]` and coercive symbol `1−ρĈ ≥ ε>0`. **Abstracted + migrated to `Analysis/` 2026-07-19** — the concrete `oz_linear_op_bounded_injective` is now a THEOREM instantiating it at `C := c_HS` (support from `c_HS_outer`; `radial_fourier`/`oz_linear_op` unfold definitionally). The L∞ analog of the *proved* (L²) MA.12: Plancherel coercivity does not survive to L∞, so the space — not the physics — is why this one is assumed. ⚠ `hCsupp` is load-bearing (symbol integrates `(0,∞)`, the operator only `[0,σ]`; false without it). Consumer: `OZ.10`. See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.15. |
| MA.15 (matrix) | `matRadialShell_bounded_injective` | `Analysis/MatrixRadialWienerHopf.lean` | The **matrix** analog of MA.15: L∞ Wiener–Hopf injectivity for a radial shell operator with an *arbitrary* `N×N` matrix kernel `C` and coercive symbol. **Committed + abstracted to `Analysis/` in raw-integral form 2026-07-30** (MML.8 value route); `MixtureRDFUniqueness.lean` re-exposes it as a theorem via definitional bridges → `matOzStar_unique`. Same L∞-Plancherel gap as the scalar. See [MATH_AXIOMS.md](MATH_AXIOMS.md). |

**Physics axioms (1)** — one axiom for the *mixture* track, **NOW CONSUMED (2026-08-20)** by the
general-`N` unequal-σ RDF uniqueness capstone `matOzStar_unequalDiam_unique_uncond` (via the
coercivity's middle-region `det Q̂₀ ≠ 0`).
✅ **The single-component track is still at ZERO physics axioms**: `pyhs_no_spinodal` (OZ.20) was
retired **2026-07-19**; the mixture axiom stays inert for every SCALAR result
(`#print axioms g0_HS_contact_value` does not list it) — but the mixture RDF capstone now legitimately
rests on it (same footing as MA.15). It is **no longer** "pre-placed, consumer-less".

| Task | Axiom | File | Meaning / why axiomatized |
|------|-------|------|---------------------------|
| MRS.0 | `pyhs_mixture_no_spinodal` | `HSMixture/MixtureNoSpinodal.lean` | **Only physics axiom; NOW CONSUMED (2026-08-20)** by `matOzStar_unequalDiam_unique_uncond`. `det Q̂₀(ik) ≠ 0` for real `k≠0`, N-component (⟺ the now-proven scalar `pyhs_no_spinodal`); needs PHYSICAL coeffs (free `Qp/Qpp` ⇒ FALSE). `n=1` bridge proves it REDUNDANT there (`pyhs_mixture_no_spinodal_n1`, std-3). Not scalar-`k⁶`-provable (needs a winding argument, MA.14-class). Full detail → [MATH_AXIOMS.md](MATH_AXIOMS.md). |


### Numerically verified — not proved in Lean

*(The three axioms that carry a numerical witness. Standard-math axioms — the two contour-deformation
MA.1's, S–P MA.7, homotopy-Cauchy MA.8, L∞ Wiener–Hopf MA.15 — are not "numerical" and are omitted.)*

| Axiom (task) | Claim | File | Numerical witness |
|------|-------|------|-------------------|
| `wiener_causal_resolvent` (MA.13) | Wiener `1/f`: symbol `1−q̂ ≠ 0` on the closed RHP ⇒ causal resolvent `R ∈ L¹`, `R = q + q⋆R` | `Analysis/WienerRenewal.lean` | `verify_ma13_route.py`: spectral radius `=‖q‖₁>1` (Neumann diverges); simulated renewal decay rate `= Im k₁` (Ornstein–Zernike), `ψ ∈ L¹` |
| `zeroFree_lowerHalfPlane_of_homotopy` (MA.14) | Argument-principle/Hurwitz: open-LHP zero count is homotopy-invariant | `Analysis/ZeroCountHomotopy.lean` | `verify_ma14_route.py`: deflated zero count `= 0` (robust in `R,ε,η`); two elementary routes refuted at `k=−it₀` |
| `pyhs_mixture_no_spinodal` (MRS.0) | `det Q0_mat_c_phys(ik) ≠ 0` for real `k≠0`, N-component | `HSMixture/MixtureNoSpinodal.lean` | 300 mixtures × 4 `k` × `N=1..4`, two det routes agree `2e-15`; `min_k\|det\| ≥ 0.375`; `n=1` bridge PROVED redundant |

### Symbolic-computation axioms (sympy-certified exact polynomial identities)

*A distinct category — **not** physics assumptions and **not** missing-Mathlib math. Each is a specific
exact polynomial identity that is provable IN PRINCIPLE but that `ring`/`linear_combination` cannot
normalize in feasible time. **Measured 2026-08-22:** one `(cos,sin,exp)`-graded deg-≈22 slice (323
monomials) costs `ring` **3 h 12 m / 23 GB**; the irreducible per-order reassembly extrapolates to
~weeks / ~200 GB; `native_decide` is blocked (`MvPolynomial` semiring noncomputable). So they are
certified externally by **exact** (rational, not floating-point) symbolic computation and asserted as
axioms — the honest `ring`-scale boundary, not a heartbeat budget.*

| Axiom (task) | Claim | File | sympy certificate |
|------|-------|------|-------------------|
| `exactMSA_hcore` (MSAEXACT.6) | scalar Blum–Høye closure-recovery ring `ρ(𝓕[c_core]+𝓕[c_tail]) = 2Dt·X − Dt²·Y` on the BH manifold | `YukawaOZ/MSAFullFactorization.lean` | `exactMSA_cert.py`: `Δ = m29·r29 + m33·r33`, polynomial-division remainder 0. Its Fourier layer IS discharged (out-of-build `ExactMSACertificate.lean` reduces it to `exactMSA_kspace_residual`) |
| `exactMSA_kspace_residual` (MSAEXACT.6) | the same identity with both radial transforms in **closed cos/sin/exp form** (no `radial_fourier`) — the pure-algebra residual | `YukawaOZ/ExactMSACertificate.lean` (**out of `defaultTargets`**, lib `ExactMSACertificate`) | same `exactMSA_cert.py`; `exactMSA_hcore_of_residual` derives the original axiom's exact statement from this (`#print axioms` = std-3 + this) |
| `matExactMSAEqualDiam_hcore` (MSAEMIX.4/.1) | matrix analog of MSAEXACT.6 at general `N`, **equal σ** — closes MSAEMIX.1 at equal diameter | `YukawaOZMix/MSAMixtureBHRoot.lean` | `msaemix_hcore_cert.py` + `msaemix_core_coeffs.py`: mixture core = scalar 5-basis with Σ_l-coupled coeffs (all 5 cracked, held-out 1e-16) |
| `matExactMSAEqualDiam_kspace_residual` (MSAEMIX) | Fourier layer of the equal-σ mixture ring in closed cos/sin/exp form — the pure-algebra residual (matrix analog of `exactMSA_kspace_residual`) | `YukawaOZMix/MatExactMSAEqualDiamCertificate.lean` (**out of `defaultTargets`**, lib `MatExactMSAEqualDiamCertificate`) | same mixture cert; reduces `matExactMSAEqualDiam_hcore` to this residual |
| `matExactMSAUnequalDiam_hcore` (MSAEMIX.4) | matrix analog at general `N`, **unequal σ** — closes MSAEMIX.1 at unequal diameter (piecewise `matCoreUneq` at `\|λ_ij\|`) | `YukawaOZMix/MSAMixtureBHRootUneq.lean` | `msaemix_uneq_*` + `baxterConvCore_eq_matCoreUneq` (BRK.13 seam); real-space Baxter-convolution core, symbolic-σ, case-split-free |
| `matHSexactUnequalDiam_kspace` (MSAEMIX.1) | unequal-σ HS Baxter–Fourier anchor `cHShatUneq = √(ρᵢρⱼ)·𝓕[matCoreHSuneq]` — the coupling-`0` sibling of `matExactMSAUnequalDiam_hcore`, puts the HS DCF in `radial_fourier(Φ_HS)` form | `YukawaOZMix/MSAMixtureBHRootUneq.lean` | sympy-backed (the physical real-space HS DCF is the transform of the Baxter-`Q̂` combo) |

### Conditional-theorem hypotheses — ✅ all resolved (ledger)

*Theorems that were proved carrying one explicit open hypothesis (`theorem T (h : …) : P`, not a
bare `axiom`). **As of 2026-07-17 the live table is empty — every tracked hypothesis has been
discharged, closed, or falsified.** Kept below as a disposition ledger for traceability; do not
re-open. Genuine axioms live in the Axioms table above.*


### Open tasks

**Single-component / HS-Baxter track: essentially closed as of 2026-07-21.** The former big open
items are done — see *Recently closed* below. The **mixture** RDF assembly (**MML.8**) is
**FULLY CLOSED, general `N`, unequal σ, UNCONDITIONALLY (2026-08-20)** —
`matOzStar_unequalDiam_unique_uncond` (`YukawaOZMix/MixtureRDFUnequalDiam.lean`): two `MatOZStar`
solutions with the physical symmetric forcing `PhiSymN` coincide on `r>0` from ONLY physical data
(`0<σᵢ`, `0<ρᵢ`, `η<1`, `0<ρ`) + routine solution regularity. **`#print axioms` = std-3 +
`matRadialShell_bounded_injective` (MA.15) + `pyhs_mixture_no_spinodal`** — the SAME two axioms as the
equal-diameter capstone, no `sorry`. The coercivity is now a proved theorem `matSymbolCoercive_PhiSymN`
(no longer a hypothesis): near-`0` `matDCF_hfac0` (origin Gram via `ext_on`, `det Q0_mat_c_repr(0)≠0`,
std-3), middle `matDCF_hfack` (T-symmetry Gram, std-3) + no-spinodal, tail `htail`
(`|matRadialSymbol|≤(4π/|k|)∫|r·Φ|` decay). ⭐ the feared reverse-geometry ODE port was ELIMINATED via
the DCF a.e.-symmetry `matDCF_ae_symmN` (already axiom-clean). Earlier route landmarks: the abstract
value route `matOzStar_unique` (2026-08-11, `MixtureRDFUniqueness.lean`, conditional on the coercive
symbol); MIXCHS.6/7/7-N (`shellForcing = cMixDCF`, the Baxter–WH `hODE`, all diameter cases). The
equal-diameter capstone is `matOzStar_equalDiam_unique` (rank-1 coercivity).

| Task | Title | Depends on | Notes |
|------|-------|-----------|-------|
| `MSAEXACT.1–6` *(msa_exact)* | Exact MSA closed form, single component | MSAX.1 gate 0 ✓ | ◑ **.1(→ reduced to .6)+.2+.3(core)+.4+.5 done; .6 = `hcore` ring `ring`-INFEASIBLE (measured 2026-08-22; Fourier layer discharged via out-of-build `ExactMSACertificate`, residual = 1 pure-algebra axiom `exactMSA_kspace_residual`)**; ⛔ compact `exactMSA_iff_core` route dead. See the Task-Status table → [msa_exact](proof_notes_msa_exact.md) |
| `MSAEMIX.0–3` *(msa_exact)* | Same at general `N` (matrix) | UNGATED 2026-08-19 | ◑ **.0+.1(dp)+.3 done; .1 staged to matrix `hcore`** (`matMixtureFactorization_of_core`, analog of MSAEXACT.6); .2 factorization half ← .1. → [msa_exact](proof_notes_msa_exact.md) |
| `PYE.4` *(closures)* | Abstract equivalence `DP-map[g_HS·(−βu)] = OZ+PY first order` — the **function-space lift** | PYE.1–3, PYE.5–7 ✓ | ◑ **substantially reduced 2026-08-03**: the lift is now built except for ONE named classical input. Proved: half-line uniform + **L¹** tail-fit density (`exists_yukawa_tail_fit_halfLine`/`_L1`), the transform stage `‖Û₁(k)‖ ≤ ‖Ψ‖_{L¹}` uniformly in k (`norm_transform_le_L1`), and the reduction `tailFitWHConvergent_of_L1_tendsto` + capstone `exists_tailFit_whConvergent` — so `TailFitWHConvergent` is **derived**, not assumed. … → [closures](proof_notes_closures.md) PYE.4 |
| `FOEQ.1–9` *(closures)* | The two "first order"s agree, at every order (D1 truncation vs D2 `d/ds c_MSA(sK)`) | PYE.2/.5 ✓ | ◑ **.1–.4, .6–.9 done; .5 ✅ at N=1,γ=1** (`msa_amplitude_differentiableAt_yukawa`, via MSAFAM.1–2); general N ← MSAFAM.7. See the Task-Status table → [closures](proof_notes_closures.md) |
| `MSAFAM.1–7` *(closures)* | Remove Theorem I.1's hypothesis — construct the MSA solution family, smooth at 0 | .5 ← MSAEXACT.6; .7 ← MSAEMIX | ◑ **.1–.4 done; .5/.6 ring-free half done** (`MSAFamilyConcrete.lean`, build 8631: `exists_contDiffAt_bhRoot` + `msaFamily_taylor_eq_hierarchy_concrete`) **⇒ group reduced to ONE input = MSAEXACT.6**. ⚠ still construction-(B): certifying `C̃=1−Q̂Q̂` = MSA DCF is MSAEXACT.6; Thm-I.1 bullet STAYS. → [closures](proof_notes_closures.md) |
| `HNCB.2–3` *(closures)* | fixed-rate first-order HNCB = closure expansion + finite `(I−L)⁻¹` + DP map | **HNCB.1 ✓** (2026-08-03), PYE.1/PYE.2 ✓ | **HNCB.1 is CLOSED** — `exp`-form half + contractive pivot `c₁ = −βu + B·h₁` + the `B ∈ [0,1)` contraction bound, all axiom-clean. **Remaining in the group: HNCB.2 (affine pull-back `K̃' = a + L·K̃`) and HNCB.3 (`K̃* = (I−L)⁻¹a`)**, both reusing PYE.2's linearity; HNCB.4 is a boundary marker, not work. → [closures](proof_notes_closures.md) Group HNCB (Inventory section) |

### MIXCHS — Mixture hard-sphere `c_HS` / Baxter–WH ODE *(hs_mixture)*

The M-independent (hard-sphere) Baxter/DCF content of the mixture (`q0MixEntry` factor, Lebowitz PY
solution, seed + value routes). Carved out 2026-08-11; `Mix` now literally `extends HSMix` (Yukawa-free
at the HSMixture layer). **Whole group ✅ DONE.** Detail → **Group MIXCHS** in
`proof_notes_hs_mixture.md` (neither `_rdf.md` nor `_dcf.md` is HS-level — both are Yukawa-tail). Full
task-group + proof_notes layer reorg DEFERRED per user (2026-08-11).

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| MIXCHS.1 | N=1 Baxter ODE `matDCFreCore'(s)=−2πρ·s·c_HS(s)` on `(0,σ)` | ✅ DONE (`baxterODE_n1`) | `HardSphere/BaxterForcingDeriv.lean` |
| MIXCHS.2 | `cHSmixRenewal` = scalar `c_HS` at equal σ; N=1 physical reduction UNCONDITIONAL (constructed Banach–Volterra renewal; `hcore`/`hUouter`/`hint` discharged) | ✅ DONE (`cHSmixRenewal_physMixN_fin1_uncond`) | `YukawaOZMix/MixtureHSDCFFin1.lean` |
| MIXCHS.3 | Windowing loss, both seed arms, general-N: un-transposed + transposed seed SUM = symmetrized fold-kernel `Ĉ₀` sub-zero tail (numerics <1e-3) | ✅ DONE (`windowing_loss_sum_eq_symTail`, `physMixN_windowing_sum`) | `HSMixture/HSMixWindowingBridge.lean` |
| MIXCHS.4 | Seed route → pair DCF at UNEQUAL σ | ✅ **DISPOSITIONED REDUNDANT (2026-08-20)** — the VALUE route (MML.8 `matOzStar_unequalDiam_unique_uncond` + MIXCHS.7-N `shellForcing_eq_cMixDCFN`, ALL pairs) owns the pair DCF UNCONDITIONALLY. Equal-σ seed `=r·c_HS` DONE (`matBaxterUQmSymFullExtRho_physHSMix_eq_rcHS`); unequal-σ seed confirmed numerically (`mixchs4_extseed_vs_cMixDCFN.py`: seed row `i` = `cMixDCFN(i,k*)`), left unformalized by design | `YukawaOZMix/ExtendedSeedRhoWeight.lean` |
| MIXCHS.5 | REFACTOR: pure-HS layer + M=0 bridge; `Mix extends HSMix` (Yukawa-free HSMixture stack, `toHSMix` rfl bridges) | ✅ DONE (full-repo task-group/proof_notes reorg DEFERRED per user) | `HSMixture/HSMix.lean`, `PhysHSMixWindowing.lean` |
| MIXCHS.6 | VALUE route — MRS.8's Baxter–WH `shellForcing=c_HS` at EQUAL σ (mixture ODE → scalar `baxterODE_n1` via pair-independence + `rhoGeoPhys_mul_eq`) | ✅ DONE (`shellForcing_eq_cHS_equalDiam`) | `YukawaOZMix/MixtureBaxterODEEqualDiam.lean` |
| MIXCHS.7 | VALUE route — BINARY `σᵢ<σₖ` `shellForcing=cMixDCF` (two-piece Lebowitz `c_ij` on `(0,Rᵢₖ)∖{λᵢₖ}`, both pieces + C⁰ knot) | ✅ DONE (`shellForcing_eq_cMixDCF`) | `YukawaOZMix/MixtureBaxterODEUnequalDiam.lean` |
| MIXCHS.7-N | VALUE route — GENERAL-N `σᵢ<σₖ` `shellForcing=cMixDCFN` (symbolic `∑ₗ`; moving-limit Leibniz + √-collapse; knot via `ξ₂` alone) | ✅ DONE (`shellForcing_eq_cMixDCFN`) | `YukawaOZMix/MixtureBaxterODEUnequalDiamN.lean` |





---

## Category index

The per-group task status has been split by content track (the `## Task Status` block moved out of
this file). Project-wide status (the axiom/sorry ledger above) stays here.

| Track | Task file | Scope-gate `.lean` | Dominant groups |
|---|---|---|---|
| **Foundations** (非闭包依赖基础) | [todo_foundations.md](todo_foundations.md) | — (depended-upon) | MA · 2 · 3 · M · OZ · BAXTER · CONTACT · POLE · OZFIX · MIXCHS · FW · F |
| **FMSA** | [todo_fmsa.md](todo_fmsa.md) | [FMSAProject.lean](LeanCode/FMSAProject.lean) | 1 · 4 · 5 · GAP · C · Y1 · MML · MRS · MPOLY · IB · (chsY · P · GA) |
| **Exact MSA** (+ FMSA↔ExactMSA bridge) | [todo_exact_msa.md](todo_exact_msa.md) | [ExactMSAProject.lean](LeanCode/ExactMSAProject.lean) | MSAEXACT · MSAEMIX · MSAEXACT.5 · BRK · MSAFAM · FOEQ · leg-3 |
| **Other closures** (其他闭包) | [todo_closures_other.md](todo_closures_other.md) | [ClosuresProject.lean](LeanCode/ClosuresProject.lean) | PYE · HNCB |

See [README.md](README.md) for the project's content-logic map (the four tracks and how the
directories, proof_notes, scope-gate files, and these task files fit together).
