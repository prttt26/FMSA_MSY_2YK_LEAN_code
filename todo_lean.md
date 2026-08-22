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
| **L3** Yukawa · single | `YukawaOZ/` | `FMSA.YukawaWH`, `MSAExact`, `InnerOriginBC` | yukawa_dcf, yukawa_wh(Grp 3), msa_exact | 1, 3, 4, 5, GAP, C, MSAEXACT |
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
As of 2026-08-22 it returns **14 raw hits = 3 false + 11 real**:
3 false positives (prose lines that happen to begin `axiom `, in `PYOZ_GHS.lean`,
`HalfDiskArgumentPrinciple.lean`, and `YukawaOZMix/MixturePoleExhaustion.lean`) and 11 real axioms —
**7 math + 1 physics + 3 sympy-computation**. So the bucket counts are
**`Analysis` 7 (math) + `HardSphere` 0 + `HSMixture` 1 (physics) + `YukawaOZ` 2 + `YukawaOZMix` 1** —
the 1 HSMixture being `pyhs_mixture_no_spinodal` (physics), and the `YukawaOZ` 2 + `YukawaOZMix` 1
being the sympy-certified `msaexact6_hcore` / `msaexact6_kspace_residual` / `matMSAexact6_hcore`
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
| `msaexact6_hcore` (MSAEXACT.6) | scalar Blum–Høye closure-recovery ring `ρ(𝓕[c_core]+𝓕[c_tail]) = 2Dt·X − Dt²·Y` on the BH manifold | `YukawaOZ/MSAFullFactorization.lean` | `msaexact6_cert.py`: `Δ = m29·r29 + m33·r33`, polynomial-division remainder 0. Its Fourier layer IS discharged (out-of-build `MSAExact6Certificate.lean` reduces it to `msaexact6_kspace_residual`) |
| `msaexact6_kspace_residual` (MSAEXACT.6) | the same identity with both radial transforms in **closed cos/sin/exp form** (no `radial_fourier`) — the pure-algebra residual | `YukawaOZ/MSAExact6Certificate.lean` (**out of `defaultTargets`**) | same `msaexact6_cert.py`; `msaexact6_hcore_of_residual` derives the original axiom's exact statement from this (`#print axioms` = std-3 + this) |
| `matMSAexact6_hcore` (MSAEMIX.4) | matrix analog of MSAEXACT.6 at general `N` (equal σ) — closes MSAEMIX.1 at equal diameter | `YukawaOZMix/MSAEMixBHRoot.lean` | `msaemix_hcore_cert.py` + `msaemix_core_coeffs.py`: mixture core = scalar 5-basis with Σ_l-coupled coeffs (all 5 cracked, held-out 1e-16) |

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
| `MSAEXACT.1–6` *(msa_exact)* | Exact MSA closed form, single component | MSAX.1 gate 0 ✓ | ◑ **.1(→ reduced to .6)+.2+.3(core)+.4+.5 done; .6 = `hcore` ring `ring`-INFEASIBLE (measured 2026-08-22; Fourier layer discharged via out-of-build `MSAExact6Certificate`, residual = 1 pure-algebra axiom `msaexact6_kspace_residual`)**; ⛔ compact `msaexact1_iff_core` route dead. See the Task-Status table → [msa_exact](proof_notes_msa_exact.md) |
| `MSAEMIX.0–3` *(msa_exact)* | Same at general `N` (matrix) | UNGATED 2026-08-19 | ◑ **.0+.1(dp)+.3 done; .1 staged to matrix `hcore`** (`matEMIXfactorization_of_core`, analog of MSAEXACT.6); .2 factorization half ← .1. → [msa_exact](proof_notes_msa_exact.md) |
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

## Task Status

### Group MA — MathAxioms: General-Purpose Math Axioms & Missing-Mathlib Machinery *(analysis)*

*Cross-cutting infrastructure group (2026-07-15): surveys the project for missing-Mathlib-machinery
gaps, pre-places admissible axioms (named classical theorems only, numerically pre-checked,
narrowest form — see the admissibility discipline in [MATH_AXIOMS.md](MATH_AXIOMS.md)), and proves
what's provable. Lean home: `LeanCode/Analysis/` (project-independent, no `FMSA.*` def usage).
Registry + task records: [MATH_AXIOMS.md](MATH_AXIOMS.md). Axiom declarations are cross-listed in
the Axioms table above.*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| MA.1 | Founding pieces (re-filed from the `OZFIX.10` Route B effort): circular + half-disk contour-deformation axioms, their derived residue-sum theorems, and the… | ✓ DONE | `Analysis/ContourDeformation.lean`, `Analysis/JordanLemma.lean` |
| MA.2 | **Mittag-Leffler expansion** (simple poles + bounded on expanding circles ⇒ circle-grouped pole expansion) | ✓ DONE (**proved from the circle-deformation axiom; its own axiom RETIRED**) — ~430 lines. First stated with an *ordered*-partial-sum conclusion, which is **false** (pole-pair-splitting counterexample); fixed to the classical grouped form. See [MATH_AXIOMS.md](MATH_AXIOMS.md) bug 2. | `Analysis/MittagLeffler.lean` |
| MA.3 | **One-pole Fourier kernel** `∫_{-R}^{R} e^{ixr}/(x-k₀)dx → 2πi·e^{ik₀r}` (`Im k₀>0`, `r>0`) — genuine theorem, `#print axioms` = halfDisk axiom + standard three; with… | ✓ DONE (no new axiom) | `Analysis/MittagLeffler.lean` |
| MA.4 | **Van der Corput first-derivative test** (`\|φ'\|≥λ`, `φ'` monotone ⇒ `‖∫e^{iφ}ψ‖ ≤ (3/λ)(‖ψ(b)‖+∫‖ψ'‖)`) | ✓ DONE (**proved; axiom RETIRED**) — ~370 lines. The textbook `C¹` form is **true but unprovable** here (needs Stieltjes IBP / 2nd MVT, neither in Mathlib); restated at `C²` (no consumers ⇒ free). See [MATH_AXIOMS.md](MATH_AXIOMS.md) bug 3. | `Analysis/VanDerCorput.lean` |
| MA.5 | **Jensen counting bound** (no poles + finite divisor support ⇒ `circleAverage(log‖f‖) ≤ M·logR+C`) | ✓ DONE (**proved, no axiom**) — ~90 lines from Mathlib's Jensen. First stated over the *literal* zero set, which is **false** under junk values; fixed to divisor support. Discharges `MZERO.11`'s `hJensen`. See [MATH_AXIOMS.md](MATH_AXIOMS.md) bug 1. | `Analysis/JensenCounting.lean` |
| MA.6 | Relocate misfiled pure math `HardSphere/→Analysis/`: `ResidueAtSimplePole.lean`, `BanachPoleFamily.lean` (+5 consumer imports; namespaces kept) | ✓ DONE (`lake build` green) | `Analysis/ResidueAtSimplePole.lean`, `Analysis/BanachPoleFamily.lean` |
| MA.7 | **Sokhotski–Plemelj boundary values** (upper, integrated form; P.V. existence as hypothesis) — user-requested pre-placement, numerically pre-checked (3 test functions,… | ✓ DONE | `Analysis/SokhotskiPlemelj.lean` |
| MA.8 | **Homotopy-invariance Cauchy** (free-homotopy-through-loops of loops in open `U`, `f` holomorphic ⇒ equal contour integrals) — was pre-placed as the intended future… | ✓ **RETIRED to a THEOREM 2026-07-24 — axiom removed** (gap closed upstream). Mathlib `v4.31.0` gained the Poincaré lemma for `1`-forms (`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`, `CurveIntegral/Poincare.lean`), so the "Mathlib lacks homotopy/winding machinery" justification is stale. Proved axiom-free in `Analysis/ContourHomotopy.lean`: … [detail in linked notes] | `Analysis/ContourHomotopy.lean`, `Analysis/HomotopyInvariance.lean` |
| MA.9 | **Radial Fourier inversion** — left inverse of `radial_fourier`: `f(r) = (1/(2π²r))∫₀^∞ k·F(k)·sin(kr)dk`, plus the antiderivative form a jump discontinuity forces (`k·F… | ✓ DONE (**never axiomatized — proved** from Mathlib's `fourierInv_fourier_eq`; fully closed, no `hC` hypothesis). Also gives reusable `fourier_of_odd`/`fourier_of_even` bridges. The `4π/k` cancels ⇒ radial inversion = sine inversion + ~20 lines. First antiderivative form had an **unsatisfiable `∀ k` hypothesis** (vacuous at the junk `k=0`); fixed to `∀ k ∈ Ioi 0`. See [MATH_AXIOMS.md](MATH_AXIOMS.md) bug 4. | `Analysis/RadialFourierInversion.lean` |
| MA.10 | **Volterra integral equation of the second kind — existence & uniqueness** (continuous kernel, on compacts): `u(r) = g(r) + ∫ᵃ^r K(r,t)·u(t)dt` has a unique solution… | ✓ **DONE 2026-07-17 (never axiomatized — proved, axiom-clean, ~130 lines).** Route: **iterate bound, not Bielecki** (reuses `C(Icc a b, ℝ)`'s existing metric — no new normed structure). Engine `volterra_iterate_bound`: `|Tⁿu(r)−Tⁿw(r)| ≤ Mⁿ(r−a)ⁿ/n!·dist u w` — the local `(r−a)ⁿ` (not `(b−a)ⁿ`) is what lets the induction close; sup form is a one-line weakening. Then … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.10. | `Analysis/Volterra.lean` |
| MA.11 | **Argument principle / zero-count** — for `f` meromorphic on a disc, `(1/2πi)∮_{C(c,R)} f'/f = Z − P` (interior zeros minus poles, each weighted by order).… | ✓ **DONE 2026-07-17 — DERIVED THEOREM, no new axiom** (`Analysis/ArgumentPrinciple.lean`, ~90 code lines). As predicted, it is **MA.1 applied to `F := logDeriv f`**. The genuinely new content is the per-circle bridge `circleIntegral_logDeriv_zpow_smul_eq`: `∮_{C(k,r)} logDeriv((·−k)^n·g) = 2πi·n` for `g` analytic-nonzero on the disk — **axiom-clean** (`#print axioms` = … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.11. | `Analysis/ArgumentPrinciple.lean` |
| MA.12 | **Krein / Wiener–Hopf half-line unique solvability** — would let `OZ.10` (`oz_fixed_pt_unique`) be derived. Scoping brief in [MATH_AXIOMS.md](MATH_AXIOMS.md). | ✓ **DONE 2026-07-17 — PROVED, no new axiom** (`Analysis/WienerHopf.lean`, ~110 code lines, axiom-clean). **The spec's premise was wrong:** it assumed axiomatization because Mathlib lacks WH/Toeplitz/index/winding theory (confirmed absent — all unformalized in `docs/1000.yaml`). That holds for the *full index theorem* but **not** for the recommended (Q2) **positive-symbol** … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.12. | `Analysis/WienerHopf.lean` |
| MA.13 | **Paley–Wiener / Wiener-algebra renewal decay** — a right-compactly-supported kernel whose Laplace symbol `1−q̂(z)` is nonvanishing on `{Re z ≥ 0}` gives a decaying… | ✓ **AXIOM (legitimate) + WIRED, 2026-07-18.** Unlike MA.12, this is a **genuine axiom**: recon confirmed Mathlib has no Wiener `1/f`/Wiener-algebra inversion, no L¹ convolution Banach algebra, no Laplace transform, no Paley–Wiener/renewal theory — and **no elementary shortcut** (the classical proof needs the Gelfand-spectrum identification of the Wiener algebra with the … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.13. | `Analysis/WienerRenewal.lean`, `HardSphere/BaxterRenewalDecay.lean` |
| MA.14 | **Hermite–Biehler root location** — `Q̂≠1` on the closed lower half-plane (all physical η<1) ⇒ every Baxter pole in the open UHP; supplies MA.13's symbol-nonvanishing… | ✓ **AXIOM (bounded core) + END-TO-END LOOP CLOSED, 2026-07-18** (processed by another session). The axiom was **shrunk** from the whole closed LHP to the bounded core `G_baxter_ne_zero_on_lower_core` on `{Im k≤0, k≠0, ‖Npoly‖≤‖Dpoly‖}`: the outer region became the axiom-clean THEOREM `G_baxter_ne_zero_of_norm_dominant` (a zero forces `‖Npoly‖=‖Dpoly‖·e^{σ·Im k}≤‖Dpoly‖`; the … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.14. | `HardSphere/BaxterHermiteBiehler.lean`, `HardSphere/BaxterExteriorRegularityGeneral.lean` |
| MA.15 | **Bounded (`L∞`) Wiener–Hopf injectivity, radial shell operator** — arbitrary kernel `C` supported in `[0,σ]`, coercive symbol `1−ρĈ ≥ ε>0` ⇒ `I−K` injective on bounded… | ✓ **AXIOM, abstracted + migrated to `Analysis/` 2026-07-19.** Created by abstracting the former OZ.10 axiom `oz_linear_op_bounded_injective` (a domain-referencing math axiom) into a project-independent statement; that concrete result is **now a THEOREM** instantiating it at `C := c_HS` (support from `c_HS_outer`; `radial_fourier` and `oz_linear_op` unfold definitionally). … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.15. | `Analysis/RadialWienerHopf.lean` |
| MA.16 | **Leibniz rule with a variable upper limit AND an `r`-dependent integrand** — `d/dr ∫_a^r K(r−t)·φ(t)dt = K 0 · φ r + ∫_a^r K'(r−t)·φ(t)dt`. Consumer: `OZFIX.25` (★DIFF). | ✓ **DONE 2026-07-19 — PROVED, no new axiom** (~200 lines, axiom-clean). `K` need only be differentiable **a.e.**; regularity across the kink is carried by one `LipschitzOnWith` hypothesis on the window of arguments that occur. **Split at the base point** (`∫_a^r = ∫_a^{r₀} + ∫_{r₀}^r`) rather than the spec's `r ↦ (r,r)` chain rule, which would have needed *joint* differentiability; the … See [MATH_AXIOMS.md](MATH_AXIOMS.md) MA.16. | `Analysis/ConvolutionLeibniz.lean` |

### Group 1 — Closed-Form Integral Identities *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 1.1 | I₁ antiderivative | ✓ DONE | `YukawaOZ/I1I2Integrals.lean` |
| 1.2 | I₂ antiderivative | ✓ DONE | `YukawaOZ/I1I2Integrals.lean` |
| 1.3 | I₁/I₂ vanish at ℓ=0 | ✓ DONE | `YukawaOZ/I1I2Integrals.lean` |

### Group 2 — Hard-Sphere Baxter Factor *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 2.1 | φ₁, φ₂ auxiliary formulas | ✓ DONE | `HardSphere/BaxterFactor.lean` |
| 2.2 | det(s) non-vanishing | ✓ DONE | `HardSphere/BaxterFactor.lean` |

### Group 3 — Wiener–Hopf Structure *(hard_sphere)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 3.1 | B₁+D₁ = T_U identity | ✓ DONE | `YukawaOZ/Splitting.lean` |
| 3.2 | Support of T_S on (−∞, R_ij] | ✓ DONE | `YukawaOZ/Splitting.lean` |

### Group chsY — FMSA_chsY Formula Failure *(failures)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 4.3 | (1+A)² ≠ 1−g² — root cause of HSY spike | ✓ RESOLVED | `FMSAPoly/OriginCheck.lean` |

### Group 4 — Single-Component Reduction *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 4.1 | b_ij N=1 collapse formula | ✓ DONE | `YukawaOZ/BijReduction.lean` |
| 4.2→M.9 | g + a·exp(−z) = 1 — *re-IDed to* **M.9** *(Group M, hard-sphere)* | ✓ DONE | see M.9 — `HardSphere/SingleCompIdentity.lean` |
| 4.4 | Full N=1 reduction Eq.41→42 | ✓ DONE | `HardSphere/SingleCompReduction.lean` |

### Group M — Multi-Component Baxter Identity *(hard-sphere Baxter matrix)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| M.1 | Abstract matrix identity Ĝ+Â·c=I | ✓ DONE | `Analysis/MatrixIdentity.lean` |
| M.2 | N=1 limit: Ĝ₀₀=g, Â₀₀=a | ✓ DONE | `HardSphere/MatrixN1.lean` |
| M.3 | det(Q̂₀) ≠ 0 multi-component | ✓ **DONE, axiom-clean** — unconditional `Q0_mat_phys_isUnit_det` (`#print axioms` = `[propext, Classical.choice, Quot.sound]`); conditional Gershgorin `..._of_diag_dom` kept as historical partial | `HSMixture/MatrixQ0.lean`, `HSMixture/Q0DetRankTwo.lean` |
| M.4 | Unconditional `det(Q0_mat_phys) > 0` (in fact `≥ 1`) for all `z > 0` | ✓ **DONE, axiom-clean (`Q0_moment_det_pos` axiom RETIRED → theorem, 2026-07-16)** — Route B: `det = 1+(a+d)−(bc−ad)`, `moment_key` (`bc−ad ≤ a+d`) ⇒ `det ≥ 1`; core is the elementary 2-var kernel `kernel_nonneg` (`G=M·Φ+M·Φ`), summed via `per_pair_f`. See [proof_notes_matrix_q0.md](proof_notes_matrix_q0.md) M.4 | `HSMixture/Q0DetRankTwo.lean` |
| M.5 | `nAux_eq_mAux_div_two` (`nAux u = mAux u/2`) | ✓ DONE | `HSMixture/Q0DetRankTwo.lean` |
| M.6 | `one_add_half_sq_lt_cosh` (`1+u²/2 < cosh u` for `u>0`) | ✓ DONE | `HSMixture/Q0DetRankTwo.lean` |
| M.7 | `ratioPM_strictAntiOn` (`pAux/mAux` decreasing on `(0,∞)`) | ✓ DONE | `HSMixture/Q0DetRankTwo.lean` |
| M.8 | `moment_ad_le_bc` (**`bc ≥ ad`** for all N) | ✓ DONE | `HSMixture/Q0DetRankTwo.lean` |
| M.9 | g + a·exp(−z) = 1 — single-comp Baxter contact identity *(ex-4.2)* | ✓ DONE | `HardSphere/SingleCompIdentity.lean` |
| M.10 | Concrete Q̂₀=P̂+Ê·exp(−z·σ_min) *(ex-B.2)* | ✓ DONE | `HardSphere/QhatDecomposition.lean` |
| M.11 | Coefficient algebra (1−g²)−a²c²=2acg *(ex-B.3)* | ✓ DONE | `HardSphere/SingleCompIdentity.lean` |


### Group GAP — FMSA_GA_matrix_mix Algebraic Foundation and Polynomial Determination *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 2.3 *(ex-B.1)* | Shifted-exponent integral (pure HS Baxter factor; moved from Group GAP 2026-07-17) | ✓ DONE | `HardSphere/BaxterFactor.lean` |
| B.2→M.10 | Concrete Q̂₀=P̂+Ê·exp(−z·σ_min) — *re-IDed to* **M.10** *(Group M, hard-sphere)* | ✓ DONE | see M.10 — `HardSphere/QhatDecomposition.lean` |
| B.3→M.11 | Coefficient algebra (1−g²)−a²c²=2acg — *re-IDed to* **M.11** *(Group M, hard-sphere)* | ✓ DONE | see M.11 — `HardSphere/SingleCompIdentity.lean` |
| GAP.4 | Origin BC automatic for FMSA_GA_matrix_mix | ✓ DONE | `YukawaOZ/InnerOriginBC.lean` |
| GAP.5 | Degree bound exisr: deg P_{ij} ≤ 4 (no r^n for n≥N with N=4) | ✓ DONE | `YukawaOZMix/MixturePolyCoeffs.lean` |
| GAP.6 | Origin uniqueness: only A_{ij}=−E_{ij}(0) forced at r=0 | ✓ DONE | `YukawaOZMix/MixturePolyCoeffs.lean` |
| GAP.7 | No contact BC: B,C,D,E^{(4)} not fixed by r=R_{ij} | ✓ DONE | `YukawaOZMix/MixturePolyCoeffs.lean` |
| GAP.8 | Laurent extraction: all five coefficients from R_{ij}(s) at s=0 | ⚠ **VACUOUS — reopened 2026-07-16**: `poly_coeff_from_laurent` is an `∃` closed by 5 `rfl`s with an **unused** `AnalyticAt` hyp — asserts only "five reals exist". **Root cause: `P_ij` does not exist as a Lean object** (it is MPOLY.5's deliverable), so the intended claim had nothing to predicate on ⇒ GAP.8 is *half* a theorem, completable only with MPOLY.5. … | `YukawaOZMix/MixturePolyCoeffs.lean` |
| GAP.9 | D_{ij} generically nonzero for unlike pairs | ❌ **FALSIFIED 2026-07-17 — the claim is FALSE: `D_{ij} ≡ 0`.** The shipped `fmsa_double_prop` closed form gives, for an unlike pair, `r·c⁽¹⁾` piecewise with r³ coefficient **identically zero on both pieces** (inner `(0,λ)` is degree 1; outer `(λ,R)` has r³ and r⁵ cancelling **exactly**) — verified `≡0` (≤2e-12) over 12 random parameter sets **and at GAP.9's own cited point** σ=[1,1.2], ρ*=0.5, … | `YukawaOZMix/MixturePolyCoeffs.lean` |
| GAP.10 | Degree: `natDegree ≤ 4` always; `= 4` **iff** leading coeff ≠ 0 | ⚠ **RELAXED 2026-07-17 (was "exact degree = 4", which is false as an unconditional claim)** — ✓ DONE in the relaxed form, axiom-clean: `poly_natDegree_le_four` (**unconditional `≤ 4`**), `poly_natDegree_eq_four` (`= 4` given `a ≠ 0`), **new** `poly_natDegree_eq_four_iff` (`= 4 ↔ a ≠ 0`, the sharp characterisation). … | `YukawaOZMix/MixturePolyCoeffs.lean` |

### Group IB — Inner-Core Mediated Breakpoints *(breakpoints)*

*Split out of Group GAP once the mediated inner-core breakpoint work outgrew it.
**IB.1–IB.8 were formerly B.11–B.18**; the old B.19 (hard-sphere `λ_ij` kink) moved to Group OZ as
**OZ.18** (it is FMT hard-sphere, outside the Yukawa mediated chain). The Lean identifiers in
`YukawaOZMix/InnerDecomp.lean` were made **task-ID-free** (e.g. `b11_…`→`terms_II_III_zero`),
so IB.* can be renumbered without touching Lean source. Proof records:
[proof_notes_breakpoints.md](proof_notes_breakpoints.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| IB.1 | Terms II+III ≡ 0 in the inner region (unconditional: `alpha = r−σ_a−R_ij < 0`) | ✓ DONE | `YukawaOZMix/InnerDecomp.lean` |
| IB.2 | Term IV geometry: `Δ_ai = −R[i,a]` ⇒ `Alm=0`, `c_exp=d_exp=r*=R[a,b]+R[i,a]`; sub-term ≡ 0 below `r*` (unconditional) | ✓ DONE | `YukawaOZMix/InnerDecomp.lean` |
| IB.3 | mediated ≡ 0 on `(0,R_ij)` when no `(a,b)` satisfies A∧B; **binary N=2 ⇒ mediated ≡ 0 for any σ** | ✓ DONE (both; size chain `σ_a<σ_b<σ_j` via `active_pair_size_chain`) | `YukawaOZMix/InnerDecomp.lean` |
| IB.4 | Piecewise rigidity: when is the inner-core residue a *single* polynomial? *(redone 2026-07-17)* | ✅ **REDONE, axiom-clean** — real content = **piecewise rigidity**: `single_poly_forces_pieces_eq` (`f=P₁` on `(0,λ)`, `=P₂` on `(λ,R)`, `=Q` on `(0,R)` ⇒ `P₁=Q=P₂`; via `Polynomial.eq_of_infinite_eval_eq` + `Set.Ioo_infinite`) + `not_single_poly_of_pieces_ne` (`P₁≠P₂` ⇒ **no single Q exists**). … | `YukawaOZMix/InnerDecomp.lean` |
| IB.5 | Sharpness witness: σ=[1,4,8], `(a,b,j)=(0,1,2)` satisfies A∧B and `r* < R[0,2]` | ✓ DONE, no sorry (`ternary_148_active`) | `YukawaOZMix/InnerDecomp.lean` |
| IB.6 | r** switch identity: `qP(u_lo_bj)=0` ⇒ integrand vanishes at moving boundary ⇒ C¹ at `r**=r*+(3d_b−d_j)/2` (no slope jump) | ✓ DONE (`qP_at_uLo_zero`, `ivIntegrand_at_uLo_zero`; full Leibniz-C¹ + curvature stay numerical) | `YukawaOZMix/InnerDecomp.lean` |
| IB.7 | r** interior ⟺ Condition C (`d_a+2d_b<d_j`); `C ∧ B ⟹ A`; both mediated knots interior iff `d_a+2d_b<d_j<3d_b` | ✓ DONE (`rstarstar_interior_iff_C`, `condC_activeB_imp_activeA`) | `YukawaOZMix/InnerDecomp.lean` |
| IB.8 | Mediated knot completeness: `u_hi_eff=r` under A∧B (upper limit never switches ⇒ only `r*`,`r**` knots) | ✓ DONE (`uHiEff_eq_r`, `uHiEff_eq_r_of_active`) | `YukawaOZMix/InnerDecomp.lean` |
| IB.9 | *(opt.)* First-order **DCF** breakpoint set on `(0,R_ij)` is exactly `{λ_ij}` (unlike: 1 knot, C¹; like: none) for all N — mediated `r*` and intermediate `λ_im` add… | ✓ **support geometry CLOSED (2026-07-18)** — `YukawaOZMix/MixtureConvolution.lean` (axiom-clean, sorry-free): kernels `bMixEntry`(`ℬ`)/`pMixEntry`(reflected `𝒬⁻`), mediated `bConvP`/triple `pbpConv` + support lemmas. **`pbp_breakpoints_subset` + the 4 edge identities `pbp_edge_eq`/`_lu`/`_ul`/`_uu`: ALL four breakpoints of `P_im⋆ℬ_mn⋆P_jn` … [detail in linked notes] | `YukawaOZMix/MixtureConvolution.lean` + `MixtureDCFSmooth.lean` |


### Group C — FMSA_GA_matrix_mix Consistency *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| C.1 | N=1: corrected formula = FMSA_pure | ✓ DONE | `HardSphere/SingleCompReduction.lean` |
| C.2 | N=1 like-pair inner formula bounded: `(1−G²₀₀)·exp(z(R−r))` ≤ C on (0,d) via exp-cancellation | ✓ DONE (`c1_n1_twoexp_bounded`) | `HardSphere/SingleCompReduction.lean` |
| C.5 | Leading Yukawa-pole residue of the first-order MSA amplitude. **CORRECTED:** exact single-tail residue is `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}` (doubly-propagated), **not** `K·G` (the… | ◑ core (`c5_residue_eq_K_mul_Ginv`) + single-tail exact residue (`spectralAmp_residue`, `spectralAmp_residue_n1`) DONE; multi-tail + Wiener–Hopf derivation of `b_{ij}(s)` → **Group Y1** | `YukawaOZMix/YukawaPoleResidue.lean`, `YukawaOZMix/SpectralAmplitude.lean` |

### Group Y1 — First-Order Yukawa RDF/DCF (Wiener–Hopf derivation) *(yukawa_wh)*

*The ε¹-order analog of Group BAXTER (same **algebraic** Wiener–Hopf machinery — causal/anti-causal
split + support + residues, **not** the Hilbert transform of [LN] §6.3 which Mathlib lacks; see Y1.3
— applied to the first-order OZ equation `H̃₁(I−C̃₀)=(I+H̃₀)C̃₁`). Split off as the full
concrete-C.5 derivation. Source: **[LN]** §5–§6. Records: [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md).*

✅ **Group Y1 is CLOSED — re-audited 2026-07-31.** `#print axioms` run on all 19 Y1 declarations:
**every one returns exactly `[propext, Classical.choice, Quot.sound]`**, so Y1 consumes **no
Group-MA axiom of any kind**. Build green (8714 jobs), no `sorry` in `LeanCode/`. Two deliberate
non-goals, recorded so they are not mistaken for gaps: **[LN] Eq. 14**'s closed-form `W/det` inverse
(Y1.1 — `adj/det` is what everything uses, and the concrete N=2 entry comes from MML.1's
`Q0inv_zero_one`) and **[LN] Eq. 67**'s contour-closure formula (Y1.4 — bypassed by Y1.3's
real-space re-route; formalizing it would re-import the very machinery Y1.3 avoided).

| Task | Title ([LN] ref) | Status | Lean file |
|------|-------|--------|-----------|
| Y1.1 | Complex Baxter matrix `Q̂₀(s):ℂ→Matrix` (Eq. 10–13) + inverse-as-`adj/det` (Eq. 14) | ✓ DONE (`q0_entry_c`, `Q0_mat_c`, `q0_entry_c_real`, `inv_apply_eq_adj_div_det`); closed-form Eq. 14 deferred — **and staying deferred** (no consumer; concrete N=2 entry served by MML.1 `Q0_det_fin_two`/`Q0inv_zero_one`) | `HSMixture/Q0Complex.lean` |
| Y1.2 | Outer MSA DCF Laplace transform `U₁(k)_{ij}=K_{ij}e^{−ikR_{ij}}/(ik+z_{ij})` (Eq. 34/46) + Yukawa pole at `k=iz_{ij}` | ✓ DONE (`integral_Ioi_cexp`, `outerDCF_transform`) | `YukawaOZ/OuterDCF.lean` |
| Y1.3 | Wiener–Hopf one-sided projection isolating `B₁={T_U}^{[R,∞)}` (Eq. 55–66) — **algebraic split + support + residues, NOT Hilbert transform** (Mathlib lacks it; mirror… | ✓ **DONE (a/b/c, axiom-clean, real-space route)**. a: `q0_poly_support_subset`, `q0MixEntry`+`_support_subset`, `integral_/fourier_{Iic,Ici}_eq_of_support/_eq_full`. b: `causal_projection_real`/`_fourier` (support-orthogonality = `1_{[R,∞)}·`, no FT injectivity). c: `matrix_conj_residue_analytic`, `outer_residue`, `outer_residue_eq_spectralAmp_residue` (`Res T_U = Res b_{ij}`). … | `WHSupports.lean` (a); `YukawaCausalProjection.lean` (b); `YukawaCausalResidue.lean`+`YukawaWienerHopf.lean` (c) |
| Y1.4 | Residue evaluation of the WH projection → `B₁(k)` (§6.4.1, Eq. 63–67) | ✓ DONE — residue-theorem step (`matrix_conj_residue`, `triple_apply`) + the Eq. 63 integrand now supplied by Y1.3c (`matrix_conj_residue_analytic`, `outer_residue`). **Eq. 67's literal contour formula is deliberately NOT formalized** — it is [LN]'s k-space intermediate, bypassed by Y1.3's real-space projection, and `B₁` is already closed-form via Y1.5's `bMulti`. … | `YukawaOZMix/YukawaWienerHopf.lean`, `YukawaCausalResidue.lean` |
| Y1.5 | Spectral amplitude `b_{ij}(s)` four-term/multi-tail (Eq. 73) + tie `A` to `Q̂₀(s)⁻¹` | ✓ **DONE** — single-tail (`spectralAmp_residue`/`_n1`), collapse (`bMulti_single_eq`/`_residue`), **general distinct-`z`** (`simplePole_offResidue`, `bMulti_residue` = per-pole term matching, `bMulti_residue_Qinv` = tie to `Q̂₀⁻¹` via `one_add_sub_one`) | `YukawaOZMix/SpectralAmplitude.lean` |
| Y1.6 | First-order RDF `Ĥ₁=[Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` (Eq. 68) + the exact C.5 residue corollary | ✓ DONE (`Hhat1`, `Hhat1_spec`, `Hhat1_residue`) | `YukawaOZMix/YukawaWienerHopf.lean` |
| Y1.7 | inner-core `S₁(k)` (§9, Eq. 45) + origin constraint (Eq. 76) + contact matching (§7) — Group Y1 capstone | ✓ DONE (axiom-clean): `innerS1`/`innerS1_support_subset_Iio` (Eq. 45, Proof 2 anti-causal), `b1_causal_eq_U1_fourier` (§9.3, instantiates Y1.3b for concrete `S₁`), `origin_constraint_eq76` (Eq. 76, reuses P.2 + `eij_at_origin`), `innerS1_contact_value` (§7, reuses Group 5.1) | `YukawaOZ/YukawaInnerCore.lean` |


### Group MML — N=2 Mixture Mittag-Leffler Inner-Core *(mixture_rdf)*

For N=2, Q̂₀(z) and its 2×2 inverse (adj/det) are fully algebraic (Y1.1 DONE), so the HS-pole
residue `B_k = −Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)` is provable without Y1.3 via `residue_of_simple_pole`.
This resolves the "no closed form for N=2" claim: the exact inner DCF **is** a convergent
Mittag-Leffler series; the only transcendental obstacle is the pole *locations* `s_k` (roots of
`det(Q̂₀)=0` — see **Group MZERO**), not the residues. Full assembly (MML.8) needs Y1.3 (done).
See [proof_notes_mixture_rdf.md](proof_notes_mixture_rdf.md) Group MML.

**MML.3 retired (2026-07-16):** it bundled ~5 independent sub-results and its genuine difficulty
(the series-equals-true-DCF *collapse*) is the N=2 matrix analog of the still-open scalar
`hcollapse` (OZFIX.6/9/10). **Superseded by the five topic-scoped tasks MML.4–MML.8** below
(Lean identifiers in `MixtureMLSeries.lean`/`MixtureInnerDCF.lean` are task-ID-free). MML.4–MML.7
✓ DONE (axiom-clean); MML.8 is the hard collapse (scoped only); **MML.9 + MML.10 ✓ DONE
(2026-07-24)** — the structure-factor form `Ĥ₁ = S₀·Ĉ₁·S₀`, which localizes every RDF HS pole in
`S₀ = (I−Ĉ₀)⁻¹` and so narrows MML.8's residual input to the **hard-sphere** side, plus the
residue-matrix factorization of term (II) and the mixture collapse factor `R_k = R_k·Ĉ₀(s_k)`.

**Group status (2026-07-24).** Every MML task is closed **except MML.8's collapse**: MML.1, MML.2,
MML.4, MML.5 (closed this session — no bookkeeping remainder), MML.6, MML.7, MML.9, MML.10, MML.11,
MML.12, MML.13 all ✓ axiom-clean; MML.3 retired. **MML.14 ◑ IN PROGRESS** — the matrix real-space
infrastructure MML.8's collapse needs, first rung (antiderivative tower) done. MML.8 retains the pole
set, pole order, both Laurent coefficients, the HS × Yukawa factorization, the per-pole collapse
factor, (MML.11) a **concrete** pole family carrying all of term (II)'s data, and (MML.12) a
correctly-scoped target region; what is missing is the **real-space** identification of the summed
series with the inner-core value (matrix `OZFIX.12`/`OZFIX.22`), now under construction as MML.14 —
and by MML.12 that identification can only ever be established on `(λ₀₁, R₀₁)`, never on the inner
piece `(0, λ₀₁)`.

| Task | Title | Status | Route / Lean file |
|------|-------|--------|-----------|
| MML.1 | Explicit 2×2 adjugate/det formulas for Q̂₀: `adj(Q̂₀)₀₁=−Q̂₀₀₁`, `[Q̂₀⁻¹]₀₁=−Q̂₀₀₁/det(Q̂₀)` | ✓ DONE (axiom-clean): `adjugate_fin_two_zero_one`, `inv_zero_one_eq`, `Q0_det_fin_two`, `Q0inv_zero_one` | `HSMixture/MixtureHSPoles.lean` |
| MML.2 | B_k residue formula: `Res_{s=s_k}[Q̂₀⁻¹]₀₁ = −Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)` from `residue_of_simple_pole` + MML.1 | ✓ DONE (axiom-clean): `b_k_residue` (simple-zero data as hyps, matching `residue_of_simple_pole`) | `HSMixture/MixtureHSPoles.lean` |
| ~~MML.3~~ | ~~Full inner-DCF Mittag-Leffler assembly~~ — **RETIRED, superseded by MML.4–MML.8** (2026-07-16) | ✗ retired | — |
| MML.4 | HS-pole Mittag-Leffler *term* (II): `mixHSterm B_k s_k r = B_k·e^{−s_k r}`, `mixHS_series` (`2·Re`-of-tsum), Yukawa coupling `Σ_t K_t/(z_t²−s²)`, and the… | ✓ DONE (axiom-clean): `mixHSterm`, `mixHS_series`, `yukawaCoupling`, `yukawaCoupling_continuousAt`, `b_k_residue_coupled` | `YukawaOZMix/MixtureMLSeries.lean` |
| MML.5 | *(**RDF-only** — not on the DCF path, see Group MRS)* Convergence of the HS-pole sum `Σ_k 2·Re[B_k e^{−s_k r}]` | ✓ DONE, axiom-clean (RDF-only, off the DCF path) → `proof_notes_mixture_rdf.md` | `HSMixture/MixtureChordFamily.lean`, `MixtureMLSeries.lean`, `Analysis/BanachPoleFamily.lean` |
| MML.6 | Yukawa doubly-propagated base (I): `yukawaBaseAmp = [Q̂₀⁻¹K Q̂₀⁻ᵀ]₀₁`, real-space `yukawaBaseTerm = Σ_t amp_t·e^{z_t(R−r)}`, and its certification as the exact Y1.5 residue | ✓ DONE (axiom-clean): `yukawaBaseAmp`, `yukawaBaseTerm`, `yukawaBaseAmp_eq_spectralAmp_residue` (reuses `spectralAmp_residue`). Real-space `e^{z_t(R−r)}` envelope derivation = MML.8 | `YukawaOZMix/MixtureInnerDCF.lean` |
| MML.7 | Origin constant `p₀ = −(base+HS-sum)\|_{r→0}` | ✓ DONE (axiom-clean): `origin_constant_mix` (generic, via P.2 `origin_necessity` with `E:=base+hsum`), `origin_constant_eij_mix` (Yukawa specialization, `base:=eij`, continuity via `fun_prop`; gives `_precompute_p0`'s `−(E_ij(0)+Σ_k 2Re B_k)` form) | `YukawaOZMix/MixtureInnerDCF.lean` |
| MML.8 | RDF-only assembly/collapse (I)+(II)+(III) | ◑ literal collapse PROVABLY BLOCKED (DCF premise `Ĉ₁=Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` carries no `Q̂₀⁻¹`, refuted 2026-07-16); **MML.8 closed via the VALUE route** `matOzStar_unequalDiam_unique_uncond` instead — [[project_mml8_disposition]]. → `proof_notes_mixture_rdf.md` | `YukawaOZMix/MixtureInnerDCF.lean` |
| MML.9 | **Structure-factor form of the first-order RDF**: `Ĥ₁ = S₀·Ĉ₁·S₀` (the RDF dual of MRS.2's `oz1_C1_eq`), HS-pole localization, and both term-(II) Laurent coefficients in… | ✓ DONE, axiom-clean (`Ĥ₁=S₀·Ĉ₁·S₀`, RDF dual of MRS.2) → `proof_notes_mixture_rdf.md` | `YukawaOZMix/MixtureRDFStructureFactor.lean` |
| MML.10 | Term (II)'s coefficient factored as **HS residue × (finite Yukawa DCF) × HS residue**, + the **mixture collapse factor** (matrix analog of the scalar `ρĈ(kₙ)=1`) | ✓ DONE, axiom-clean (HS-residue × finite-Yukawa-DCF × HS-residue + collapse factor) → `proof_notes_mixture_rdf.md` | `YukawaOZMix/MixtureRDFStructureFactor.lean` |
| MML.11 | **Concrete term-(II) data**: one explicit pole family carrying pole locations, the order-2 coefficient, and MML.5's summability | ✓ DONE, axiom-clean (concrete term-(II) pole family) → `proof_notes_mixture_rdf.md` | `YukawaOZMix/MixtureRDFPoleData.lean` |
| MML.12 | **The collapse REGION** — scoping correction + a permanent bound on the ML series' reach | ✓ DONE, axiom-clean (collapse region / ML-reach bound) → `proof_notes_mixture_rdf.md` | `YukawaOZMix/MixtureRDFPoleData.lean` |
| MML.13 | **`n=1` soundness bridge** for MML.9–MML.12 (the only mechanical test a consumer-less body of statements admits; MRS.0b's precedent) | ✓ **DONE (2026-07-24, axiom-clean, full build green) — all three checks PASS, no statement bug.** (1) collapse factor: MML.10's `R_k=R_k·Ĉ₀(s_k)` at `Fin 1` gives `Ĉ₀(s_k)=1` = the scalar `ρĈ(kₙ)=1` (`cmix_eq_one_fin_one`, via `hsResidueMatrix_fin_one`: `adj=1` ⇒ `R=det′⁻¹•I`). … See [proof_notes_mixture_rdf.md](proof_notes_mixture_rdf.md) MML.13 | `YukawaOZMix/MixtureRDFPoleData.lean` |
| MML.14 | Matrix real-space infrastructure I — antiderivative tower of term (II) (mixture analog of `residue_term→Hterm→Kterm`) | ◑ first rungs DONE, axiom-clean (`expLinTerm` closed under antidiff `expLinTerm_antideriv_hasDerivAt`; `mixHSAntideriv1/2`). ⚠ **route SUPERSEDED** — MML.8 is now closed UNCONDITIONALLY via the value route (`matOzStar_unequalDiam_unique_uncond`); the literal pole-series collapse is PROVABLY BLOCKED ([[project_mml8_disposition]]). → `proof_notes_mixture_rdf.md` MML.14/15 | `YukawaOZMix/MixtureRDFAntideriv.lean`, `HSMixture/MixtureOzStar.lean` |
| MML.16 | **RDF parity partner annihilated exactly** — the one-sided-vs-sine ("even pseudo-trace") question | ✓ DONE (2026-08-03, axiom-clean): Tang & Lu 1995 pp. 91–94 **checked against the original** — they keep `H̃=[Ĥ(−k)−Ĥ(k)]/(ik)` and write the partners `Q̂₀ᵀ(k)Ĥ₁(−k)Q̂₀(k)`, `−[Q̂₀(−k)]⁻¹Ĉ₁(−k)[Q̂₀ᵀ(−k)]⁻¹` explicitly in Eq. (10); support analysis kills them **exactly** (not asymptotically). … | `YukawaOZMix/ReflectedTermSupports.lean` |

### Group MRS — Mixture Real-Space Baxter Route to the Inner DCF *(mixture_dcf)*

**The DCF route**, replacing MML.8's refuted premise. Pivot: **(★)** `Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)`
— an algebraic consequence of [LN] eq:OZ1_Baxter (a) + `Hhat1_spec` (b) that **contains no `Q̂₀⁻¹`**.
`Q̂₀` entire ⇒ `Ĉ₁` has **only Yukawa poles** ⇒ the `det Q̂₀` zeros (Group MZERO) **never enter the
DCF**, and the inner DCF is a **finite closed form** (polynomial + finitely many exponentials),
piecewise at the support-overlap knots (`λ_ij` first — exactly Group IB's set). Numerics: (★) to
**4.4×10⁻¹³**; the finite-basis fit split at `λ_01` drops the residual ~1000× (1.9×10⁻³ → 1.3×10⁻⁶,
then at the quadrature noise floor). **MZERO / MML.5-concrete are NOT needed here** — they stay
load-bearing for the RDF `h₁` only. **The inverses are the DCF/RDF dividing line.**
Source: `todo/to_Lean.md` §1–§2 (2026-07-16 numerical session). See
[proof_notes_mixture_dcf.md](proof_notes_mixture_dcf.md) Group MRS.

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| ~~MRS.1~~ | ~~Matrix WH factorization `Q̂₀(k)·Q̂₀ᵀ(−k) = I − Ĉ₀(k)`~~ — **DECOMPOSED (2026-07-17) into MRS.6/MRS.7/MRS.8** (pure-numeric) | ✗ retired → MRS.6–8 | — |
| MRS.6 | *(ex-MRS.1a)* WH factorization **frame**: define `Ĉ₀ := I − Q̂₀(k)·Q̂₀ᵀ(−k)`; discharge MRS.2's `hfact` for free; **reduce** `hT0symm` to the swap identity… | ✓ **DONE (2026-07-17, axiom-clean)** — `MixtureRealSpace.lean` (ns `FMSA.MRS`): `Cmix0`, `Cmix0_factorization` (hfact), `Cmix0_transpose`, `Cmix0_isSymm_iff` (symmetry ⟺ swap), `T0_isSymm_of_swap` (⇒ `hT0symm`). `YukawaOZMix/MixtureRealSpace.lean` + `fin2_transpose_eq_iff_offdiag`/`T0_isSymm_iff_offdiag` (N=2 symmetry ⟺ single off-diagonal scalar; diagonal … | `YukawaOZMix/MixtureRealSpace.lean` |
| MRS.7 | *(ex-MRS.1b)* the **swap identity** `Q̂₀(−k)Q̂₀ᵀ(k) = Q̂₀(k)Q̂₀ᵀ(−k)` for the physical `Q0_mat_c` — discharges `hT0symm` | ✓ **DONE (2026-07-17, axiom-clean)** — `MixtureRealSpace.lean`. **`Qphys_T0_isSymm`**: `T₀=Q̂₀(k)Q̂₀ᵀ(−k)` symmetric for the physical matrix. Chain: KEY 1/2 (`Q0phys_key_relation`/`Qppphys_key_relation`) + **`swap_offdiag_of_keys`** (coefficient-free structural swap under 4 minimal hyps, proved via `E₀=e^{σ₀k/2}`/`E₁=e^{σ₁k/2}` atoms + `field_simp`+`ring`) + physical instantiation (discharge 4 … | `YukawaOZMix/MixtureRealSpace.lean` |
| MRS.8 | *(ex-MRS.1c)* validate `Ĉ₀ = I−Q̂₀(k)Q̂₀ᵀ(−k)` **is** the physical HS DCF transform (behind MRS.2's OZ hyps) | ☐ **deferred + deprioritized (2026-07-17)**. **Search: a mixture PY DCF `Ĉ₀` does NOT exist in Lean** (only scalar `c_HS`+transforms; `cHS_FMT` is the FMT DCF; rank-2 `Q0_mat_phys=I−UV` is a factorization of Q̂₀ itself, not the WH product). **NOT on the critical path**: the finite-form payoff needs only (★)+`Q̂₀` entire, not `Ĉ₀`; `hTS` is definitional, `hoz` is the OZ axiom. … | `YukawaOZMix/MixtureHSDCF.lean` (new) |
| MRS.2 | [LN] eq:OZ1_Baxter (a) `Q̂₀ᵀ(k)Ĥ₁Q̂₀(k) = [Q̂₀(−k)]⁻¹Ĉ₁[Q̂₀ᵀ(−k)]⁻¹`; **physical route:** derive (★) from first-order OZ + MRS.1 | ◑ **backbone DONE (2026-07-17, axiom-clean)** — `MixtureRealSpace.lean`: `oz1_C1_eq` (`Ĥ₁T₀=S₀Ĉ₁`+`T₀S₀=I` ⇒ `Ĉ₁=T₀Ĥ₁T₀`) + **`star_of_first_order_oz`** ((★) from 5 named matrix identities: OZ `hoz`/`hTS`, MRS.1 `hfact`, `Ĉ₀`-symmetry `hT0symm`, `Hhat1_spec` `hB1`). **Pins the exact conventions** the algebra needs (OZ form `Ĥ₁T₀=S₀Ĉ₁`, factor order `Q̂₀(k)Q̂₀ᵀ(−k)`, `Ĉ₀` symmetric). … | `YukawaOZMix/MixtureRealSpace.lean` |
| MRS.3 | **(★)** `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` from (a)+(b) — pure algebra; corollary: only Yukawa poles, no HS poles | ✓ DONE, axiom-clean (`star_of_oz1_baxter`; `star_entry_differentiableAt` — `Ĉ₁` entries differentiable with NO `det Q̂₀` hyp ⇒ MZERO zeros impose no DCF singularity; conditional on (a)=MRS.2). → `proof_notes_mixture_dcf.md` | `YukawaOZMix/MixtureRealSpace.lean` |
| MRS.4 | Real-space `q_ij` quadratic + the `λ_ij` delta in `q'_ij` (amplitude `−σᵢσⱼ/(2Δ)`, ξ₂ cancels) + its symmetry ⇒ delta-cancellation | ◑ **jump-value core DONE (2026-07-17, axiom-clean, general `N`)** — `q0Mix_jump_amplitude` (`=−πσᵢσⱼ/vac`=`−σᵢσⱼ/(2Δ)`, **ξ₂ cancels**), `q0Mix_jump_amplitude_symm` (i↔j-symmetric ⇒ cancellation), `lam_sub_R_eq`, `q0Mix_quad_at_R` (delta is one-sided). … | `YukawaOZMix/MixtureRealSpace.lean` |
| MRS.5 | Convolution `𝒞 = 𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ` ⇒ **finite closed form**, piecewise at the knots | ✅ **CLOSED, EXPLICIT, GENERAL `N`, AXIOM-FREE (audited 2026-07-31).** Three layers: *atoms* `MixtureRealSpace.lean` (`integral_poly_exp_conv`/`_linear_`/**`_quadratic_`**, FTC poly⋆exp=poly+exp); *engine* `MixtureClosedForm.lean` (the convolution ⇄ interval-integral bridges `indicator_ici/icc_conv_indicator_icc/ici` + `indicator_icc_conv_general`; sign-paired atoms; … [detail in linked notes] | `MixtureRealSpace.lean`, `MixtureConvolution.lean`, `MixtureClosedForm.lean`, **`MixtureDCFSmooth.lean`** |
| MRS.5 note | *(historical — the 2026-07-17 audit called MRS.5 "the single blocker for a concrete `c1_inner`".)* The object is `c1_inner_ij(r) = [𝒲(r)−𝒲(−r)]/(2π√(ρᵢρⱼ)r)`, `𝒲 = 𝒬⁻ ⋆… | ✅ **superseded by the MRS.5 row above** | → [mixture_dcf](proof_notes_mixture_dcf.md) Group MRS · `YukawaOZMix/MixtureConvolution.lean`, `MixtureDCFSmooth.lean` |
| MRS.9 | **`HSMixture/` library reorganization** (not DCF math — the layered-directory work that placing the `MRS.0` axiom triggered; consolidates ex-`MRS.0c/0d/0e/0f`). `9a`… | ✓ **DONE — 9a–9c 2026-07-19, 9d 2026-07-27** (build 8699, layering re-verified, axiom ledger byte-identical). `9d`: extracted `p1_limit`/`p2_limit`/`p2_quartic_coeff` → `Analysis/Taylor4Calculus`, moved `MixtureLaurent` → `HSMixture/`, renamed the 4 generic `mixHS*` in `Analysis/PoleSeriesSummable` → `poleExp*` (derived `mixHSterm2`/`detF_mixHS_summable` kept). … | → [mixture_rdf](proof_notes_mixture_rdf.md) `### Task MRS.9` (record co-located with its history, not in `mixture_dcf`) · `LeanCode/HSMixture/`, `LeanCode/Analysis/` |

### Group MZERO — Mixture `det(Q̂₀)` Zero Family (HS-pole existence) *(mixture_rdf)*

**⚠ Scope (2026-07-16): RDF-only.** (★) (Group MRS) shows the inner **DCF** has no HS poles, so this
group is **not** on the DCF path. It stays load-bearing for the **RDF `h₁`**, whose
`Ĥ₁=[Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` *does* carry the inverses ⇒ genuine HS poles.

**MZERO.2–MZERO.11 decompose MZERO.1** (`det(Q̂₀)` has ∞ many complex zeros; foundation done,
`MixtureHSZeros.lean`) into two independent routes — **Route A** Banach (MZERO.2–MZERO.7) and
**Route B** Rouché/Jensen (MZERO.8–MZERO.11); either route alone closes MZERO.1. The N=2
`det(Q̂₀)` is an exponential polynomial in `s` (quasi-polynomial) — the analog of `Qhat_complex`
for N=1 (POLE.3 `Qhat_complex_zeros_infinite`). See [proof_notes_mixture_rdf.md](proof_notes_mixture_rdf.md) Group MZERO.

**✅ GROUP CLOSED — audited 2026-07-24.** All of MZERO.1–MZERO.11 are ✓, and the audit was
mechanical, not a re-read of statuses: every named deliverable was `#print axioms`-checked and each
returns the standard three only. Checked constants — `detC_zeros_infinite_unconditional`,
`chordPoleFamily_detC_exists` (MZERO.1/5); `chord_zero_exists_of_bounds`, `chordPhi_fixedPt_iff`,
`chordPhi_lipschitzOnWith`, `mapsTo_closedBall_of_lipschitzOnWith_of_dist_le` (MZERO.3/4/6, all in
`FMSA.BanachPoleFamily`, **not** `FMSA.MixtureHSPoles` — the generic Banach layer was migrated to
`Analysis/`); `Q0_det_c_zeros_infinite`, `Q0_det_c_pole_family_growth` (MZERO.7);
`det_meromorphicOn` (MZERO.8); `det_divisor_nonneg`, `detC_jensen_log_bound` (MZERO.9);
`detBoundaryGrowth_of_linear` (`FMSA.BoundaryGrowth`), `detC_boundaryGrowth_iff_infinite_zeros`
(MZERO.10); `detC_zeros_infinite_of_boundaryGrowth` (MZERO.11). No open item remains in this group.

✅ **RE-AUDITED 2026-07-31 — holds; three findings.** All **20** MZERO constants re-measured,
`#print axioms` = standard three (nothing shifted in `be70ac4` "General N" or the MRS.9d shuffle).
(1) **Machinery vs headline split.** `detF_family_magnitude_bound` is **load-bearing** (consumed by
`MixtureMLBound`/MML.5, `MixtureInnerDCF`/MML.8, `MixtureRDFPoleData`/MML.11) and the generic
`ChordPoleFamily`/`zeros_infinite_of_chordPoleFamily` layer is **reused by the scalar track**
(`HardSphere/BaxterChordFamily.lean`, `BaxterPoles.lean`) — the `Analysis/` migration paid off beyond
the mixture. But the **`Set.Infinite` headlines of both routes have NO Lean consumer** (all hits are
docstrings): MRS.3 removed the DCF consumer (`det Q̂₀` zeros never enter `Ĉ₁`) and the only remaining
one, MML.8, is open. Proved-and-unconsumed is expected here, not a defect — but it is the hazard class
MRS.0b was invented for, so record it. (2) ⚠ **`MixParams.Phys` is a naming trap** — it means "ordered
positive diameters + entrywise positive matrices", **not** the Lebowitz PY coefficients;
`Q0phys`/`Qppphys`/`rhoGeoPhys` appear in **none** of the three MZERO files, so `hP : P.Phys` must not
be read as "instantiated at the physical mixture". (3) **The physical bridge is available and
favourable but unwritten** — `Q0phys`/`Qppphys` are manifestly entrywise positive for `vac>0, σ>0,
ρ≥0`; checked at the reference mixture (η=0.4549) `min Q0phys = 19.03`, `min Qppphys = 26.53`, and the
zeros were located at those **physical** coefficients (8 zeros, `|detC| ≤ 3.4e-15`, mean Im spacing
**3.098** vs predicted `2π/σ₁ = 3.1416`, reproducing MZERO.2's GO gate). ⇒ **MZERO.12 written, see
the row below.**

| Task | Title | Status | Route / Lean file |
|------|-------|--------|-----------|
| MZERO.1 | Infinitely many HS poles for N=2: `det(Q̂₀(s))=0` has infinitely many complex roots (analog of `POLE.3`) | ✓ **DONE (2026-07-17) — CLOSED via MZERO.5**: `detC_zeros_infinite_unconditional` (`HSMixture/MixtureChordFamily.lean`, axiom-clean, parameter-only hypotheses `0<σ₀<σ₁`, `rr/Qp/Qpp>0`). Foundation (earlier, axiom-clean): `Q0_det_c_tendsto_one`, `q0_diag_c_tendsto_one`, `q0_offdiag_prod_tendsto_zero`, `Q0_det_c_not_identically_zero`, holomorphy `Q0_det_c_differentiableAt` (s≠0). … | `HSMixture/MixtureChordFamily.lean`, `MixtureHSZeros.lean` |
| MZERO.2 | *(Python, POLE.2 analog — GO/NO-GO gate)* feasibility | ✓ **GO** (`verify_mixture_hs_poles.py`): quasi-periodic zero family (Δ Im≈π, 22 zeros to Im≈239), chord-Newton `g=s−F/F'(s1)` on `r=0.15` — both Banach conds hold uniformly, **K≈0.30–0.35 (does NOT drift to 1)**, self-map gap≪r(1−K). Banach path viable w/ chord-Newton | Banach; `verify_mixture_hs_poles.py` |
| MZERO.3 | generic chord-Newton Banach wrapper (Lipschitz self-map ⇒ ∃ zero); map-independent | ✓ DONE (axiom-clean): `chord_zero_exists_of_bounds` (via `ContractingWith.exists_fixedPoint'`) | Banach; **`Analysis/BanachPoleFamily.lean`** (ns `FMSA.BanachPoleFamily`; migrated out of `MixtureHSZeros.lean` by MRS.9b) |
| MZERO.4 | chord map `s↦s−F s/Fp1` + `fp ⟺ F=0` (unconditional; simpler than log-map, no branch-safety) | ✓ DONE (axiom-clean): `chordPhi`, `chordPhi_fixedPt_iff` | Banach; **`Analysis/BanachPoleFamily.lean`** (ns `FMSA.BanachPoleFamily`) |
| MZERO.5 | magnitude bounds: `‖1−det′(s)/det′(s₁)‖ ≤ K` (chord-Lipschitz) + self-map `hstep` (`‖det(s₁)/Fp1‖ ≤ r(1−K)`) | ✓ **DONE (2026-07-17) — CLOSED**, axiom-clean, no sorry, full build green: `chordPoleFamily_detC_exists` + **`detC_zeros_infinite_unconditional`** (`HSMixture/MixtureChordFamily.lean`, 3497 lines) — hypotheses = parameter positivity/ordering ONLY (`0<σ₀<σ₁`, `rr/Qp/Qpp > 0`) ⇒ **MZERO.1 CLOSED too**. … See [proof_notes_mixture_rdf.md](proof_notes_mixture_rdf.md) MZERO.5. | `HSMixture/MixtureChordFamily.lean` |
| MZERO.6 | `LipschitzOnWith K (chordPhi F Fp1) ball` (from `HasDerivAt`+MZERO.5 bound) + `MapsTo` disk-into-itself | ✓ DONE (axiom-clean): `chordPhi_lipschitzOnWith` (`Convex.lipschitzOnWith_of_nnnorm_deriv_le`), `mapsTo_closedBall_of_lipschitzOnWith_of_dist_le` | Banach; **`Analysis/BanachPoleFamily.lean`** (ns `FMSA.BanachPoleFamily`) |
| MZERO.7 | single-`n` (`det_zero_exists_for_n`) → Im-spaced family (`Q0_det_c_pole_family_exists`) → distinctness ⇒ `{s:det=0}` infinite | ✓ DONE (axiom-clean): `Q0_det_c_zeros_infinite` (`Set.Infinite`, via `Set.infinite_of_injective_forall_mem`) — the ∀-hypothesis layer, formerly conditional on MZERO.5. **2026-07-17: MZERO.5 CLOSED**, and the unconditional conclusion is now available directly as `detC_zeros_infinite_unconditional` (`MixtureChordFamily.lean`, parameter-only hypotheses) | Banach; `MixtureHSZeros.lean`, `MixtureChordFamily.lean` |
| MZERO.8 | `det(Q̂₀)` meromorphic (for Jensen) | ✓ **DONE** (`det_meromorphicAt`/`det_meromorphicOn`): meromorphic algebra (`φ=entire/sⁿ` ratio) + `fun_prop` — **no continuation needed**, s=0 hard part dissolves | Rouché; `MixtureHSZeros.lean` |
| MZERO.9 | `divisor det ≥ 0` + Jensen-counting bound (`hJensen`) | ✓ **`divisor det U ≥ 0` now UNCONDITIONAL** — `det_divisor_nonneg` (axiom-clean). The "det has a limit at `0`" hyp of `det_divisor_nonneg_of_tendsto` is discharged by the Baxter removable values `φ₁(0)=−σ²/2`, `φ₂(0)=σ³/6` (`phi1_tendsto`/`phi2_tendsto`, from exp-Taylor `(e^w−1−w)/w²→½` `expTaylor2`, `(e^w−1−w−w²/2)/w³→⅙` `expTaylor3`) → `q0_entry_c_tendsto` → `detC_tendsto`. … | Rouché; `MixtureHSCounting.lean` |
| MZERO.10 | boundary growth → hypothesis | ✓ `DetBoundaryGrowth` + `detBoundaryGrowth_of_linear` (a `≥c·R` estimate ⟹ it, via `isLittleO_log_id`). Axiom-clean. **⚠ EQUIVALENT to MZERO.1 (2026-07-16, PROVED `detC_boundaryGrowth_iff_infinite_zeros`, axiom-clean, `0<σᵢ`):** via Jensen `circleAverage(log‖detC‖) 0 R = ∫n(t)/t dt+const`, super-log growth ⟺ ∞-many zeros. … | Rouché; `HSMixture/MixtureHSCounting.lean` + **`Analysis/BoundaryGrowth.lean`** (`DetBoundaryGrowth`, `detBoundaryGrowth_of_linear`, ns `FMSA.BoundaryGrowth`) |
| MZERO.11 | Jensen capstone ⇒ ∞ many zeros | ✓ **structural capstone** `infinite_zeros_of_growth` + `detC_zeros_infinite_of_growth` (indep. Route-B proof of `Set.Infinite {detC=0}`, matches Route A). Axiom-clean; reuses `det_meromorphicOn` (MZERO.8). **With MZERO.9's `hJensen` now proved, `detC_zeros_infinite_of_boundaryGrowth` gives the infinitude modulo ONLY `DetBoundaryGrowth` (MZERO.10)** — the hJensen hypothesis is discharged | Rouché; `HSMixture/MixtureHSCounting.lean` + **`Analysis/BoundaryGrowth.lean`** (`infinite_zeros_of_growth`) |
| **MZERO.12** *(new 2026-07-31)* | **The PHYSICAL instantiation** — MZERO.1/5 at the Lebowitz PY coefficients, not merely at an entrywise-positive parameter pack | ✓ **DONE, axiom-clean, build green (8716)** — new **`HSMixture/MixtureZerosPhys.lean`** (a *new file*, so `MixtureChordFamily.lean` and the rest of the MML.8 working set are untouched). `Pdens_one` (`Pdens sigma rho 1` **is** the physical pack, `1•ρ=ρ`) → **`detC_zeros_infinite_phys`** (`0<σᵢ`, `σ₀<σ₁`, `0<ρᵢ`, `η<1` ⇒ `{s \| detC ![σ₀,σ₁] ↑rhoGeoPhys ↑Q0phys ↑Qppphys s = … [detail in linked notes] | `HSMixture/MixtureZerosPhys.lean` |


### Group MPOLY — Mixture Inner-Core Polynomial Coefficients *(mixture_dcf)*

*(optional)* Faithful inner-core polynomial coefficients `D_ij = R'_ij(0)/6` (and A,B,C,E⁴) via the
inside-core Laplace remainder `R_ij(s) = s⁵[e^{sR}·S_ij(s) − Y_ij(s)]` ([LN] §9.4, Eqs 106–120) —
promotes **GAP.9 Option B** (cubic-coefficient *mechanism*, DONE) to the exact `R'_ij(0)/6` identity.
Decomposed into MPOLY.1–MPOLY.5; **MPOLY.1–MPOLY.3 DONE** (2026-07-16,
axiom-clean — the order-4 Taylor calculus + `Δ_Q` + inverse entry). **MPOLY.4–MPOLY.5 ❌ NOT COMPLETABLE —
falsified 2026-07-17:** [LN] Eq (101)'s single deg-≤4 `P_ij` holds only for **like** pairs; for **unlike**
pairs the inner core **splits at `λ_ij`** (`fmsa_double_prop` closed form: `(0,λ)` deg 1 / `(λ,R)` deg 4), so
the target unlike `D_01` does not exist (rigidity `not_single_poly_of_pieces_ne`, IB.4). A second, independent
contradiction: the shipped `Ĉ₁=Q̂₀(−k)B₁(k)Q̂₀ᵀ(−k)` has **no `Q̂₀⁻¹` and no HS poles**, against the MPOLY
umbrella's "`S_ij` involves `Q̂₀⁻¹`". **What survives** = the generic order-4 Taylor machinery (MPOLY.1–3) +
`taylor4_coeff_unique`, reusable off Eq (101). Correct path for the piecewise inner core = **Group MRS**
(real-space Baxter, `MRS.5`). See [proof_notes_mixture_dcf.md](proof_notes_mixture_dcf.md) Group MPOLY.

✅ **AUDITED 2026-07-31 — group CLOSED, three corrections.** (1) **Falsification re-verified exactly on
the current tree**, no fitting: reading the analytic pieces and forming `f = 𝒲(r)−𝒲(−r)` symbolically
gives `+1.1115·r` on `(0,λ₀₁)` (deg 1, zero constant — both `±r` land in the same `[−λ,+λ]` piece so
`f` is odd there) versus `−1.2813 + 1.1890r + 0.2029r² + 0.0447r⁴` on `(λ₀₁,R₀₁)` (deg 4, nonzero
constant, `r³`/`r⁵` absent); max coeff difference **1.2813** ⇒ no single `Q`. **Digit-for-digit
identical to the 2026-07-17 record**, so `b3896eb`/"General N" did not invalidate it; like pair `(0,0)`
(`λ=0`, one piece) confirms Eq (101) is correct there. ⚠ **Epistemic status:** the *rigidity* is a Lean
theorem, the *premise* `P₁≠P₂` is a machine computation from the validated closed form — a disproof by
counterexample, not a Lean disproof. (2) **All file paths in the MPOLY notes are stale — MRS.9d moved
this code 2026-07-27.** `HSMixture/MixtureLaurent.lean` **no longer exists**: the order-4 Taylor calculus
(incl. both survivors `taylor4_coeff_unique`/`poly4_eq_zero_of_littleO`) is now **`Analysis/Taylor4Calculus.lean`**
(ns **`FMSA.Taylor4`**), only `q0_entry_taylor4`/`taylor4_inv_entry` remain in **`HSMixture/MixtureLaurent.lean`**,
and `MixturePolyCoeffs.lean`'s namespace is **`FMSA.MixturePoly`**. **That move upgraded "what survives"
from mixture leftovers into a general-purpose `Analysis/` library.** (3) `#print axioms` on all 18
MPOLY-related declarations = **standard three**; GAP.8's vacuity re-confirmed by reading the proof term
(`⟨…, rfl×5⟩`, `hR : AnalyticAt` unused).

| Task | Title | Status | Route / Lean file |
|------|-------|--------|-----------|
| MPOLY.1 | *(MPOLY pipeline)* order-4 Taylor of `q0_entry` = `δ − ρ·Ep₄·Pp₄` (the 5-coeff `q_ij(s)=q^[0]+…+q^[4]s⁴` structure, [LN] Eq 134) | ✓ DONE (axiom-clean, re-verified 2026-07-31): `q0_entry_taylor4` + `p1_quartic_coeff`(`−σ⁶/720`), `p2_quartic_coeff`(`σ⁷/5040`), `exp_neg_quartic_rem`; extends GAP.9's `q0_entry_taylor3` by one order (`Real.exp_bound`) | `HSMixture/MixtureLaurent.lean` (`q0_entry_taylor4`) + `Analysis/Taylor4Calculus.lean` (the `p*` lemmas) |
| MPOLY.2 | *(MPOLY pipeline, ✓ re-verified 2026-07-31)* reciprocal series `1/Δ_Q`: `δ₀=1/d₀`, `δₙ=−(1/d₀)Σₘ dₘδₙ₋ₘ` ([LN] Eq 136–137) | ✓ DONE (2026-07-16, axiom-clean): `taylor4_recip` — `Tendsto` convention, `rₖ` as the Eq-137 hyps; cleared convolution `e0..e4` + tail identity `1−P₄Q₄=z⁵(c₅+…)` via `linear_combination (-1)*e0+(-z)*e1+…`. **Route note: `PowerSeries.inv` is a TRAP** (no `FormalMultilinearSeries.inv`/`HasFPowerSeriesAt.inv`; `AnalyticAt.inv` coefficient-free; 0 `PowerSeries` uses in `LeanCode/`). … | **`Analysis/Taylor4Calculus.lean`** (ns `FMSA.Taylor4`; moved by MRS.9d 2026-07-27 — the note's `MixtureLaurent.lean` is stale) |
| MPOLY.3 | *(MPOLY pipeline, ✓ re-verified 2026-07-31)* `Δ_Q=q₁₁q₂₂−q₁₂q₂₁` order-4 coeffs (from MPOLY.1) + `[Q̂₀⁻¹]₀₁=−q₁₂·(1/Δ_Q)` order-4 series ([LN] Eq 130; **analytic at 0**… | ✓ DONE (2026-07-16, axiom-clean): order-4 Taylor **calculus** `taylor4_tendsto_const`/`taylor4_mul` (Cauchy product)/`taylor4_sub`/`taylor4_neg`, then `taylor4_deltaQ` (Eq 131/135) + `taylor4_inv_entry` (Eq 130) as pure compositions. **Deps MPOLY.1, MPOLY.2 — NOT MML.1** (MML.1 is over ℂ, the MPOLY Taylor line is over ℝ; Eq 131 is stated algebraically over abstract `q_ij`, sidestepping the seam). … | **`Analysis/Taylor4Calculus.lean`** (the `taylor4_*` calculus) + **`HSMixture/MixtureLaurent.lean`** (`taylor4_inv_entry`) |
| MPOLY.4 | *(MPOLY pipeline)* Laurent→coeff machinery (Eq 105/120) | ❌ **NOT COMPLETABLE (2026-07-17)** — the target does not exist. (a) It was to "extend GAP.8", but **GAP.8 is vacuous** (`∃` closed by 5 `rfl`s; its `AnalyticAt` hypothesis is unused) ⇒ nothing to inherit. (b) More fundamentally: [LN] Eq (101)'s **single** deg-≤4 polynomial `P_ij` is **falsified for unlike pairs** (see MPOLY.5) ⇒ there is no `P_ij` to extract. … | ~~`MixtureLaurent.lean`~~ → survivors in `Analysis/Taylor4Calculus.lean` |
| MPOLY.5 | *(MPOLY pipeline, ex-CRUX)* exact `S_01` ⇒ `D_01=R'_01(0)/6` | ❌ **NOT COMPLETABLE (2026-07-17)** — **premise falsified**. Decisive evidence (structural, not a fit): reading the shipped, validated `fmsa_double_prop` closed form (2YK) shows the **unlike** pair (0,1) inner core **splits at λ_ij**, with different rate-0 polynomials on the two sides — `(0,λ)`: `f_poly = 1.111·r` (degree 1, zero constant ✓ [LN] Eq 102 origin regularity); `(λ,R)`: `−1.281 + 1.189r … | ~~new `YukawaDCF/…`~~ |

### Groups MSAEXACT / MSAEMIX — The Exact MSA Closed Form *(msa_exact)*

Waisman/Blum–Høye/Ginoza analytic MSA for a hard-core Yukawa fluid, split scalar (**MSAEXACT**) /
matrix (**MSAEMIX**). **No new axiom** (algebra over ℝ, `e^{−zσ}` a parameter). Detail, substrate,
boundaries, non-vacuity: [proof_notes_msa_exact.md](proof_notes_msa_exact.md). Numerical: Group MSAX.

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| MSAEXACT.1 | non-compact Baxter factorization `\|1−ρQ̂(ik)\|²=1−ρĉ_MSA` | ◑ **reduced to MSAEXACT.6** (staged via `factorization_of_core`); ⛔ compact `msaexact1_iff_core` route dead | `YukawaOZ/{MSABaxterKSpace,MSAFullFactorization}` |
| MSAEXACT.6 ⭐ | **the gap** — discharge the `hcore` closure-recovery ring | ⊘ **`ring`-INFEASIBLE, measured 2026-08-22** (clean 323-mono deg-22 slice = `ring` 3h12m/23GB; irreducible per-order reassembly ~weeks/~200GB; atom form worse deg≈35; `native_decide` blocked by noncomputable `MvPolynomial`). ✅ **Fourier layer DISCHARGED** (`YukawaOZ/MSAExact6Certificate.lean`, out-of-`defaultTargets` lib): `msaexact6_hcore_of_residual` ⇒ exact `msaexact6_hcore` statement from ONE pure-cos/sin/exp axiom `msaexact6_kspace_residual`. **"Upgradeable/30-min" RETRACTED.** Sole gap of .1, MSAFAM.5/.6@N=1; MSAEMIX.1 = matrix analog | `YukawaOZ/{MSAFullFactorization,MSAExact6Certificate}` |
| MSAEXACT.2 | degree-8 elimination = two quartics; physical branch quartic | ✓ DONE | `YukawaOZ/MSAElimination` |
| MSAEXACT.3 ⭐ | `msaRoot_unique_of_coupling_lt` — unique physical root below coupling threshold | ◑ core DONE (`βK≈3` measured) | `YukawaOZ/MSAClosedForm` |
| MSAEXACT.4 | PY coeffs annihilate Waisman's eqns at `K=0`, ∀`w` | ✓ DONE | `YukawaOZ/MSAClosedForm` |
| MSAEXACT.5 ⭐ | `fmsa_eq_firstOrder_msa` — 1st-order MSA = FMSA-DP HS-dressed amplitudes | ✓ DONE (needs FOEQ.5 for "linearise"="differentiate") | `Closures/FirstOrderEquivalence` |
| MSAEMIX.0 ⭐ | mixture positivity + stability det (spinodal = `det F=0`) | ✓ DONE | `YukawaOZMix/MSAMixturePositivity` |
| MSAEMIX.1 | matrix factorization (matrix form of MSAEXACT.1) | ◑ (★) cancellation DONE + **staged to matrix `hcore`** (`matEMIXfactorization_of_core`, analog of MSAEXACT.6) | `YukawaOZMix/{MSAMixtureCancellation,MSAEMixFactorization}` |
| MSAEMIX.2 | `N=1` reduces to MSAEXACT.1 | ◑ positivity half; factorization half ← MSAEMIX.1 | `YukawaOZMix/MSAMixturePositivity` |
| MSAEMIX.3 ⭐ | Eq.(41) mixture root selection = `g_ij=g_ji` | ✓ DONE | `YukawaOZMix/MSAMixtureSelection` |

### Group FOEQ — The Two Definitions of "First Order" Agree *(closures)*

**Opened 2026-08-10** (paper §IV). Two definitions of "first order": **(D1)** truncate the hierarchy order-by-order at `γ=1` (what the WH construction builds; unconditional); **(D2)** `c⁽¹⁾ = d/ds[c_MSA(sK)]|₀` (differentiate the exact family; needs only differentiability at `s=0`). FOEQ proves they agree. ⚠ Distinct from MSAEXACT.5 (which *assumes* the derivative exists — the gap) and from PYE (which identifies *which* closure). → [closures](proof_notes_closures.md) Group FOEQ.

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| FOEQ.1 | `msa_exterior_linear_in_coupling` — the MSA exterior is `c = −βsU`, **linear in `s`**, so on `r>R_ij` (D1) and (D2) are the *same expression*, with no remainder and no `O(s²)` | **✓ DONE 2026-08-10** as `msaOuter_hasDerivAt` + `msaOuter_eq_smul_deriv` + `mayerF_ne_msaOuter` (`Closures/FirstOrderEquivalence.lean`). ⚠ `msa_first_order_outer` does **not** already say this: it is the `y₀ ↦ 1` case of the *Mayer* factor `e^{−βsu}−1`, which agrees with MSA at first order but is not the MSA closure. The honest statement is `HasDerivAt` at **every** `s` with vanishing second derivative | `Closures/ClosureExpansions.lean` |
| FOEQ.2 | the WH split's support obligations are **coupling-independent** (`h_ij = −1` on `r<R_ij` is exact at every `s`; `R_ij` is core data, not tail data) | ☐ **record only — discharged by construction.** The supports are already `s`-free constants in every WH statement in the tree, so there is nothing to prove. Named anyway because it is precisely what a *moving-boundary* perturbation problem violates, and there order-by-order solution and differentiation do **not** commute. A reader who does not see it named will assume it needs an argument, or worse, will not notice it was needed | — |
| FOEQ.3 ⭐ | `oz_gamma_one_is_the_derivative_equation` — differentiating `(I+H̃)(I−C̃) = I` at `s=0` returns the `γ=1` line **term for term**. OZ is quadratic, so this is the product rule  | **✓ DONE 2026-08-10** as `oz_deriv_eq_firstOrderLine`, axiom-clean. ⚠ **Do not state it at `Matrix`** — the `HasDerivAt` hypotheses elaborate with the ambient `Pi` topology while `HasDerivAt.mul` supplies `Matrix.linftyOp*`, and they are not defeq. Over an abstract `[NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]` it goes through at once, and matrices follow by `open scoped Matrix.Norms.Operator` + instantiation. No new axiom | `Closures/FirstOrderEquivalence.lean` |
| FOEQ.4 | `first_order_solution_determined` — the `γ=1` equation **plus** the `s`-free support conditions determines `C̃₁`, so (D1)'s answer *is* the derivative once FOEQ.3 supplies the equation | ◑ **algebraic half done 2026-08-10** — `firstOrder_dcf_of_oz_deriv` gives `C̃₁ = Hinv·(H₁(I−C̃₀))` from a left inverse of `I+H̃₀`. The WH-uniqueness half still wants PYE.2 linearity (`dpDCFLinear`) + `radial_fourier_injective` (PYE.5) / `MixtureDCFAEInjective` | `Closures/FirstOrderEquivalence.lean`, `Closures/DPClosureMap.lean` |
| FOEQ.5 ⭐⭐ | `msa_solution_differentiable_at_zero_coupling` — **the one input algebra does not settle.** The physical MSA root is differentiable in `K` at `K=0`, by the implicit function t | ◑ ⭐ **the Jacobian condition is CLOSED (2026-08-10), in closed form.** At the PY base point `Dt = 0`, which kills every `G`-dependence (it enters only through `M,N ∝ Dt`), so the Jacobian is block lower-triangular and `det J = (2π)^n ∏_u F₀(z_u)²` — verified numerically to 6e-11…9e-10 over ξ∈{0.05,0.20,0.40,0.49} × n∈{1,2,3}. Nonsingular ⟺ `F₀(z_u) ≠ 0`, which is **`Q0_ne_zero_at_yukawa`, already proved**. … | `Closures/…` |

### ⭐⭐ Scope raised to arbitrary order (2026-08-10, paper Theorem IV.1)

FOEQ.1–5 were `γ=1`; **the equivalence holds at every order** (product rule → general Leibniz, in Mathlib). FOEQ.6–9 add the general-order versions (FOEQ.1/3 stay as the `γ=1` instances the paper consumes). Consequences: (a) the hypothesis becomes `C^∞` differentiability at `s=0` — still weaker than analyticity; (b) what's special about first order is only **finite-closed-form solvability** — the middle convolution `∑_{m=1}^{γ−1}` is empty iff `γ=1` (FOEQ.9).
| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| FOEQ.6 | `msa_closure_taylor_coeffs_terminate` — generalises FOEQ.1 to all orders. The closure is a **degree-≤1 polynomial in `s`**, so its Taylor coefficients are identities that *ter | **✓ DONE 2026-08-10** as `msaOuter_iteratedDeriv_terminates` (+ reusable `iteratedDeriv_linear_higher`: a degree-≤1 `s↦s•c` has `iteratedDeriv γ = 0` for `γ≥2`). Contrast PY/HNC, whose Mayer exterior has a nonvanishing coefficient at **every** order — FOEQ.1's `mayerF_ne_msaOuter` is the `γ=1` shadow of that | `Closures/FirstOrderEquivalence.lean` |
| FOEQ.7 ⭐ | `oz_taylor_coeff_eq_cauchy_convolution` — generalises FOEQ.3 to order `γ`. Dividing `∑ᵢ C(γ,i)·f⁽ⁱ⁾·g⁽ᵞ⁻ⁱ⁾` by `γ!` turns the binomial into `1/(i!(γ−i)!)`, so the order-`γ` co | **✓ DONE 2026-08-10, load-bearing** (`oz_taylor_coeff_eq_cauchy_convolution`). Via **`iteratedDeriv_mul`** applied to the *constant* product `(1+H̃)(1−C̃)=1`, so its order-γ coefficient (`iteratedDeriv_const`, γ≥1) is `0` = the finite Cauchy convolution. Hypothesis `ContDiffAt ℝ γ` (γ-fold, **not** `C^∞`), over abstract `[NormedRing 𝔸][NormedAlgebra ℝ 𝔸]` *not* `Matrix` (FOEQ.3 pitfall inherited). Axiom-clean | `Closures/FirstOrderEquivalence.lean` |
| FOEQ.8 ⭐ | `oz_msa_taylor_eq_hierarchy` — the capstone: assemble FOEQ.6+FOEQ.7 (+FOEQ.2) into *for every `m ≤ γ`, the order-`m` Taylor coefficient of the exact solution satisfies the ord | **✓ DONE 2026-08-10** as `oz_msa_taylor_eq_hierarchy` (`∀ m≥1` from FOEQ.7 under `ContDiff ℝ ∞`) + the `γ=1` corollary `oz_deriv_eq_firstOrderLine_of_taylor` (`iteratedDeriv 1 = deriv`, recovers FOEQ.3's `deriv H 0·(1−C 0)=(1+H 0)·deriv C 0`). Axiom-clean | `Closures/FirstOrderEquivalence.lean` |
| FOEQ.9 | *(record only)* the empty-convolution characterisation: `∑_{m=1}^{γ−1}` is empty **iff** `γ=1` | **✓ DONE 2026-08-10** as `cauchy_convolution_middle_empty_iff` (`Finset.Ico 1 γ = ∅ ↔ γ=1`, via `Finset.Ico_eq_empty_iff`+`omega`) — the precise statement of what §XII's obstruction *is*, naming it prevents the misreading that higher orders are ill-defined rather than merely not closed-form | `Closures/FirstOrderEquivalence.lean` |

**Numerical witness for FOEQ.5** (it is measured, not proved — say so wherever it is quoted;
⚠ it is also **`γ=1` only**, so it does not test FOEQ.6–8):
BH-linearised ≡ FMSA-DP to **6.4e-7 … 2.8e-5** over 25 states, `η ∈ [0.05,0.40]`, `z ∈ [1.8,28.75]`,
on `∂_K(∂βp/∂ρ)` at `N=1`; central difference in `±s` of converged OZ+MSA agrees to **5e-6**, with the
estimator itself linear in `s` to 2e-5 between `s=1e-4` and `1e-5`. Neither is evidence that the
derivative *exists* — both presuppose it.

**Constraint: no new axiom.** FOEQ.1–4 are calculus and linear algebra; FOEQ.5 is the IFT on an
algebraic system over `ℝ` with `e^{−zσ}` a parameter. Needing an axiom means a route was abandoned.

⚠ **Do not mark FOEQ closed on FOEQ.1–4 alone.** Those give "(D1)=(D2) *as soon as the derivative
exists*", which is the algebraic half and is not the claim. Without FOEQ.5 the group's headline
remains conditional, and the paper's §"What is *not* formalized" must keep saying so.

### Group PYE — No-Pull-Back Construction ≡ First-Order PY *(closures)*

The `pullback_passes=0` YK-tail FMSA-DP construction **is** first-order PY; the only error vs true
first-order PY is the finite-Yukawa-tail re-approximation of the outer closure `g_HS·(−βu)`. Sits on
Groups Y1 (DP linearity) + MRS (finite closed form). Source: `hncb_first_order.md`, `HNCB_FMSA_dp.py`.
See [proof_notes_closures.md](proof_notes_closures.md) Group PYE.

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| PYE.1 | PY closure to O(coupling): outer `c₁ = g_HS·(−βu)` (`y₀=g_HS`) | ✓ DONE (2026-07-31, axiom-clean): `py_first_order_outer`, `cavity_zero_coupling`, `py_first_order_outer_cavity`, `msa_first_order_outer`; **+ the γ₁-collapse** `pass_zero_eq_py_first_order` (with `hncbClosure`, `hncb_first_order_outer`, `hncb_outer_zeroth_order_eq_zero`) | `Closures/ClosureExpansions.lean` |
| PYE.2 | DP first-order solution map **linear** in the outer closure (corollary of Y1 `bMulti`/`Ĉ₁` linearity) | ✓ DONE (2026-07-31, axiom-clean): `b1OfCouplingLinear` (Y1.5 `bMulti` linear in `K`) ∘ `starConjLinear` ((★), MRS.3) = `dpDCFLinear`, fixed-rate family `dpTailsLinear`; stage 1 `outerTransform_add/_smul`. ⚠ needs the rates **frozen** — free rates sit in `s + z_mp` and the map is not linear | `Closures/ClosureExpansions.lean` |
| PYE.3 ⭐ | **DCF error = DP-map[finite-tail fit residual]** ⇒ "only error = the YK re-approximation"; needs `wh_solution_operator_bounded` *(recommended first target)* | ✓ DONE (2026-07-31, axiom-clean): `dp_error_eq_dp_of_residual` (= `map_sub`), physical form `dp_sub_py_first_order_eq_conj_residual` (via MRS.2 `star_of_first_order_oz`), headline `dp_error_entry_norm_le`. **`wh_solution_operator_bounded` is a THEOREM, not a new axiom** — explicit `whOperatorBound = T·N⁴·Qb²·Ab²/δ` | `Closures/ClosureExpansions.lean` |
| PYE.4 | Abstract equivalence `DP-map[g_HS·(−βu)] = OZ+PY first order` (needs WH map lifted to an L¹/L² function-space closure) | ◑ partial (2026-07-31, axiom-clean): `dp_eq_py_first_order_of_exact_fit` + `dpDCF_entry_tendsto`/`dp_tendsto_py_first_order`; the lift itself is carried by the `Prop` `TailFitWHConvergent` (**not** an axiom) — see the Open-tasks row | `Closures/ClosureExpansions.lean` |
| PYE.5 | **`k → r` bridge** — k-space `Ĉ₁` identity ⇒ real-space `c₁(r)` on the core `(0,R)` | ✓ DONE (2026-08-03, axiom-clean): `radial_fourier_injective` (on the project's own `radial_inversion`, a theorem not an axiom), dictionary `IsRadialEntry`, `inner_core_dcf_eq_of_khat_eq`, capstone `inner_core_dcf_eq_of_exact_fit` + structural non-vacuity `example`. ⚠ open core only (contact jump), and **no real-space error bound** (`k·Ĉ₁(k) ∉ L¹` under a k-uniform bound) | `Closures/ClosureExpansions.lean` |
| PYE.6 | the zeroth-order factor **is** the PY hard-sphere Baxter factor | ✓ DONE at `N = 1` (2026-08-03, axiom-clean) — **the library already had it**: BAXTER.3 `baxter_wiener_hopf_complex` (= MRS.8 at `N=1`) + `pyhs_no_spinodal` + the MRS.0b chain `Q0phys_n1`/`Qppphys_n1`/`qhat_complex_eq_mixture_kernel`. Wired in as `pyBaxterMat`/`pyT0Mat`/`pyT0Mat_entry`/`pyT0Mat_isUnit_det`/`dp_zeroth_order_is_py_n1`/`dp_eq_py_first_order_n1` ⇒ `hfact`+`hT0symm`+`hTS` discharged with the physical PY objects, … | `Closures/{ClosureExpansions,DPClosureMap}.lean` |
| PYE.7 | density of finite Yukawa-tail fits ⇒ PYE.3's residual → 0 on the outer window | ✓ DONE (2026-08-03, axiom-clean): `exists_yukawa_tail_fit` (+ `_pyOuter` for the actual target `r·g_HS·(−βu)`). **Route: Weierstrass after `t = e^{−r}`, NOT Stone-Weierstrass** — polynomials in `e^{−r}` *are* exponential sums, so no adjoin/span extraction; one `δ`-shift makes the `k=0` constant a legal tail. Rates come out **unit-spaced** (third independent argument for fixed separated rates). … | `Closures/ClosureExpansions.lean` |

### Group HNCB — First-Order HNCB Bridge Pull-Back Construction *(closures)*

The whole **fixed-rate** first-order HNCB (`'solve'`) = closure expansion + finite `(I−L)⁻¹` + DP map
+ linear OZ apply — finite linear algebra, the finite-tail truncation the only approximation. Exact
self-consistent HNCB-1 is the **RDF** ⇒ HS poles ⇒ not finite-closed-form (HNCB.4, boundary). See
[proof_notes_closures.md](proof_notes_closures.md) Group HNCB.

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| HNCB.1 | HNCB closure to O(coupling): outer `c₁ = −βu + B·h₁`, `B=h_HS/g_HS=1−1/g_HS` | ✓ **DONE (2026-08-03, axiom-clean)**. `exp`-form half (PYE.1 by-products): `hncbClosure`, `hncb_outer_zeroth_order_eq_zero`, **`hncb_first_order_outer`**, `pass_zero_eq_py_first_order`. Audit additions: `hncb_base_point_gamma_eq` (the two hypotheses **force `γ₀ = g_HS−1 = h_HS`**) + non-vacuity `example`. … | `Closures/ClosureExpansions.lean` |
| HNCB.2 | Fixed-rate pull-back map **affine** `K̃'=a+L·K̃` (reuses Y1 `Ĥ₁`) | ☐ not started | new `…Closures.lean` |
| HNCB.3 | Fixed point `K̃*=(I−L)⁻¹a`; `(I−L)` invertible (finite matrix) | ☐ not started | new `…Closures.lean` |
| HNCB.4 | *(record only)* Exact HNCB-1 carries the RDF `h₁` ⇒ HS poles ⇒ not finite-closed-form (MZERO/MML.5 wall) | ☐ **boundary marker, NOT a to-do** — nothing to prove; the `☐` reads like unstarted work and is not | — |

### Group GA — FMSA_GA_matrix_mix Inner-Core Conditioning Failure *(failures)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| GA.1 | Unlike-pair two-exp base unbounded `K·exp(z·R)→∞`; additive HS-pole sum (≤ C/z²) cannot cancel it | ✓ DONE, axiom-clean — `unlike_pair_twoexp_unbounded` + `hs_pole_additive_insufficient` + `residue_propagator_bound` (the last **discharges** the `hB` bound structurally: HS-only `A_k,s_k` are `z`-independent ⇒ `‖B_k‖ ≤ (4/3)·C·K/z²` for `2‖s_k‖≤z`; **no open hypothesis**) | `FMSAPoly/PolyApproxFails.lean` |
| GA.2 | *(opt.)* Off-diagonal `G_{01}(z)→0` exponentially as `z·(σ₁−σ₀)→∞`; structural cause of unlike-pair divergence | ✓ DONE, axiom-clean — mechanism (`g_mat_offdiag_decay'` Tendsto form / `g_mat_offdiag_decay` exp-bound form) + concrete N=2 discharge `g_mat_offdiag_decay_concrete` (`Q0_mat_phys 0 1/det→0`); rests on `p1/p2_tendsto_zero`⇒`Q0_mat_phys_offdiag01_tendsto_zero` + `Q0_mat_phys_det_tendsto_one` (`det→1`, **not** via the `Q0_moment_det_pos` axiom) | `YukawaOZMix/OffDiagDecay.lean`, `HSMixture/Q0DetLimit.lean` |
| GA.3 | **GA-matrix split's** unlike-pair ratio unbounded: `K·exp(z·R_{01}) / ‖c_HS_{01}‖ → ∞` as `z·R → ∞`. Corollary of GA.1: the split's growing branch dwarfs the… | ✓ DONE, axiom-clean — `perturbation_ratio_unbounded` (∀ `K>0`, fixed `z`-independent HS bound `M_HS>0`, target `M`: ∃ `(z,R)`, `M ≤ K·exp(z·R)/M_HS`); direct corollary of GA.1 at target `M·M_HS`; `M_HS` threaded as hypothesis (cf. `hs_pole_additive_insufficient`'s `hB`) | `FMSAPoly/PolyApproxFails.lean` |
| ~~GA.4~~ | ~~*(post-MML.8 corollary)* MSA `ε`-series convergence radius `R_conv ≤ C·e^{−z·R_{01}} → 0` as `z·R_{01} → ∞`~~ — **RETIRED 2026-07-17, doubly falsified.** (i)… | ✗ retired | — |


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
| OZ.2 | g₀_HS via OZ fixed point | ◑ fixed-point framework (`oz_h`, `oz_fixed_pt_unique`) live and reused by the Fourier line. See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) | `HardSphere/PYOZ_GHS.lean` |
| OZ.2b | Gap A: exterior 3D-OZ equation for `oz_h` (`oz_h_satisfies_conv_ext`) | ✓ DONE, transform-independent — reused verbatim by OZ.7. See [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) | `HardSphere/OZExteriorBridge.lean` |
| OZ.3 | g₀_HS via OZ Laplace inversion | ◑ conditional on OZ.2 + `oz_h_exterior_regularity` axiom (see CONTACT.5) | `HardSphere/PYOZ.lean`, `HardSphere/JumpAsymptotic.lean` |
| OZ.4 | Linearised OZ: Ĥ¹=Ĉ¹·S₀ | ✓ DONE | `HardSphere/PYOZ.lean` |
| OZ.6 | Radial sine/Fourier transform convolution theorem | ✓ DONE, no axiom | `HardSphere/RadialFourier.lean` |
| OZ.7 | Fourier-domain exterior OZ equation (Gap A ∪ Gap B) | ✓ DONE, conditional only on OZ.9 (`hcore`) | `HardSphere/OZFourierBridge.lean` |
| OZ.8 | Closed-form sine-transform formula for `c_HS` + bridge to `C_HS_laplace`/`S0` via `s↔-ik` | ✓ DONE (Parts A+B), no axiom/sorry. Bridge to `g0_HS_contact_value` — see Group CONTACT `CONTACT.1`/`5` | `HardSphere/RadialFourierCHS.lean` |
| OZ.9a | PY core closure (Gap B) for `r < σ` — promoted to a named, numerically-verified axiom | ✓ DONE (axiom `oz_core_closure`, Route A; not proved from Mathlib real-analysis — needs Group BAXTER's full construction, staged not started) | `HardSphere/PYOZ_GHS.lean` |
| OZ.9b | `oz_fourier_oz_eq_of_PY_core`: OZ.7 specialized to consume `oz_core_closure` instead of an externally-supplied `hcore` — most complete/trustworthy result in the whole OZ… | ✓ DONE | `HardSphere/OZFourierBridge.lean` |
| OZ.10 | Uniqueness of the OZ fixed point (`oz_fixed_pt_unique`) | ✓ **NO LONGER AN AXIOM** — `oz_fixed_pt_unique_thm` (`OzWienerHopfBounded.lean:153`) is a theorem. ⚠ It is *not* axiom-clean: `#print axioms` (2026-08-04) gives the standard three **plus** `radialShell_bounded_injective` (MA.15), `wiener_causal_resolvent` (MA.13) and `zeroFree_lowerHalfPlane_of_homotopy` (MA.14) — all **math** axioms, so the physics assumption is gone but three Mathlib gaps … | `HardSphere/PYOZ_GHS.lean` |
| OZ.10-dilute | Dilute-regime (`eta<1`, `24·eta·bracket<1`, i.e. `eta≲0.088`) Banach existence/uniqueness for `oz_fixed_pt_unique`, exterior-only | ✓ DONE — `oz_fixed_pt_unique_dilute`, genuine theorem, no axiom/sorry. Mid/high density (`eta≈0.3–0.5`) is TRUE but gated by the BAXTER line (K non-compact ⇒ not compact Fredholm; `24η·bracket` = K's spectral radius = the dilute threshold; Baxter factorization + POLE.4/Group OZFIX explicit inverse), not attempted here — see [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md) Task OZ.10-dilute. | `HardSphere/OzFixedPtDilute.lean` (+ `c_HS_abs_t2_integrableOn` in `HardSphere/PYDCF.lean`) |
| OZ.18 | Hard-sphere `λ_ij` kink: `c_HS,ij` is C⁰ (slope kink) at `λ_ij=\|d_i−d_j\|/2`, unlike pairs *(formerly B.19)* | ✓ **DONE, slope now CLOSED-FORM (2026-07-16, axiom-clean)** — C⁰ + both one-sided slopes; **`cHS_core_deriv_at_cutoff`: `F′(λ)=2(χ₂₂−χ₁/(4π))`** (all `χ₃/χ₂/χ₁` cancel; indep. of `Rᵢ,Rⱼ,χ₀,χ₂,χ₃`) ⇒ the ex-numerical `hslope` is now the elementary `χ₂₂≠χ₁/(4π)` (`cHS_core_deriv_at_cutoff_ne_zero_iff`, `cHS_FMT_not_differentiableAt_of_chi`). … | **✅ 2026-07-17: kink now UNCONDITIONAL on `0<η<1`** — `cHS_FMT_kink_WB`/`_fmt` (`CHSKinkWB.lean`, axiom-clean) discharges `χ₂₂≠χ₁/(4π)` via the closed form `χ₂₂−χ₁/(4π)=E_WB=n₂·g(η)/(12η²v²)` + `g_wb_pos` (`g>0` on `(0,1)` by nested monotonicity `g′=4p`, `p′=−log(1−η)>0`); vanishes only at the ρ→0 boundary. Left-slope cleaned by OZ.19. |
| OZ.19 | `c_HS,ij` **exactly constant on `(0, λ_ij)`** — interval flatness, **functional-agnostic** (weight-support geometry, no Φ). **Strengthens OZ.18**: left slope 0 ⇒ its… | ✓ **DONE 2026-07-17, axiom-clean** — `cHS_flat_of_convs_const` (reduction, ∀ Φ) + `cHS_fmt_inner_const` + the OZ.18-cleanup kink lemmas `hasDerivWithinAt_Iic_zero_of_flat` / `not_differentiableAt_of_flat_below_of_right_deriv` (kink off `clampedBelow`) | `HSMixture/CHSFlatInner.lean` |

**Tasks OZ.5, OZ.11–OZ.17 (and `OZ.13`) have moved to Group BAXTER**

### Group BAXTER — Baxter Q-Factor & Wiener–Hopf Factorization Foundations *(hard_sphere)*

*Depends on Group OZ above (uses `oz_h`, `c_HS`, `radial_fourier`, `oz_core_closure`, etc.);
Group OZ does not depend on this group. Feeds Groups CONTACT/POLE/OZFIX below. See
[proof_notes_baxter.md](proof_notes_baxter.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| `BAXTER.1` | Baxter real-space convolution identity *(formerly OZ.5)* | ✓ DONE | `HardSphere/BaxterRealSpace.lean` |
| `BAXTER.2` | Re-derive Baxter's second relation (Route B) from a primary source *(formerly OZ.11)* | ☐ not started — residue-series construction validated 3 independent ways (ground truth, pole-growth law, real-space OZ check); staged into Group POLE (`POLE.1`–`5`) + Group OZFIX (`OZFIX.1`–`8`) | — |
| `BAXTER.3` | Baxter's Wiener–Hopf factorization `(1-ρQ̂(k))(1-ρQ̂(-k)) = 1-ρĈ_sine(k)` *(formerly OZ.12)* | ✓ DONE — `baxter_wiener_hopf_factorization`, genuine theorem, no sorry/axiom; uses existing `q0_poly` | `HardSphere/BaxterWienerHopf.lean` |

### Group CONTACT — `g0_HS_contact_value` via the Jump-Asymptotic Route *(hard_sphere)*

*Split from Group BAXTER (`BAXTER.4`–`8`). Depends on Group BAXTER (`BAXTER.1`–`3`)
and Group OZ (`oz_h`, OZ.8/OZ.9b). See [proof_notes_contact.md](proof_notes_contact.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| `CONTACT.1` | Derive `g0_HS_contact_value` from OZ.8's Fourier-domain closed form (full residue inversion) *(formerly `BAXTER.4`/OZ.13)* | ☐ deliberately parked — fully absorbed into `BAXTER.2`'s scope, not independent | — |
| `CONTACT.2` | Extract `g0_HS_contact_value` via a jump-asymptotic argument on `Ĥ(k)`'s large-`k` behavior *(formerly `BAXTER.5`/OZ.14)* | ✓ DONE as a whole — split into `CONTACT.3`/`4`/`5`, all three done | — |
| `CONTACT.3` | General jump-asymptotic lemma for `radial_fourier`: `f k = 4πσJ·cos(kσ)/k² + o(1/k²)` for `f` with jump `J` at `σ` *(formerly `BAXTER.6`/OZ.15)* | ✓ DONE — `radial_fourier_jump_asymptotic`, genuine theorem, no sorry/axiom; via one IBP + Mathlib's Riemann-Lebesgue lemma | `HardSphere/JumpAsymptotic.lean` |
| `CONTACT.4` | Concrete closed-form asymptotic of `Ĥ(k)=Ĉ(k)/(1-ρĈ(k))`: leading coefficient `4πσ(1+η/2)/(1-η)²` *(formerly `BAXTER.7`/OZ.16)* | ✓ DONE — `Hhat_closed_asymptotic`, genuine theorem, no sorry/axiom | `HardSphere/RadialFourierCHS.lean` |
| `CONTACT.5` | Assembly: apply `CONTACT.3` to `oz_h`, match against `CONTACT.4`, conclude `g0_HS_contact_value` *(formerly `BAXTER.8`/OZ.17)* | ✓ DONE — `g0_HS_contact_value_of_oz_h_regularity` (conditional theorem, no sorry/axiom) **plus** its unconditional consequence: the bare `g0_HS_contact_value` axiom is now **retired**, replaced by `oz_h_exterior_regularity` bundling `CONTACT.5`'s `oz_h` hypotheses, from which `theorem g0_HS_contact_value` is proved. … | `HardSphere/JumpAsymptotic.lean` |

### Group POLE — Complex-Analytic Pole/Residue Construction for the Baxter Q-Factor *(hard_sphere)*

*Split from Group BAXTER (`BAXTER.9`,`10`,`11`,`12`,`14`). Depends on Group BAXTER
(`BAXTER.1`–`3`); feeds Group OZFIX. See [proof_notes_pole.md](proof_notes_pole.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| `POLE.1` | `Qhat_complex : ℂ → ℂ` in closed form, proved entire *(formerly `BAXTER.9`)* | ✓ DONE — `Qhat_complex_entire` + `Qhat_complex_formula`, genuine theorems, no sorry/axiom; entireness via `entire_poly_exp_integral` (dominated-convergence differentiation under the integral), closed form via new `zeta0`/`zeta1`/`zeta2` moment lemmas; numerically cross-checked against the raw integral and against `BAXTER.3`'s real-`k` formulas | `HardSphere/BaxterZeros.lean` |
| `POLE.2` | Numerical/symbolic feasibility check for the Banach-pole-existence strategy *(formerly `BAXTER.10`)* | ✓ DONE — **GO**: uniform contraction bound (`max_L→0.369`, margin `≈63%`) found for `n≥10`, robust across `η∈[0.05,0.45]` | — (Python, not Lean) |
| `POLE.3` | Pole existence in Lean via Banach contraction *(formerly `BAXTER.11`)* | ✓ DONE (conditional) — `Qhat_complex_zeros_infinite`, no sorry/axiom; all magnitude bounds, branch-safety, Lipschitz/MVT, Banach wiring, distinctness/infinitude proved unconditionally for general `η∈(0,1),σ>0,ρ>0`; one explicit "good guess" hypothesis (`hstep`, numerically validated by `POLE.2`) not yet discharged for the specific asymptotic guess formula. … | `HardSphere/BaxterPoles.lean` |
| `POLE.4` | Residue formula + convergence for `h_explicit` *(formerly `BAXTER.12`)* | ✓ DONE — `residue_of_simple_pole`, `Chat_complex`, `G_baxter_deriv`, `Hhat_residue_at_pole`, `G_baxter_zero_mirror`, `h_explicit`/`h_explicit_term`/`h_explicit_summable`, and `G_baxter_pole_family_exists` all done; `POLE.5` (below) closes the one remaining gap (the magnitude-bound hypothesis, now proved rigorously not just numerically). No sorry/axiom. | `Analysis/ResidueAtSimplePole.lean`, `HardSphere/BaxterResidue.lean`, `HardSphere/RadialFourierCHSComplex.lean`, `HardSphere/BaxterPoles.lean` |
| `POLE.5` | Rigorous `n^{1-2r/σ}` magnitude bound + concrete `h_explicit` instantiation *(formerly `BAXTER.14`)* | ✓ DONE — `residue_term_norm_bound` (rigorous `‖residue_term(k)‖≤C·‖k‖^{1-2r/σ}`, assembled from new `Npoly_upper_bound`/`Dpoly_upper_bound`, `G_baxter_deriv_lower_bound_of_zero`/`G_baxter_neg_lower_bound` (direct lower-bound versions of the old non-vanishing theorems), `abs_exp_neg_ikn_sigma_lower/upper`, `abs_exp_ikr_eq_rpow`/`abs_exp_ikr_upper_of_zero`, … | `HardSphere/BaxterResidue.lean`, `HardSphere/BaxterPoles.lean`, `HardSphere/RadialFourierCHSComplex.lean` |
| `POLE.6` | Concrete pole family wired into `h_explicit`'s summability | ✓ DONE (axiom-clean) — `h_explicit_summable_concrete` consumes `G_baxter_pole_family_exists_growth`'s conclusion tuple (existentially, since that theorem's hypotheses mention the `private` `baxterP0/1/2` — same cross-file-privacy pattern as POLE.5's wrappers) + a new centre hypothesis `hk1im : r ≤ Im(k1 n)`, and yields an injective, `G_baxter`-zero, upper-half-plane family with `Summable … See [proof_notes_pole.md](proof_notes_pole.md) `POLE.6`. | `HardSphere/HExplicitConcrete.lean` |
| `POLE.7` | Discharge `hstep` via the derived log-lift guess | ✓ **DONE — `hstep` PROVED (eventually form), axiom-clean, no sorry, full build green (2026-07-16)**: `k1_guess_hstep_eventually` — for the fit-free guess `k1_guess(n)=2πn/σ+(i/σ)·ln(‖Npoly(xₙ)‖/‖Dpoly(xₙ)‖)` (supersedes POLE.2's fitted `2ln x−2.12`; `hk1re` exact by construction), `∃N, ∀n≥N, dist(k1_guess n, baxterPhi n (k1_guess n)) ≤ rr(1−KK)` for **every** positive target and all physical … See [proof_notes_pole.md](proof_notes_pole.md) `POLE.7`. | `HardSphere/BaxterPoleGuess.lean` (new) |
| `POLE.8` | Fire the log-route family: POLE.3 unconditional | ✓ **DONE (2026-07-16) — `POLE.3` CLOSED UNCONDITIONALLY**, axiom-clean, sorry-free, first build green: **`Qhat_complex_zeros_infinite_unconditional`** + `G_baxter_zeros_infinite_unconditional` (hypotheses = physical parameters only!) + POLE.6 payoff **`h_explicit_summable_unconditional`** (`∃ g` injective `G_baxter`-zero family, `Im≥0`, `Summable (h_explicit_term … y g)` for every `y>σ` — the … See [proof_notes_pole.md](proof_notes_pole.md) `POLE.8`. | `HardSphere/BaxterPoleFamilyConcrete.lean` (new) |
| `POLE.9` | Chord `ChordPoleFamily (G_baxter)` (shared MZERO.5 obligation) | ✓ **DONE (2026-07-16)** — `chordPoleFamily_G_baxter_exists` + `G_baxter_zeros_infinite_chord` (axiom-clean, sorry-free, zero warnings): the 1-freq chord obligation is CLOSED for all physical params; pivotal lemmas `exp_at_k1_guess` (exact phase kill via `exp_int_mul_two_pi_mul_I`) and `norm_sub_ratio_mul_le` (algebraic unit-phase-difference bound, no arg/trig); `r=1/(10σ)`, `K=1/2`; 2-freq … See [proof_notes_pole.md](proof_notes_pole.md) `POLE.9`. | `HardSphere/BaxterChordFamily.lean` (new) |
| `POLE.10` | **Pole-family EXHAUSTION**: the constructed family enumerates *all* UHP zeros of `G_baxter`, injectively, with non-degenerate mirror pairing | ☐ **opened 2026-07-16 — on the critical path for BOTH remaining `hcollapse` routes** (`OZFIX.14` options (b) and (c)). Needed: `Function.Injective kfam`; `∀ z, 0 < z.im → G_baxter … z = 0 → ∃ n, z = kfam n ∨ z = -conj (kfam n)`; and pairing non-degeneracy (`(kfam n).re ≠ 0`, else `k = -conj k` and `Hterm`/`Kterm` double-count; `kfam m ≠ -conj (kfam n)`). **`POLE.8`'s … [detail in linked notes] | `HardSphere/BaxterPoleFamilyConcrete.lean` or new |

### Group OZFIX — `h_explicit`'s Closed-Form Assembly into `OzFixedPt` *(hard_sphere)*

*Split from Group BAXTER (`BAXTER.13`/`15`) — both retired, replaced by the eight
topic-scoped tasks below. Depends on Group BAXTER (`BAXTER.1`–`3`) and Group POLE. See
[proof_notes_ozfix.md](proof_notes_ozfix.md).*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| `OZFIX.1` | Strategy scoping (`B.0`) + zeroth-moment inner integral (`B.1`/`B.2`) | ✓ DONE — `moment0_formula`; `B.0` (pole-family completeness) resolved as not needed for the termwise strategy. No sorry/axiom. | `HardSphere/BaxterResidue.lean` |
| `OZFIX.2` | Complex-`k` Wiener–Hopf bridge (`OZFIX.6`'s key prerequisite) | ✓ DONE — `baxter_wiener_hopf_complex`, via analytic continuation/identity theorem, unconditional, no new axiom | `HardSphere/BaxterWienerHopfComplex.lean` |
| `OZFIX.3` | Sum/integral interchange machinery (`B.3`–`B.4` core) | ✓ DONE — `h_explicit_series_hasDerivAt` (`hasDerivAt_tsum_of_isPreconnected` payoff), `h_explicit_series_integral` (two-sided FTC, `lo>σ`), `s_mul_h_explicit_integral` (closed-form value `oz_linear_op` needs). No sorry/axiom. | `HardSphere/BaxterResidue.lean` |
| `OZFIX.4` | The `σ`-boundary case | ✓ DONE (conditional on `hint`) — `residue_term_norm_bound` weakening, `Hterm_uniform_summable_bound_of_pole_family`, `h_explicit_series_integral_from_sigma` (one-sided FTC); `hint` is a confirmed-genuine integrability gap, not Lean bookkeeping (see `proof_notes_ozfix.md` for the `g0_HS_contact_value`/Group CONTACT investigation that ruled out a quick reuse). No sorry/new axiom. | `HardSphere/BaxterResidue.lean` |
| `OZFIX.5` | Outer `t`-integral assembly (`B.3` proper) | ✓ DONE — `oz_forcing_add_linear_op_h_explicit_eq_outer_integral` eliminates the raw inner `∫s` integral entirely (closed `Hterm` form), case split `r-t≷σ` via `inner_h_explicit_integral_bridge`; no sorry/axiom | `HardSphere/OzFixedPtHExplicit.lean`, `HardSphere/BaxterResidue.lean` |
| `OZFIX.6` | Algebraic collapse (`B.5`, the mathematical payoff) | ◑ **split → `OZFIX.11` (`r≥2σ`, ✓ DONE 2026-07-16) + `OZFIX.12`/`OZFIX.13` (`σ≤r<2σ` + endpoint, scoped)**. The old scoping's "per-pole route FALSE (`-2.72`)" is now fully understood: it is specific to `σ≤r<2σ` (where `oz_forcing≠0`); for `r≥2σ` the per-pole collapse is TRUE and **proved** (collapse factor `ρ·Ĉ(k_n)=1`, see `OZFIX.11`). Aggregate target well-confirmed numerically. | see `OZFIX.11`–`13` |
| `OZFIX.7` | Regularity (`B.6`): `ContinuousOn`+boundedness | ✓ DONE on `(σ,∞)`/`[r0,∞)`, `r0>σ` — `h_explicit_continuousOn_Ioi`, `h_explicit_bounded_on_Ici`, no sorry/axiom. Closed endpoint `r=σ` remains open (same `σ`-boundary gap as `OZFIX.4`/`6`) | `HardSphere/HExplicitRegularity.lean` |
| `OZFIX.8` | Final assembly (`B.7`): invoke `oz_fixed_pt_unique` | ✓ DONE, conditional on `hcollapse` (`OZFIX.6`) + `hcont_sigma` (`OZFIX.7`'s σ-endpoint gap) — `oz_h_eq_spliced_h_explicit`, `#print axioms` only `oz_fixed_pt_unique` beyond the standard three; retiring `oz_core_closure` itself is a separate Phase C follow-on. … | `HardSphere/OzFixedPtHExplicitFinal.lean`, `HardSphere/OzCollapseTwoSigma.lean` |
| `OZFIX.9` | `hcollapse` via **Route A** (`oz_forcing` termwise Mittag-Leffler expansion), alternative to Route B (whole-series `radial3d_conv` + Mathlib-axiom, done elsewhere) | ☐ **Direction (user-confirmed 2026-07-15): Route B closes `hcollapse`** (favorable axiom trade — physics `oz_core_closure` → standard/reusable residue axiom); Route A kept as the future *unconditional* (axiom-free) path, `r≥2σ` part now tractable. **UNBLOCKED — the POLE fix resolved the aggregate; Route A viable but research-scale (≈ Route-B difficulty).** Re-scoped against … | new `HardSphere/OzForcingResidue.lean` |
| `OZFIX.10` | `hcollapse` via **Route B** (growing-contour Fourier inversion: `∫_{-R}^{R} k·Ĥ·e^{ikr} → 2πi·Σres`, then back to `radial3d_conv`) — the user-confirmed closing route… | ◑ **infrastructure DONE, arc-vanishing OPEN.** Done (2026-07-15, `lake build` clean): (a) **`jordan_lemma_arc_bound`** (`Analysis/JordanLemma.lean`) — quantitative Jordan's lemma `‖∫_arc g·e^{iaz}‖≤πM/a`, **proved outright, NO axiom** (`Real.mul_le_sin` + ML-inequality + `Complex.norm_exp` + FTC); (b) **half-disk residue theorem** — axiom … → **`−1/ρ`** (smoking gun: the recorded circle bounds … See [proof_notes_ozfix.md](proof_notes_ozfix.md) `OZFIX.10`–`12`. | `Analysis/JordanLemma.lean`, `Analysis/ContourDeformation.lean`; application file TBD |
| `OZFIX.11` | `hcollapse` for `r ≥ 2σ` — per-pole collapse via `ρ·Ĉ(k_n)=1` | ✓ **DONE (2026-07-16), axiom-clean** (`#print axioms` = standard three; NO `hint`-family hypothesis — vacuous on this region): `oz_collapse_of_two_sigma_le` — `OZFIX.5`'s outer integral collapses **per pole**: each pole's `t`-integral closes to `residue_term(r,k)·Ĉ(k)/(2π)` (`integral_Chat_poly_exp_pair` + `Chat_F_neg_sub_eq`, pure `Chat_F`/`Chat_J` moment algebra), and **`ρ·Ĉ(k)=1` at every … See [proof_notes_ozfix.md](proof_notes_ozfix.md) `OZFIX.11`. | `HardSphere/OzCollapseTwoSigma.lean` (new) |
| `OZFIX.12` | `hcollapse` for `σ < r < 2σ` — exact defect algebra + reduction to the core-closure series identity (★) | ◑ **Reduction target IDENTIFIED + numerically CONFIRMED; `Kterm` infra ✓ DONE (axiom-clean, build green); assembly remains.** Derived the exact defect: `oz_forcing + oz_linear_op[h_explicit] = h_explicit + (ρ/r)·Re ∑'ₙDₙ(r)` with `Dₙ(r) = ∫_{r−σ}^σ Chat_poly(r−u)[Hterm n u − Hterm n σ]du` (uses `integral_Chat_poly_mul_Hterm_pair`, which needs **no** `r≥2σ`) ⇒ `hcollapse` ⟺ … See … See [proof_notes_ozfix.md](proof_notes_ozfix.md) `OZFIX.12`. | `HardSphere/OzCollapseInner.lean` (new) |
| `OZFIX.13` | `σ`-endpoint + full `hcollapse` discharge wiring | ☐ **scoped**: `r=σ` from `hcont_sigma` + continuity of the LHS at `σ⁺` (forcing explicit; linop via `OZFIX.5`'s closed form + `Σ'Hterm` continuity down to `σ`, `OZFIX.4` machinery); then the fully-discharged `oz_h_eq_spliced_h_explicit` variant (hypotheses = `OZFIX.11`'s + `OZFIX.12`'s bundle + `hcont_sigma`). … | TBD |
| `OZFIX.14` | **Circularity: (★) ⟺ core closure ⇒ Group OZFIX CANNOT retire `oz_core_closure`** | ✗ **NEGATIVE RESULT (2026-07-16), closed.** Closing the UHP contour on (★)'s pole sum **provably cannot** prove it. With `ρĈ(kₙ)=1` the summands are `Res_k[S]·Ξ(k)/(iρ)`, `S:=1/(1−ρĈ)=z⁶/(G(z)G(−z))`, `Ξ` **entire**; writing `S=1+ρĤ`, the `ρĤ` arc →0 (Jordan + two-regime) and the `1` part cancels **exactly at every R** between line and arc (`∮Ξ=0`) ⇒ `2πi·∑'Res_k[S]Ξ(k) = ρ∫_ℝ … See … See [proof_notes_ozfix.md](proof_notes_ozfix.md) `OZFIX.14`. | — |
| `OZFIX.15` | **Real-space Baxter/Wertheim–Thiele — the ψ construction (claims A/B/C ⇒ `ψ ⋆ Q₊ ⋆ Q₋ = φ`)** | ✓ **DONE 2026-07-17 — axiom-clean, `lake build` green** (`HardSphere/BaxterRenewal.lean`). Target **`baxter_psi_conv_eq_phi`**: `(ψ⋆Q₊⋆Q₋)(r) = r·c_HS(r) = φ(r)` for **every** `r>0`, every object concrete. **(1) Global ψ by uniqueness-as-glue:** `MA.10` gives a different `C(Icc σ b, ℝ)` per `b` (dependent type, useless to a convolution identity on `ℝ`); `volterraSol_compat` … → [ozfix](proof_notes_ozfix.md) `OZFIX.15` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.16` | **The `1D-odd ↔ 3D-radial` bridge: `d/dr[r·(f ⊛₃ g)(r)] = −2π·(f̃ ⋆ g̃)(r)`** — turns the real-space Baxter identity `ψ⋆Q₊⋆Q₋=φ` into OZ for all `r>0` | ✓ **DONE 2026-07-17 — BOTH HALVES PROVED, axiom-clean** (`HardSphere/BaxterRenewal.lean`). Target theorem **`hasDerivAt_radial3d_conv_bridge`**. Chain: `radial3d_conv_eq_oddExt` (kills the `\|r−t\|` via `integral_shell_eq_oddExt`) + **brick 1 `hasDerivAt_shell`** (FTC on the shell: `d/dx ∫_{x−t}^{x+t} φ = φ(r+t)−φ(r−t)`, needing continuity of `φ` **only at the two endpoints**; … → [ozfix](proof_notes_ozfix.md) `OZFIX.16` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.17` | **Assembly ⇒ `oz_core_closure` becomes a THEOREM (Phase C)** | ☐ **RE-SCOPED 2026-07-17 — was NOT one task.** Investigating the chain found a structural obstacle the old sketch hid: **`Q̂` is a 1D transform but `Ĉ` is a 3D radial one** (`Qhat_complex` of `q0_poly` vs `radial_fourier` of `c_HS`), so `OZFIX.2`'s `(1−Q̂(k))(1−Q̂(−k)) = 1−ρĈ(k)` does **not** make `1−ρĈ` the transform of `δ−ρc̃`; the two differ by `2πi/k` = an … → [ozfix](proof_notes_ozfix.md) `OZFIX.17` | `HardSphere/PYOZ_GHS.lean`, `HardSphere/BaxterRenewal.lean` |
| `OZFIX.18` | **Real-space Baxter factorization `Q₊ ⋆ Q₋ = δ − ρ·K`** | ◑ **CORE FORM `rho_baxterK_eq_q0_self_conv` PROVED 2026-07-17, axiom-clean**: `ρ·K(v) = q0(v) − ∫_v^σ q0(t)·q0(t−v)dt` for `v∈(0,σ)` (the double integral IS `(q0·1_{[0,σ]} ⋆ q0(−·)·1_{[−σ,0]})(v)`). Proof = **two FTC evaluations + `field_simp`/`ring` under `heta_def`** (degree-4 antiderivative `Gpoly` for `∫ s·c_HS`, degree-5 `Fpoly` for `∫ q0·q0`; `HasDerivAt` via … → [ozfix](proof_notes_ozfix.md) `OZFIX.17` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.19` | **The antiderivative bridge `r·(f ⊛₃ g)(r) = (g̃ ⋆ K_f)(r)`** | ✓ **DONE 2026-07-17, axiom-clean** (`radial3d_conv_eq_baxterK_shell`): `r·(c_HS ⊛₃ g)(r) = ∫₀^σ K(u)·(g̃(r−u)+g̃(r+u))du` for `r>0` (= `(K⋆g̃)(r)` folded onto `[0,σ]` by `K` even). **KEY REALIZATION: it is NOT a differentiation argument — just Fubini** (differentiate-in-`u` would break at `u=σ−r` where `g̃=ψ` jumps; Fubini only needs integrability, jump-proof). … → [ozfix](proof_notes_ozfix.md) `OZFIX.17` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.20` | **Convolution associativity `(ψ ⋆ Q₊) ⋆ Q₋ = ψ ⋆ (Q₊ ⋆ Q₋)` (Fubini)** | ✓ **DONE 2026-07-17, axiom-clean** (`dbl_conv_reindex`): `∫₀^σ∫₀^σ q0(t)q0(s)ψ(r+t−s) = ∫₀^σ(∫_u^σ q0(t)q0(t−u)dt)(ψ(r−u)+ψ(r+u))` for **any** ψ (numerically verified 3 ψ to 1e-16). **Both sides reduce to `∫ t in 0..σ,∫ s in 0..t, q0(t)q0(s)(ψ(r+t−s)+ψ(r+s−t))`**: RHS by `intervalIntegral_triangle_swap_gen` (the new 2-var triangle Fubini) + inner change-of-var `s=t−u`; LHS by splitting the inner … → [ozfix](proof_notes_ozfix.md) `OZFIX.17` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.21` | **OZ★ linchpin + axiom consolidation** | ✓ **OZ★ DONE 2026-07-17, axiom-clean** (`baxterPsi_eq_phi_add_rho_conv`): `baxterPsi(r) = r·c_HS(r) + ρ·r·radial3d_conv(c_HS, baxterPsi/·)(r)` ∀`r>0` — the concrete real-space **OZ equation** solved by the constructed `baxterPsi`, assembled from `baxter_psi_conv_eq_phi` (`OZFIX.15`) + `radial3d_conv_eq_baxterK_shell` (`OZFIX.19`) + `rho_baxterK_eq_q0_self_conv` (`OZFIX.18` KDEF) + … → [ozfix](proof_notes_ozfix.md) `OZFIX.21` | `HardSphere/BaxterRenewal.lean` |
| `OZFIX.22` | **Axiom consolidation — RETIRE `oz_core_closure` + `oz_h_exterior_regularity` (net 3→2)** | ✓ **DONE 2026-07-17, full build green (8653 jobs), no cycles.** New file `HardSphere/OzCoreClosure.lean`: `radial3d_conv_cHS_congr` (decay-free brick: `radial3d_conv c_HS g r` depends on `g` only on `(0,r+σ)`), `oz_core_closure_of_bridge` (decay-free reduction: closure = OZ★ ⊘ r + bridge), `ozBaxterFixedPt := if r<σ then -1 else baxterPsi r/r`, `oz_h_eq_ozBaxterFixedPt` (**the … → [ozfix](proof_notes_ozfix.md) `OZFIX.22` | `HardSphere/OzCoreClosure.lean` |
| `OZFIX.24` | **RETIRE `ozExterior_triple_shell_sin_integrable` (6h): axiom → theorem** | ✓ **DONE 2026-07-19, full build green (8675 jobs), no new axiom, no `sorry`** — `axiom` keyword deleted, name/signature unchanged so no consumer edit needed. It had been axiomatized on an **effort** argument ("formalizing the triple `lintegral` chain is substantial"), not a gap argument — in tension with Group MA admissibility rule (c); same category as MA.10/11/12, all retired by proving. … → [ozfix](proof_notes_ozfix.md) `OZFIX.24` | `HardSphere/BaxterExteriorConvIntegrable.lean` |

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
| FW.1 | FMT species symmetry: `betaf_hs` depends on `rho` only through `∑ᵢρᵢ` when all diameters equal | ✓ DONE, no axiom (`betaf_hs_species_symmetry`) | `HSMixture/WhiteBearFMT.lean` |
| FW.2 | BMCSL/White-Bear thermodynamic consistency: virial pressure (from `g0_bmcsl`) = FMT scaled pressure (from `betaf_hs`) | ✓ DONE, no axiom (`bmcsl_virial_eq_fmt_pressure`) | `HSMixture/WhiteBearFMT.lean` |


### Group 5 — Matching at Contact *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 5.1 | Inner/outer matching at r=R_ij (2YK only) | ✓ structural (I1/I2=0) / **⊥ physical claim disproved** | `YukawaOZ/ContactMatching.lean` |

**5.1 disproof note:** The Lean proof establishes only that `I1(0) = I2(0) = 0` (integral over an
empty interval — trivially true) and `eij(R,R) = ΣA_k`. It explicitly states in a comment that
full DCF continuity additionally requires the MSA closure condition `K = A_k` at each Yukawa
pole, which is NOT proved and does NOT hold.

Numerical evidence from `FMSA_pure` (verify_pure.py V.1): the first-order c₁ gap at r = d_bh is
~1.1–1.7 across liquid-range state points, far from the ~1e-6 numerical-precision level.  The
total-c gap is smaller (~0.02–0.7) only because the FMT c₀ accidentally partially compensates.
Since the pure-fluid limit is the simplest case, the same discontinuity must appear in mixtures.
The intended physical matching property (DCF continuity at contact for the 2YK FMSA) is false.

---

*Numerical verification tasks are in `../todo/todo_numerical.md`.*


### General-N (2026-07-29) — ✅ mixtureDet_pole_free_N UNCONDITIONAL, all N, no new axiom
`MixtureDetGeneralN.lean`: `det Q̂₀(I·z)≠0` on the open LHP, **any N**, physical mixture, no new axiom — via `matDet_zeroFree_lowerHalfPlane_of_homotopy` (diagonal-similarity phase-strip `det_Q0_eq_det_gauge` ⇒ `Mgauge=1−A`, `‖A‖→0`; base=dilute, real-axis=no-spinodal, origin=`detMdens_origin_ne_zero`). Resolves OZFIX.17 pole↔decay all N. → `proof_notes_mixture_rdf.md`.


### MML.8 re-evaluation (2026-07-29) — OZ★-route assembled up to one scoped gap
`MixtureRDFUniqueness.lean`: the abstract matrix OZ★ value route `matOzStar_unique` (non-circular; conditional on the coercive symbol; axioms = std-3 + MA.15 `matRadialShell_bounded_injective`). **NOW SUPERSEDED** — MML.8 is fully closed UNCONDITIONALLY via `matOzStar_unequalDiam_unique_uncond` (coercivity proven, 2026-08-20). Literal pole-series collapse stays circular (project_mml8_disposition).

### L² matrix Wiener–Hopf PROVED via matrix Plancherel (2026-07-30) — axiom-clean, mirrors MA.12
`Analysis/MatrixWienerHopf.lean` `matWienerHopf_positive_symbol_injective` (std-3, no axiom): matrix analog of MA.12 via matrix-Plancherel coercivity (`matrix_quadratic_coercive`). Matrix L²=theorem / L∞=axiom `matRadialShell_bounded_injective` mirrors scalar MA.12/MA.15.
### Group PYE PYE.1–PYE.3 CLOSED (2026-07-31) — no-pull-back construction ≡ first-order PY, **no new axiom**
`Closures/ClosureExpansions.lean` (ns `FMSA.FirstOrderClosure`): PYE.1–3 axiom-clean (std-3, all decls). PYE.1 `c₁=g_HS·(−βu)`; PYE.2 DP map **linear** (frozen rates); PYE.3 error = DP-map[fit residual] (`map_sub`), `wh_solution_operator_bounded` = THEOREM (`whOperatorBound=T·N⁴·Qb²·Ab²/δ`). Non-vacuity certified by a non-degenerate `example`. See the Group PYE table.

### PYE.5 + PYE.6 (2026-08-03) — the k→r bridge, and the zeroth-order factor IS PY's (N=1)
PYE.5 k→r bridge (`radial_fourier_injective` + `IsRadialEntry` ⇒ `inner_core_dcf_eq_of_exact_fit`, pointwise on `(0,R)`; ⚠ open core only, no real-space error bound). PYE.6 zeroth-order factor = PY Baxter: `N=1` already in the library (BAXTER.3 = MRS.8@N=1); **general `N` DONE 2026-08-19** (`dp_zeroth_order_is_py_N`, `#print axioms` = std-3 + `pyhs_mixture_no_spinodal`). See the Group PYE table.

### PYE.7 CLOSED (2026-08-03) — Yukawa-tail fits are dense; PYE.4 still open
`exists_yukawa_tail_fit`(+`_pyOuter`), axiom-clean: Yukawa-tail fits are dense (Weierstrass after `t=e^{−r}`, NOT Stone–Weierstrass; rates unit-spaced). ⚠ does NOT close PYE.4 (compact window ≠ half-line; function residual ≠ WH-datum distance).

### PYE.4 REDUCED to one classical input (2026-08-03) — the function-space lift, built
PYE.4's function-space lift is built except ONE classical input `WHProjectionL1` (hypothesis, MA.13/15-class Wiener 1/f — kept, not axiomatized). Proved: half-line + **L¹** tail-fit density, `‖Û₁(k)‖≤‖Ψ‖_{L¹}` uniform in k, `TailFitWHConvergent` **derived**. ⚠ amplitude route is a DEAD END (unbounded); the norm must be real-space L¹ (Riesz, not sup-k). See the Open-tasks PYE.4 row.

### MML.16 (2026-08-03) — the RDF "even pseudo-trace" is annihilated EXACTLY, and [LN] deviates from Tang & Lu here
The WH machinery's unilateral `Ĥ₁` vs the physical sine transform `H̃₁`: the RDF even "pseudo-trace" is **exactly annihilated** by support disjointness (O(1), not small). `YukawaOZMix/ReflectedTermSupports.lean` (axiom-clean): parity-partner terms are `(−∞,R_ij]`-supported ⇒ causal projection = 0; fourth atom closed via MA.10 (local renewal, no MA.13). ⚠ [LN] deviates from Tang & Lu 1995 here (`H̃₁=Ĥ₁` step is FALSE) — derive from the paper. → `rdf_parity_no_pseudotrace.md`.
