# FMSA — task status

The FMSA-DP first-order construction: the doubly-propagated first-order mixture DCF/RDF, its
Wiener–Hopf spectral amplitude, the Mittag-Leffler inner-core series, and the method-failure analyses
that bound it. **Scope + axiom gate: [`LeanCode/FMSAProject.lean`](LeanCode/FMSAProject.lean)** (the
FMSA-DP paper's chain).

↩ **Index:** [`todo_lean.md`](todo_lean.md) — layer map, project-wide axiom/sorry ledger, category index.

**Detailed records:**
- [proof_notes_yukawa_dcf.md](proof_notes_yukawa_dcf.md) — Groups 1, 4, GAP, C, 5
- [proof_notes_breakpoints.md](proof_notes_breakpoints.md) — Group IB
- [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md) — Group Y1
- [proof_notes_mixture_rdf.md](proof_notes_mixture_rdf.md) — Groups MML, MZERO
- [proof_notes_mixture_dcf.md](proof_notes_mixture_dcf.md) — Groups MRS, MPOLY
- [proof_notes_failures.md](proof_notes_failures.md) — Groups chsY, P, GA

---

## Task Status

### Group 1 — Closed-Form Integral Identities *(yukawa_dcf)*

| Task | Title | Status | Lean file |
|------|-------|--------|-----------|
| 1.1 | I₁ antiderivative | ✓ DONE | `YukawaOZ/I1I2Integrals.lean` |
| 1.2 | I₂ antiderivative | ✓ DONE | `YukawaOZ/I1I2Integrals.lean` |
| 1.3 | I₁/I₂ vanish at ℓ=0 | ✓ DONE | `YukawaOZ/I1I2Integrals.lean` |

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
| MML.8 | RDF-only assembly/collapse (I)+(II)+(III) | ✅ **CLOSED via the VALUE route** `matOzStar_unequalDiam_unique_uncond` (std-3 + MA.15 + `pyhs_mixture_no_spinodal`); the literal RDF collapse is PROVABLY BLOCKED (DCF premise `Ĉ₁=Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` carries no `Q̂₀⁻¹`, refuted 2026-07-16) so the task stands on the value route — [[project_mml8_disposition]]. → `proof_notes_mixture_rdf.md` | `YukawaOZMix/MixtureInnerDCF.lean` |
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
| MRS.6 | *(ex-MRS.1a)* WH factorization **frame**: define `Ĉ₀ := I − Q̂₀(k)·Q̂₀ᵀ(−k)`; discharge MRS.2's `hfact` for free; **reduce** `hT0symm` to the swap identity… | ✓ **DONE (2026-07-17, axiom-clean)** — `MixtureRealSpace.lean` (ns `FMSA.MixtureBaxterCore`): `Cmix0`, `Cmix0_factorization` (hfact), `Cmix0_transpose`, `Cmix0_isSymm_iff` (symmetry ⟺ swap), `T0_isSymm_of_swap` (⇒ `hT0symm`). `YukawaOZMix/MixtureRealSpace.lean` + `fin2_transpose_eq_iff_offdiag`/`T0_isSymm_iff_offdiag` (N=2 symmetry ⟺ single off-diagonal scalar; diagonal … | `YukawaOZMix/MixtureRealSpace.lean` |
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

### MML.16 (2026-08-03) — the RDF "even pseudo-trace" is annihilated EXACTLY, and [LN] deviates from Tang & Lu here
The WH machinery's unilateral `Ĥ₁` vs the physical sine transform `H̃₁`: the RDF even "pseudo-trace" is **exactly annihilated** by support disjointness (O(1), not small). `YukawaOZMix/ReflectedTermSupports.lean` (axiom-clean): parity-partner terms are `(−∞,R_ij]`-supported ⇒ causal projection = 0; fourth atom closed via MA.10 (local renewal, no MA.13). ⚠ [LN] deviates from Tang & Lu 1995 here (`H̃₁=Ĥ₁` step is FALSE) — derive from the paper. → `rdf_parity_no_pseudotrace.md`.
