# Proof Notes: N=2 Mixture Inner-Core RDF — Mittag-Leffler HS-Pole Series (Groups MML / MZERO)

Proof records for the **N=2 mixture inner-core RDF `h₁`** line: **Group MML** (Mittag-Leffler
inner-core: 2×2 inverse → residue → assembly) and **Group MZERO** (`det(Q̂₀)` zero / HS-pole family).
Split out of `proof_notes_yukawa_wh.md` on 2026-07-17 — the RDF counterpart to the DCF real-space
groups in [proof_notes_mixture_dcf.md](proof_notes_mixture_dcf.md).

**Why RDF, not DCF — the (★) dividing line (2026-07-16).** The RDF `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` carries
**two** `Q̂₀⁻¹` factors ⇒ genuine HS poles (zeros of `det Q̂₀`) ⇒ a genuine **Mittag-Leffler HS-pole
series**, which is exactly what MML/MZERO formalize. By contrast the inner **DCF**
`Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` (MRS.3 (★)) has **no** inverse ⇒ no HS poles ⇒ a finite closed form — so
MML.8's DCF reading is refuted and superseded by Group MRS (`proof_notes_mixture_dcf.md`). **The
`Q̂₀⁻¹`-factor count is the dividing line: none ⇒ DCF; two ⇒ RDF `h₁` (this file).**

**Foundation.** These groups build on **Group Y1** (the first-order Wiener–Hopf RDF derivation:
spectral amplitude `b_{ij}(s)`, `Ĥ₁`) in [proof_notes_yukawa_wh.md](proof_notes_yukawa_wh.md), and on
Group POLE (the N=1 HS-pole existence analog, `proof_notes_pole.md`).

**History.** Split from the former flat "Group Y2" on 2026-07-15 (into MML / MZERO / MPOLY); MPOLY
went with the DCF groups to `proof_notes_mixture_dcf.md`, and MML / MZERO moved here on 2026-07-17.

## ⭐ SEED ROUTE — END-TO-END STATUS (COMPLETE, 2026-08-08)

The **corrected-seed real-space route** to the unequal-diameter mixture RDF identity
`matBaxterUQmSymFullExt = r·Φ` (MML.8) is assembled end-to-end and every structural step is axiom-clean.
The canonical in-code summary lives at the end of `MixtureCorrectedSeed.lean` (`## The corrected-seed
route to MML.8`).  The chain, obstruction → resolution:

1. **a.e.-symmetry** `matDCF_ae_symm` (dissolves obstruction (b), Fourier a.e.-injectivity).
2. **corrected seed** `matBaxterUt = matBaxterU` at `Qᵀ` (rfl) — transposes the first convolution.
3. **momentum linchpin** `Qphys_prod_eq_one_sub_dcf_transform` (`Q̂₀·Q̂₀ᵀ = 1 − 𝓛[matDCFfull]`).
4. **symbol identity** `matDCFfull_shell_laplace` (+ `laplace_shift`/`foldShell_laplace`) closes the
   windowed↔full-line gap at the transform level.
5. **full-line extension** `matBaxterUtExt`; `matBaxterUExt_eq_matBaxterU_sub_tail` makes the `[λ,0)`
   sub-zero tail explicit.
6. **three-region closed form** of the first convolution: `matBaxterUtExt_core` (core moments),
   `matBaxterUtExt_intermediate_closed` (intermediate), claim `(A)` = 0 (outer).
7. **seed fully explicit** `_core_reduce`→`_conv_boundary_split`→`_conv_moment_part`→`_core_assembled`
   →`_conv_outer_part_closed`→`_core_fully_explicit`→`_fully_explicit_momentLead`/`_intermediateLead`:
   ZERO symbolic `matBaxterUtExt` — an expression in `Q` and the constructed `matBaxterPsiOuter`.
8. **`Ψouter` coupling pinned** to `matBaxterPsiOuter` (read-out `matRenewalConv_eq_sub`/`_contact`;
   alignment `renewalForm_peel_subzero_tail`/`matRenewalForm_readout_add_tail`; coupling
   `renewalForm_eq_outer`/`matBaxterUtExt_intermediate_closed_outer`).
9. **WT terminus `= r·Φ`**: `matBaxterUQmSymFullExt_eq_rPhi_of_seed` reduces to one `hseed`; PROVED at
   equal diameters (`matBaxterUQmSymFullExt_eq_rcHS_of_equalDiam` ← `baxter_core_seed`); numerically
   CONFIRMED `<1e-3` at unequal diameters (`mixwt_lebowitz_check.py`, Lebowitz coeffs, `Ψouter` =
   renewal Picard, claim A ~1e-8).

**✅ Full-line seed → DCF-shell `hclaimA` in the genuinely-symmetric kernel (2026-08-10,
`MixtureCorrectedSeed.lean`, std-3, full build 8759).**  The windowed `correctedSeed_hclaimA` supplied
`hclaimA` only for the `[0,σ]`-windowed Baxter kernel (`ρK = Q − matSelfConv`), whose a.e.-symmetry is
FALSE at unequal diameters — the object `matOzStar_of_asymK_ae` cannot symmetrize.  New chain reindexes
the FULL-LINE extended seed `matBaxterUQmSymFullExt` (no `[0,σ]` truncation) directly onto the full-line
DCF fold kernel `Ĉ₀ᵢₖ(v) = Qᵢₖ(v) + Qₖᵢ(−v) − (matCorrFull Q)ᵢₖ(v)` — the genuinely (a.e.)
transpose-symmetric object `matOzStar_of_matDCF_ae` consumes.  Lemmas: **`matCorrFull`** (full-line
correlation `∑ₘ ∫_ℝ Qᵢₘ(t)Qₖₘ(t−v)dt`); **`km_reindex`** (per-pair double-conv → correlation, via
inner sub `integral_sub_left_eq_self` + Fubini `integral_integral_swap`); **`dblConvFull_reindex`**
(the species-summed Term C); **`matBaxterUQmSymFullExt_eq_psi_sub_dcfShell_sep`** (Terms A[reflected,
`integral_neg_eq_self`]+B[forward]+C reindexed: `= Ψ − ∑ₖ∫Qᵢₖ·Ψ − ∑ₖ∫Qₖᵢ(−·)·Ψ + ∑ₖ∫matCorrFull·Ψ`);
**`matDCFfoldKernel`** + **`matBaxterUQmSymFullExt_eq_psi_sub_dcfShell`** (combined: `= Ψ − ∑ₖ∫_ℝ Ĉ₀·Ψ`);
**`correctedSeedExt_hclaimA`** (combine with `matBaxterUQmSymFullExt_eq_rPhi_of_seed`: `Ψᵢⱼ(r) =
r·Φᵢⱼ(r) + ∑ₖ ∫_ℝ Ĉ₀ᵢₖ(v)·Ψₖⱼ(r+v)dv` — the OZ-renewal `hclaimA` in the full-line DCF kernel).
**✅ Fold-repackage into `matShellConvAsym` DONE (2026-08-10, same file, std-3, full build 8759).**  The
raw `∫_ℝ Ĉ₀·Ψ` shell is now repackaged into the exact `matShellConvAsym (Ĉ₀/ρ) (Ĉ₀/ρ)ᵀ (Ψ/·)`
`[0,σ]`-two-arm/`oddExt` form `matOzStar_of_matDCF_ae` consumes.  Lemmas: **`matCorrFull_neg_swap`**
(`(matCorrFull Q)ᵢₖ(−v) = (matCorrFull Q)ₖᵢ(v)`, a shift `t↦t+v`); **`matDCFfoldKernel_transpose_odd`**
(`Ĉ₀ᵢₖ(−v) = Ĉ₀ₖᵢ(v)` **unconditional** — forward↔reflected swap + `matCorrFull_neg_swap`, the
a.e.-symmetry hook: transpose-odd + a.e.-symmetric ⇒ even); **`matDCFfold_to_twoArm`** (compactly
supported `Ĉ₀` ⇒ `∫_ℝ Ĉ₀·Ψ(r+v) = ∫₀^σ Ĉ₀ᵢₖ·Ψ(r+u) + ∫₀^σ Ĉ₀ₖᵢ·Ψ(r−u)`, split at 0 + `u↦−v` maps
the `v<0` half to the reflected arm via transpose-odd); **`dcfShell_eq_rho_matShellConvAsym`**
(`∑ₖ ∫_ℝ Ĉ₀·Ψ = ρ·matShellConvAsym (Ĉ₀/ρ) (Ĉ₀/ρ)ᵀ (Ψ/·)`, via the fold + `matShellConvAsym_transpose_raw`
[`oddExt(Ψ/·)`↔`Ψ` for odd `Ψ`] + `ρ·(Ĉ₀/ρ)=Ĉ₀`); capstone **`correctedSeedExt_hclaimA_matShellConvAsym`**
(`Ψᵢⱼ(r) = r·Φᵢⱼ(r) + ρ·matShellConvAsym (Ĉ₀/ρ) (Ĉ₀/ρ)ᵀ (Ψ/·)ᵢⱼ(r)` — the EXACT `hclaimA` of
`matOzStar_of_matDCF_ae`, `Kmat = matDCFfoldKernel Q/ρ`).  **✅ Physical identification DONE (2026-08-10, `MixtureDCFAEInjective.lean`
`section PhysicalIdentification`, std-3, full build 8759).**  The abstract fold kernel is pinned to the
physical DCF core.  **`qWeighted`** = the `ρ_geo`-weighted physical Baxter factor
`Qwᵢₖ(v) = ρ_geoᵢₖ·q0MixEntry(physMix)ᵢₖ(v)`; **`matDCFfoldKernel_qWeighted_eq_matDCFreCore`**:
`matDCFfoldKernel (qWeighted) i k v = matDCFreCore rho sigma hsig i k v` (both linear terms match
directly; `matCorrFull (qWeighted) = Re(matCorrW)` via `Complex.ofReal_sum` + `integral_complex_ofReal`
— the whole `matDCFfull` is `((matDCFfoldKernel Qw)ᵢₖ(v) : ℝ) : ℂ`, so its `.re` IS the fold kernel).
Corollaries **`qWeighted_dcfKernel_div_eq`** (funext: `matDCFfoldKernel(Qw)/ρ = matDCFreCore/ρ`) +
**`hclaimA_qWeighted_to_matDCFreCore`** (rewrites the `matShellConvAsym`-form `hclaimA` from the abstract
`matDCFfoldKernel(Qw)` kernel to the physical `matDCFreCore` kernel) — so composing
`correctedSeedExt_hclaimA_matShellConvAsym` (at `Q = qWeighted`) with this swap yields EXACTLY the
`hclaimA` input of `matOzStar_of_matDCF_ae_canonical` (`Kmat = matDCFreCore/ρ`).  (`MixtureDCFAEInjective`
now imports `MixtureCorrectedSeed`.)  **Remaining to fully discharge `matOzStar_of_matDCF_ae_canonical`**:
(i) the qWeighted side-conditions of the `hclaimA` capstone; (ii)
`hbridge` (`matRadialConv_eq_matShellConv`); (iii) the seed `hseed` itself — the Wertheim–Thiele identity,
proved at equal diameters, only numerically confirmed at unequal (the one genuinely-open analytic input).

**✅ qWeighted geometric side-conditions (`hsupp`, `hQlam`) DISCHARGED (2026-08-10, same file
`section PhysicalIdentification`, std-3, full build 8759).**  The purely-geometric support inputs of the
`hclaimA` capstone are proved from `q0MixEntry_support_subset` (`[λᵢₖ,Rᵢₖ]`, `λ=(σₖ−σᵢ)/2`,
`R=(σᵢ+σₖ)/2`).  **`q0_physMix_eq_zero_of_notMem`** (vanishing off the support Icc);
**`qWeighted_eq_zero_of_notMem`** + **`qWeighted_eq_zero_of_sigmaS_lt_abs`** (`qWeighted` vanishes for
`|t|>sigmaS` given a shell radius `sigmaS ≥` every diameter); **`matCorrFull_qWeighted_eq_zero_of_R_lt_abs`**
(the correlation `matCorrFull(qWeighted)ᵢₖ = 0` for `|v|>Rᵢₖ` — the two Baxter factors' `v`-shifted supports
`[λᵢₘ,Rᵢₘ]`, `[λₖₘ,Rₖₘ]` cannot overlap, so the integrand is identically 0); **`matDCFfoldKernel_qWeighted_eq_zero_of_lt_abs`**
= the **`hsupp`** input (`matDCFfoldKernel(qWeighted)ᵢₖ(v)=0` for `sigmaS<|v|`, both linear terms + the
correlation vanishing); **`qWeighted_eq_zero_of_lt_neg_sigmaS`** = the **`hQlam`** input (`lam=−sigmaS`).
**✅ qWeighted integrability side-conditions — 6 of 9 DISCHARGED from `Ψ`-continuity (2026-08-10, same
file `section PhysicalIdentification`, std-3, full build 8759).**  Given `hΨ : ∀ k, Continuous (Ψ k j)`,
the linear + DCF-kernel integrability inputs are proved.  Engine **`integrable_of_bddSupp_mul_continuous`**
(measurable `f` bounded by `C` and supported in `[a,b]`, times continuous `g`, is integrable — product
supported in `[a,b]`, bounded by `C·sup_{[a,b]}‖g‖`, via `integrable_indicator_iff` +
`Measure.integrableOn_of_bounded`).  Building blocks: **`qWeighted_abs_le`** (global bound, from
`q0MixEntry_abs_le`), **`qWeighted_measurable`**; **`q0_corr_real_continuous`** (the real correlation
`v↦∫q0ᵢₗ(t)q0ⱼₗ(t−v)` is continuous, `Re` of `q0MixEntry_corr_continuous`) → **`matCorrFull_qWeighted_continuous`**
+ **`matCorrFull_qWeighted_abs_le`** (correlation continuous + globally bounded via compact support).
General-`g` lemmas **`qWeighted_mul_cont_integrable`** / **`qWeightedRefl_mul_cont_integrable`** /
**`matCorrFull_mul_cont_integrable`** / **`matDCFfoldKernel_mul_cont_integrable`** (the last splits the
kernel into the two linear Baxter terms + the correlation, each integrable).  Capstone-shaped `∀k`
corollaries **`hB_qWeighted`** (`Qᵢₖ·Ψ(r+·)`), **`hA_qWeighted`** (`Qₖᵢ(−·)·Ψ(r+·)`), **`hC_qWeighted`**
(`matCorrFull·Ψ(r+·)`), **`hint_qWeighted`** (`matDCFfoldKernel·Ψ(r+·)`), **`hIfwd_qWeighted`** /
**`hIbwd_qWeighted`** (interval versions, `Ψ(r+·)`/`Ψ(r−·)`).  **Remaining 3 of 9**: the NESTED/2D inputs
`hI1` (`Qᵢₖ·(∫Qₘₖ·Ψ(r+·−·))` — needs continuity of the inner convolution), `hI2`
(`(∫Qᵢₖ·Qₘₖ(·−v))·Ψ` — single-correlation continuity), and `hfub` (the product-measure Fubini
integrand — 2D compact-support integrability); plus `hbridge` and the open `hseed` remain.

**✅ `hI2` DISCHARGED (2026-08-10, same file `section PhysicalIdentification`, std-3, full build 8759)
— 7 of 9 integrability inputs now done.**  The single cross-correlation `∫ Qᵢₖ(t)·Qₘₖ(t−v)` (one
summand shape, `Q = qWeighted`) is handled exactly like `matCorrFull` but without the `∑`:
**`qWeighted_corr_eq_zero_of_R_lt_abs`** (vanishes for `|v|>(σₐ+σᵦ)/2` — supports `[λₐₗ,Rₐₗ]`,
`[λᵦₗ,Rᵦₗ]+v` cannot overlap; the middle index `l` cancels, giving the symmetric support
`[−(σₐ+σᵦ)/2,(σₐ+σᵦ)/2]`), **`qWeighted_corr_continuous`** (`const · q0_corr_real_continuous`),
**`qWeighted_corr_abs_le`** (continuous + compact support ⟹ globally bounded); capstone
**`hI2_qWeighted`** (`(∫ Qᵢₖ·Qₘₖ(·−v))·Ψₘⱼ(r+·)` integrable via `integrable_of_bddSupp_mul_continuous`).
**Remaining 2 of 9**: `hI1` (inner-convolution continuity) and `hfub` (2D product-measure Fubini
integrand); plus `hbridge` and the open `hseed`.

**✅ `hI1` DISCHARGED (2026-08-10, same file `section PhysicalIdentification`, std-3, full build 8759)
— 8 of 9 integrability inputs now done.**  The inner convolution `t ↦ ∫ Qₘₖ(s)·Ψₘⱼ(r+t−s) ds` is
continuous — the standard Mathlib convolution-continuity lemmas need the compact-support factor to be
continuous (`qWeighted` isn't; it jumps in `s`), so proved directly by **`continuousAt_of_dominated`**
at each `t₀`: the integrand is continuous in `t` pointwise (`Ψ` continuous, `qWeighted` `t`-constant)
and, for `t` in a unit ball around `t₀`, dominated by `M·|qWeightedₘₖ|` (`M` bounds `Ψ` on the compact
`[r+t₀−1−R, r+t₀+1−λ]` — the range of `r+t−s` over `s ∈ supp qWeightedₘₖ`, `t ∈ ball(t₀,1)`).  Lemmas
**`qWeighted_integrable`** (bounded × compact support), **`qWeighted_conv_continuous`** (the crux),
**`hI1_qWeighted`** (`Qᵢₖ · (that convolution)` integrable via the compact-support helper).  **Remaining
1 of 9**: `hfub` (the product-measure Fubini integrand — 2D compact-support integrability); plus
`hbridge` and the open `hseed`.

**✅✅ `hfub` DISCHARGED — ALL 9 integrability inputs now done (2026-08-10, same file
`section PhysicalIdentification`, std-3, full build 8759).**  The 2D Fubini integrand
`Qᵢₖ(t)·Qₘₖ(t−v)·Ψₘⱼ(r+v)` (`Q = qWeighted`) is bounded, measurable, and compactly supported in the
rectangle `[λᵢₖ,Rᵢₖ] × [λᵢₖ−Rₘₖ, Rᵢₖ−λₘₖ]`, hence integrable on `volume ×ˢ volume`.  General helper
**`integrable_of_bddOn_support`** (any measure: measurable `F` supported in a finite-measure set,
bounded by `C` on it, is integrable — `integrable_indicator_iff` + `Measure.integrableOn_of_bounded`);
capstone **`hfub_qWeighted`** (finite rectangle measure via `Measure.prod_prod`; the bound `C₁·C₂·M`
where `M` bounds `Ψ(r+·)` on the compact `v`-support; the support inclusion from both Baxter factors'
supports).  **⇒ every integrability side-condition of the seed-route `hclaimA` capstone
(`correctedSeedExt_hclaimA_matShellConvAsym` / the `matOzStar_of_matDCF_ae_canonical` hclaimA) is now
discharged from `Ψ`-continuity** (`hB`/`hA`/`hC`/`hI1`/`hI2`/`hfub`/`hint`/`hIfwd`/`hIbwd`), alongside
the geometric `hsupp`/`hQlam` (from `q0MixEntry` support) and the physical identification
`matDCFfoldKernel(qWeighted) = matDCFreCore`.  **Remaining for the full unequal-diameter `MatOZStar`**:
the `Ψ`/`Φ`-property hypotheses `hodd` (Ψ odd), `hUtouter`/`hPhiOuter` (outer vanishing), `hbridge`
(`matRadialConv_eq_matShellConv`, provable), and the open `hseed` (the Wertheim–Thiele identity —
proved equal-diameter, numerically confirmed unequal).

**✅ `hbridge` DISCHARGED in `shellKernel Φ` form (2026-08-10, same file `section PhysicalIdentification`,
std-3, full build 8759).**  **`matBridge_of_regular`**: `r·matRadialConv Φ (Ψ/·) = matShellConv
(shellKernel Φ) (Ψ/·)` via `matRadialConv_eq_matShellConv_of_shellKernel`, with BOTH its side-conditions
discharged from `Ψ` odd+continuous and `Φ` bounded+measurable+compact-support.  `hshell`
(interval-integrability of `oddExt(Ψ/·)`) uses `oddExt_div_self_eq_of_odd` (`oddExt(Ψ/·) = Ψ` for odd Ψ) +
`Continuous.intervalIntegrable`; `hjoint` (the 2D integrand `(Ioi u).indicator(s·Φᵢₖ)·(oddExt(Ψ/·)(r−u)+
oddExt(Ψ/·)(r+u))`) is bounded (`|s·Φ|≤σ·Cφ`, `|Ψ(r±u)|≤M` on `[r−σ,r+σ]`) + measurable (`{p|p.1<p.2}`
-indicator) on the FINITE restricted product measure `(vol.restrict Ioc0σ)²` (via `Measure.prod_restrict`
+ `Measure.integrableOn_of_bounded`), then `Integrable.congr` from the `Ψ`-form.  (`MixtureDCFAEInjective`
now imports `HSMixture/MixtureOzStar`.)  **This gives `hbridge` with kernel `shellKernel Φ`**; to feed the
capstone (whose kernel is `matDCFreCore/ρ`) still needs the **shell-kernel↔DCF identity**
`shellKernel(Φ) = matDCFreCore/ρ` — the cosine-transform/Baxter-WH-factorization step (the open
Wertheim-class gap, `matRadialSymbol_eq_shellKernel_cos` + WH factorization), alongside `hodd`/`hUtouter`/
`hPhiOuter` (Ψ/Φ properties) and the open `hseed`.

**◑ shell-kernel↔DCF identity — REDUCTION formalized, identity ISOLATED as the open Baxter-WH gap
(2026-08-10, same file, std-3, full build 8759).**  The identity `shellKernel(Φ) = matDCFreCore/ρ` is
**NOT a mechanical discharge**: cosine-transforming it gives `radial_fourier(Φ)` (`matShellKernel_cos_eq_radial_fourier`)
on the left and the 1D transform of `matDCFreCore` (= `Cmix0`, via `matDCFfullN_laplace`) on the right —
bridging the **3D-radial** and **1D** transforms is exactly the Baxter–Wiener–Hopf factorization the
project flags as open (and it carries a subtle `ρ`-normalization: at `N=1`, `matCorr = matSelfConv` on
`(0,σ)` but the `ρ_geo·q0` weight vs `q0_poly` differ by the density factor).  Delivered instead the
honest **reduction** **`matBridge_matDCFreCore`**: `r·matRadialConv Φ (Ψ/·) = matShellConv (matDCFreCore/ρ)
(Ψ/·)` from `matBridge_of_regular` (kernel `shellKernel Φ`) + the single real-space hypothesis
`hShellDCF` (`shellKernel(Φᵢₖ)(v) = matDCFreCore(i,k)(v)/ρ` on `(0,σ)`, applied a.e. under the shell
integral).  **⇒ the capstone's `matDCFreCore/ρ`-kernel `hbridge` follows from `hShellDCF` alone** — the
sole remaining analytic input is now this one isolated identity (the open Baxter-WH step), everything
else in the bridge being discharged.

**◑ `hShellDCF` reduced to a first-order ODE (2026-08-10, same file, std-3, full build 8760).**  Even
the equal-diameter `hShellDCF` is NOT a mechanical computation — it is the differential Baxter–WH
relation between the DCF core and the forcing.  `shellKernel c σ` is the antiderivative-type object:
**`shellKernel_eq_of_hasDerivAt`** (`F σ = 0` + `F' = −2π·s·c(s)` on `[v,σ]` ⟹ `shellKernel c σ v = F v`,
via `intervalIntegral.integral_eq_sub_of_hasDerivAt`) and the continuity variant
**`shellKernel_eq_of_hasDeriv_of_continuousOn`** (`F` differentiable only on the OPEN `(v,σ)`, continuous
on `[v,σ]` — matching the piecewise-polynomial `matDCFreCore` with its kink at `σ`).  Capstone
**`hShellDCF_of_deriv`**: `shellKernel(Φᵢₖ)(v) = matDCFreCore(i,k)(v)/ρ` on `(0,σ)` FROM (i) boundary
`matDCFreCore(σ)/ρ = 0` (provable at equal diameters — `q0MixEntry` vanishes at `R=σ` and the
correlation's support-overlap `{σ}` is null), (ii) continuity, (iii) the **first-order relation**
`(matDCFreCore/ρ)'(s) = −2π·s·Φᵢₖ(s)`.  **⇒ `hShellDCF` is isolated to the ODE `(matDCFreCore/ρ)' =
−2π·s·Φ`** — the differential form of the Baxter–WH factorization; even at equal diameters this
derivative identity (relating the DCF core to the physical forcing `c_HS`) is the residual open content.

**◑ the ODE `(matDCFreCore/ρ)' = −2π·s·Φ` DISCHARGED by CONSTRUCTION (2026-08-10, same file, std-3,
full build 8760).**  The ODE is first-order, so it **defines** the forcing: **`shellForcing`** :=
`Φᶜᵢₖ(s) = −matDCFreCore'(i,k)(s)/(ρ·2π·s)` (the shellKernel-inverse).  With `Φ = shellForcing`,
**`hasDerivAt_matDCFreCore_div`** proves `(matDCFreCore/ρ)'(s) = −2π·s·Φᶜᵢₖ(s)` **by construction**
(from `matDCFreCore` differentiable at `s ≠ 0` — `−2π·s·(−d/(ρ·2π·s)) = d/ρ`, `field_simp`), and
**`hShellDCF_construct`** feeds it through `hShellDCF_of_deriv` to give
`shellKernel(Φᶜᵢₖ)(v) = matDCFreCore(i,k)(v)/ρ` on `(0,σ)`.  **⇒ the ODE is no longer an obstruction**:
`hShellDCF` (hence the whole seed-route bridge) now reduces to just (a) `matDCFreCore`'s C¹ regularity
(differentiable + continuous + vanishing at `σ`, all mechanical for the piecewise-polynomial DCF), and
(b) identifying the constructed `shellForcing` with the physical DCF forcing `c_HS` — the sole genuinely
open (Baxter–WH) content, now a clean forcing-identification statement rather than a functional identity.

**◑ item (a) — `matDCFreCore` C¹ regularity, linear term DONE + reduced to the correlation (2026-08-10,
same file, std-3, full build 8760).**  **`qWeighted_contDiffOn`**: the linear Baxter term
`qWeightedᵢₖ = ρ_geoᵢₖ·q0MixEntry` is `C^∞` on the open support `(λᵢₖ,Rᵢₖ) = ((σₖ−σᵢ)/2,(σᵢ+σₖ)/2)` — a
quadratic there, via `q0MixEntry = indicator·quad` (`Set.indicator_of_mem`) + `ContDiff.contDiffOn.congr`,
the same technique as `cHSmixRaw_contDiffOn`'s `hqFwd`.  **`matDCFreCore_contDiffOn_of_corr`**: via the
physical identification `matDCFfoldKernel(qWeighted) = matDCFreCore`, the DCF core is `ContDiffOn` on
`s ⊆ (λᵢₖ,Rᵢₖ)` whenever the reflected linear term `qWeightedₖᵢ(−·)` and the correlation
`matCorrFull(qWeighted)ᵢₖ` are (the forward term done).  **Remaining for (a)**: `matCorrFull`'s
`ContDiffOn` — follows from the PROVEN `qpConv_contDiffOn` (`upper`/`lower`) via the normalization bridge
`matCorrFull(qWeighted)ᵢₖ(v) = ∑ₗ qpConv(physMix)ᵢₗₖ(v)/(2π)²` (a convolution/`√ρ` computation); at equal
diameters the reflected term is `0` on `(0,σ)`.  So the DCF-core regularity reduces to that one
normalization identity onto the already-smooth `qpConv`.

**✅ item (a) FULLY DISCHARGED on the upper piece (2026-08-10, same file, std-3, full build 8760).**  The
normalization bridge is proved: **`matCorrFull_eq_qpConv`** — `matCorrFull(qWeighted)ᵢₖ(v) = ∑ₗ
qpConv(physMix)ᵢₗₖ(v)/(2π)²`, since `qFwd = 2π·qWeighted` and `pMixEntry = 2π·qWeighted(−·)` (so the
convolution integrand is `(2π)²·` the correlation integrand; `qFwd(physMix)i l = 2π·qWeightedᵢₗ` via
`√(ρᵢρₗ) = rhoGeoPhys`, the convolution unfolds by `rfl` with `open scoped Convolution`, then `field_simp`).
**`matCorrFull_contDiffOn_upper`** (`ContDiffOn.sum` of `qpConv_contDiffOn_upper (physMix) i l k / (2π)²`);
**`qWeightedRefl_contDiffOn_upper`** (the reflected term is `0` on the upper piece — its support lies
below); capstone **`matDCFreCore_contDiffOn_upper`**: `matDCFreCore` is `C^∞` on `(λᵢₖ,Rᵢₖ)` (= `(0,σ)`
at equal diameters), via `matDCFreCore_contDiffOn_of_corr`.  (`MixtureDCFAEInjective` now imports
`MixtureHSDCF`.)  **⇒ item (a) is done**: on the upper piece the DCF core is smooth, so
`hShellDCF_construct`'s regularity hypotheses (`hFc`/`hdiff`) hold there — the seed route's only open
residue is item (b), identifying `shellForcing` with the physical `c_HS` (the Baxter–WH forcing map),
plus the open `hseed`.

**◑ item (b) — `shellForcing = c_HS` IS the open Baxter–WH gap, characterized by uniqueness (2026-08-10,
same file, std-3, full build 8760).**  Item (b) is NOT mechanically dischargeable: `c_HS` (the mixture
real-space PY DCF) is not even defined in-project (the deferred Wertheim/Lebowitz closed form), and the
identity is the Baxter–WH factorization.  What IS provable — the honest characterization — is that the
forcing is UNIQUELY pinned by `hShellDCF`: **`shellKernel_hasDerivAt`** (`(shellKernel c σ)'(v) =
−2π·v·c(v)` on `(0,σ)`, FTC lower-limit `intervalIntegral.integral_hasDerivAt_left` + `|v|=v` locally);
**`forcing_eq_shellForcing_of_hShellDCF`** — ANY continuous `Φ` satisfying `hShellDCF` (`shellKernel Φ =
matDCFreCore/ρ` on `(0,σ)`) is FORCED to equal `shellForcing` there (differentiate the identity:
`−2π·v·Φ(v) = (matDCFreCore/ρ)'(v)`, so `Φ(v) = −(matDCFreCore/ρ)'(v)/(2π·v) = shellForcing(v)`).  **⇒
identifying the physical `c_HS` with `shellForcing` is EXACTLY the claim that `c_HS` satisfies `hShellDCF`
— there is no independent content, and the reduction chain (hShellDCF → ODE → shellForcing = c_HS) is
closed: the sole genuinely-open analytic residues of the seed route are the Baxter–WH factorization
(hShellDCF for the physical DCF) and the Wertheim `hseed`; everything else is proved std-3.**

**✅ the `hseed` residue is DISCHARGED at equal diameters (2026-08-10, `MixtureCorrectedSeed.lean`, std-3,
full build 8760).**  Unlike item (b), the Wertheim `hseed` is genuinely PROVED at equal diameters (not
merely numerically confirmed).  **`hseed_equalDiam`** supplies the exact `hseed` hypothesis of
`matBaxterUQmSymFullExt_eq_rPhi_of_seed`/`correctedSeedExt_hclaimA` (`lam = 0`, `Φ = c_HS`): its LHS is
`matBaxterUQmSymFullExt` on the core (`matBaxterUQmSymFullExt_core_reduce`), which the already-proven
`matBaxterUQmSymFullExt_eq_rcHS_of_equalDiam` shows equals `r·c_HS` — grounded in the proved scalar
`baxter_core_seed` (Wertheim–Thiele moment algebra) via the equal-diameter row-sum collapse
`∑ₖ Qᵢₖ = q0_poly`.  **⇒ at equal diameters BOTH the seed's hclaimA and its `hseed` are now proved**, so
the corrected-seed hclaimA chain is fully instantiable there (the equal-diameter MatOZStar is separately
closed by the value route `matOzStar_equalDiam_unique`); the sole open residue reduces to the
unequal-diameter Baxter–WH content (hShellDCF/`c_HS` + the unequal `hseed`, both classical
hard-sphere-mixture analysis).

**✅ unequal-diameter `hseed` — the `Ψouter` coupling is fully pinned to the constructed solution
(2026-08-10, `MixtureCorrectedSeed.lean`, std-3, full build 8760).**  For the glued solution
`Ψ = matBaxterPsi Ψouter Ψcore σ`, **`matBaxterUQmSymFullExt_fully_explicit_intermediateLead_outer`**
rewrites BOTH coupling terms of the fully-explicit intermediate lead — the leading `∫_σ^{r−λ}
Qₘᵢ(r−w)·Ψₘⱼ(w)` and the intermediate `∫_σ^{r+t−λ} Qₘₖ(r+t−w)·Ψₘⱼ(w)` (the latter under the `∫ t`,
handled by `intervalIntegral.integral_congr`) — via `renewalForm_eq_outer` (`Ψₘⱼ(w) = Ψouterₘⱼ(w)` for
`w ≥ σ`, `matBaxterPsi_outer`).  **⇒ on the genuine intermediate-lead region `σ+λ ≤ r < σ` the ENTIRE
fully-explicit unequal-diameter WT LHS is `Q`-moments + concrete integrals of the CONSTRUCTED
`matBaxterPsiOuter`, with no abstract `Ψ` remaining** — the coupling is not a free unknown but a definite
functional of the built outer Volterra solution.  The sole residual is then the numerical WT identity
`= r·c_HS_mix` (the classical Lebowitz mixture DCF); the non-circular value route `matOzStar_unique`
still discharges MML.8 without evaluating it.

**⚠ CORRECTION (2026-08-10) — the last-turn `cHSodd`-based `c_HS_mix` is DEGENERATE; the N=1
consistency check DISPROVED it, and the definition is corrected here (std-3, full build 8761).**

Last turn I defined `c_HS_mix X i j r := cHSodd X i j r/(2π√(ρᵢρⱼ)·r)` claiming `cHSodd = 2π√ρ·r·c^HS`.
**The N=1 consistency test proved that FALSE:** `cHSodd` (numerator) is the odd part of the zeroth-order
assembly `cHSmixRaw = qFwd + pMixEntry − ∑ qpConv`, and **`cHSmixRaw X i i` is EVEN**
(`cHSmixRaw_diag_even`), so **`cHSodd X i i ≡ 0`** (`cHSodd_diag_eq_zero`) ⇒ **`c_HS_mix X i i ≡ 0`**
(`c_HS_mix_diag_eq_zero`) — it does NOT reduce to the (nonzero) scalar `c_HS`.  Proof: `qFwd X i i(t)
+pMixEntry X i i(t)` is even (each the other's reflection) and every `qpConv X i l i = qFwd ⋆ (qFwd∘neg)`
is an **autocorrelation** (even by translation invariance, `qpConv_diag_even`).  The docstring's claim
`cHSmixRaw = 2π√ρ·t·c^HS` was internally inconsistent (even ≠ odd).  **The first-order `dcfOdd` escapes
this only because the Yukawa `ℬ` breaks the even symmetry — at zeroth order there is nothing to break
it.**  (Numerically `cHSmixRaw` is ALSO not `∝ c_HS`: ratio `raw/c_HS` runs `24→1.7` across the core.)

**Root cause + fix.** The physical `c^HS` is EVEN; the object the OZ★/Baxter route uses is the odd
`S(r)=r·c^HS`, given by the Baxter *derivative* form **`HardSphere.baxter_factorization_inner`**
(`2πρ r c_HS = ∫_r^σ q0_poly(r'−r)·q0_poly'(r') − q0_poly'(r)`, the shell-kernel inverse of `cHSmixRaw`,
carrying `q0_poly'` + a boundary term — neither present in the plain self-convolution).  Verified vs the
scalar `c_HS` to machine precision.  **CORRECTED N=1 consistency** (`MixtureHSDCFFin1.lean`, new file):
**`rcHS_physMixN_fin1`** — `2π·ρ₀·r·c_HS(η,σ₀,r) =` the Baxter-derivative form, `η=π ρ₀σ₀³/6`
(`etaMix_n1`), directly from `baxter_factorization_inner`; and **`q0MixEntry_physMixN_fin1_core`** —
`ρ₀·q0MixEntry(physMixN) 0 0 = q0_poly` on `[0,σ₀]` (physical Lebowitz coeffs collapse to scalar PY via
`Q0phys_n1`/`Qppphys_n1`; `q0MixEntry` lacks the `ρ₀` that `q0_poly` carries).  **⇒ the physical mixture
kernel DOES reproduce `c_HS` at one component — through the derivative form, not the odd extraction.**
`cHSodd`/`c_HS_mix` are retained only to record the failed route; the seed forcing `Φ` is `c_HS`
(scalar/Baxter-derivative), NOT the degenerate `c_HS_mix`.

**⚠ UNEQUAL-DIAMETER derivative form (2026-08-10) — the naive `q0`-convolution is WRONG; the correct
object is the renewal `Ψ` (`matBaxterUQmSymFullExt`), the open residual (std-3, build 8761).**  Tried
to build the unequal-diameter mixture derivative form as the direct generalization of
`baxter_factorization_inner`: `2π r c_ij = −q0MixDeriv_ij(r) + ∑ₗ ρₗ ∫ q0MixEntry_il(r'−r)·q0MixDeriv_lj(r')`.
**DISPROVED numerically:** for a σ={1.0,0.7} binary it is not even symmetric (`c_ij≠c_ji`) and
disagrees with a direct **OZ+PY solve** (converged, round-trip 1e-13) by **5–13%** across all index
variants (I tested 8 index/transpose forms); it is exact ONLY at N=1 and equal diameters (there it hits
`c_HS(η_total)` to machine precision).  **Root cause (now fully understood):** with the codebase
convention (`Q̂₀ = δ − √(ρᵢρⱼ)·Laplace[q0MixEntry]`, **no 2π** — from `qhat_entry_decomp`), the k-space
factorization `I − Q̂₀(ik)Q̂₀ᵀ(−ik) = √(ρᵢρⱼ)·ĉ_ij(k)` holds (ratio≈1.00 at low k), but `Cmix0` is the
**3D Fourier** transform while `Q̂₀` is **1D Laplace** — the `4π/k` between them means `c_ij` is the
**shell-kernel inverse** (odd `r·c` / derivative), NOT the even self-convolution.  For unequal diameters
that inverse needs the **renewal function `Ψ`** (the OZ solution), which a `q0`-only convolution lacks.
**⇒ the correct object is the renewal form `matBaxterUQmSymFullExt`** (`= r·c_HS` at equal-diam via
`…_eq_rcHS_of_equalDiam`, `Ψ`-outer pinned to `matBaxterPsiOuter`); its unequal-diameter value is the
classical Lebowitz result = the acknowledged **open residual** (DCF↔`Ĉ₀`, `DPClosureMap`:538).  This
**vindicates the memory's "don't fabricate the Lebowitz mixture `c_HS`" guidance.**  Shipped the FTC
building blocks **`q0MixDeriv`** (`= Q0ᵢⱼ + Qppⱼ·(r−Rᵢⱼ)`) + **`hasDerivAt_q0MixEntry`** (`MixtureHSDCFFin1`)
for whoever formalizes the shell-inverse form.

**✅ SHELL-INVERSE FORM REDUCTION of `matBaxterUQmSymFullExt` DONE (2026-08-10, std-3, build 8761,
`MixtureDCFAEInjective` §PhysicalIdentification).**  The renewal seed's correct (unequal-diameter)
`r·c^HS` derivative form IS the **shell-kernel inverse** `shellForcing = −matDCFreCore'/(ρ·2π·s)`; the
reduction now ties the seed to it explicitly.  **`matShellConvAsym_matDCFreCore_eq_shellForcing`** —
the seed's `matDCFreCore/ρ`-kernel `matShellConvAsym` equals the one with kernel
`shellKernel(shellForcing)` (since `matDCFreCore/ρ = shellKernel(shellForcing)` on `(0,σ)` by
`hShellDCF_construct`, and the shell convolution only samples its kernel there — one `integral_congr_ae`
on `(0,σ)`, `u=σ` measure-zero).  **`hclaimA_qWeighted_to_shellForcing`** — composes this with
`hclaimA_qWeighted_to_matDCFreCore` to take the seed's `qWeighted`-fold `hclaimA`
(`= matBaxterUQmSymFullExt`'s fold, `matDCFfoldKernel_qWeighted_eq_matDCFreCore`) **directly** to the
`shellKernel(shellForcing)` form.  **⇒ the renewal seed `matBaxterUQmSymFullExt`'s forcing is exactly
`shellForcing` (the shell-inverse), for ALL diameters** — no naive convolution, no `Ψ` guesswork.  The
sole residual is the identification `shellForcing = c_HS` (`forcing_eq_shellForcing_of_hShellDCF`) — the
open Baxter–WH gap `hShellDCF` — plus `matDCFreCore`'s C¹ regularity (mechanical, piecewise-poly).  The
gap is now a single differential/boundary condition, not a closed-form Lebowitz derivation.

**✅ `matDCFreCore` C¹ REGULARITY — `hdiff`/`hFc`/`hbdry` DISCHARGED (2026-08-10, std-3, build 8761,
`MixtureDCFAEInjective` §PhysicalIdentification).**  Three of the four `hShellDCF_construct` /
`matShellConvAsym_matDCFreCore_eq_shellForcing` inputs are now proved outright (equal diameters):
**`matDCFreCore_differentiableAt`** (hdiff) — `DifferentiableAt` on the open `(0,σ)`, straight from
`matDCFreCore_contDiffOn_upper`'s `C^∞`; **`matDCFreCore_continuousOn_Icc`** (hFc) — `ContinuousOn [v,σ]`
up to the boundary: on `[v,σ]⊆[0,σ]` the forward Baxter term is `√(ρᵢρₖ)·quadratic` (indicator `= 1`),
the reflected term vanishes (support `< 0`), and the correlation is **globally** continuous via the new
**`matCorrFull_continuous`** (each species term = `√(ρᵢρₘ)√(ρₖρₘ)·` the `q0MixEntry` autocorrelation,
`Re` of the complex `q0MixEntry_corr_continuous` through `integral_complex_ofReal`);
**`matDCFreCore_boundary`** (hbdry) — `matDCFreCore(σ)=0`: the forward quadratic vanishes at `R=σ`, the
reflected support is `<0`, and the correlation integrand is identically `0` (the supports `[0,σ]` and
`[σ,2σ]` touch only at `t=σ`, where the forward factor is already `0`).  **⇒ the shell-inverse
reduction's residue is now only (i) `hint` — `IntervalIntegrable` of `−2π·s·shellForcing = matDCFreCore'/ρ`
on `[v,σ]` (the derivative up to the kink), and (ii) the open Baxter–WH identification
`shellForcing = c_HS`.**  Everything else in the unequal-diameter route is mechanical and done.

**◑ `hint` (shellForcing integrability) — REDUCED to the pure derivative-integrability (2026-08-10,
std-3, build 8761).**  **`hint_of_deriv_intervalIntegrable`** strips the `shellForcing`/`ρ`/`s`
bookkeeping: on `[v,σ]` (`0 < v ≤ σ`) the integrand `−2π·s·shellForcing = deriv(matDCFreCore)/ρ` (the
`2π·s` cancels since `s ≠ 0`), so `hint` ⟺ `IntervalIntegrable (deriv matDCFreCore) v σ` (via
`IntervalIntegrable.congr` on the `EqOn`).  **`matDCFreCore_deriv_continuousOn`** — the derivative is
CONTINUOUS on the open interior (from `matDCFreCore_contDiffOn_upper`'s `C^∞`), so every compact
SUBinterval `[v,w]⊂(0,σ)` is integrable.  **Residual = the single boundary point `σ`:** `matDCFreCore`
has a kink at `σ` (the forward Baxter linear term's slope `√Q0` vs `0`), so Lean's two-sided `deriv(σ)`
is `0` while the left-limit is finite — integrability up to `σ` needs the convolution `matCorrFull`'s
derivative to be bounded there (`~(σ−s)²` ⇒ `matCorrFull'→0`), which is the piecewise-polynomial
boundary asymptotics the project deliberately avoids computing.  So `hint` is now a **single
endpoint-boundedness fact**, cleanly separated from all the shellForcing structure.

**✅⭐ `matCorrFull'` BOUNDED AT `σ` ⇒ `hint` FULLY DISCHARGED (2026-08-10, std-3, build 8761,
equal diameters).**  The boundedness is proved via **Lipschitz** (Lipschitz ⟺ bounded derivative),
with a key simplification that avoids any region-split:
- **`qWeighted_lipschitzOnWith`** — `qWeighted i m` is Lipschitz on `Ici 0`.  On `[0,∞)` the Baxter
  kernel's only jump (left edge `0`) is never reached and the quadratic vanishes at the right edge
  `σ`, so `q0MixEntry i m x = quad(min x σ)` there — a Lipschitz composition (`quad` Lipschitz on the
  compact `[0,σ]` by the algebraic factoring `|quad(u)−quad(v)| ≤ (|Q0|+|Qpp|σ)|u−v|`, `min·σ`
  `1`-Lipschitz).
- **`matCorrFull_lipschitzOnWith`** — `matCorrFull` Lipschitz on `Ici 0`.  In the SUBSTITUTED form
  `∑ₘ ∫ qim(u+v)·qkm(u) du` (translation `integral_sub_right_eq_self`) the MOVING kernel is `qim`,
  argument `u+v ≥ 0` (the jump is never reached), so `qWeighted_lipschitzOnWith` bounds the integrand
  difference **pointwise** — NO region-split, NO L¹ translation-modulus theory.  Constant
  `∑ₘ Lip(qim)·‖qkm‖₁`.  This IS the `matCorrFull'`-at-`σ` boundedness.
- **`matDCFreCore_lipschitzOnWith`** — on `Ioi 0` the reflected term vanishes, so
  `matDCFreCore = qWeighted i k − matCorrFull`, Lipschitz (difference).
- **`hint_discharged`** — `deriv(matDCFreCore)` is bounded on `Ioi 0` (`norm_deriv_le_of_lipschitzOn`)
  + measurable (`measurable_deriv`) ⇒ `IntervalIntegrable` (`Measure.integrableOn_of_bounded`) ⇒ via
  `hint_of_deriv_intervalIntegrable`, **`hint` is PROVEN**.

**⇒ The ENTIRE mechanical route of the unequal-diameter shell-inverse reduction is now closed at
equal diameters** (`hdiff`/`hFc`/`hbdry`/`hint` all discharged).  The ONLY remaining open content is
the genuine Baxter–WH identification `shellForcing = c_HS` (`forcing_eq_shellForcing_of_hShellDCF`) —
a single differential/boundary condition, the irreducible analytic core.

**◑⭐ `shellForcing = c_HS` REDUCED to the Baxter ODE (2026-08-10, std-3, build 8761).**
**`shellForcing_eq_cHS_of_baxterODE`** — GIVEN the pointwise Baxter–Wertheim differential relation
`(matDCFreCore/ρ)'(s) = −2π·s·c_HS(s)` on `(0,σ)`, the physical identification `shellForcing i k v =
c_HS v` follows.  Every OTHER input is discharged internally: the boundary `matDCFreCore(σ)=0`
(`matDCFreCore_boundary`), continuity up to `σ` (`matDCFreCore_continuousOn_Icc`), integrability of the
`c_HS`-integrand (`fun_prop`, `c_HS` polynomial rep continuous), and the shell-kernel inversion
(`hShellDCF_of_deriv` → `forcing_eq_shellForcing_of_hShellDCF`, using the continuous inner-polynomial
representative of `c_HS` since `c_HS` jumps at `σ`).  **⇒ the ENTIRE open Baxter–WH content is now
EXACTLY this one ODE** — the classical real-space factorization (a genuine identity in `η`, requiring
the explicit convolution the route deliberately avoids; `matOzStar_unique` still discharges MML.8
without ever evaluating it).  This is the maximally-honest statement of what remains open: a single
pointwise differential relation, with all surrounding scaffolding proved.

**◑ N=1 Baxter ODE — the Leibniz step DONE (2026-08-10, std-3, build 8761, `BaxterForcingDeriv.lean`).**
The N=1 ODE `matDCFreCore'(s) = −2πρ·s·c_HS(s)` IS provable from the proven `baxter_factorization_inner`:
`matDCFreCore = q0_poly − (autocorrelation)`, so `matDCFreCore'(s) = q0_poly'(s) − matCorrFull'(s)`, and
`q0_poly'(s) − ∫_s^σ q0_poly(r'−s)q0_poly'(r') = −2πρ s c_HS(s)` is exactly baxter.  The key analytic
step — the **correlation derivative** — is now proved: **`hasDerivAt_q0Corr`** shows the `q0_poly`
autocorrelation `s ↦ ∫₀^σ q0_poly(t−s)·q0_poly(t)dt` (scalar `matCorrFull`) has derivative
`∫₀^σ −q0PolyDeriv(t−s)·q0_poly(t)`, via **MA.16** (`hasDerivAt_intervalIntegral_param`) with the
REFLECTED kernel `K = q0_poly∘neg` (`K(x−t)=q0_poly(t−x)`), the kernel data (continuity, a.e. deriv,
measurability, Lipschitz) obtained by composing `BaxterKernelDeriv`'s data with `neg`.  (Also
`hasDerivAt_q0Conv`, the convolution variant, in scratch.)  **Remaining for the full N=1 ODE:** an IBP
relating this correlation derivative `∫ −q0PolyDeriv(t−s)q0_poly(t)` to baxter's integral
`∫_s^σ q0_poly(r'−s)q0PolyDeriv(r')` (they differ by which factor is differentiated + a boundary term),
plus the `q0_poly`↔`q0MixEntry` bridge (scalar framework uses `q0_poly`; the mixture uses the
indicator-cutoff `q0MixEntry`).  So the N=1 ODE's Leibniz core is discharged; the residue is a
mechanical IBP + the closed-form baxter identity.

**✅ IBP connecting correlation derivative ↔ baxter integral DONE (2026-08-10, std-3, build 8761).**
**`q0_ibp`** (`BaxterForcingDeriv.lean`): on `[s,σ]` (`0<s<σ`),
`∫_s^σ q0_poly(t)·q0PolyDeriv(t−s) = −q0_poly(s)·q0_poly(0) − ∫_s^σ q0PolyDeriv(t)·q0_poly(t−s)`.
Proved via `intervalIntegral.integral_mul_deriv_eq_deriv_mul` with the **smooth polynomial** `P` (on
`[s,σ]⊆Iic σ`, `q0_poly=P`, `q0PolyDeriv=P'` — dodging the σ-kink via `q0_poly_inner`), the top
boundary killed by `q0_poly(σ)=0`, and `integral_congr_ae` for the single `q0PolyDeriv`-at-`σ` point.
**Numerically confirmed the full N=1 ODE structure:** the correct scalar DCF-core is
`q0M(s) − corrM(s) = 2πρ∫_s^σ t·c_HS(t)dt` (machine precision), where `q0M` is the **cutoff** factor and
`corrM(s) = ∫_s^σ q0_poly(t)·q0_poly(t−s)dt` (VARIABLE lower limit `s`).  Its Leibniz derivative has a
`−q0_poly(s)·q0_poly(0)` boundary from the variable limit which **exactly cancels** the `q0_ibp`
boundary, leaving `matDCFreCore'(s) = q0PolyDeriv(s) − ∫_s^σ q0_poly(r'−s)·q0PolyDeriv(r') = −2πρ s
c_HS(s)` by `baxter_factorization_inner`.  **Remaining for the full N=1 ODE:** the variable-lower-limit
Leibniz for `corrM` (`hasDerivAt_q0Corr` is the FIXED-limit version; `corrM`'s cutoff makes the lower
limit `s`) — a combined FTC-endpoint + parameter differentiation.  So the N=1 ODE is down to that one
variable-limit Leibniz; the Leibniz-core, the IBP, and the boundary cancellation are all proved.

**✅ corrM DERIVATIVE DONE (2026-08-10, std-3, build 8761) — variable-limit Leibniz SIDESTEPPED.**
**`hasDerivAt_corrM`** (`BaxterForcingDeriv.lean`): `corrM(s) = ∫₀^σ q0_poly(t+s)·q0_poly(t)dt` (the
`q0M` autocorrelation, extended to FIXED limits `[0,σ]` because `q0_poly(t+s)=0` for `t>σ−s` kills the
tail) is differentiable with derivative `∫₀^σ q0PolyDeriv(t+s)·q0_poly(t)dt`.  **Key move: the
`q0_poly(σ)=0` extension turns the variable lower limit into a FIXED one**, so `corrM(s)` equals
`hasDerivAt_q0Corr`'s function at `−s`, and its derivative is just the **chain rule** (`∘ neg`) on the
already-proved fixed-limit correlation derivative — no variable-limit-Leibniz machinery (no combined
FTC-endpoint + parameter differentiation) needed.  **⇒ every ingredient of the N=1 Baxter ODE is now
proved:** `hasDerivAt_q0Corr` (correlation deriv), `q0_ibp` (IBP), `hasDerivAt_corrM` (corrM deriv),
`baxter_factorization_inner` (the closed form).  The capstone `matDCFreCore'(s) = q0PolyDeriv(s) −
corrM'(s) = q0PolyDeriv(s) − ∫_s^σ q0_poly(r'−s)q0PolyDeriv(r') = −2πρ s c_HS(s)` is a mechanical
assembly (shift `corrM'` to the baxter integral via `integral_comp_add_right` + the `q0PolyDeriv=0`
tail vanishing, then `baxter_factorization_inner` + `linarith`) — all analytic content is discharged.

**✅✅ N=1 BAXTER ODE CAPSTONE — PROVEN (2026-08-10, std-3, build 8761).**  **`baxterODE_n1`**
(`BaxterForcingDeriv.lean`): for `s ∈ (0,σ)`,
`HasDerivAt (fun x => q0_poly(x) − ∫₀^σ q0_poly(t+x)·q0_poly(t)) (−2πρ·s·c_HS(s)) s` —
i.e. `matDCFreCore'(s) = −2πρ·s·c_HS(s)`, the N=1 Baxter–WH differential relation.  Assembly, exactly
as forecast: `hval : q0PolyDeriv(s) − corrM'(s) = −2πρ s c_HS(s)` from (i) `hA` carrying
`corrM'(s) = ∫₀^σ q0PolyDeriv(t+s)q0_poly(t)` onto the Baxter integral `∫_s^σ q0_poly(r'−s)(ρq'+ρq''(r'−σ))`
— a shift `integral_comp_add_right` to `[s,σ+s]`, an `integral_add_adjacent_intervals` split at `σ`, the
`[σ,σ+s]` piece killed by `q0PolyDeriv_eq_zero_of_ge`, and `integral_congr_ae` rewriting `q0PolyDeriv=`
the smooth quadratic on `(s,σ)` — (ii) `baxter_factorization_inner` + `linarith`; then `rw [← hval]` +
`.sub` of the two derivatives.  Supporting: `q0PolyDeriv_of_lt`, `q0PolyDeriv_eq_zero_of_ge`,
`q0PolyDeriv_q0_poly_iintegr` (integrability via bounded-measurable + `integrableOn_of_bounded`).
**⇒ the entire N=1 leg of the unequal-diameter shell-inverse route is now closed to the Baxter ODE and
that ODE is proved** — the only open item on this route is the general-N Lebowitz mixture `c_HS`.

**✅ GENERAL-N MIXTURE `c_HS` — CORRECT OBJECT PACKAGED (2026-08-10, std-3, build 8761).**  Honest
state after investigation: there is **no large unproven closed form left** on this route.  The
equal-diameter case is proved (`matBaxterUQmSymFullExt_eq_rcHS_of_equalDiam` = `r·c_HS`), the
unequal-diameter WT-identity LHS is already **fully explicit in the constructed `Ψouter`**
(`matBaxterUQmSymFullExt_fully_explicit_intermediateLead_outer` + `renewalForm_eq_outer`, both
proven), and the remaining unequal-diameter **numerical value is the classical Lebowitz result**,
which the seed-free `matOzStar_unique` (kept axiom MA.15 only) route makes unnecessary for MML.8.  New: **`cHSmixRenewal`**
(`MixtureCorrectedSeed.lean`) `:= matBaxterUQmSymFullExt Psi Q i j r / r` — the CORRECT general-N
mixture DCF (the renewal-seed shell inverse), replacing the DISPROVED odd-extraction
`MixtureHSDCF.c_HS_mix` (degenerate diagonal `c_HS_mix_diag_eq_zero`; not even symmetric for unequal
diameters).  Proved std-3: **`cHSmixRenewal_eq_cHS_of_equalDiam`** (at equal diameters = scalar
`c_HS(η)`, grounded in `baxter_core_seed`) and **`cHSmixRenewal_zero_outer`** (vanishes for
`r ≥ σ−λ`, supported in the core).  ⚠ The explicit UNEQUAL-diameter Lebowitz value is **deliberately
not fabricated** — it stays the acknowledged open numerical residual routed around by
`matOzStar_unique`.

**✅ N=1 PHYSICAL REDUCTION of `cHSmixRenewal` (2026-08-10, std-3, build 8762).**
**`cHSmixRenewal_physMixN_fin1`** (`MixtureHSDCFFin1.lean`): for the PHYSICAL one-component mixture
`physMixN` (Baxter factor `Q i j := ρ₀·q0MixEntry(physMixN) 0 0`) and ANY renewal solution `Psi`
satisfying the standard outer/core hypotheses (`hUouter`, `hint`, `hcore`), `cHSmixRenewal Psi Q i j r
= c_HS (etaMix) (σ₀) r`.  The **entire Q-side** of `cHSmixRenewal_eq_cHS_of_equalDiam` is discharged
from the physical `q0MixEntry`: `hQsupp` (support ⊆ `[λ,R]=[0,σ₀]` via `q0MixEntry_support_subset`),
`hsym` (`Fin 1` subsingleton, `rfl`), `hrow` (row-sum = scalar `q0_poly` via
`q0MixEntry_physMixN_fin1_core` + `Fin.sum_univ_one`), `hQ0`/`hQ1` (via
`q0MixEntry_intervalIntegrable` / `_mul_id_` `.const_mul ρ₀`, the latter with an `EqOn` `.congr`).
Only the renewal `Psi` conditions remain — the OZ solution the project builds via `matBaxterPsi` and
routes around via `matOzStar_unique` (NOT fabricated).  So the physical N=1 Baxter factor plugs
correctly into the general-N renewal-seed mixture DCF, recovering the scalar `c_HS`.

**✅ `hcore` CONSTRUCTED (2026-08-10, std-3, build 8762).**  **`cHSmixRenewal_physMixN_fin1_ofOuter`**
(`MixtureHSDCFFin1.lean`): instantiating the renewal solution as the glued
`matBaxterPsi Ψouter (fun _ _ v => −v) σ₀` — i.e. taking the physical core `Ψcore = −v` — the `hcore`
hypothesis is discharged OUTRIGHT by `matBaxterPsi_core` (the definitional core branch `matBaxterPsi
= Ψcore` on `(−σ,σ)`).  So the physical N=1 reduction now needs ONLY the two renewal-EQUATION
conditions on the outer solution `Ψouter` (`hUouter`: `matBaxterU = 0` on `[σ,∞)`; `hint`:
integrability of the seed integrand) — the core `Ψ = −v` is no longer a free assumption.  Remaining
open: `hUouter` + `hint`, which pin `Ψouter` to the OZ renewal (Volterra) solution — the part the
seed-free `matOzStar_unique` route (kept axiom MA.15 only) makes unnecessary for MML.8.

**✅ `hUouter` CONSTRUCTED (2026-08-10, std-3, build 8762).**  **`physN1_hUouter`**
(`MixtureHSDCFFin1.lean`) — instantiating `Ψouter` as the **Banach–Volterra renewal solution**
`matBaxterPsiOuterFun σ₀ (physN1Qm) (physN1Fm)` (the `1×1` continuous `q0_poly` kernel `physN1Qm` and
core-convolution forcing `physN1Fm = baxterForcing`), the outer-vanishing `matBaxterU = 0` on
`[σ₀,∞)` holds for the physical truncated Baxter factor.  `matBaxterPsi_hUouter` supplies it for the
continuous `q0_poly` kernel — `hQsupp` from `q0_poly_eq_zero_of_ge`, `hforcing` from the
`baxterForcing` def (`Fin.sum_univ_one`), the renewal from `matBaxterPsiOuter_matRenewalEq` (global
Banach Volterra) — and a **kernel bridge** (`integral_congr` over `[0,σ₀]`, where
`ρ₀·q0MixEntry(physMixN) 0 0 = q0_poly` by `q0MixEntry_physMixN_fin1_core`) carries it from the
continuous kernel to the truncated DCF factor — the truncation matters only off `[0,σ₀]`, which
`matBaxterU`'s `∫₀^σ` never samples.  Supporting: `physN1Qm`/`physN1Fm` (defs), `physN1Qm_continuous`
/`physN1Fm_continuous` (`continuous_matrix` + `q0_poly_continuous`/`baxterForcing_continuous`).  **⇒
the physical N=1 renewal `Ψ` now has BOTH its core (`hcore`, `matBaxterPsi_core`) and its
outer-equation (`hUouter`) discharged from the CONSTRUCTED Volterra solution; only `hint`
(integrability, `matBaxterU_hint_of_regular`) remains to make the N=1 reduction unconditional.**

**✅✅ N=1 PHYSICAL REDUCTION NOW UNCONDITIONAL (2026-08-10, std-3, build 8762).**  `hint` discharged
(**`physN1_hint`**, `MixtureHSDCFFin1.lean`) exactly like `hUouter`: `matBaxterPsi_hint` gives
interval-integrability of the seed integrand for the continuous `q0_poly` kernel (via
`matBaxterPsi_entry_measurable`/`_bddOn` + `matBaxterU_hint_of_regular`), and the reusable
**`matBaxterU_kernel_congr`** (`matBaxterU` only samples its kernel via `∫₀^σ`) + `IntervalIntegrable.congr`
carry it to the truncated `ρ₀·q0MixEntry` (= `q0_poly` on `[0,σ₀]`).  Capstone
**`cHSmixRenewal_physMixN_fin1_uncond`**: with `Ψ` the fully-constructed glued renewal
`matBaxterPsi (Banach–Volterra Ψouter) (−v) σ₀`, ALL three renewal hypotheses are discharged
(`hcore`=`matBaxterPsi_core`, `hUouter`=`physN1_hUouter`, `hint`=`physN1_hint`), so
`cHSmixRenewal Ψ (ρ₀·q0MixEntry(physMixN)) i j r = c_HS (etaMix) (σ₀) r` with **NO remaining
assumptions on `Ψ`**.  So the physical one-component renewal-seed mixture DCF is proved, outright, to
equal the scalar PY `c_HS` — the general-N object correctly specializes at one component, unconditionally.

**✅ N=2 UNEQUAL-DIAMETER `hUouter` + `hint` (2026-08-10, std-3, build 8762).**  The renewal
structural conditions now hold at N=2 unequal diameters for the CONSTRUCTED renewal.  Key: use the
**continuous** mixture Baxter polynomial **`q0MixPoly X i j r := Q0ᵢⱼ·(min r Rᵢⱼ − Rᵢⱼ) +
Qppⱼ·(min r Rᵢⱼ − Rᵢⱼ)²/2`** (`MixtureHSDCFFin1.lean`) as the Banach–Volterra kernel — continuous by
construction (the `min` clamp; `q0MixPoly_continuous` by `fun_prop`), `= q0MixEntry` on `[λᵢⱼ,Rᵢⱼ]`,
extending the polynomial continuously below `λᵢⱼ` (where the truncated `q0MixEntry` JUMPS for unequal
diameters — the reason the N=1 `q0_poly` bridge does not transfer).  New general infrastructure:
**`matForcingCore`** (the core-convolution forcing `∑ₖ∫₀^σ Qm(r−s)ᵢₖ·(−s)` for any kernel) +
**`matForcingCore_continuous`** (parametric-integral continuity, generalizing `baxterForcing`, via
`continuous_parametric_intervalIntegral_of_continuous'` + `Continuous.matrix_elem`).  Then, for ANY
`Mix` with `σ` bounding every `Rᵢⱼ`: **`q0MixPoly_hUouter`** (`matBaxterPsi_hUouter`, `hQsupp` =
`q0MixPoly_eq_zero_of_ge`, `hforcing` = `matForcingCore` def) and **`q0MixPoly_hint`**
(`matBaxterPsi_hint`).  Concrete N=2 corollaries **`physMix_hUouter`**/**`physMix_hint`** for the
binary `physMix` at `σ = max(σ₀,σ₁)` (edge bound `Rᵢⱼ = (σᵢ+σⱼ)/2 ≤ max` by `fin_cases`).  ⚠ These
are for the CONTINUOUS `q0MixPoly` renewal kernel — the structural renewal solvability +
integrability at N=2 unequal diameters; the relation to the truncated `q0MixEntry` DCF factor for
unequal diameters is the windowing-loss handled by the EXTENDED seed (`matBaxterUExt`, `∫_ℝ`), and
the unequal-diameter DCF VALUE stays the open Lebowitz residual.

**✅ WINDOWING-LOSS BRIDGE (2026-08-10, std-3, build 8762).**  The extended (`∫_ℝ`) vs windowed
(`∫₀^σ`) first Baxter convolution difference is made PRECISE and discharged where it vanishes.
**`q0MixEntry_subZeroTail_zero`** (`MixtureHSDCFFin1.lean`): the sub-zero tail
`∫_{≤0} q0MixEntry X i k·f = 0` when `λᵢₖ ≥ 0` (support `⊆ [λᵢₖ,Rᵢₖ]` vanishes for `t<0`; `{0}` null,
via `setIntegral_congr_ae` + `ae_ne`).  **`q0MixEntry_intSplit`**: the additivity `∫_ℝ q0MixEntry·g =
∫₀^σ + ∫_{≤0}` for the compactly-supported kernel (`integral_add_compl` at `Iic 0`; the `(σ,∞)` piece
`= 0` past `Rᵢₖ ≤ σ`; `setIntegral_union` on `Ioi 0 = Ioc 0 σ ∪ Ioi σ`), resting only on
integrability.  **⭐ `matBaxterUExt_eq_matBaxterU_of_row_lam_nonneg`**: on a row `i` whose species is
the SMALLEST (`λᵢₖ ≥ 0` ∀k, i.e. `σᵢ ≤ σₖ`), `matBaxterUExt = matBaxterU` OUTRIGHT — **no windowing
loss** — via `matBaxterUExt_eq_matBaxterU_sub_tail` (the tail split) + `Finset.sum_eq_zero` over the
vanishing sub-zero tails, resting only on interval-integrability of each `q0MixEntry·Ψ`.  ⚠ Honest
scope: for LARGER species some `λᵢₖ < 0` and the sub-zero tail is a genuine `[λᵢₖ,0)` contribution —
NOT fabricated away; that non-vanishing tail is precisely the extended seed's raison d'être and the
unequal-diameter content.  So the bridge is proved exactly where the windowing loss is absent, and
the loss is pinned to the `σᵢ > σₖ` pairs where it persists.

**✅ LARGER-SPECIES SUB-ZERO TAIL — MADE EXPLICIT (2026-08-10, std-3, build 8762).**  The non-vanishing
tail (for `λᵢₖ < 0`) is now a concrete polynomial moment, not just "nonzero".
**`q0MixEntry_intIic_lam_eq_zero`**: `∫_{≤λᵢₖ} q0MixEntry·g = 0` (below the support).
**`q0MixEntry_subZeroTail_compact`**: for `λᵢₖ ≤ 0`, `∫_{≤0} q0MixEntry·g = ∫_{λᵢₖ}^0 q0MixEntry·g` —
the tail COLLAPSES to a compact interval (`Iic 0 = Iic λ ∪ Ioc λ 0` via `Iic_union_Ioc_eq_Iic` +
`setIntegral_union`, the `Iic λ` piece killed).  **`q0MixEntry_inner_expand`**: on `[λᵢₖ,Rᵢₖ]` the
kernel is the bare Lebowitz quadratic (`indicator_of_mem`).  **⭐ `q0MixEntry_subZeroTail_poly`**: the
tail `= ∫_{λᵢₖ}^0 (Q0ᵢₖ·(t−Rᵢₖ) + Qppₖ·(t−Rᵢₖ)²/2)·g(t) dt` — the explicit polynomial moment.  **⭐⭐
`matBaxterUExt_eq_matBaxterU_sub_polyTail`** (DUAL of the smallest-species bridge): on the LARGEST
species row (`λᵢₖ ≤ 0` ∀k, `σᵢ ≥ σₖ`), `matBaxterUExt = matBaxterU − ∑ₖ ∫_{λᵢₖ}^0 (Lebowitz
quadratic)·Ψₖⱼ(r−t)` — the exact windowing loss as a sum of polynomial moments (diagonal `k=i` empty,
`λᵢᵢ=0`; only smaller partners contribute).  **⇒ the binary mixture is fully characterized: smallest
species → NO loss (`…_of_row_lam_nonneg`); largest species → EXPLICIT polynomial-moment loss.**  The
unequal-diameter windowing loss is now pinned to concrete `[λᵢₖ,0)` Lebowitz-quadratic moments — the
DCF VALUE they sum to is the still-open Lebowitz residual, but its STRUCTURE is fully explicit.

**✅ `hint` PHYSICAL INTEGRABILITY DISCHARGED (2026-08-10, std-3, build 8762) — the windowing-loss
bridges are now `hint`-free.**  **`q0MixEntry_mul_integrable`** (`MixtureHSDCFFin1.lean`): the general
full-line integrability of `q0MixEntry X i k · g` for any measurable `g` bounded on the support
`[λᵢₖ,Rᵢₖ]` — via `integrableOn_iff_integrable_of_support_subset` (compact support from
`q0MixEntry_support_subset`) + `Measure.integrableOn_of_bounded` (finite-measure `Icc`,
`q0MixEntry_abs_le` × `g`-bound, `q0MixEntry_measurable`).  **`q0MixEntry_matBaxterPsi_integrable`**:
the `hint` DISCHARGED for the constructed renewal — `matBaxterPsi Po Pc σ k j (r−·)` is measurable
(`matBaxterPsi_entry_measurable` ∘ `(r−·)`) and bounded on the compact `r−[λᵢₖ,Rᵢₖ]`
(`matBaxterPsi_entry_bddOn`), so the seed integrand is integrable.  **⭐⭐
`matBaxterUExt_eq_matBaxterU_smallest_of_cont`** / **`matBaxterUExt_sub_polyTail_of_cont`**: both
windowing-loss bridges restated with the integrability side-condition ELIMINATED — for `Ψ =
matBaxterPsi Po Pc σ` with CONTINUOUS `Po,Pc` (exactly the constructed Banach–Volterra renewal, whose
`Ψouter = matBaxterPsiOuterFun` is continuous and core `= −v` is continuous), the smallest-species
bridge (no loss) and largest-species bridge (explicit polynomial-moment loss) hold with NO remaining
integrability hypothesis.  **⇒ the windowing-loss bridges now need only continuity of the renewal
data, which the constructed renewal supplies — the integrability plumbing is fully discharged.**

**✅✅ N=2 PHYSICAL INSTANTIATION at σ = max diameter (2026-08-10, std-3, build 8762) — the binary
windowing loss, fully assembled.**  **`physMixPsiouter`** (`MixtureHSDCFFin1.lean`): the constructed
Banach–Volterra outer renewal for the physical binary mixture at seed scale `σ = max(σ₀,σ₁)` (from the
continuous `q0MixPolyMat` kernel + `matForcingCore`), with **`physMixPsiouter_continuous`** (its
entries continuous via `matBaxterPsiOuterFun_continuous.matrix_elem`) and **`physMix_R_le_max`**
(`Rᵢₖ = (σᵢ+σₖ)/2 ≤ max` by `fin_cases`).  **⭐⭐⭐ `physMix_windowing_smallest`**: on the SMALLEST
species row (`σᵢ ≤ σₖ ∀k`), `matBaxterUExt = matBaxterU` — NO windowing loss — fully instantiated (the
`hlam` from `Mix.lam = (σₖ−σᵢ)/2 ≥ 0`, continuity/`hRσ`/integrability all discharged).  **⭐⭐⭐
`physMix_windowing_largest`**: on the LARGEST species row (`σₖ ≤ σᵢ ∀k`), `matBaxterUExt = matBaxterU −
∑ₖ ∫_{λᵢₖ}^0 (Q0ᵢₖ·(t−Rᵢₖ) + Qppₖ·(t−Rᵢₖ)²/2)·matBaxterPsi(…)ₖⱼ(r−t)` — the EXPLICIT unequal-diameter
windowing loss for the constructed physical renewal, with every side condition discharged.  **⇒ the
binary-mixture windowing loss is now a fully-assembled, side-condition-free physical theorem: both
species rows, at the physical seed scale `σ = max diameter`, with the constructed renewal.  The only
thing still un-fabricated is the classical Lebowitz VALUE the largest-species polynomial moments sum
to (routed around by `matOzStar_unique`).**

**✅ LARGEST-SPECIES LEBOWITZ VALUE — NUMERICALLY VERIFIED (2026-08-11, `mixwt_windowing_largest_check.py`).**
For binary mixtures σ={1.0/0.9, 1.0/0.6, 1.2/0.7} with the constructed renewal `Ψ` (renewal Picard =
`matBaxterPsi`) and the truncated `q0MixEntry` Baxter factor, three checks: **(1)** the exact Lean
decomposition `matBaxterUExt = matBaxterU − ∑ₖ ∫_{λᵢₖ}^0 (Q0ᵢₖ(t−Rᵢₖ)+Qppₖ(t−Rᵢₖ)²/2)·Ψₖⱼ(r−t)`
(`physMix_windowing_largest`) holds to **grid precision** (residual 4.6e-6 / 1.6e-6 / 1.1e-5) — the
identity is exact, as the Lean proves; **(2)** the sub-zero polynomial-moment tail is **genuinely
nonzero** on the LARGEST-species row (‖tail‖ ~ 1.0e-2…2.8e-2) and **exactly `0`** on the smallest
(confirming `physMix_windowing_smallest`) — the windowing loss is real, unequal-diameter-only content;
**(3)** the largest-species EXTENDED seed (transposed `matBaxterUtExt`, the value arm) reproduces the
classical **Lebowitz `r·c_ij`** to **<1e-3** (2.4e-4 / 9.7e-5 / 6.5e-4).  ⇒ the explicit Lebowitz-
quadratic moments the Lean makes explicit are exactly what carry the extended seed onto the classical
Lebowitz mixture `c_HS` value — the DCF value the Lean deliberately does not fabricate but which is
numerically confirmed to be reproduced by the constructed renewal (claim A to ~1e-10 via Picard).

**✅ TRANSPOSED SEED ARM `matBaxterUtExt` — WINDOWING LOSS (2026-08-11, std-3, build 8762) — the DUAL.**
The seed `matBaxterUQmSymFullExt` uses the TRANSPOSED arm `matBaxterUtExt` (kernel `Qₖᵢ`); its
windowing loss mirrors the un-transposed arm.  Since `matBaxterUtExt Psi Q = matBaxterUExt Psi Qᵀ` and
`matBaxterUt Psi Q σ = matBaxterU Psi Qᵀ σ` (both `rfl`, `MixtureCorrectedSeed`), the transposed loss
uses `q0MixEntry X k i` (transposed indices, `λₖᵢ = (σᵢ−σₖ)/2`) — so the ROLES SWAP: the transposed
arm VANISHES on the LARGEST species (`λₖᵢ ≥ 0`) and carries the explicit tail on the SMALLEST.
**`matBaxterUtExt_eq_matBaxterUt_of_row`** (largest, no loss) / **`…_sub_polyTail`** (smallest, explicit
`∑ₖ ∫_{λₖᵢ}^0 (Q0ₖᵢ(t−Rₖᵢ)+Qppᵢ(t−Rₖᵢ)²/2)·Ψₖⱼ(r−t)`) — both via the two `…_eq_transpose` rfls +
`matBaxterUExt_eq_matBaxterU_sub_tail` + `q0MixEntry_subZeroTail_{zero,poly}` at the (k,i) entry.
Hint-free (**`q0MixEntry_matBaxterPsi_integrable_gen`**, DECOUPLED indices since the transposed
`q0MixEntry` second index ≠ `Ψ` first index): **`matBaxterUtExt_eq_matBaxterUt_of_cont`** /
**`matBaxterUtExt_sub_polyTail_of_cont`**.  Physical σ=max: **`physMix_windowing_t_largest`** (no loss)
/ **`physMix_windowing_t_smallest`** (explicit loss).  **⇒ BOTH seed arms are now fully characterized:
un-transposed `matBaxterUExt` (largest→loss, smallest→none) and transposed `matBaxterUtExt`
(largest→none, smallest→loss) — the complete windowing-loss picture for the binary mixture.**  The
numerically-verified value arm is the transposed `matBaxterUtExt` (smallest-species explicit tail).

**✅ TRANSPOSED-ARM LEBOWITZ VALUE — NUMERICALLY VERIFIED (2026-08-11, `mixwt_windowing_transposed_check.py`).**
Dual of the un-transposed numerical check, for σ={1.0/0.9, 1.0/0.6, 1.2/0.7} with the constructed
renewal: **(1)** the exact Lean transposed decomposition `matBaxterUtExt = matBaxterUt −
∑ₘ ∫_{λₘᵢ}^0 (Q0ₘᵢ(t−Rₘᵢ)+Qppᵢ(t−Rₘᵢ)²/2)·Ψₘⱼ(r−t)` (`physMix_windowing_t_smallest`) holds to grid
precision (5.0e-6 / 1.1e-6 / 5.9e-6); **(2)** ROLE SWAP CONFIRMED — the transposed sub-zero tail is
NONZERO on the SMALLEST species (3.4e-3…2.75e-2) and EXACTLY `0` on the LARGEST
(`physMix_windowing_t_largest`), the exact dual of the un-transposed arm; **(3)** the smallest-species
transposed EXTENDED seed (`matBaxterUtExt`, the SEED's leading arm) reproduces the classical
**Lebowitz `r·c_ij`** to **<1e-3** (2.6e-4 / 5.9e-5 / 3.0e-4).  **⇒ BOTH seed arms are now numerically
confirmed against the Lean structure**: the transposed `matBaxterUtExt` is the value-carrying arm, and
its smallest-species windowing loss — the explicit Lebowitz-quadratic moments the Lean makes explicit
— is exactly what the classical Lebowitz mixture `c_HS` value depends on.

**✅ SUM OF THE TWO ARMS' WINDOWING LOSSES — NUMERICALLY VERIFIED (2026-08-11,
`mixwt_windowing_bootharms_check.py`).**  By linearity, `L_un(i,j) + L_t(i,j) = ∑ₖ ∫_{≤0} (Q_ik + Q_ki)·Ψ_kj`
— the sub-zero tail of the **SYMMETRIZED** Baxter kernel `Q + Qᵀ`, i.e. the un-reflected part of the
DCF fold kernel `Ĉ₀_ij = Q_ij(v) + Q_ji(−v) − matCorr` that the symmetric DCF `r·c` is built from.
For σ={1.0/0.9, 1.0/0.6, 1.2/0.7}: **(1)** `L_un + L_t == sym-kernel sub-zero tail` to grid precision
(1.4e-5 / 6.6e-6 / 1.9e-5); **(2)** BOTH species rows carry part of the loss — the un-transposed arm on
the LARGEST row (‖L_un‖~1e-2, ‖L_t‖~1e-6≈0), the transposed arm on the SMALLEST (‖L_un‖~0,
‖L_t‖~1e-2) — so the two complementary arms together cover EVERY row (neither alone does); **(3)** the
full both-arm extended seed reproduces `r·c` (Lebowitz) to <1e-3 (2.6e-4 / 7.4e-5 / 6.5e-4).  **⇒ the
windowing-loss picture is now complete and self-consistent: the two seed arms are complementary
(each covers one species), their SUM is the natural symmetric object (the fold-kernel `Ĉ₀` windowing
loss), and that symmetric loss is exactly what the classical Lebowitz mixture `c_HS` value is built
from — the DCF value the Lean deliberately does not fabricate, structure fully proved + verified.**

**✅ SYMMETRIC-KERNEL WINDOWING LOSS — FORMALIZED IN LEAN (2026-08-11, std-3, build 8762).**  The
both-arms sum (previously only numerical) is now proved: **`windowing_loss_sum_eq_symTail`**
(`MixtureHSDCFFin1.lean`) — `(matBaxterU − matBaxterUExt) + (matBaxterUt − matBaxterUtExt) = ∑ₖ ∫_{≤0}
(q0MixEntry X i k + q0MixEntry X k i)·Ψₖⱼ`, on ANY row (raw `∫_{Iic 0}` form, via the general
`matBaxterUExt_eq_matBaxterU_sub_tail` + the two `_eq_transpose` rfls + `integral_add`).  Hint-free
**`windowing_loss_sum_eq_symTail_of_cont`** (continuous `Po,Pc`), physical
**`physMix_windowing_sum`** (binary mixture, σ=max, both rows).  So the fold-kernel `Ĉ₀` windowing
loss (sum of the two arms = symmetrized-kernel sub-zero tail) is now a proved Lean theorem, matching
the numerical `mixwt_windowing_bootharms_check.py`.  *(Note: the bloated `todo_lean.md` MML.8 cell was
split — this whole mixture-`c_HS`/windowing-loss thread now lives under the concise `MIXCHS` task row +
this file + memory `project_matrix_ozstar_assembled.md`.)*

**✅ GENERAL-N (N≥3) physical windowing sum (2026-08-11, std-3, build 8762).**  `windowing_loss_sum_eq_symTail`
is already any-`N`; the physical instantiation is generalized from `Fin 2` to any `N`:
**`physMixN_windowing_sum`** (`MixtureHSDCFFin1.lean`) — for the general-N physical mixture `physMixN`
with the constructed renewal at a seed scale `sigmax` bounding every diameter (`physMixNPsiouter`,
`physMixN_R_le`), the two-arm loss sum = the symmetrized-kernel sub-zero tail, on ANY row.  Numerics
(`mixwt_windowing_genN_check.py`, N=3 ternary + N=4 quaternary): the identity holds to grid precision
(6e-6…2e-5), and — the N≥3-specific point — the MIDDLE species carries BOTH arms (e.g. N=3 row 1:
|L_un|=1.9e-3 from smaller partners, |L_t|=2.1e-3 from larger), unlike N=2 where each row had only
one.  *(todo `MIXCHS` reorganized into a proper HSMix task GROUP — no Yukawa-tail dependence.)*

**Two routes + the dead end.** The **non-circular value route** `matOzStar_unique`
(`MixtureRDFUniqueness.lean`) discharges MML.8 **seed-free / pole-free** (no seed, no pole
enumeration) from `det Q̂₀ ≠ 0` (`mixtureDet_pole_free_N` + `pyhs_mixture_no_spinodal`) — **std-3
except for the one committed kept axiom MA.15 `matRadialShell_bounded_injective`, NOT axiom-free**.
The literal
pole-series route is provably BLOCKED (`even_subfamily_not_exhaustive`, `MixturePoleExhaustion.lean`:
`MZERO.1` infinitude ≠ pole-exhaustion), so `MixRDFInnerCollapse` stays a `Prop`.

**Net.** Every structural step std-3; equal-diameter WT identity proved; unequal-diameter WT
identity numerically confirmed with its `Ψouter` coupling pinned to a constructed object; MML.8
discharged (seed-free / pole-free, resting on the one kept axiom MA.15
`matRadialShell_bounded_injective`) by `matOzStar_unique` regardless.  The detailed ✅ log follows
below.

**Non-circular value route — consolidated status (2026-08-08, `MixtureRDFUniqueness.lean`).**  The
canonical in-code summary is the `## The non-circular value route to MML.8` section at the end of
`MixtureRDFUniqueness.lean`.  Status: (a) **assembled** — `matOzStar_unique` gives RDF uniqueness
unconditionally, given `MatSymbolCoercive` + regularity, resting only on the committed WH axiom MA.15
(`matRadialShell_bounded_injective`); (b) **equal diameters FULLY CLOSED** — `matOzStar_equalDiam_unique`
(RDF = density-weighted single-component `baxterPsi`), coercivity `matSymbolCoercive_equalDiam` via the
rank-1 reduction `Φᵢⱼ = uᵢuⱼ·c_HS` to the proved scalar `one_sub_rho_radial_fourier_c_HS_coercive`;
(c) **general N — ONE input remaining**, the uniform coercivity `I − ρĈ(k) ⪰ εI`, whose POINTWISE part is
`det Q̂₀ ≠ 0` (`Cmix0_factorization` `T₀ = Q̂₀(k)Q̂₀(−k)ᵀ` + `matStructureFactor_isUnit_of_det_ne_zero`, from
`mixtureDet_pole_free_N` + `pyhs_mixture_no_spinodal`), leaving only the uniform `ε` (a `k`-compactness
argument).  So this route needs no seed, no WT identity, no pole-exhaustion; its only axioms are MA.15 +
the physics no-spinodal — the same footing as the scalar `oz_fixed_pt_unique`.

**✅ General-N uniform coercivity — compactness gluing DISCHARGED (2026-08-08,
`MixtureCoercivityReduction.lean`, std-3, build 8601).**  The uniform `ε` of the general-N
`MatSymbolCoercive` is no longer an open analytic gap — its `k`-compactness "gluing" is now proved
abstractly:
- **`matSymbolCoercive_of_sphere`** — homogeneity: a uniform lower bound of the symbol quadratic form
  `F(k,u) = ∑ᵢuᵢ² − ρ∑ᵢⱼ Ĉ(k)ᵢⱼuᵢuⱼ` on the L²-unit sphere `∑uᵢ²=1` upgrades to full `MatSymbolCoercive`
  (`ε∑vᵢ² ≤ F(k,v)`), since `F` is degree-2 homogeneous in `v`.
- **`sphere_isCompact`** — the L²-unit sphere in `Fin N → ℝ` is compact (closed+bounded, finite dim).
- **`matSymbolCoercive_of_regions`** — the three-region compactness: from uniform sphere bounds in the
  near-`0` (`|k|≤a`) and tail (`b≤|k|`) regions, plus symbol continuity and pointwise positivity on the
  compact middle `a≤|k|≤b`, the middle gives a positive min (`IsCompact.exists_isMinOn`) and
  `matSymbolCoercive_of_sphere` lifts it — so `MatSymbolCoercive` follows.

**⇒ the general-N coercivity now reduces to exactly the three CONCRETE symbol facts** (matrix analogs of
the scalar `one_sub_rho_radial_fourier_c_HS_coercive`'s three regions): near-`0` sign, middle continuity
+ pointwise `det Q̂₀ ≠ 0` positivity (from `mixtureDet_pole_free_N` + `pyhs_mixture_no_spinodal`), and
tail `Ĉ → 0` decay.  The abstract analytic obstruction (the 2-variable `k`×sphere compactness) is
formalized; only the three concrete per-region bounds for the mixture DCF symbol remain — each a
bounded, isolated matrix analog of a scalar-proved fact.

**✅ Middle pointwise positivity from `det Q̂₀ ≠ 0` (2026-08-08, `MixtureCoercivityReduction.lean`,
std-3, build 8601).**  The second of the three concrete inputs — the middle-region pointwise positivity
`uᵀ(I − ρĈ(k))u > 0` — is now discharged from `det Q̂₀ ≠ 0`:
- **`matSymbol_pos_of_factor`** — the algebraic core: if the symbol quadratic form factors as a squared
  norm `∑ᵢuᵢ² − ρ∑ᵢⱼĈ(k)ᵢⱼuᵢuⱼ = ∑ₗ|(B·u)ₗ|²` through an invertible complex `B` (`B = Q̂₀(−k)ᵀ` on the
  real axis via `Cmix0_factorization`), it is `> 0` on the L²-unit sphere — `B·u ≠ 0` (from `det B ≠ 0`,
  via `Matrix.nonsing_inv_mul`/`mulVec` injectivity) forces a strictly-positive term.
- **`matSymbol_middle_pos`** — packaged as the exact `hpos` hypothesis of `matSymbolCoercive_of_regions`:
  a per-`k` factorization with `det B(k) ≠ 0` (`= det Q̂₀(−k)`, from `pyhs_mixture_no_spinodal` +
  `mixtureDet_pole_free_N`) yields the middle positivity for all `k` in `[a,b]∪[−b,−a]`.

So the middle input is reduced to the factorization identity (`hfac`: `uᵀ(I−ρĈ)u = ‖Q̂₀(−k)ᵀu‖²`, the
concrete `Cmix0_factorization` bridge) + `det Q̂₀ ≠ 0` (already unconditional).  Of the three concrete
coercivity inputs, the middle positivity is now the PD-from-invertible-factorization done; the remaining
two are the near-`0` sign bound and the tail `Ĉ → 0` decay (each a scalar-proved-fact matrix analog).

**✅ Tail `Ĉ → 0` decay bound (2026-08-08, `MixtureCoercivityReduction.lean`, std-3, build 8601).**  The
third of the three concrete inputs — the tail region `b ≤ |k|` — is now discharged from the DCF's
`Ĉ(k) → 0` decay.  **`matSymbol_tail_bound`**: a uniform entry bound `|Ĉ(k)ᵢⱼ| ≤ M` on `b ≤ |k|` with
`ρMN < 1` gives `htail` of `matSymbolCoercive_of_regions` with `δ = 1 − ρMN > 0`, by Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`): `∑ᵢⱼĈᵢⱼuᵢuⱼ ≤ M(∑ᵢ|uᵢ|)² ≤ MN∑ᵢuᵢ² = MN` on the L²-unit sphere, so
`∑ᵢuᵢ² − ρ∑ᵢⱼĈᵢⱼuᵢuⱼ ≥ 1 − ρMN`.  This is the matrix analog of the scalar `radial_fourier_c_HS_le`
(`|Ĉ(k)| ≤ cHS_bound/k²`), and it reduces the tail input to a uniform entry decay bound for the mixture
DCF symbol.

**⇒ Two of the three concrete coercivity inputs are now structured** (middle positivity from
`det Q̂₀ ≠ 0`; tail from `Ĉ → 0` decay), each reduced to an isolated symbol fact.  Together with the
abstract compactness gluing (`matSymbolCoercive_of_regions`) and the equal-diameter closure, the ONLY
remaining piece of the general-N value route is the near-`0` sign bound (`vᵀĈ(k)v ≤ 0` near `k = 0`, the
matrix analog of the scalar's `c_HS < 0`, `sin(kr) ≥ 0` argument).

**✅ Near-`0` sign bound — ALL THREE coercivity inputs now reduced (2026-08-08,
`MixtureCoercivityReduction.lean`, std-3, build 8601).**  The last of the three concrete inputs — the near-`0`
region — is now discharged from the sign argument:
- **`matRadialSymbol_neg`** — the symbol is even in `k` (`sin` odd, `1/k` odd).
- **`matSymbol_near_bound`** — if the real-space DCF quadratic form `g(r) = ∑ᵢⱼΦᵢⱼ(r)uᵢuⱼ` is `≤ 0` on the
  core `(0,σ)` (matrix analog of `c_HS < 0`) and `0` outside, then `∑ᵢⱼĈ(k)ᵢⱼuᵢuⱼ ≤ 0` for `|k| ≤ π/σ`, so
  `hnear` holds with `ε₀ = 1`.  Cases: `0 < k ≤ π/σ` — `∑ᵢⱼĈᵢⱼuᵢuⱼ = (4π/k)∫₀^∞ r·g(r)·sin(kr) ≤ 0`
  (`setIntegral_nonpos`: integrand `≤ 0` since `r>0`, `g≤0`, `sin(kr) ≥ 0` from `kr ≤ π`); `k=0` — the
  `4π/k` junk value gives `0`; `k<0` — evenness.

So **all three concrete coercivity inputs are now reduced to isolated DCF-symbol facts**: near-`0` ← the
real-space DCF being NSD in the core; middle ← `Cmix0_factorization` + `det Q̂₀ ≠ 0`; tail ← `Ĉ → 0` decay.
Combined with the abstract `k`×sphere compactness gluing (`matSymbolCoercive_of_regions`) and the fully-closed
equal-diameter case, the general-N non-circular value route to MML.8 now rests only on: (i) the committed WH
axiom MA.15, (ii) the physics no-spinodal (`det Q̂₀ ≠ 0`), and (iii) these three concrete per-region symbol
estimates for the mixture DCF — each a proved matrix analog of a scalar-established fact, with no abstract
analytic obstruction remaining.

**✅ Real-space DCF core-NSD — PROVED for equal diameters (2026-08-09, `MixtureCoercivityReduction.lean`,
std-3, build 8601).**  The near-`0` sign hypothesis `hNSD` (`∑ᵢⱼΦᵢⱼ(r)uᵢuⱼ ≤ 0` on the core) is itself
discharged for the equal-diameter forcing.  **`matDCF_coreNSD_equalDiam`**: for `Φᵢⱼ = √(ρᵢρⱼ)/ρ·c_HS`, the
core quadratic form is **rank-1** — `∑ᵢⱼΦᵢⱼ(r)uᵢuⱼ = (c_HS(r)/ρ)·(∑ᵢ√ρᵢuᵢ)²` (via `Real.sqrt_mul` +
`Finset.sum_mul_sum`) — so `c_HS(r) < 0` on `(0,σ)` (the proved scalar `c_HS_neg`) times the nonneg square
gives `≤ 0`.  So the near-`0` sign route (`matSymbol_near_bound`) has ALL its hypotheses discharged for the
equal-diameter mixture: the core-NSD is the `c_HS < 0` rank-1 fact.

**⇒ For equal diameters, every input of the general-N value route is now proved** (near-`0` sign via
`matDCF_coreNSD_equalDiam` + `matSymbol_near_bound`; middle via `det Q̂₀ ≠ 0`; tail via `Ĉ → 0`; the
compactness gluing; plus the direct rank-1 `matSymbolCoercive_equalDiam`).  For UNEQUAL diameters the
pointwise core sign (`∑ᵢⱼc_ij(r)uᵢuⱼ ≤ 0`) was thought to be the sole remaining estimate — **but it is
FALSE on the band `(σ_min, R₀₁)`; see the RETRACTED block immediately below.**  So the near-`0` reduction of
lines 123–134 (near-`0` ← real-space DCF NSD) is itself equal-diameter-specific and needs the correction
below; the middle and tail reductions are unaffected.

**❌ RETRACTED — the unequal-diameter DCF is NOT core-NSD (2026-08-09).**  An earlier claim in this file
("unequal-diameter mixture DCF core-NSD numerically confirmed", and "N=2 unequal PROVED modulo 3 per-`r`
facts") was **WRONG** and is retracted.  The three per-`r` inequalities (`Φ₀₀ ≤ 0`, `Φ₁₁ ≤ 0`,
`Φ₀₀Φ₁₁ ≥ Φ₀₁²`) are **FALSE** on the band `σ_min < r < R₀₁ = (σ₀+σ₁)/2`.  **Cause of the error:** the
numerical scan (`mixdcf_nsd_check.py`) ran only over `r ∈ (0, 0.95·σ_min)` with `σ_min = min_ij R_ij`, so
it never sampled the band.  **The refutation is rigorous, not merely numerical:** on the band the PY
like-pair DCF `Φ₀₀` has already vanished (its range is the like-contact `σ₀`) while the unlike-pair `Φ₀₁`
is still nonzero (range `R₀₁ = (σ₀+σ₁)/2 > σ₀`), so the `2×2` block is `[[0, Φ₀₁],[Φ₀₁, Φ₁₁]]` with
determinant `−Φ₀₁² < 0` — INDEFINITE, one strictly positive eigenvalue.  The corrected full-range scan
finds a robust `+0.1 … +0.26` positive eigenvalue on the band for **every** unequal case (N=2 and N=3);
equal diameters have `R₀₁ = σ`, an EMPTY band, and remain NSD.

**Lean refutation — `matSym_2x2_pos_of_zero_diag`** (`MixtureCoercivityReduction.lean`, std-3): a symmetric
`2×2` matrix with a zero diagonal entry and nonzero off-diagonal has `∃u, ∑ᵢⱼMᵢⱼuᵢuⱼ > 0`
(`u = ((1−M₁₁)/(2M₀₁), 1)` gives form `= 1`).  ⇒ the `hNSD` hypothesis of `matSymbol_near_bound` cannot
hold on the full core for unequal diameters.

**What survives.**
- `matNSD_2x2_of_det` (the `2×2` determinant NSD criterion) and `matDCF_coreNSD_N2_of_conditions` (its
  `hNSD`-shaped packaging) are still **valid conditional theorems** — they are correct; it is their
  *hypotheses* that are unmeetable on the band for unequal diameters.  Retained with corrected docstrings.
- `matDCF_coreNSD_equalDiam` (equal-diameter, all `N`, rank-1 `c_HS < 0`) is **correct and unaffected**
  (equal diameters have no band).
- The DCF matrix **is** NSD on `(0, σ_min)` (all diagonals still active), just not on the band.

**Consequence for the value route — the near-`0` region needs a different argument.**  The physics is
intact: `1 − ρĈ(k)` is coercive near `k = 0` for a stable mixture.  But the near-`0` *proof sub-strategy*
I built (`matSymbol_near_bound`: pointwise real-space DCF-NSD ⟹ `∑Ĉ(k)uu ≤ 0` for `|k| ≤ π/σ`) is
**EQUAL-DIAMETER-SPECIFIC** — for unequal diameters `Ĉ(k)` is not NSD near `0`.  The correct unequal-diameter
near-`0` argument is **continuity of the regular `1 − ρĈ(k)` at `k = 0` plus positive-definiteness at
`k = 0`** (thermodynamic stability, tied to `det Q̂₀ ≠ 0` at the origin via `det_Q0_contour_origin_ne_zero`,
which is already proved with no physics axiom) + compactness — i.e. the same `det Q̂₀ ≠ 0` machinery as the
middle region, extended through `k = 0` on the *regular* symbol rather than the (origin-singular) Baxter
factor.  The middle (`|k| ≥ a`, `det Q̂₀ ≠ 0`) and tail (`Ĉ → 0` decay) regions are unaffected.

**✅ Corrected near-`0` reduction — FORMALIZED (2026-08-09, `MixtureCoercivityReduction.lean`, std-3, full
build 8748).**  The open item above is now discharged; the pointwise-DCF-NSD `matSymbol_near_bound` is
replaced by a continuity+PD-at-`0` route valid for unequal diameters.  Two lemmas:
- **`matSymbol_near_of_continuous_pd`** — the near-`0` reduction.  `matRadialSymbol Φ k` jumps at `k = 0`
  (the `4π/k` junk value is `0`), but the true DCF transform has a continuous PD extension there.  Given a
  continuous regularizer `Csym` agreeing with the symbol off `0` (`hagree`), continuous on `[−a₀,a₀]`
  (`hcont`), and PD at `0` (`hpd0`: `∑uᵢ² − ρ∑Csym(0)uu ≥ ε₀` on the sphere), a **compactness argument**
  produces a neighborhood `|k| ≤ a` and `ε > 0` with the `hnear` bound of `matSymbolCoercive_of_regions`.
  Mechanism: the L²-sphere is compact ⇒ the sublevel set `Bad = {(k,u) : form ≤ ε₀/2}` is compact ⇒ its
  `k`-projection is a compact set missing `0` (PD-at-`0` gives `form(0,u) ≥ ε₀ > ε₀/2`), so it is bounded
  off `0` by a ball whose radius is the `a`.  At `k = 0` the junk value gives form `= 1 ≥ ε`; off `0`,
  `hagree` + continuity + PD-at-`0`.  std-3.
- **`matSymbolCoercive_of_regularNear`** — the capstone: assembles `MatSymbolCoercive` end-to-end from the
  corrected near-`0` (`matSymbol_near_of_continuous_pd`) + the UNCHANGED middle (`hpos_all`: pointwise
  positivity for every `k ≠ 0`, the `matSymbol_pos_of_factor`/`det Q̂₀ ≠ 0` fact) + tail (`htail`: `Ĉ → 0`).
  The near lemma supplies `a`; the middle runs on `[min a b, b]` and the tail on `|k| ≥ b`, covering the
  whole line via `matSymbolCoercive_of_regions`.  std-3.

So the near-`0` region no longer needs pointwise DCF-NSD: its concrete inputs are now (i) continuity of the
regular symbol through `0` and (ii) PD-at-`0` (thermodynamic stability), BOTH true for unequal diameters.

**✅ `hpd0` (PD-at-`0`) DISCHARGED from the Gram factorization — connectedness NOT needed (2026-08-09,
`MixtureCoercivityReduction.lean`, std-3, full build 8748).**  Correction to the previous plan: the
density-path connectedness argument is UNNECESSARY.  The Baxter factorization at the regularized `k = 0` is
already a **real Gram form** `1 − ρĈ(0) = B₀B₀ᵀ`, and any `AAᵀ` is automatically PSD — so PD follows the
moment `det B₀ ≠ 0`, exactly as in the middle region.  Three lemmas:
- **`quadForm_pos_of_gram_factor`** — the symbol-agnostic core of `matSymbol_pos_of_factor`: for ANY real
  `C`, a Gram factorization `∑uᵢ² − ρ∑Cuu = ∑ₗ|(B·u)ₗ|²` with `det B ≠ 0` gives `> 0` on the sphere.
- **`matSymbol_pd_at_zero_of_gram`** — produces `hpd0` from the `k = 0` Gram factor `B₀` + `det B₀ ≠ 0`:
  pointwise positivity (`quadForm_pos_of_gram_factor` at `C = Csym 0`) + a compact-sphere min gives the
  uniform `ε₀ > 0`.  No eigenvalue-path / connectedness.  The near-`0` analog of `matSymbol_middle_pos`.
- **`matSymbolCoercive_of_gramFactors`** — the complete value-route assembly: `MatSymbolCoercive` from the
  Baxter Gram factorizations (`B₀` at `k = 0`, `Bfun k` at `k ≠ 0`) with their `det ≠ 0`, plus symbol
  continuity and `Ĉ → 0` tail decay.  **Every region reduced to `det Q̂₀ ≠ 0`** (origin +
  off-origin) + continuity + decay; no pointwise DCF-NSD, no connectedness.

**Remaining concrete input for the value route:** supply the two Baxter Gram factorizations as actual
matrices — `hfack` at `k ≠ 0` (the real-axis `Cmix0_factorization`, `B = Q̂₀(−k)ᵀ`, already the middle's
input) and `hfac0` at the regularized `k = 0` — plus their determinants nonzero, the symbol's continuity
off `0`, and the `Ĉ → 0` tail bound.

**✅ Origin Baxter factor + `det B₀ ≠ 0` — FORMALIZED (2026-08-09, `Q0OriginFactor.lean`, std-3, NO
physics axiom, full build 8749).**  The `hfac0` `k = 0` input has two halves; the determinant half is now
concrete.  The raw `Q0_mat_c_phys 0` is Lean junk (`÷ s²`, `÷ s³`), but the singularity is removable — the
entire representative `q0_entry_c_repr` (`Q0ComplexRepr.lean`) is `Differentiable ℂ` everywhere.  Assembled
into a matrix:
- **`Q0_mat_c_repr`** — the FINITE Baxter factor including `s = 0`, built from `q0_entry_c_repr`.
- **`Q0_mat_c_repr_eq_of_ne`** / **`continuous_Q0_mat_c_repr`** — agrees with `Q0_mat_c_phys` off `0`,
  continuous through `0`.
- **`det_Q0_mat_c_repr_origin_ne_zero`** — `det (Q0_mat_c_repr 0) ≠ 0`.  Since the representative is
  continuous through `0` and equals `Q0_mat_c_phys` off it, `det (Q0_mat_c_repr 0)` IS the removable value
  `c` of `det_Q0_contour_origin_ne_zero`, whence `≠ 0` — **std-3, no physics axiom** (`k = 0`
  compressibility positivity is proved from `moment_key`, not assumed).

This supplies the `hB₀` (`det B₀ ≠ 0`) input with `B₀ = (Q0_mat_c_repr 0)ᵀ` (`det Bᵀ = det B`).  **The
one remaining input** is the Gram *identity* itself — `hfac0`/`hfack` written in `matRadialSymbol Φ` terms
— which is the **shared real-space ⇄ Fourier DCF bridge** (`Ĉ₀ =` the physical radial DCF transform,
MRS.8-level): the SAME bridge the middle `hfack` needs, not a separate origin obstacle.  Both determinants
(`mixtureDet_pole_free_N` off-origin, `det_Q0_mat_c_repr_origin_ne_zero` at it), the symbol continuity, and
the tail bound are all in hand.

**◑ MRS.8 bridge — connective links FORMALIZED, gap ISOLATED (2026-08-09, `MixtureSymbolBridge.lean`,
std-3, full build 8750).**  The coercivity symbol is now routed onto the established Baxter machinery,
reducing `hfack`/`hfac0` to a single named analytic fact.  Two links:
- **`matRadialSymbol_eq_radial_fourier`** — DEFINITIONAL (`rfl`): `matRadialSymbol Φ k i j =
  radial_fourier (Φ i j) k`.  The coercivity symbol IS the scalar radial Fourier transform per entry, so
  the whole `radial_fourier` scalar theory applies to it.
- **`matRadialSymbol_eq_shellKernel_cos`** — each symbol entry `= 2∫₀^σ shellKernel(Φᵢⱼ)·cos(kv) dv` (via
  the matrix `F[K]=Ĉ` `matShellKernel_cos_eq_radial_fourier`); the entrypoint onto the Baxter-kernel side.

**Irreducible remaining content = the Fourier-space Baxter WH factorization `F[ρK] = I − Q̂₀(ik)Q̂₀(−ik)ᵀ`**
(shell kernel `K` = the mixture DCF's Baxter kernel, matched to its WH factor `Q̂₀`).  This is the genuine
MRS.8/Wertheim theorem, **research-scale, NOT a transcription** — confirmed by direct exploration (the
memory-noted "inverse-transform theorem `cHSmixRaw = [Cmix0]_ij real`" is still open).  It decomposes into
two concrete sub-facts:
- **(1) the DCF Fourier identity `ρ·radial_fourier(Φ) = Cmix0`** — STILL OPEN.  **❌ RETRACTED sub-plan
  (2026-08-09): the `radial_fourier_conv` assembly of `cHSmixRaw` does NOT work.**  I had planned to
  assemble `cHSmixRaw = qFwd + pMixEntry − ∑ qpConv` into `Cmix0` by applying the proven convolution theorem
  `radial_fourier_conv` to the `qpConv` term.  On inspection this is wrong on **two** counts: (a)
  `qpConv = qFwd ⋆[mul, volume] pMixEntry` is **Mathlib's 1D convolution**, while `radial_fourier_conv` is
  for the **3D radial** convolution `radial3d_conv` (`(2π/r)∫∫` triangle) — different objects, so the
  convolution theorem does not apply to `qpConv`; (b) the DCF relates to `cHSmixRaw` by the **odd-part/`r`
  factor** `cHSodd = cHSmixRaw(r) − cHSmixRaw(−r) = 2π√ρ·r·c^HS` (proved def, `MixtureHSDCF.lean:131`), so
  `radial_fourier(cHSmixRaw) ≠ Cmix0` — the 3D radial FT the coercivity route uses is *not* a transform of
  `cHSmixRaw` at all.  ⇒ the four sub-lemmas I built on this path
  (`radial_fourier(qFwd)` diagonal + off-diagonal, `radial_fourier(pMixEntry)`, `psi3_formula`,
  `cubic_moment`, `RadialFourierQFwd.lean`/`RadialFourierQFwdOffdiag.lean`/`RadialFourierPMix.lean`) are
  **correct, reusable 3D-radial-FT facts about the Baxter factors**, but they do NOT assemble into `Cmix0`.
  **The correct MRS.8 bridge is the cosine-transform/shell-kernel route `matRadialSymbol_eq_shellKernel_cos`
  (`radial_fourier(Φ) = 2∫shellKernel(Φ)·cos`, PROVED earlier), whose remaining gap is shell-kernel ⟷ Baxter
  WH factorization.**  (Cautionary parallel: `radial_laplace_conv` was a *false* axiom of exactly this
  transform flavor; here careful inspection caught the flaw before any axiom was committed.)

  **✅ On the WH route, the SCALAR bridge is already PROVED and the `N = 1` matrix Gram input is discharged
  from it (2026-08-09, `MixtureWienerHopfN1.lean`, std-3, full build 8755).**  The scalar shell-kernel ⟷
  Baxter chain is in the library: `shellKernel(c_HS) = baxterK` (`shellKernel_c_HS`), `ρ·baxterK = q0 −
  ∫q0·q0` (`rho_baxterK_eq_q0_self_conv`, the KDEF), and above all the scalar WH factorization
  **`baxter_wiener_hopf_factorization`**: `(1 − ∫q0·cos)² + (∫q0·sin)² = 1 − ρ·radial_fourier(c_HS)(k)` —
  i.e. `|1 − q̃₀(k)|² = 1 − ρĉ(k)`.  New **`hfac_fin_one_of_baxterWH`** shows this IS the value-route Gram
  input `hfack`/`hfac0` at `N = 1`: with `B = 1 − q̃₀(k)` (`Re = 1 − ∫q0·cos`, `Im = −∫q0·sin`), the
  `∑ₗ|(B·v)ₗ|²` shape equals `∑vᵢ² − ρ∑ᵢⱼ matRadialSymbol(c_HS) uᵢuⱼ` (via `matRadialSymbol_eq_radial_fourier`
  + `Complex.normSq_mul`/`normSq_ofReal` + the scalar theorem).  So on the correct route MRS.8 is PROVED at
  `N = 1` (not axiomatized).

  **✅ General-`N` Gram MECHANICS done — `hfack` reduced to a SINGLE structure-factor identity (2026-08-09,
  `MatrixGramWienerHopf.lean`, std-3, full build 8756).**  The value-route Gram input `hfack` at general `N`
  is now reduced to one named identity.  Three pure-linear-algebra lemmas: **`matGram_normSq_expand`**
  (`∑ₗ|(B·v)ₗ|² = ∑ₗ∑ᵢ∑ⱼ Bₗᵢ·conj(Bₗⱼ)·vᵢvⱼ`, real `v`, via `z·conj z = |z|²`); **`matGram_normSq_eq_QQ`**
  (with the proved Hermitian reality `Qneg = conj Q`, `∑ₗ|(Qᵀ·v)ₗ|² = ∑ᵢⱼ (Q·Qnegᵀ)ᵢⱼ vᵢvⱼ`);
  **`matWH_hfack_of_structureFactor`** — the reduction: given the matrix WH factorization
  `(Q·Qnegᵀ)ᵢⱼ = δᵢⱼ − ρ·Cᵢⱼ` (`Cᵢⱼ = radial_fourier(Φᵢⱼ)`) + `Qneg = conj Q`, the whole `hfack` Gram shape
  `∑vᵢ² − ρ∑ᵢⱼ Cᵢⱼ vᵢvⱼ = ∑ₗ|(Qᵀ·v)ₗ|²` holds.  ⇒ **the general-`N` value route now rests on exactly one
  open input: the matrix structure-factor identity `(Q·Qnegᵀ)ᵢⱼ = δᵢⱼ − ρ·radial_fourier(Φᵢⱼ)`** — the
  matrix analog of `baxter_wiener_hopf_factorization` (`matShellKernel` ⟷ `MatBaxterFactorization`/`Q̂₀`).

  **✅ The single remaining input `hSF` PROVED at `N = 1`, and the reduction verified consistent
  (2026-08-09, `MixtureWienerHopfN1.lean`, std-3, full build 8756).**  New **`Q0fourier_fin_one`** is the
  `1×1` Fourier Baxter factor `Q̂₀(ik) = 1 − q̃₀(k)` (`Re = 1 − ∫q0·cos`, `Im = −∫q0·sin`), and
  **`hSF_fin_one_of_baxterWH`** proves the structure-factor identity itself at `N = 1`:
  `(Q̂₀·(conj Q̂₀)ᵀ)ᵢⱼ = δᵢⱼ − ρ·radial_fourier(c_HS)(k)`.  The proof is `(Q̂₀·(conj Q̂₀)ᵀ)₀₀ =
  Q̂₀₀₀·conj(Q̂₀₀₀) = normSq(1 − q̃₀) = (1 − ∫q0cos)² + (∫q0sin)²`, then the scalar
  `baxter_wiener_hopf_factorization` (via `Complex.mul_conj` + `Matrix.cons_val_fin_one` for the `Fin 1`
  entry).  **`hfack_fin_one_via_reduction`** then feeds this proved `hSF` through the general-`N`
  reduction `matWH_hfack_of_structureFactor` (with `Qneg = conj Q̂₀` by `rfl`), reproducing the `N = 1`
  Gram input — so the two `N = 1` routes (direct `hfac_fin_one_of_baxterWH`; via the general `hSF`) agree,
  confirming the general mechanics specialize to the scalar case.

  **✅ General-`N` `hSF` reduced one level deeper — `Φ`/shellKernel ELIMINATED from the frontier
  (2026-08-09, `MatrixBaxterFourierWH.lean`, std-3, full build 8757).**  The general-`N` `hSF` still
  mentioned the DCF `Φ` and its shell kernel (whose real-space closed form is the open Wertheim theorem).
  This turn removes them, leaving a self-contained 1D Fourier identity in the Baxter factor `q` alone
  (which DOES have closed forms, `q0MixEntry`).  The scalar `baxter_wiener_hopf_factorization` was proved
  by brute-force closed forms only because BOTH `q̃₀` and `radial_fourier(c_HS)` have them; at general `N`
  the DCF side does not, so two done facts route `ρ·radial_fourier(Φᵢⱼ)` through `q`: the shell-cosine
  bridge (`matShellKernel_cos_eq_radial_fourier`, `radial_fourier(Φᵢⱼ) = 2∫₀^σ Kᵢⱼ·cos`) and the
  real-space KDEF (`MatBaxterFactorization`, `ρKᵢⱼ = qᵢⱼ − (matSelfConv q)ᵢⱼ` on `(0,σ)`).  Four results:
  **`matBaxterFactor_cos_eq_rho_radial_fourier`** collapses bridge+KDEF to the `q`-only real identity
  `2∫₀^σ(qᵢⱼ − (matSelfConv q)ᵢⱼ)·cos = ρ·radial_fourier(Φᵢⱼ)` (KDEF holds only on the open core; the two
  endpoints are null, handled by `integral_congr_ae` + `Real.volume_singleton`); the frontier predicate
  **`MatBaxterFourierWH`** `(Q̂₀·Q̂₀(−·)ᵀ)ᵢⱼ = δᵢⱼ − 2∫₀^σ(qᵢⱼ − (matSelfConv q)ᵢⱼ)·cos` (the matrix 1D
  Baxter WH convolution identity, pure `q`); **`matSF_of_baxterFourierWH`** (`hSF` from
  `MatBaxterFourierWH` + KDEF + bridge); **`matWH_hfack_of_baxterFourierWH`** (capstone: chaining with
  `matWH_hfack_of_structureFactor`, the value-route Gram input `hfack` from `MatBaxterFourierWH` +
  Hermitian reality + KDEF + bridge, general `N`); and **`matBaxterFourierWH_fin_one`** (non-vacuity: at
  `N = 1` the frontier IS the proven scalar `baxter_wiener_hopf_factorization`, via
  `hSF_fin_one_of_baxterWH` + the KDEF/bridge collapse).  **⇒ the sole open input to the general-`N` value
  route is now `MatBaxterFourierWH` — a self-contained 1D Fourier identity in the Baxter factor `q`, with
  the DCF `Φ` and shell kernel eliminated.**

  **✅ `MatBaxterFourierWH` DECOMPOSED — crux isolated as Wiener–Khinchin ⊕ D-symmetry (2026-08-09,
  `MatrixBaxterFourierWH.lean`, std-3, full build 8757).**  KEY FINDING: `MatBaxterFourierWH` is **NOT an
  identity for abstract `q`**.  With the concrete `1D` Fourier Baxter factor `matFourierFactor`
  (`Q̂₀ᵢⱼ = δᵢⱼ − q̃ᵢⱼ`, `q̃ᵢⱼ = ∫₀^σ qᵢⱼ e^{ikv}`), the pure algebra **`matFourierFactor_mul_conj_expand`**
  gives `(Q̂₀·Q̂₀(−·)ᵀ)ᵢⱼ = δᵢⱼ − q̃ᵢⱼ − conj(q̃ⱼᵢ) + ∑ₗ q̃ᵢₗ·conj(q̃ⱼₗ)`, which is generally
  **complex/asymmetric**, whereas the target `δᵢⱼ − 2∫(qᵢⱼ − mSCᵢⱼ)cos` is **real/symmetric**.  So
  `MatBaxterFourierWH` for the concrete factor decomposes into exactly two ingredients, proved by
  **`matBaxterFourierWH_of_wk_sym`**: (1) the matrix **Wiener–Khinchin identity** `hWK`
  `∑ₗ q̃ᵢₗ·conj(q̃ⱼₗ) = (∫mSCᵢⱼcos+∫mSCⱼᵢcos) + i(∫mSCᵢⱼsin−∫mSCⱼᵢsin)` — TRUE for any
  compactly-supported `q` (`f̃·conj g̃ = ∫Corr(f,g)e^{ikv} + ∫Corr(g,f)e^{-ikv}`, a Fubini/triangle fact),
  the **standard-Fourier-analysis crux**; and (2) the **physical D-symmetry** `∫Dᵢⱼ = ∫Dⱼᵢ`
  (`Dᵢⱼ = qᵢⱼ − mSCᵢⱼ`, from the physical DCF symmetry / `matBaxterK_symm_of_dcf`).  The reduction proof:
  expand, substitute `hWK`, match real part (via D-symmetry-cos) and imaginary part (`= 0`, via
  D-symmetry-sin).  **`matFourierFactor_fin_one`** checks the concrete factor is `Q0fourier_fin_one` at
  `N = 1`.  **⇒ the crux is now cleanly separated: `hWK` (physics-free Fourier analysis) vs. D-symmetry
  (physics).  `hWK` — the matrix Wiener–Khinchin identity (a 2D Fubini/triangle Fourier fact) — is the
  remaining analytic atom; the previously-stated "single open input" now has physics vs. analysis split.**

  **✅✅ `hWK` (the matrix Wiener–Khinchin identity) PROVED — general `N` (2026-08-09,
  `MatrixWienerKhinchin.lean`, std-3, full build 8758).**  The analytic crux is discharged (modulo
  integrability side-conditions, the `radial_fourier_conv` precedent).  Chain: **`triangle_swap`** — the
  triangular Fubini swap `∫ x in 0..σ ∫ y in x..σ Φ = ∫ y in 0..σ ∫ x in 0..y Φ` (indicator +
  `integral_integral_swap`; the diagonal `x=y` null set bridged by `setIntegral_congr_ae` +
  `Real.volume_singleton`) — **THE hard part**; **`corrCos_eq_lower`/`corrSin_eq_lower`** (correlation →
  lower-triangle iterated integral, via `triangle_swap` + shift CoV `integral_comp_sub_left`);
  **`upper_eq_corrCos`/`upper_eq_negCorrSin`** (upper triangle `= corrCos g f` cos-even / `= −corrSin g f`
  sin-odd, via `triangle_swap`+`cos_neg`/`sin_neg` — the sin sign is exactly why the sine identity is a
  DIFFERENCE); **`corrCos_add`/`corrSin_sub`** — the scalar Wiener–Khinchin identities `Cf·Cg+Sf·Sg =
  corrCos f g + corrCos g f`, `Sf·Cg−Cf·Sg = corrSin f g − corrSin g f` (product→square via
  `cos_sub`/`sin_sub`, split via `integral_add_adjacent_intervals`, then the two triangle lemmas);
  **`mscCos_eq_sum`/`mscSin_eq_sum`** (`∫mSCᵢⱼcos = ∑ₗ corrCos(qᵢₗ,qⱼₗ)`, via `integral_finsetSum`);
  **`qtil_mul_conj_qtil`** (per-pair complex term from the scalar identities); **`hWK_matrix`** — the
  matrix `hWK`, summed over species.  Verified end-to-end: `matBaxterFourierWH_of_wk_sym` fed
  `hWK_matrix` (fed the `corrCos_add`/`corrSin_sub` outputs `hC`/`hS`) produces `MatBaxterFourierWH` for
  the concrete `matFourierFactor`.  **⇒ the general-`N` value route's analytic content is COMPLETE modulo
  (i) the physical D-symmetry (`matBaxterK_symm_of_dcf`) and (ii) the integrability side-conditions.**

  **❌ CORRECTION (2026-08-09): the windowed D-symmetry `hDc`/`hDs` is FALSE for unequal diameters — my
  windowed `MatBaxterFourierWH`/`hWK` route is EQUAL-DIAMETER/`N = 1` ONLY.**  Last turn claimed the
  D-symmetry `∫Dᵢⱼcos = ∫Dⱼᵢcos` (`Dᵢⱼ = qᵢⱼ − matSelfConvᵢⱼ`) is "dischargeable from
  `matBaxterK_symm_of_dcf`".  WRONG: that lemma's `hCsym` hypothesis is itself numerically FALSE for
  unequal diameters (already documented `MixtureRowSum.lean:943-953`; re-confirmed here,
  `scratchpad/k_symm_test.py`: `Q(0,1)−mSC(0,1)` vs `Q(1,0)−mSC(1,0)` differ ~3e-3 at v=0.2/0.4/0.6, NOT
  just at jumps).  **Root cause:** the mixture Baxter factor `q0MixEntry` is supported on `[λᵢⱼ, Rᵢⱼ]`
  with `λᵢⱼ = (σⱼ−σᵢ)/2 ≠ 0`, so the windowed single-linear `Dᵢⱼ` is NOT the symmetric DCF.  The object
  that IS a.e.-symmetric is the **full-line two-linear-term DCF** `Ĉ₀ᵢⱼ(v) = q0(i,j)(v) + q0(j,i)(−v) −
  matCorrᵢⱼ(v)` (`matDCFfull`); its a.e.-symmetry **`matDCF_ae_symm` is already PROVED (N=2,
  `MixtureDCFAEInjective.lean`)** via the momentum symmetry `Qphys_Cmix0_entry_symm` + Fourier
  a.e.-injectivity, and it feeds the **SEED route** (`matOzStar_of_asymK_ae`), not the windowed value
  route.  So MML.8 at unequal diameters goes through the full-line DCF / seed route (N=2 done), and my
  windowed `MatBaxterFourierWH` chain (`hSF`/`hfack`) applies only at equal diameters / `N = 1`.

  **General-`N` D-symmetry — the real target, reduced + numerically confirmed.**  The correct D-symmetry
  = full-line DCF a.e.-symmetry, which reduces to the general-`N` physical **swap identity**
  `(Q̂₀(k)Q̂₀ᵀ(−k))ᵢⱼ = (Q̂₀(k)Q̂₀ᵀ(−k))ⱼᵢ` (via the general-`N` `Cmix0_symm_of_swap` + full-line DCF Fourier
  machinery).  Numerically TRUE at N=2,3,4 (`scratchpad/swap_n3.py`, `<1e-14`) but it is an **AGGREGATE**
  identity (`swap_term.py`: per-species-pair terms differ 0.02–1.45, only the `∑ₗ` is symmetric) — NOT a
  fixed `field_simp;ring` like the `N=2` `swap_offdiag_of_keys`, so general `N` is research-scale.  The
  two `KEY` relations (`Q0phys_key_relation`/`Qppphys_key_relation`) are ALREADY general `N`; only the
  coefficient-free structural swap is `N=2`-specific.  **Structural reduction found:** `λⱼₗ − λᵢₗ = −λᵢⱼ`
  (independent of `ℓ`) + the new **`rhoGeoPhys_mul_eq`** `rgᵢₗ·rgⱼₗ = ρₗ·rgᵢⱼ` (general `N`, std-3,
  `MatrixQ0.lean`, the general-`N` analog of the `N=2` `hrgprod`) collapse the swap's quadratic term to
  `rgᵢⱼ·e^{−λᵢⱼk}·∑ₗ ρₗ Tᵢₗ(k)Tⱼₗ(−k)`, so the swap ⟺ `Hᵢⱼ(k) := e^{−λᵢⱼk}·(Tᵢⱼ(k)+Tⱼᵢ(−k)−∑ₗρₗTᵢₗTⱼₗ)`
  is EVEN in `k` (coupled through `ξ₂ = Σρσ²`).

  **⬆ UPGRADE (2026-08-09): the general-`N` swap is a CLEAN algebraic identity (provable, not
  research-scale) + the abstract a.e.-symmetry machinery is now general `N`.**  (i) **Symbolic check**
  (`scratchpad/swap_sym.py`, sympy): with FULLY symbolic `ρ,σ` (N=3), the swap defect `Cmix0(0,1) −
  Cmix0(1,0)` `simplify`s to **exactly `0`** — so it holds for ANY profile using only the coefficient
  definitions, i.e. it is a formal identity (last turn's "research-scale" was too pessimistic; it is
  laborious moment-bookkeeping, not new math).  (ii) **Clean path — rank-2 separability:** the physical
  coefficients factor, `Tᵢⱼ(k) = P(σᵢ,k)·Qppⱼ + Q(σᵢ,k)·c·σⱼ` (KEY 1), so `Q̂₀(k) = I − U(k)·W(k)ᵀ` with
  `U,W` being `N×2`; the `2×2` moment matrix **`W(k)ᵀW(−k)` is `k`-INDEPENDENT** (the `e^{±σₗk/2}`
  factors CANCEL), `= ∑ₗ ρₗ[Qppₗ, cσₗ]ᵀ[Qppₗ, cσₗ]` (entries `∑ρQpp², c∑ρQppσ, c²ξ₂`).  So the swap
  reduces to a **constant-`2×2`-matrix identity** in the Woodbury form — the tractable general-`N` route
  (vs. brute-force `∑ₗ` moment bookkeeping).  (iii) **Abstract machinery now general `N`:** new
  **`ae_eq_of_zOfW_transform_offdiag`** (`MixtureDCFAEInjective.lean`, std-3) packages the
  Fourier-a.e.-injectivity + `w=0`-edge/continuity argument as an `N`-independent lemma (any `f,g : ℝ→ℂ`;
  `matDCF_ae_symm` refactored to use it).  ⇒ **general-`N` full-line DCF a.e.-symmetry = this abstract
  transfer (done, general `N`) + the concrete Fin-`N` `matDCFfull`/`matDCFfull_laplace` (mechanical) + the
  swap identity (clean, rank-2 path).**

  **✅ The general-`N` swap CORE PROVED — `swap_pair_core` (2026-08-09, `MixtureRealSpace.lean`, std-3).**
  Sharpened the rank-2 analysis (`scratchpad/swap_rank2.py`): in the per-pair defect **only `M11 = c²ξ₂`
  matters** — `M00 = ∑ρQpp²` and `M01 = c∑ρσQpp` appear in the quadratic term but CANCEL (the `P·P` and
  `P·Q` structures are automatically `(i,j)`-symmetric), so they are left FREE.  With `M11 = c²ξ₂` + KEY 2
  (`Qpp = 2c+c²ξ₂σ`) the per-pair defect is EXACTLY `0` (sympy).  Formalized as **`swap_pair_core`** — the
  general-`N` analog of the `N=2` `swap_offdiag_of_keys`: with `Ei = e^{σᵢk/2}`, `Ej = e^{σⱼk/2}` (exp
  atoms), the `P`/`Q` Baxter factors, `Qpp = 2c+c²ξ₂σ`, and `Sᵢⱼ = ∑ₗρₗTᵢₗ(k)Tⱼₗ(−k)` in moment form
  (`mu0, mu1` FREE, `xi2`), the per-pair swap `(Ei/Ej)·(Tᵢⱼ(k)+Tⱼᵢ(−k)−Sᵢⱼ) = (Ej/Ei)·(…)` (i.e.
  `Cmix0ᵢⱼ = Cmix0ⱼᵢ`, `rgᵢⱼ` factored) holds by **`field_simp; ring`** (~5 s, std-3).  **⇒ the
  fixed-size algebraic HEART of the general-`N` swap is now PROVED (the `field_simp;ring` that sympy
  confirmed).**

  **✅ The sum→moment reduction FORMALIZED (2026-08-09, `MixtureRealSpace.lean`, std-3).**  Piece (a) —
  the `Finset.sum` expansion collapsing the `ℓ`-sum into the moments — is done: **`sum_to_moment`**
  (`∑ₗ ρₗ·(Pᵢ·Qppₗ+Qᵢ·cσₗ)(Pⱼ·Qppₗ+Qⱼ·cσₗ) = PᵢPⱼ·∑ρQpp² + c·∑ρσQpp·(PᵢQⱼ+QᵢPⱼ) + c²·∑ρσ²·QᵢQⱼ`, the
  core species-sum collapse via `Finset.mul_sum`/`sum_mul`/`sum_add_distrib` + per-term `ring`);
  **`sum_reduction`** (the full quadratic term: `∑ₗ rggₗ·BBₗ = rg·W·Sᵢⱼ` in moment form, given the density
  factoring `rggₗ = ρₗ·rg` [`rhoGeoPhys_mul_eq`] and the bracket product `BBₗ = W·Tᵢₗ(k)Tⱼₗ(−k)`);
  **`exp_lambda_cancel`** (`e^{−λᵢₗk}·e^{−λⱼₗ(−k)} = e^{−λᵢⱼk}`, the `ℓ`-independent factor `W`, since
  `λⱼₗ−λᵢₗ = −λᵢⱼ`).  `sum_reduction`'s output is EXACTLY `swap_pair_core`'s `Sᵢⱼ`.  ⇒ the general-`N`
  swap now needs only: discharge `sum_reduction`'s `hBB` for the PHYSICAL bracket + chain to
  `swap_pair_core`.

  **✅ Physical instantiation — the bracket side DONE (2026-08-09, `MixtureRealSpace.lean`, std-3).**
  The `q0_entry_c` bracket is now connected to the abstract machinery: **`Q0_mat_c_eq_id_sub`** (`hQ`:
  `Q̂₀ᵢⱼ = δᵢⱼ − ρ_geoᵢⱼ·Bbraᵢⱼ`, the `Cmix0_entry_of_id_sub` shape, by `q0_entry_c` unfold + `ring`);
  **`Bbra_sep`** (rank-2 separation via KEY 1: `Bbra = e^{−λs}(pP·Qpp + pQ·cσ)`, `pP,pQ` the Baxter
  factors); **`Bbra_prod`** (the `hBB`: `B(k)ᵢₗ·B(−k)ⱼₗ = e^{−λᵢⱼk}·Tᵢₗ(k)·Tⱼₗ(−k)`, via `Bbra_sep`
  twice + `exp_lambda_cancel`, `Qpp` single-index); **`phys_sum`** (the physical `∑ₗ`:
  `∑ₗ ρgᵢₗρgⱼₗ·B(k)ᵢₗB(−k)ⱼₗ = rgᵢⱼ·e^{−λᵢⱼk}·Sᵢⱼ` in moment form, = `sum_reduction` fed `Bbra_prod` +
  the density hyp).  **So the physical `Cmix0_entry_of_id_sub`'s `∑ₗ` term is now the exact `Sᵢⱼ` of
  `swap_pair_core`.**

  **✅✅✅ The general-`N` physical swap `Cmix0ᵢⱼ = Cmix0ⱼᵢ` PROVED (2026-08-09,
  `MixtureDCFAEInjective.lean`, std-3, full build 8758).**  The final assembly is done — the
  research-scale blocker from several turns ago is CLOSED.  **`Cmix0_phys_reduce`** reduces each entry
  to `Cmix0ᵢⱼ = ρgᵢⱼ·e^{−λᵢⱼk}·(Tᵢⱼ(k)+Tⱼᵢ(−k)−Sᵢⱼ)` (via `Cmix0_entry_of_id_sub` + `phys_sum` + the two
  linear terms `Bbra_sep`); **`Cmix0_phys_swap`** applies it twice, factors `ρgᵢⱼ` (via `ρ_geo`
  symmetry), and closes the per-pair bracket by inlining `swap_pair_core`'s `field_simp;ring` — the
  `Ei = exp(kσᵢ/2)` bridge (`exp(−kσᵢ) = 1/Ei²`, `exp(−λᵢⱼk) = Ei/Ej`, six `Complex.exp_add`/`exp_neg`
  `have`s) + KEY 2 (`Qpp1 = 2c+c²ξ₂σ`, `ξ₂ = ∑ρσ²`).  Coefficient-free given the two `KEY` relations +
  `ρ_geo` symmetry/product — the **general-`N` `Qphys_Cmix0_entry_symm`** (the `N=2`-only
  `swap_offdiag_of_keys` route is superseded).  **⇒ the momentum-space DCF symmetry `Cmix0` symmetric
  holds for ANY number of components** — which (via `ae_eq_of_zOfW_transform_offdiag` [general `N`,
  done]) is exactly the physics input the full-line DCF a.e.-symmetry needs.

  **✅✅✅ The general-`N` full-line DCF a.e.-symmetry `matDCF_ae_symmN` PROVED (2026-08-10,
  `MixtureDCFAEInjective.lean` `section GeneralNDCF`, std-3, full build 8759).**  The `Fin 2`
  `matDCFfull` infrastructure is lifted to arbitrary `N`, closing general-`N` a.e.-symmetry.  New
  lemmas: **`physMixN`** (the general-`N` physical `Mix N 0`); **`q0MixEntry_physMixN_laplace`/
  `_fullline`** (window/full-line kernel Laplace transform `= Bbra` bracket); **`matCorrWN`** +
  **`matCorrWN_laplace`** (weighted-correlation `∑ₗ` transform = product of the two full-line
  transforms); **`QphysN`** (physical `Q̂₀` matrix, general `N`); **`matDCFfullN`**
  (`ρgᵢⱼ·q0ᵢⱼ(v) + ρgⱼᵢ·q0ⱼᵢ(−v) − matCorrWN`); **`matDCFfullN_laplace`**
  (`𝓛[matDCFfullN]ᵢⱼ = Cmix0(QphysN)ᵢⱼ`, via `Cmix0_entry_of_id_sub` + `Q0_mat_c_eq_id_sub`,
  bypassing the `Fin 2`-only `Cmix0_Qphys_eq`); **`q0MixEntry_continuousAt_N`** +
  **`matCorrWN_continuous`** + **`matDCFfullN_integrable`** + **`matDCFfullN_ae_continuous`** (the
  regularity ports); **`matDCFfullN_transform_offdiag`** (off-`0` transform symmetry via
  **`Cmix0_phys_swap`** — its six hyps discharged from `Q0phys_key_relation`, `Qppphys_key_relation`,
  the `xi2` def, and `rhoGeoPhys` symmetry / `rhoGeoPhys_mul_eq`, all cast to `ℂ`); **`matDCF_ae_symmN`**
  (the capstone, via `ae_eq_of_zOfW_transform_offdiag`).  **⇒ obstruction (b) is now dissolved for ANY
  number of components** — the `Fin 2` `matDCF_ae_symm` is fully generalized.
- **(2) the Hermitian reality `Q̂₀(−ik) = conj(Q̂₀(ik))`** — **✅ PROVED (2026-08-09, `Q0HermitianAxis.lean`,
  std-3, full build 8751).**  Real Baxter coefficients on the imaginary axis; this is what turns
  `vᵀ Q̂₀(ik)Q̂₀(−ik)ᵀ v` into `∑ₗ|(Q̂₀(ik)ᵀ v)ₗ|²` (the `∑ₗ normSq` shape of `hfack`/`hfac0`).  Chain:
  **`q0_entry_c_conj`** (entry Schwarz reflection `conj(q̂₀(s)) = q̂₀(conj s)` for real coefficients — one
  `simp only` pushing `conj` through `map_sub`/`map_mul`/`map_div₀`/`Complex.exp_conj`/`conj_ofReal`) →
  **`Q0_mat_c_phys_conj`** (matrix version, per entry) → **`Q0_mat_c_phys_neg_axis`** / **`_map`** (the
  on-axis reality `Q̂₀(−ik) = conj(Q̂₀(ik))` entrywise / as `Matrix.map (starRingEnd ℂ)`, via `conj(ik) =
  i(−k)` from `Complex.conj_I` + `Complex.conj_ofReal`).

Everything else in the value route (three region reductions, both determinants, symbol continuity, tail,
**and now sub-fact (2)**) is proved or reduced; **the single remaining open analytic input is sub-fact (1)**
— the DCF Fourier identity `ρ·radial_fourier(Φ) = Cmix0`, whose correct route is the shell-kernel cosine
bridge (`matRadialSymbol_eq_shellKernel_cos`), open at shell-kernel ⟷ Baxter WH factorization (the
`radial_fourier_conv`/`cHSmixRaw` sub-plan was retracted — see above).

## Group MML — N=2 Mixture Mittag-Leffler Inner-Core (2×2 inverse → residue → assembly)

**Motivation (2026-07-15).** For N=2, Q̂₀(z) is a 2×2 matrix with fully algebraic entries
(Y1.1 DONE). Its inverse is Q̂₀(z)⁻¹ = adj(Q̂₀)/det(Q̂₀), also proved (Y1.1:
`inv_apply_eq_adj_div_det`). For the (0,1) off-diagonal entry:

    [Q̂₀(z)⁻¹]₀₁  =  adj(Q̂₀)₀₁ / det(Q̂₀)  =  −Q̂₀₀₁(z) / det(Q̂₀(z))     (2×2 identity)

The zeros s_k of det(Q̂₀(z)) (the "HS poles") then give residues:

    Res_{z=s_k} [Q̂₀⁻¹]₀₁  =  −Q̂₀₀₁(s_k) / det′(Q̂₀)(s_k)     (residue_of_simple_pole)

This is the B_k coefficient used in `fmsa_hs_pole_residue.py`. **MML.1 + MML.2 DONE (2026-07-15)**,
axiom-clean (`HSMixture/MixtureHSPoles.lean`) — the 2×2 adj/det/inverse algebra and the `B_k`
residue via `residue_of_simple_pole`. MZERO.1 (infinitely many HS poles for det(Q̂₀)) is a harder
structural result; MML.8 (full assembly) uses Y1.3 (now done). Together they prove the exact inner
DCF for N=2 unlike pairs IS a convergent Mittag-Leffler series — resolving the "no closed
form" claim.

---

### Task MML.1 — Explicit 2×2 adjugate/det for Q̂₀

**Statement.** For N=2 (`Fin 2` indexing):

    adj(Q̂₀)₀₁  =  −Q̂₀₀₁
    det(Q̂₀)     =  Q̂₀₀₀·Q̂₀₁₁ − Q̂₀₀₁·Q̂₀₁₀
    [Q̂₀(z)⁻¹]₀₁ = −Q̂₀₀₁(z) / det(Q̂₀(z))      (combining adj/det with Y1.1)

**Proof strategy.** Direct `simp` using Mathlib:
- `Matrix.det_fin_two`: `det M = M 0 0 * M 1 1 − M 0 1 * M 1 0`
- `Matrix.adjugate_fin_two`: explicit 2×2 formula
- `Matrix.inv_def` (Y1.1's `inv_apply_eq_adj_div_det`): connects to the above

**Depends on.** Y1.1 (`inv_apply_eq_adj_div_det`), Mathlib `Matrix.det_fin_two`,
`Matrix.adjugate_fin_two`.
**Lean (`HSMixture/MixtureHSPoles.lean`, namespace `FMSA.MixtureHSPoles`).** `adjugate_fin_two_zero_one`
(`adj(M)₀₁ = −M₀₁`), `inv_zero_one_eq` (`M⁻¹₀₁ = −M₀₁/det M`, unconditional via
`inv_apply_eq_adj_div_det`), `Q0_det_fin_two` (`det(Q̂₀) = Q̂₀₀₀Q̂₀₁₁ − Q̂₀₀₁Q̂₀₁₀`), `Q0inv_zero_one`
(`[Q̂₀(s)⁻¹]₀₁ = −Q̂₀₀₁(s)/det(Q̂₀(s))`).
**Status.** ✓ DONE (2026-07-15), axiom-clean.

---

### Task MML.2 — B_k residue formula for N=2

**Statement.** Let s_k ∈ ℂ be a simple zero of `z ↦ det(Q0_mat_c z)` (an HS pole),
i.e., `det(Q̂₀(s_k)) = 0` and `(d/dz det(Q̂₀(z)))|_{z=s_k} ≠ 0`. Then:

    Res_{z=s_k} ([Q̂₀(z)⁻¹]₀₁)  =  −Q̂₀₀₁(s_k) / det′(Q̂₀)(s_k)

(This is the Q̂₀-residue part of the B_k amplitude in `fmsa_hs_pole_residue.py`.
The Yukawa-propagator factor `K/(z_t²−s_k²)` requires Y1.3 and is not part of this task.)

**Proof chain.**
1. MML.1: `[Q̂₀(z)⁻¹]₀₁ = N(z)/D(z)` where `N(z) = −Q̂₀₀₁(z)`, `D(z) = det(Q̂₀(z))`.
2. `N` and `D` are meromorphic / holomorphic near s_k (Y1.1 — entries are entire).
3. `residue_of_simple_pole` (BaxterResidue.lean DONE): gives `Res = N(s_k)/D′(s_k)`.
4. Conclude `= −Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)`.

**Depends on.** MML.1, `residue_of_simple_pole` (DONE), M.3/M.4 (for det′ ≠ 0 hypothesis,
currently conditional).
**Lean (`HSMixture/MixtureHSPoles.lean`).** `b_k_residue` — given a simple zero `s_k` of
`s ↦ det(Q̂₀(s))` (`HasDerivAt` det with `Dprime`, `det(s_k)=0`, `Dprime ≠ 0`, `Q̂₀₀₁` continuous at
`s_k` — all as hypotheses, matching `residue_of_simple_pole`), concludes
`Res_{z=s_k}[Q̂₀(z)⁻¹]₀₁ = −Q̂₀₀₁(s_k)/Dprime`.  Proof: rewrite via `Q0inv_zero_one` (holds for all
`z`), then `residue_of_simple_pole` with `N = −Q̂₀₀₁`, `D = det(Q̂₀)`.  Discharging the analytic
hypotheses concretely (entry/det holomorphy at `s_k ≠ 0`) is left to a later pass / MZERO.1.
**Status.** ✓ DONE (2026-07-15), axiom-clean (residue wiring; analytic hyps taken as inputs).

---

### Task MML.3 — RETIRED (2026-07-16), superseded by MML.4–MML.8

The single "full inner-DCF Mittag-Leffler assembly" task bundled ~5 independent sub-results, and its
genuine difficulty — proving the residue *series equals the true inner DCF* (the "collapse") — is the
N=2 matrix analog of the scalar `hcollapse` (OZFIX.6/9/10), **still open even in the scalar HS case**.
As one atomic task it could not be tracked or landed incrementally. Split (per the proof-notes
convention of promoting differently-scoped leftover work to new task numbers) into the five
topic-scoped tasks below. The target identity (N=2 unlike pair (0,1), r ∈ (0, R₀₁]) is unchanged:

    r · c^{inner}_{01}(r) = Σ_t [Q̂₀(z_t)⁻¹·K_t·Q̂₀(z_t)⁻ᵀ]₀₁ · exp(z_t(R₀₁−r))     (I)  MML.6
                           + Σ_k 2·Re[B_k · exp(−s_k·r)]                          (II) MML.4/MML.5
                           + p₀                                                   (III) MML.7
                           [ (I)+(II)+(III) = true inner DCF                            MML.8 ]

MML.4–MML.7 are **DONE (axiom-clean)**; MML.8 (the collapse) is scoped-only. Lean home:
`YukawaOZMix/MixtureMLSeries.lean` (MML.4/MML.5), `YukawaOZMix/MixtureInnerDCF.lean` (MML.6/MML.7, and
the eventual MML.8).

---

### Task MML.4 — HS-pole Mittag-Leffler term (II) + Yukawa-coupled residue *(**RDF-only**)*

> **⚠ Scope (2026-07-16).** Term (II) (an HS-pole sum) exists **only for the RDF `h₁`** — by (★) the DCF
> carries no `Q̂₀⁻¹`, hence no `det Q̂₀` zeros and no term (II) (finite closed form — Group MRS). The
> definitions/lemmas below stay valid, RDF-scoped. See the MML.8 box.

**Statement.** Define the per-pole term `mixHSterm B_k s_k r n = B_k(n)·exp(−s_k(n)·r)` and the series
`mixHS_series = 2·Re[∑' n, mixHSterm n]` (term (II)). The `B_k` amplitude of `fmsa_hs_pole_residue.py`
is `Res_{s_k}[Q̂₀⁻¹]₀₁ · Σ_t K_t/(z_t²−s_k²)`; MML.4 ties a given `B_k` to the proven MML.2 residue by
showing that multiplying MML.2's `−Q̂₀₀₁(s_k)/det′` by any factor `coupling` continuous at `s_k`
yields the coupled residue `coupling(s_k)·(−Q̂₀₀₁(s_k)/det′)`.

**Design (key).** The term is kept **generic in the coefficient** `Bcoef : ℕ → ℂ` and pole family
`sfam : ℕ → ℂ` (mirroring how the scalar `h_explicit_term` takes an abstract `kfam`). This defers the
singly-vs-doubly-propagation modeling choice to MML.8 (see there), keeping MML.4 grounded in the
already-proven MML.2 residue.

**Depends on.** MML.2 (`b_k_residue`), Y1.1 (`Q0_mat_c`).
**Lean (`YukawaOZMix/MixtureMLSeries.lean`, namespace `FMSA.MixtureHSPoles`).**
`mixHSterm`, `mixHS_series`; `yukawaCoupling K z nt s = Σ_{t<nt} K_t/(z_t²−s²)` with
`yukawaCoupling_continuousAt` (continuous where `z_t²≠s_k²`, via `tendsto_finsetSum` + `ContinuousAt.div`);
`b_k_residue_coupled` (`b_k_residue` × the continuous coupling via `Tendsto.mul` + a `ring` regrouping).
**Status.** ✓ DONE (2026-07-16), axiom-clean.

---

### Task MML.5 — Convergence of the HS-pole series (abstract; concrete deferred) *(**RDF-only**)*

> **⚠ Scope (2026-07-16).** HS-pole series exist **only for the RDF `h₁`**. By (★)
> `Ĉ₁ = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` the **DCF** has no `Q̂₀⁻¹`, hence no `det Q̂₀` zeros and no HS-pole
> sum at all (finite closed form — Group MRS). So MML.5 (and its deferred `MML.5-concrete`
> magnitude gate, and MZERO) are **not on the DCF path**; they are load-bearing for `h₁` only.
> Everything below is RDF-scoped. See the MML.8 box.

**Statement (abstract).** If `‖mixHSterm n‖ ≤ C·(n+1)^p` with `p < −1`, then
`Summable (mixHSterm B_k s_k r)`.

**Proof.** Near-copy of the scalar `h_explicit_summable` (`HardSphere/BaxterResidue.lean`): reduce to
`Summable (n ↦ (n+1)^p)` via `Real.summable_nat_rpow` (holds iff `p < −1`) + `summable_nat_add_iff`
index shift, then `Summable.of_norm_bounded`.

**Reduction (DONE 2026-07-16, axiom-clean).** `mixHS_summable_of_growth` (`MixtureMLSeries.lean`):
given (i) a linear pole-growth `c·n+d ≤ ‖sfam n‖` (`c,d>0`) and (ii) the per-pole power bound
`‖mixHSterm n‖ ≤ C·‖sfam n‖^p` (`p<−1`), the series is `Summable`. Converts the `‖s_k‖`-power bound
to `mixHS_summable`'s `(n+1)^p` form via the negative-exponent `rpow` antitone step
(`Real.rpow_le_rpow_iff_of_neg`) — mirrors `h_explicit_summable_of_pole_family`. This **isolates**
the concrete gate to exactly one obligation (see below).

**Growth witness (DONE 2026-07-16, axiom-clean).** The claim (in an earlier draft of this note) that
"no mixture pole-family growth witness exists" is now **retired** — it does:
- `exists_zero_family_growth_of_chordPoleFamily` (**generic**, `Analysis/BanachPoleFamily.lean`):
  from any `ChordPoleFamily F` whose centres grow linearly (`c·n+d ≤ ‖s1 n‖`), the constructed zero
  family `g` inherits `c·n + (c·N + d − r) ≤ ‖g n‖` (reverse triangle, `norm_sub_norm_le`). Reusable
  by **both** POLE.5 and MML.5.
- `Q0_det_c_pole_family_growth` (**mixture instance**, `MixtureHSZeros.lean`): the same
  `ChordPoleFamily detC` as `Q0_det_c_zeros_infinite`, exposing `π·n + (π·N − r) ≤ ‖g n‖` (centres
  `‖s1 n‖ ≥ |Im| = π·n` via `Complex.abs_im_le_norm`; with `N≥1`, `r<π/2` the offset `>π/2>0`).
  Conditional on the MZERO.5 bounds, like `Q0_det_c_zeros_infinite`.

**The remaining MML.5-concrete gate — ✅ CLOSED 2026-07-17 (superseding the "deferred" text
that follows).** The per-pole **magnitude bound** `‖B_k‖·e^{−r·Re s_k} ≤ C·‖s_k‖^p` (`p<−1`) was
the last piece; it is now proved (`detF_family_magnitude_bound`) and fed into
`mixHS_summable_of_growth` (`detF_mixHS_summable`, `HSMixture/MixtureMLBound.lean`), both
axiom-clean — see the "GATE PROVED" and "`Summable` WIRED end-to-end" notes at the top of the
MZERO.5 section. *Original scoping text (kept for the technique record):* a POLE.5-analog —
POLE.5's `Npoly/Dpoly` cubic-over-linear chain re-derived for the **two-frequency** exp-polynomial
`detC` (`detC_lam_free`); in the event this was NOT a `‖B_k‖·e^{−r·Re s_k}` bound at the raw
zeros (those have `Re s_k < 0`) but at the **reflected** family `−g n`, and the exponent's
threshold turned out to be `max(σ₀/2, (σ₁−σ₀)/2)`, not `σ₀/2`.

**Depends on.** All discharged: abstract/reduction/growth + MZERO.1 pole family (CLOSED 2026-07-17)
+ the `detC` magnitude lemma (proved 2026-07-17).
**Lean.** `mixHS_summable`, `mixHS_summable_of_growth` (`MixtureMLSeries.lean`);
`exists_zero_family_growth_of_chordPoleFamily` (`Analysis/BanachPoleFamily.lean`);
`Q0_det_c_pole_family_growth` (`MixtureHSZeros.lean`); `detF_family_magnitude_bound`,
`detF_zero_family_growth`, `detF_mixHS_summable` (`MixtureChordFamily.lean`/`MixtureMLBound.lean`).
**Status.** ✅ **FULLY CLOSED (2026-07-24), axiom-clean, no remainder** — abstract + reduction +
growth-witness (2026-07-16) + concrete magnitude gate + end-to-end `Summable` (2026-07-17) + the
`Bcoef = b_k_residue` identification (2026-07-24, below).

**✅ 2026-07-24 — the last bookkeeping item CLOSED: the summed coefficient *is* the residue.**
Until now `Bcoef n = −q01(g n)/det′(g n)` was a *formula* that resembled MML.2's `B_k` but was never
proved equal to it, so "the series converges" and "the series is the HS-pole Mittag-Leffler series"
were separate claims. Both new pieces are axiom-clean, full build green:

- `detF_family_magnitude_bound` (`MixtureChordFamily.lean`) **strengthened** with a non-vanishing
  clause `∀ n, g n ≠ 0 ∧ det′(g n) ≠ 0`. No new analysis: both are strict consequences of the
  `disk_facts` the magnitude chain already consumed (`1 ≤ ‖g n‖`, and
  `‖det′(g n)‖ ≥ σ₁μ/(24(μ+K₁)) > 0`). The proof only needed those three facts *hoisted* out of the
  per-`n` bullet into a shared `hfacts`, so both conclusions can read them.
- `detF_Bcoef_eq_b_k_residue` + `detF_eq_det_Q0` (`MixtureMLBound.lean`, which now also imports
  `MixtureHSPoles`): at any `s_k ≠ 0` with `detF s_k = 0`, `det′(s_k) ≠ 0`, the coefficient
  `−q01(s_k)/det′(s_k)` **is** `Res_{s_k}[Q̂₀(z)⁻¹]₀₁`. The three `b_k_residue` inputs come from the
  `MixParams` layer: `detF_hasDerivAt` (needs `s_k ≠ 0`), `hzero`, and
  `q0_entry_c_differentiableAt` for the entry's continuity. `detF_eq_det_Q0` is `rfl` — the
  parameter pack's `detF` *is* `det Q̂₀` of the cast matrix — and `q01_eq` was already there.
- `detF_mixHS_summable` correspondingly gains a third clause certifying the identification for the
  constructed family, so a single theorem now delivers: injective zero family + each coefficient is
  a genuine HS-pole residue + the series is `Summable`.

⚠ Note the shape of the fix: the non-vanishing was *already inside* the old proof and was simply
being discarded. Whenever a "cosmetic remainder" is logged, check first whether the missing fact is
already established and merely unexported — here that turned a projected analysis task into a
five-line restructure.

**✅ 2026-07-17 — MML.5-concrete GATE PROVED (reflected form), axiom-clean.**
`detF_family_magnitude_bound` (`HSMixture/MixtureChordFamily.lean`, module green, no `sorry`,
`#print axioms` = `[propext, Classical.choice, Quot.sound]`):

```
detF_family_magnitude_bound (P : MixParams) (hP : P.Phys) {rdist : ℝ}
    (hrd : max (P.sig0 / 2) ((P.sig1 - P.sig0) / 2) < rdist) :
    ∃ g C p, p < -1 ∧ 0 < C ∧ Function.Injective g ∧ (∀ n, P.detF (g n) = 0) ∧
      (∃ c d, 0 < c ∧ 0 < d ∧ ∀ n, c*n + d ≤ ‖g n‖) ∧
      ∀ n, ‖q01 P (g n)‖ * Real.exp (rdist * (g n).re) / ‖derivF P (g n)‖ ≤ C * ‖g n‖ ^ p
```
with `p = max((σ₀−σ₁−2r)/σ₁, (−σ₀−2r)/σ₁)`. Plus `detF_zero_family_growth` (linear growth
`c·n+d ≤ ‖g n‖`, from a local re-run of the Banach construction — the generic
`exists_zero_family_growth_of_chordPoleFamily` forgets disk membership, which the magnitude
chain needs), and the supporting `q01`/`q01_norm_le`, `derivF_at_sGuess_lower`, `disk_facts`,
`sGuess_re_dev`, `magnitude_bound_at`.

**⚠ CORRECTION to this session's own earlier scoping formula (below): the threshold is
`max(σ₀/2, (σ₁−σ₀)/2)`, NOT `σ₀/2`.** The extra branch is a genuine effect, not proof slack —
it is the `−σ₀/s` term of `q01` (from `(1 − sσ₀ − e^{−sσ₀})/s²`), decaying like `‖s‖^{2λ/σ₁−1}`,
which dominates the `e^{σ₀x}/‖s‖²` term exactly when `2σ₀ < σ₁`. **Numerically re-confirmed
2026-07-17** at σ=[0.8,2.3] (`2σ₀=1.6 < 2.3`, n=2000): measured `p(0.45) = −0.867 > −1`
(**NOT summable**) where the naive one-branch formula predicted `−1.043` — so the `σ₀/2`
threshold would have been WRONG there; true threshold ≈ 0.603, the proved `max(…) = 0.75` is
sufficient (conservative). The earlier scoping missed this because both tested σ-pairs were
degenerate for it (σ=[1,2]: `2σ₀ = σ₁`, branches coincide; σ=[1,1.5]: `2σ₀ > σ₁`, first branch
binds) — a reminder to sweep the *qualitative regimes*, not just several parameter values.

**`Summable` corollary NOW WIRED (2026-07-17) — MML.5-concrete CLOSED end-to-end.**
`detF_mixHS_summable` (`HSMixture/MixtureMLBound.lean`, new file importing both
`MixtureChordFamily` and `MixtureMLSeries`; axiom-clean, no `sorry`, full build green): for
`rdist > max(σ₀/2, (σ₁−σ₀)/2)`, `∃ g` injective `detC`-zero family with
`Summable (mixHSterm (fun n => −q01(g n)/derivF(g n)) (fun n => −g n) rdist)`. The wiring is
pure reflection + a norm computation: `mixHS_summable_of_growth` takes `Bcoef`/`sfam` as FREE
functions (no `b_k_residue` analytic hypotheses), and `‖mixHSterm‖ = ‖q01(g n)‖·e^{rdist·Re(g n)}
/‖det′(g n)‖` is *exactly* the gate's LHS (via `norm_div`/`norm_neg`/`Complex.norm_exp`), while
`‖sfam n‖ = ‖−g n‖ = ‖g n‖` transfers the linear growth. **Only cosmetic bookkeeping remains**:
identifying `Bcoef n = −q01(g n)/det′(g n)` with `b_k_residue`'s abstract `B_k` (same value,
different packaging) inside the DCF assembly — not an analytic gap.

**2026-07-16 (POLE session) — the concrete magnitude bound is REFUTED as literally stated for
the raw zero family, and CONFIRMED for the reflected family.** Scoping (`mzero5_scoping.py`):
the detC zeros have `Re z_k ≈ −(2/σ₁)ln|z_k| < 0`, so enumerating `s_k := z_k` makes
`e^{−r·Re s_k}` GROW: measured `‖B_k‖e^{−r·Re s_k} ~ |s_k|^{p_eff}` with
`p_eff(r) ≈ −0.5 + r·(2/σ₁)` — never `< −1` for `r ≥ 0` (σ=[1,2]: `p_eff(1) = +0.45`).
With the **reflected family `s_k := −z_k`** (`Re s_k > 0` — the correct enumeration for
`mixHSterm`'s decaying kernel under the inverse-Laplace convention `Σ Res·e^{z_k r} =
Σ B_k e^{−s_k r}`, `s_k = −z_k`), the bound HOLDS: measured `p_eff(r) ≈ −0.5 − r·(2/σ₁) < −1`
for `r ≳ 0.5` at both σ sets tested; analytic account: `‖q01(z)‖ ~ e^{λ|Re z|}·C/|z| =
|z|^{2λ/σ₁−1}`, `‖det′(z_k)‖ → σ₁·|Mc| = Θ(1)`. The Lean deliverable (in
`HSMixture/MixtureChordFamily.lean`) states the bound at the constructed zero family in the
reflected form; **reconciling `mixHSterm`'s family argument (feed `−z_k`, not `z_k`) is flagged
for the mixture session** — cf. the `G_baxter` ρ-bug lesson: sign conventions matter and the
numerics have now pinned this one.

---

### Task MML.6 — Yukawa doubly-propagated base term (I)

**Statement.** Define the base amplitude `yukawaBaseAmp = [Ĝ·K·Ĝᵀ]₀₁` (`Ĝ = Q̂₀(z)⁻¹`) and the
real-space base `yukawaBaseTerm = Σ_t amp_t·exp(z_t(R−r))` (term (I)). Certify that `yukawaBaseAmp` is
exactly the residue at the Yukawa pole `s = −z` of the Y1.5 spectral amplitude — i.e. the exact
**doubly-propagated** leading residue ([LN] Eq. 73), *not* the singly-propagated `K·Ĝ₀₁` leading-order
approximation shipped by the Python.

**Proof.** Direct reuse of `spectralAmp_residue` (Y1.5, `SpectralAmplitude.lean`): its limit value is
literally `(Ĝ·K·Ĝᵀ)₀₁ = yukawaBaseAmp` (defeq after `unfold`).

**Note (envelope = MML.8).** The real-space `exp(z_t(R−r))` envelope — the inverse-Laplace step
relating this residue to `yukawaBaseTerm` — is the assembly, deferred to MML.8. `outerDCF_transform`
(Y1.2, `OuterDCF.lean`) supplies one direction of that transform pair.

**Note (RDF vs DCF — CORRECTED 2026-07-16 by (★)).** `yukawaBaseAmp` is the **RDF** (`h₁`)
amplitude: at an HS pole it produces a *double* pole (`doubly_prop_entry_eq`), hence `r·e^{−s_k r}`
terms. MML.6 proves that RDF amplitude — a valid, exact object (Y1.5/Y1.6).

⚠ An earlier version of this note added: *"the DCF `c^{inner}` base is instead the **singly**-propagated
`K·[Q̂₀⁻¹]₀₁`; the DCF assembly (MML.8, reading (S)) uses it."* **That is refuted.** (★)
`Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` contains **no `Q̂₀⁻¹` at all** ⇒ the DCF has *no* HS poles and *no*
term (II); its base is not a singly-propagated inverse amplitude either. The DCF route is **Group
MRS** (finite closed form). The `Q̂₀⁻¹`-count is the dividing line: **none ⇒ DCF (MRS); two ⇒ RDF
`h₁`** — the "singly" reading corresponds to no object. See the MML.8 box.

**Depends on.** Y1.5 (`spectralAmp`/`spectralAmp_residue`), Y1.1 (`Q0_mat_c`).
**Lean (`YukawaOZMix/MixtureInnerDCF.lean`).** `yukawaBaseAmp`, `yukawaBaseTerm`,
`yukawaBaseAmp_eq_spectralAmp_residue`.
**Status.** ✓ DONE (2026-07-16), axiom-clean.

---

### Task MML.7 — Origin (singularity-cancellation) constant `p₀`

**Statement.** The constant `p₀ = −(Yukawa base + HS-pole sum)|_{r→0}` keeping `c(r)=rc₁(r)/(…·r)`
finite as `r→0` (`_precompute_p0`). Abstractly: for `base`, `hsum`, inner-polynomial `P` continuous
at 0 with the `1/r` limit existing, `P 0 = −(base 0 + hsum 0)`.

**Proof.** Instantiates P.2's fully-generic `origin_necessity` (`FMSAPoly/OriginConstraint.lean`) with
the bundled `E := base + hsum`. The Yukawa specialization fixes `base := eij` (its continuity via
`fun_prop`, as in Y1.7) and rewrites `eij(0)` via `eij_at_origin`, giving
`P 0 = −(Σ_k A_k·exp(−z_k R) + hsum 0)` — exactly `_precompute_p0`'s `−(E_ij(0) + Σ_k 2·Re[B_k])`
form. Extends Y1.7's `origin_constraint_eq76` (Yukawa-only) by folding the HS-pole sum into `E`.

**Depends on.** P.2 (`origin_necessity`), P.1 (`eij`/`eij_at_origin`), Y1.7 (pattern).
**Lean (`YukawaOZMix/MixtureInnerDCF.lean`).** `origin_constant_mix`, `origin_constant_eij_mix`.
The one deferred ingredient is `ContinuousAt (mixHS_series …) 0` (the HS-sum's continuity at 0, a
tsum-continuity fact needing the same dominated-summability machinery as MML.5-concrete); MML.7 takes
it as the hypothesis `hcSum`.
**Status.** ✓ DONE (2026-07-16), axiom-clean.

---

### Task MML.8 — Full assembly / collapse *(ex-MML.3, scoped only)*

> **⚠ PREMISE REFUTED (2026-07-16) — for the DCF, term (II) does not exist.**
>
> The numerical session's **(★)** result (`todo/to_Lean.md` §1; `fmsa_double_prop.py`,
> `probe_true_first_order.py`; verified to 4.4×10⁻¹³) removes the inverses from the DCF. Equating
> [LN] eq:OZ1_Baxter (a) with `Hhat1_spec` (b) and solving for `Ĉ₁`:
>
>     Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)                                  (★)
>
> **(★) contains no `Q̂₀⁻¹`.** `Q̂₀` is entire (the `φ₁`,`φ₂` singularities at `s=0` are removable)
> and `B₁_ij(k) = e^{−ikR_ij}·b_ij(ik)` carries only the Yukawa poles `k = i·z_q`. Hence `Ĉ₁` is
> meromorphic with **only Yukawa poles**, and the zeros of `det Q̂₀` — the whole subject of Group
> MZERO — **never enter the DCF**. Consequences:
>
> - The **stated** target above — (II) as an infinite HS-pole sum `Σ_k 2Re[B_k e^{−s_k r}]` — is
>   **false-as-premised for the DCF**. The correct target is a **finite closed form** (polynomial +
>   finitely many exponentials), **piecewise** in `r`, with knots at the support-overlap
>   breakpoints (`λ_ij` first — exactly Group IB's set).
> - The listed blockers **dissolve for the DCF**: `MZERO.1`, `MML.5`-concrete, `MZERO.5`,
>   MA.2/MA.3 termwise inversion, and — decisively — the **`OZFIX.14` circularity**. The
>   "VERY HARD, matrix analog of `hcollapse`" difficulty was an artifact of the wrong premise.
> - **Crux #1's doubly-vs-singly analysis presupposes HS poles**, so it is about the **RDF**, not
>   the DCF. It stays valid for `h₁`.
> - It vindicates the hint recorded at the end of this entry — "the only genuinely axiom-free path
>   is the **matrix real-space Baxter/Wertheim–Thiele derivation**" — and shows that path is
>   *elementary* once (★) removes the inverses.
>
> **Superseded for the DCF by → Group MRS** (below): MRS.1 (matrix WH factorization — the only
> analytic input), MRS.2 (eq:OZ1_Baxter), MRS.3 ((★) + "no HS poles"), MRS.4 (real-space `q` + the
> `λ_ij` delta), MRS.5 (convolution ⇒ finite closed form).
>
> **What survives here.** MML.8 remains meaningful **only as the RDF (`h₁`) assembly**, whose
> `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` *does* carry the inverses ⇒ genuine HS poles ⇒ a genuine Mittag-Leffler
> series. **The inverses are the DCF/RDF dividing line.** MZERO and MML.5-concrete stay
> load-bearing for that object only. Everything below this box was written under the DCF premise —
> read it as RDF-scoped or historical.

**Statement.** The full identity `(I) MML.6 + (II) MML.4/MML.5 + (III) MML.7 = r·c^{inner}_{01}(r)` —
the N=2 matrix analog of the scalar Mittag-Leffler series in POLE.4/Group OZFIX. **Effort: VERY HARD**
(same scale as Y1.3 + Group OZFIX combined; the matrix Blum–Wertheim Laplace inversion).

**Depends on.** Y1.3 (Wiener–Hopf, ✓), MML.4–MML.7 (✓), MZERO.1 (infinitely many poles),
MML.5-concrete (the `detC` magnitude/growth bound), POLE.4/OZFIX (scalar collapse precedent).

**Crux #1 — settle singly-vs-doubly propagation. RESOLVED (pole-order argument, 2026-07-16, Lean).**
The stated identity mixes a **doubly**-propagated base (I) `[Q̂₀⁻¹KQ̂₀⁻ᵀ]₀₁` (Y1.5/Y1.6 = MML.6) with a
**singly**-propagated `B_k = adj/det′` (MML.2); `to_python.md` logs three options and the naive mix
blows up numerically (`ĉ₁₂ ≈ +4.5×10⁵`). The resolution is a **pole-order** fact, now proved:

- `doubly_prop_entry_eq` (`MixtureInnerDCF.lean`, axiom-clean): since `Q̂₀⁻¹ = adj/det`
  (`Matrix.inv_def`), the doubly-propagated entry is `[Q̂₀⁻¹KQ̂₀⁻ᵀ]₀₁ = (adj·K·adjᵀ)₀₁/det²` — an
  `N/det²` object.
- `double_pole_leading_coeff` / `_ne_zero` (axiom-clean): any `N/D²` with `D` a simple zero at `s_k`
  has an **order-2** pole, leading coefficient `N(s_k)/det′(s_k)²` (= `to_python.md` option (a)'s
  `B_k^{new}`), nonzero when `N(s_k)≠0`. **A double pole inverse-Laplace-transforms to `r·e^{−s_k r}`
  (an `r`-prefactor), absent from the stated simple-exponential term (II).**

**Conclusion.** The stated term-(II) form `Σ_k 2·Re[B_k·e^{−s_k r}]` (clean exponentials) is consistent
**only** with **singly**-propagated (simple-pole) HS terms. The two readings considered were:
- ~~**(S) fully-singly** — the DCF `c^{inner}`: base `K·[Q̂₀⁻¹]₀₁`, `B_k = adj/det′` (simple poles,
  clean `e^{−s_k r}`). Matches the stated form **and** the shipped Python `get_c1_inner` **and** the
  MSA outer-DCF continuation (direct-correlation `−βu`, single-propagated).~~
  **⚠ REFUTED (★): the DCF carries *no* `Q̂₀⁻¹`, so reading (S) corresponds to no object** — the
  agreement with `get_c1_inner` was agreement with the shipped *leading-order approximation*, not with
  the exact DCF. (The exact DCF is finite/piecewise — Group MRS.)
- **(D) fully-doubly** — the RDF `h₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` (Y1.6 `Hhat1`): base `[Q̂₀⁻¹KQ̂₀⁻ᵀ]₀₁` +
  **double**-pole HS terms `(α_k + β_k r)·e^{−s_k r}`. ✅ **This is the surviving reading** — MML.4–MML.8
  are RDF-scoped, and the pole-order lemmas are load-bearing exactly here.

~~**Recommendation (CORRECTED — was "fully-doubly").** For the DCF `c^{inner}` that MML.8 targets,
pursue **(S) fully-singly**: it is the coherent reading matching the stated series, the Python, and
the DCF's physical nature. MML.4's generic-`Bcoef` design already carries the singly instance
(`b_k_residue_coupled`). The doubly-propagated MML.6 amplitude is then correctly understood as the
**RDF** base (a valid, proven object — Y1.5/Y1.6 — but not term (I) of the DCF); MML.6's docstring
labels it accordingly.~~

**⚠ The (S) recommendation above is REFUTED too (2026-07-16, by (★)) — struck.** It assumed the DCF
carries *one* `Q̂₀⁻¹`. (★) `Ĉ₁ = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` shows it carries **none**, so the DCF has no HS
poles and no term (II) at all — **reading (S) corresponds to no object**. The correct statement of the
Crux #1 content is the `Q̂₀⁻¹`-**count** as the DCF/RDF dividing line:

| `Q̂₀⁻¹` factors | object | HS poles | inner form |
|---|---|---|---|
| **none** | **DCF `Ĉ₁`** (★) | none | **finite closed form**, piecewise at `λ_ij` — **Group MRS** |
| one | *(no object)* | simple | ~~`Σ B_k e^{−s_k r}`~~ — the shape that motivated (S) |
| **two** | **RDF `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹`** | **double** | `Σ (α_k+β_k r)·e^{−s_k r}` |

So the pole-order lemmas (`doubly_prop_entry_eq`, `double_pole_leading_coeff`) are **correct and
load-bearing for the RDF row**; only the DCF attribution was wrong. What the analysis got right — that
the inverse factors dictate the pole structure — is exactly the dividing line (★) confirms.

**Crux #2 — the collapse route.** Two candidates from the scalar `hcollapse` precedent
(`proof_notes_ozfix.md`):
- **Route A** (OZFIX.9): termwise `oz_forcing` Mittag-Leffler expansion at the resolvent poles.
  Unblocked, axiom-free *target*, but the per-pole coefficients do **not** factor cleanly (the
  `R_n = H_n − L_n` ratio oscillates), so the `σ≤r<2σ` region is a genuine ML identity of
  comparable difficulty; `r≥2σ` is per-pole exact.
- **Route B** (OZFIX.10, now powered by MA.2 `mittagLeffler_expansion_of_bounded_on_circles` +
  MA.3 `fourier_kernel_one_pole`): growing-contour Fourier inversion. **Favored** (user-confirmed
  for the scalar case): trades the physics-specific axiom for standard reusable math axioms, and
  MA.2/MA.3 already dissolved its arc-vanishing blocker.
  ~~**Recommendation:** pursue the **matrix Route B** — expand each entry of `Ĥ₁(s)` (or `c^{inner}`'s
  transform) via MA.2, Fourier-invert termwise via MA.3, control the sum/limit interchange (MML.5),
  and identify the result with `mixHS_series` (II) + base (I) + `p₀` (III).~~

**Crux #2 recommendation CORRECTED (2026-07-16, from the scalar `OZFIX.11`/`OZFIX.12` findings).**
The struck-through MA.2-pointwise plan above inherits the scalar route's **false-identity
obstruction** (`proof_notes_ozfix.md` `OZFIX.10`, 2026-07-16 update): termwise inversion of the
pointwise kernel makes the `O(R)` moment `W₁` enter with coefficient = the circle-mean of `Ĥ`,
which tends to `−1/ρ` (NOT 0) — no ML degree or pairing order fixes it. The corrected scalar
route decomposes instead into (i) a **per-pole-exact region** where the forcing vanishes and the
collapse factor is the WH factorization at zeros (`ρĈ(k_n)=1`, `OZFIX.11`, proved axiom-clean
with *no* contour machinery), plus (ii) a windowed contour argument on **doubly-smoothed kernels
only** (`OZFIX.12`). For MML.8 this transfers as:
1. **First concrete sub-piece — matrix WH factorization** (mixture analog of `OZFIX.2`):
   `Q̂₀(s)·Q̂₀ᵀ(−s) = I − Ĉ_mix(s)`, currently ABSENT from Lean (`YukawaWienerHopf.lean` has only
   residue-through-conjugation). Its det corollary `det(I−Ĉ_mix)(s_k) = 0` at `det(Q̂₀)` zeros is
   the mixture collapse factor; entry-wise collapse will need the adjugate-level version
   (cf. MML.1's `[Q̂₀⁻¹]₀₁ = −Q̂₀₀₁/det`).
2. Scope numerically whether the inner-DCF assembly has a per-pole-exact sub-region (the analog
   of `r ≥ 2σ` — geometry differs for the inner core, needs its own scoping pass) before any
   whole-series work.
3. Any contour step must use doubly-smoothed kernels; run the mixture analog of the circle-mean
   check (`Ĥ₁` entries' means → a `−1/ρ`-type matrix constant) FIRST to pin the obstruction shape.

**Prerequisite ordering — UPDATED 2026-07-17: all prerequisites now DONE.** MML.8 was gated behind
MML.5-concrete (the interchange / `Summable`) and, for an *unconditional* statement, MZERO.1's full
zero-family (then conditional on MZERO.5). **Both are now closed axiom-clean (2026-07-17):**
MML.5-concrete = `detF_mixHS_summable` (`HSMixture/MixtureMLBound.lean`, `Summable` wired end-to-end
from `detF_family_magnitude_bound`); MZERO.1 = `detC_zeros_infinite_unconditional`
(`HSMixture/MixtureChordFamily.lean`, parameter-only hypotheses), with MZERO.5's `hbound`/`hstep`
retired. So the "conditional MML.8 first, unconditional later" ordering is moot — an *unconditional*
statement is no longer blocked by any prerequisite, and **the only remaining content is Crux #2, the
collapse itself.**

**Lean.** `YukawaOZMix/MixtureInnerDCF.lean` — Crux #1 pole-order lemmas `doubly_prop_entry_eq`,
`double_pole_leading_coeff`, `double_pole_leading_coeff_ne_zero` (all axiom-clean).
**Term (II) + collapse reduction target now landed (2026-07-17, axiom-clean, build green):**
- **Both Laurent coefficients of the double pole certified.** `double_pole_leading_coeff` (earlier)
  gives the order-2 `β_k = N(s_k)/D′(s_k)²` (the `r`-prefactor). **`double_pole_reg_hasDerivAt` /
  `double_pole_reg_eventuallyEq` / `double_pole_second_coeff` (2026-07-18, axiom-clean)** give the
  order-1 `α_k = N′/E(s_k)² − 2·N(s_k)·E′/E(s_k)³` via the simple-zero factorization `D = (·−s_k)·E`
  (`E(s_k)=D′(s_k)`): the regularization `reg := N/E²` equals `(·−s_k)²·(N/D²)` on `𝓝[≠]s_k`, is
  genuinely differentiable at `s_k`, and `α_k = reg′(s_k)` (read through `hasDerivAt_iff_tendsto_slope`
  as the simple-pole residue `(z−s_k)f − A/(z−s_k) → α_k`). **This avoids the (Mathlib-absent-over-ℂ)
  L'Hôpital / 2nd-order-Taylor route** — the factorization `E` is exactly what
  `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` supplies for the analytic `det Q̂₀`. So the
  real-space term (II) `(α_k + β_k·r)e^{−s_k r}` is now fully pinned by the pole data.
- `mixHSterm2` / `mixHS_series2` — term (II) in the **doubly-propagated** RDF form
  `(α_k + β_k·r)·e^{−s_k r}` (the surviving reading). `mixHSterm2_eq` / `mixHS_series2_eq` identify
  them *definitionally* with the singly `mixHSterm`/`mixHS_series` at the `r`-absorbed coefficient
  `α_k + β_k·r`, so all of MML.4/5's summability API transfers for free.
- `mixHS_series2_summable` — convergence from the (DONE) MML.5-concrete growth bounds
  (`mixHS_summable_of_growth`), i.e. the collapse target is non-vacuous.
- `mixRDFInnerAssembly` (`(I) base + (II) doubly series + (III) p₀`) + `MixRDFInnerCollapse` (the
  `Prop` `assembly = r·h₁` on `(0,Rij)`) — the reduction target, the matrix analog of the scalar
  `CoreSeriesClosure` (OZFIX.12). **Deliberately not an axiom** (sub-family trap; needs pole
  exhaustion, which MZERO.1's infinitude does not give).

The collapse identity itself (discharging `MixRDFInnerCollapse` for the genuine pole family) is the
remaining (future) content — the bridge `assembly = r·h₁`, which per the OZFIX.22 template awaits a
matrix `oz_fixed_pt_unique` + matrix OZ★ (Group MRS).

**⟳ RE-EVALUATION 2026-07-29 (after matrix OZ★ + all-`N` pole-freeness landed).**  Two findings:
1. **The blocker "awaits matrix OZ★" is STALE** — matrix OZ★ is now built (`matOzStar_of_shellClaims`,
   `MixtureOzStar.lean`).  `MixtureRDFAntideriv.lean`'s "neither built yet (i)+(ii)" is stale for (ii).
2. **The non-circular OZFIX.22-template route is now assembled up to ONE scoped gap**
   (`MixtureRDFUniqueness.lean`, axiom-clean, ledger unchanged 7):
   * `MatOZHom` + `matOzStar_sub_hom` — difference of two `MatOZStar` solutions solves the homogeneous
     matrix radial OZ★ equation (matrix analog of `oz_linear_op_sub`).
   * `matOzStar_unique_of_injective` — **conditional matrix `oz_fixed_pt_unique`**: two solutions
     coincide given the matrix WH injectivity `hinj`.
   * `matStructureFactor_isUnit_of_det_ne_zero` — `det Q̂₀ ≠ 0` ⇒ `T₀ = Q̂₀(k)Q̂₀(−k)ᵀ` a unit
     (`det_eq_of_wienerHopf_factorization`), i.e. the **coercivity input** `hinj` needs is exactly what
     `mixtureDet_pole_free_N` + `pyhs_mixture_no_spinodal` supply.
   The gap `hinj` = matrix analog of the scalar KEPT axiom `radialShell_bounded_injective`
   (bounded/`L∞` WH injectivity; the `L∞`-Wiener-algebra gap, same class as `MA.13`, that `MA.12`'s
   `L²` Plancherel does not reach).  **✅ COMMITTED 2026-07-30** as `matRadialShell_bounded_injective`
   (`MixtureRDFUniqueness.lean`, one new **math** axiom, ledger `7 → 8` = 7 math + 1 physics).
   `matOzStar_unique` now discharges `hinj` via it — the **value route is UNCONDITIONAL** (no abstract
   injectivity hypothesis), resting on: the axiom + the coercive matrix symbol `MatSymbolCoercive`
   (`vᵀ(I − ρĈ(k))v ≥ ε‖v‖²`, the multicomponent no-spinodal — a hypothesis exactly as in the scalar
   axiom, whose invertibility `det Q̂₀ ≠ 0` is `matStructureFactor_isUnit_of_det_ne_zero` from
   `mixtureDet_pole_free_N`) + the solutions' regularity.  `matRadialSymbol` = the matrix radial sine
   symbol.  **✅ ABSTRACTED to `Analysis/MatrixRadialWienerHopf.lean` 2026-07-30**: the axiom is now
   the project-independent, raw-integral `FMSA.matRadialShell_bounded_injective` (arbitrary matrix
   kernel, no project defs — mirrors the scalar `radialShell_bounded_injective`);
   `MixtureRDFUniqueness.lean` re-exposes it as a theorem via the definitional bridges `matOZHom_raw`
   (operator = raw `∑ₖ(2π/r)∫∫`) and `matRadialSymbol` (symbol).  Bucket now **`Analysis` 7 +
   `HSMixture` 1** (the 1 = physics `pyhs_mixture_no_spinodal`).
3. **The literal pole-series collapse `MixRDFInnerCollapse` stays open/circular** (Fourier route,
   inherited from scalar `CoreSeriesClosure`); the OZ★+uniqueness route above targets the RDF *value*,
   not the pole-series representation.
**Crux #2 — CIRCULARITY WARNING inherited from the scalar case (2026-07-16, 2nd pass).** The scalar
`hcollapse` was pushed to completion this session and closed as a **negative result** (`OZFIX.14`,
`proof_notes_ozfix.md`): closing the contour on the pole sum is *value-neutral* — with `ρĈ(kₙ)=1` the
summands become `Res_k[S]·Ξ(k)` (`S := 1/(1−ρĈ)`, `Ξ` entire), the `1` of `S = 1+ρĤ` cancels **exactly at
every `R`** between the real line and the arc, and one is left with
`2πi·∑'Res = ρ∫_ℝ Ĥ(x)Ξ(x)dx` — the pole sum expressed **in terms of** the core value, which is the core
closure itself. So the scalar Route B does *not* prove the collapse; it restates it.
**Expect the same for MML.8**, whose (I)+(II)+(III) identity is the matrix analogue. Practical guidance:
1. Do **not** invest in the "expand `Ĥ₁` via MA.2 → invert via MA.3 → identify with `mixHS_series`" plan
   before checking whether the mixture *inner-core value* is an independent input (it almost certainly is).
2. The genuinely axiom-free path is the **matrix real-space Baxter/Wertheim–Thiele** derivation. Y1.3 +
   the matrix WH factorization are its Fourier half; the missing half is the real-space equation fixing
   the inner-core value for the concrete `q0_poly`-analogue.
3. Cheap legitimate alternative: axiomatize the **concrete, numerically-checkable series identity** (the
   mixture analogue of the scalar `CoreSeriesClosure`, `OzCollapseInner.lean`) instead of an abstract
   closure — same axiom count, strictly better checkability.
4. **Inherit the `Kterm` trap**: the natural `tsum` form of such an identity may be absolutely **divergent**
   (the scalar one is, for `u ≤ σ/2`), which would make it a FALSE and hence vacuous hypothesis. Check the
   decay exponent and add antiderivatives until it is `< −1` (scalar fix: `Kterm`, `‖·‖ ≲ ‖k‖^{−1−2u/σ}`).
5. The scalar **arc blocker was also refuted** (`OZFIX.10`, 2nd pass): a phase-split `e^{izb}` + two-regime
   bound suffices, no Van der Corput. If a matrix arc estimate is ever needed, use that technique.

**Status.** ◑ **Crux #1 (pole order / singly-vs-doubly) RESOLVED** (2026-07-16, axiom-clean);
**all prerequisites DONE** (2026-07-17: MML.5-concrete `detF_mixHS_summable`; MZERO.1
`detC_zeros_infinite_unconditional`; MZERO.5 retired). The collapse (Crux #2, VERY HARD) remains.
**Route status (2026-07-17):** the contour route is circular (scalar precedent `OZFIX.14`), so the
realistic path is the matrix real-space Baxter/Wertheim–Thiele derivation. The scalar precedent for
that path is now much sharper — `OZFIX.15–20` completed the *entire* scalar analytic core
(`ψ⋆Q₊⋆Q₋=φ`, the bridge, `F[K]=Ĉ`, `ρK=q0(v)−∫q0q0`, the 2D reindex), all axiom-clean — **but
`OZFIX.17` then exposed a genuine analytic OBSTACLE**: the assembly still needs the Baxter poles in
the open LHP ⇔ `baxterPsi` decay (simple `L¹` contraction REFUTED, `∫₀^σ|q0|≥1` for `η≳0.13`), which
is separate hard spectral content (`POLE.4`/`h_explicit`) not supplied by the analytic core. **The
matrix RDF collapse would inherit the matrix analog of exactly this decay input.** An axiom swap on
the concrete, numerically-checkable series identity (items 3–4 above) stays the cheap legitimate
alternative.

**OZFIX.22 template (2026-07-17) — the scalar reverse-assembly is now executed, and it is exactly
MML.8's recipe.** The scalar `oz_h`/`baxterPsi` *is* the RDF analog (the total-correlation `h`), and
`OZFIX.22` (`HardSphere/OzCoreClosure.lean`, full build green) retired `oz_core_closure` +
`oz_h_exterior_regularity` to **theorems** — consolidating the 3 OZ physics axioms to 2 — via the
single bridge `oz_h = baxterPsi/·` (proved by feeding the *constructed* `baxterPsi`, a bounded
exterior-continuous `OzFixedPt`, into `oz_fixed_pt_unique`), with the collapse then falling out of the
real-space OZ★ identity. Three ways this transfers to MML.8:
1. **Proven recipe.** MML.8's RDF collapse is the matrix version step-for-step: construct the explicit
   matrix real-space solution → show it is a bounded exterior-continuous matrix OZ fixed point →
   matrix-uniqueness bridge → collapse from the matrix OZ★. Not "VERY HARD/circular" anymore — a
   transcription task once the matrix ingredients exist.
2. **Axiom-swap is now a blessed pattern, not a fallback.** The hard decay input didn't get *proved* —
   it got cleanly isolated into the new axiom `baxter_exterior_regularity`, one explicit
   boundedness/decay statement about the *constructed* `baxterPsi` (`|baxterPsi r| ≤ C` on `[σ,∞)`),
   epistemically superior to the opaque physics axioms it replaced. MML.8's collapse can land as a
   theorem modulo the **matrix analog** of exactly this axiom.
3. **No decay-free route exists (definitive).** OZFIX.22's writeup refutes the earlier "decay-free
   3→2" designs: bounded OZ-uniqueness is *irreducibly* Wiener–Hopf (`∫₀^σ|q0| ≥ 1` for `η≳0.13`), so
   the difference of two bounded fixed points solves a non-causal homogeneous equation whose
   only-zero property **is** the pole-in-LHP fact. ⇒ MML.8 must **not** hunt a decay-free matrix
   route; the matrix decay axiom is unavoidable.

**Still needed before MML.8 can run the recipe** (what OZFIX.22 got for free in the scalar case):
a **matrix `oz_fixed_pt_unique`** (matrix OZ fixed-point uniqueness, irreducibly Wiener–Hopf, not yet
built for the mixture) and a **matrix OZ★** / matrix real-space Baxter identity for the
inverse-carrying RDF `h₁` — Group MRS is building the mixture real-space infra (MRS.3 (★) done,
MRS.4/5 in progress) but on the *DCF* side. Once both exist, MML.8's collapse is a mechanical
transcription of OZFIX.22 modulo the matrix decay axiom. **Priority is unchanged: RDF-only, off the
DCF path** — the template lowers MML.8's difficulty ceiling, not its priority.

**⇒ SHARPENED 2026-07-24 by MML.9 (below): the "matrix OZ★" MML.8 still needs is a
*hard-sphere* statement, not a Yukawa one.** `Ĥ₁ = S₀·Ĉ₁·S₀` with `Ĉ₁` HS-pole-free (MRS.3) and
finite (MRS.5) ⇒ every HS pole of the first-order RDF is contributed by the two `S₀ = (I−Ĉ₀)⁻¹`
factors, which contain **no Yukawa data at all**. The Yukawa half of MML.8 is therefore already
closed by Group MRS; the residual collapse content is the mixture **hard-sphere** RDF.

---

### Task MML.9 — the structure-factor form `Ĥ₁ = S₀·Ĉ₁·S₀`, and where the RDF's HS poles come from

**Statement.** Solve the same first-order OZ equation MRS.2 solves for the DCF, but for the RDF:
from `Ĥ₁·T₀ = S₀·Ĉ₁` (`hoz`) and `T₀·S₀ = I` (`hTS`, the zeroth-order OZ `S₀ = (I−Ĉ₀)⁻¹`),

    Ĥ₁ = Ĥ₁·(T₀·S₀) = (Ĥ₁·T₀)·S₀ = (S₀·Ĉ₁)·S₀ = S₀·Ĉ₁·S₀ .

Physically: **the first-order RDF is the first-order DCF dressed on both sides by the hard-sphere
structure factor** `S₀ = I + Ĥ₀`. Pure matrix algebra, and with *strictly weaker* hypotheses than
MRS.2's `star_of_first_order_oz` (no MRS.1 factorization, no MRS.7 symmetry).

**Why it matters for MML.8.** Combined with the two established facts

* **(★)** `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` carries no `Q̂₀⁻¹` ⇒ the first-order **DCF has no HS poles**
  (MRS.3 `star_entry_differentiableAt`) and is a finite closed form (MRS.5), and
* `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` (MRS.6) ⇒ `det T₀ = det Q̂₀(k)·det Q̂₀(−k)`,

this **localizes the RDF's entire HS-pole content in the two `S₀` factors** — objects built from the
hard-sphere DCF `Ĉ₀` alone, with no Yukawa data in them. So MML.8's remaining collapse content is a
*hard-sphere* mixture statement; the Yukawa factor sandwiched between the two `S₀`s is finite and
pole-free, already delivered by Group MRS. This is a genuine narrowing of the "still needed" list
above, not a new route.

**Consequence — the pole set is reflection-symmetric, matching MML.5-concrete's convention.**
`det T₀ = det Q̂₀(k)·det Q̂₀(−k)` is invariant under `k ↦ −k`, so the RDF's HS poles are Group MZERO's
`det Q̂₀` zeros **together with their reflections**. That is exactly the "mirror pairing" the MML.8
completeness caveat refers to, and it is the same reflection `detF_mixHS_summable`
(`MixtureMLBound.lean`) already builds in (`s_k := −(g n)`, `Re s_k > 0`).

**Second, independent proof of Crux #1.** `rdf_entry_eq_num_div_det_sq` derives the `N/det²` shape —
hence the order-2 pole, hence term (II)'s `r`-prefactor — **from the OZ equation**, never mentioning
`B₁`. The original Crux #1 argument (`doubly_prop_entry_eq`) runs through Y1.6's
`Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹`. Two independent routes to the same double-pole conclusion.

**The DCF/RDF dividing line as a single hypothesis.** `rdf_entry_differentiableAt` is the exact
counterpart of MRS.3's `star_entry_differentiableAt`, with one added hypothesis: `det T₀(k) ≠ 0`.
The DCF statement pointedly has no such hypothesis. That one hypothesis *is* the dividing line.

**The four-term dressing — the HS poles' exact residence (added 2026-07-24).** Writing the structure
factor as `S₀ = I + Ĥ₀` and expanding `Ĥ₁ = S₀·Ĉ₁·S₀` (`structureFactorDressing`,
`rdf_four_term_dressing`) gives

    Ĥ₁ = Ĉ₁ + Ĥ₀·Ĉ₁ + Ĉ₁·Ĥ₀ + Ĥ₀·Ĉ₁·Ĥ₀ ,

i.e. in real space `h₁ = c₁ + h₀⋆c₁ + c₁⋆h₀ + h₀⋆c₁⋆h₀`. Since `Ĉ₁` is finite and HS-pole-free
(MRS.3/MRS.5), the undressed term carries **no** HS pole, so `rdf_sub_dcf_is_dressed`
(`Ĥ₁ − Ĉ₁ = Ĥ₀·Ĉ₁ + Ĉ₁·Ĥ₀ + Ĥ₀·Ĉ₁·Ĥ₀`) locates **every** HS pole of the first-order RDF in the three
`Ĥ₀`-dressed terms. This is the sharpest form of MML.9's "the residual collapse content is
hard-sphere": MML.8's target `assembly = r·h₁` is term-by-term over exactly these three `h₀`-dressed
convolutions, and the mixture HS RDF `h₀` (= `S₀`'s pole content) is the only object whose ML
collapse is still owed. The Fourier identity is mechanical (`noncomm_ring`); the real-space
convolution reading of `⋆` is the still-missing transform step — the same transform gap that Group
MRS's finite-form assembly (MRS.5) is working through on the DCF side.

**Cofactor-free Laurent coefficients.** `double_pole_second_coeff` states `α_k` through the analytic
cofactor `E` of the simple-zero factorization `D = (·−s_k)·E`. `E` is auxiliary — a consumer (the
concrete `detF` family, or numerics) holds `D = det Q̂₀` and its derivatives, not `E`. Eliminating it
via `D′(s_k) = E(s_k)` and `D″(s_k) = 2·E′(s_k)` gives both coefficients in terms of `D` alone:

    β_k = N(s_k)/D′(s_k)²                                  (`double_pole_leading_coeff`)
    α_k = N′(s_k)/D′(s_k)² − N(s_k)·D″(s_k)/D′(s_k)³        (`double_pole_second_coeff_deriv_form`)

⚠ **The `D″` step needs only `ContinuousAt E′`, not a second derivative of `E`.** `D′ = E + (·−s_k)·E′`,
and the extra linear factor supplies the missing differentiability all by itself: `(·−s_k)·g` has
derivative `g(s_k)` at `s_k` for merely *continuous* `g` (`hasDerivAt_sub_mul_of_continuousAt`, one
line from the slope characterization). Attempting this with a `ContDiff`/2nd-order-Taylor hypothesis
on `E` is unnecessary work — the same "the linear factor does the analysis for you" observation that
made `double_pole_second_coeff` avoid the (ℂ-absent) L'Hôpital route.

**Depends on.** MRS.2 `oz1_C1_eq` (the dual it mirrors), MRS.3 (★), MRS.6 factorization,
MML.8 `double_pole_leading_coeff` / `double_pole_second_coeff`. Nothing new is assumed.

**Lean.** New file `YukawaOZMix/MixtureRDFStructureFactor.lean` (ns `FMSA.MixtureRDF`), all
axiom-clean, full build green:
`oz1_H1_eq`, `structureFactor_eq_inv` (`T₀⁻¹ = S₀` — no invertibility hypothesis needed,
`Matrix.inv_eq_right_inv`), `rdf_eq_inv_conj`, `inv_conj_entry_eq` (the transpose-free sibling of
`doubly_prop_entry_eq`), `rdf_entry_eq_num_div_det_sq`, `det_eq_of_wienerHopf_factorization`,
`rdf_entry_star_eq` (capstone), `triple_entry_eq`, `adjugate_entry_differentiableAt` (`Fin 2`),
`rdf_entry_differentiableAt`, `rdf_entry_double_pole`; then
`hasDerivAt_sub_mul_of_continuousAt`, `factor_hasDerivAt`, `factor_hasDerivAt_at_zero`,
`factor_second_hasDerivAt`, `double_pole_second_coeff_deriv_form`; and the dressing
`structureFactorDressing`, `rdf_four_term_dressing`, `rdf_sub_dcf_is_dressed`.

**Lean pitfalls hit.** (1) `fin_cases p <;> fin_cases q` leaves indices as `⟨1, ⋯⟩`, which does **not**
match the numeral `1` for `rw` — use `Fin.forall_fin_two.2 ⟨…⟩` on a `∀ p q` conclusion instead.
(2) `field_simp` on the slope goal leaves a `s_k * (1 − 1) * g s_k` residue; close with `ring`.

**Status.** ✓ **DONE (2026-07-24), axiom-clean.** Does **not** discharge `MixRDFInnerCollapse` — it
shows which poles are being summed (`S₀`'s, at `det Q̂₀`'s zeros and their reflections) and that
their order is 2, and it narrows MML.8's residual input to the hard-sphere side.

---

### Task MML.10 — term (II)'s coefficient factors as `HS residue × (finite Yukawa DCF) × HS residue`, and the mixture collapse factor

**Statement.** MML.9 says the RDF's HS poles all come from the two `S₀` factors. This task turns
that into an identity between *numbers*, and then extracts the mixture analog of the scalar
collapse factor.

**(a) The residue-matrix sandwich.** Define the hard-sphere structure factor's residue matrix at a
simple zero `s_k` of `det T₀`,

    R_k := det′T₀(s_k)⁻¹ • adj T₀(s_k) .

`structureFactor_entry_residue` certifies that this **is** the residue of `S₀ = T₀⁻¹` entrywise
(`inv_apply_eq_adj_div_det` + `residue_of_simple_pole`): **one `S₀` factor ⇒ one simple pole**, so
the RDF's two factors give the order-2 pole of MML.9's `rdf_entry_double_pole`. Then
`num_div_det_sq_eq_sandwich` (pure `smul` algebra) rewrites the order-2 Laurent coefficient as

    β_k = (R_k · Ĉ₁(s_k) · R_k) i j ,

and with (★) substituted (`rdf_double_pole_coeff_star`)

    β_k = (R_k · Q̂₀(−s_k) · B₁(s_k) · Q̂₀ᵀ(−s_k) · R_k) i j .

`R_k` is built from `T₀ = I − Ĉ₀` alone — **no Yukawa data whatsoever** — while `Ĉ₁(s_k)` is a plain
evaluation of the finite, HS-pole-free (★) closed form (MRS.3/MRS.5). So the MML.9 narrowing is no
longer only a structural reading: term (II)'s coefficients are *literally* factored into hard-sphere
spectral data × closed-form Yukawa data.

**(b) The mixture collapse factor — MML.8 Crux #2's "first concrete sub-piece", now trivial.**
The scalar `hcollapse` (`OZFIX.11`) turns on `ρĈ(kₙ) = 1`, i.e. `1 − ρĈ` vanishes at the pole, which
kills the forcing term per pole. MML.8's own scoping named the mixture counterpart as its first
concrete sub-piece — "`det(I−Ĉ_mix)(s_k) = 0` … entry-wise collapse will need the **adjugate-level**
version". Both now land in two lines:

* the determinant statement is `det_eq_of_wienerHopf_factorization` (MML.9) — MRS.6's
  `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` with `T₀ = I − Ĉ₀` its `Cmix0` definition;
* the adjugate-level statement is `hsResidue_annihilates`: `R_k·T₀(s_k) = T₀(s_k)·R_k = 0`,
  straight from Mathlib's `adjugate_mul` / `mul_adjugate` (`adj A·A = det A • I`) at `det A = 0`.

Rewriting with `T₀ = I − Ĉ₀` gives `hsResidue_eq_mul_cmix`:

    R_k = R_k · Ĉ₀(s_k) = Ĉ₀(s_k) · R_k ,

**the literal matrix transcription of `ρĈ(kₙ) = 1`** — the residue matrix is a fixed point of
multiplication by the hard-sphere DCF at the pole. (Scalar check: at `N = 1`, `R_k` is a nonzero
number and cancels, leaving `Ĉ₀(s_k) = 1`.)

⚠ **Why this was cheap and the 2026-07-17 scoping expected it to be expensive.** That scoping listed
the sub-piece as needing a matrix Wiener–Hopf factorization "currently ABSENT from Lean". MRS.6/MRS.7
supplied the factorization in the meantime, and once `hsResidueMatrix` is *defined through the
adjugate*, the collapse factor is a Mathlib one-liner rather than an analytic construction. The
lesson is the same as MML.5's: re-check a stale blocker against what has landed since.

**Depends on.** MML.9 (`rdf_entry_double_pole`, `det_eq_of_wienerHopf_factorization`), MML.2's
`residue_of_simple_pole` route, Y1.1's `inv_apply_eq_adj_div_det`, MRS.3 (★), MRS.6.

**Lean.** `YukawaOZMix/MixtureRDFStructureFactor.lean`, axiom-clean, full build green:
`hsResidueMatrix`, `num_div_det_sq_eq_sandwich`, `structureFactor_entry_residue`,
`rdf_double_pole_coeff_sandwich`, `rdf_double_pole_coeff_star`, `hsResidue_annihilates`,
`hsResidue_eq_mul_cmix`.

**Lean pitfall.** In `hsResidue_eq_mul_cmix`, `rw [hT] at hL hR` also rewrites the `T0` *inside*
`hsResidueMatrix T0 Dprime`, desynchronising the hypothesis from the goal; and
`linear_combination (norm := module)` then reports the useless `⊢ 2 = 0`. Fix: never rewrite the
hypotheses — build `R*T₀ = R − R*C₀` as its own `have` (there `rw [hT]` rewrites *both* sides
uniformly, which is harmless), substitute `hL`, and finish with `sub_eq_zero.mp`.

**Status.** ✓ **DONE (2026-07-24), axiom-clean.** Still does not discharge `MixRDFInnerCollapse`.
What MML.8 now has: the pole set (MZERO zeros + reflections), the pole order (2), both Laurent
coefficients in closed form (MML.9), the coefficients factored HS × Yukawa (a), and the per-pole
collapse factor (b). What it lacks is unchanged and is the hard part: the **real-space** step
identifying the summed series with the inner-core value — the matrix analog of `OZFIX.12`/`OZFIX.22`,
now visibly a hard-sphere-only obligation.

---

### Task MML.11 — the *concrete* term-(II) data: one pole family carrying poles, coefficients and summability

**Statement.** MML.9/MML.10 pinned the RDF's pole structure for free matrices. MML.11 produces the
concrete instance for the actual `N=2` mixture: a single explicit pole family on which the pole
locations, the order-2 Laurent coefficient, and MML.5's summability all live simultaneously.

**⚠ Which of the two `Ĥ₁` forms to instantiate — a real choice, not bookkeeping.** MML.9's
`Ĥ₁ = S₀·Ĉ₁·S₀` has denominator `det T₀ = det Q̂₀(k)·det Q̂₀(−k)`. Making *that* concrete would
require a zero of `det Q̂₀` to remain a **simple** zero of the product, i.e. `det Q̂₀(−s_k) ≠ 0` — a
reflection-asymmetry fact nobody has proved, and one that MZERO does not supply (MZERO gives
infinitude, not asymmetry). Y1.6's `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` has denominator `det Q̂₀(k)²`, so its
poles are the `det Q̂₀` zeros **directly** and simplicity there is exactly `det′ ≠ 0` — which the
strengthened MML.5 family now exports. The two forms agree (`oz1_H1_eq` vs `Hhat1_spec`); only the
Y1.6 one has an available concrete instance. **This is why MML.5's non-vanishing clause was worth
adding: it is the enabling hypothesis for MML.11, not a cosmetic tidy-up.**

**The chain.**
- `hhat1_entry_eq_num_div_det_sq` — `Ĥ₁ i j = ((adj Q̂₀)ᵀ·B₁·adj Q̂₀) i j / (det Q̂₀)²`, from
  `(Mᵀ)⁻¹ = (det M)⁻¹ • (adj M)ᵀ` (`Matrix.adjugate_transpose` + `Matrix.det_transpose`). The
  transposed sibling of MML.9's `inv_conj_entry_eq` and of `doubly_prop_entry_eq`.
- `num_div_det_sq_eq_transpose_sandwich` + `hhat1_double_pole` — the order-2 coefficient is the
  residue-matrix sandwich `β_k = (R̃ᵀ·B₁(s_k)·R̃) i j`, `R̃ = det′(s_k)⁻¹ • adj Q̂₀(s_k)`
  (MML.10's `hsResidueMatrix`, now at `Q̂₀` instead of `T₀`).
- **`q0Residue_zero_one` — the loop closes on MML.5/MML.2**: `R̃ 0 1 = −q01(s_k)/det′(s_k)`. The
  `(0,1)` entry of MML.10's *matrix* residue is literally the `Bcoef` that `detF_mixHS_summable`
  sums and that `detF_Bcoef_eq_b_k_residue` certified to be MML.2's `B_k`. Matrix-level and
  scalar-level residues are **one object**, not two parallel constructions. (Proof: MML.1's
  `adjugate_fin_two_zero_one` `adj M 0 1 = −M 0 1`, plus `q01_eq`.)
- `detF_rdf_pole_family` — the capstone: for physical data and `rdist > max(σ₀/2,(σ₁−σ₀)/2)` there
  is **one** injective `g` with (i) `detF (g n) = 0 ∧ g n ≠ 0 ∧ det′(g n) ≠ 0`, (ii) the order-2
  pole of `Ĥ₁` at each `g n` with coefficient `rdfBeta P B1f (g n) i j`, (iii) `Summable` for the
  reflected series with coefficient `q0Residue P (g n) 0 1`.

**Non-vacuity.** The only hypothesis on the Yukawa side is entrywise continuity of `B₁`, satisfied
by any continuous matrix (and supplied in the physical case by the finite (★) closed form,
MRS.3/MRS.5); the parameter hypotheses are `P.Phys` + the `rdist` threshold, both satisfiable. The
coefficient clause states the *value* of the limit, not that it is nonzero — order-2-ness for a
particular `B₁` is `double_pole_leading_coeff_ne_zero` at `Num(s_k) ≠ 0`, separately.

**Depends on.** MML.5 (strengthened family), MML.10 (`hsResidueMatrix`), MML.2/MML.1, Y1.6
(`Hhat1`), MML.8's `double_pole_leading_coeff`.

**Lean.** New file `YukawaOZMix/MixtureRDFPoleData.lean` (ns `FMSA.MixtureRDF`), axiom-clean, full
build green: `hhat1_entry_eq_num_div_det_sq`, `num_div_det_sq_eq_transpose_sandwich`,
`triple_entry_transpose_eq`, `adjugate_entry_continuousAt`, `hhat1_double_pole`, `q0Mat`,
`q0Mat_det` (`rfl`), `q0Residue`, `q0Residue_zero_one`, `rdfBeta`, `q0Mat_entry_continuousAt`,
`detF_rdf_pole_family`. `detF_mixHS_summable` (`MixtureMLBound.lean`) correspondingly upgraded to
export the simple-zero triple.

**Lean pitfalls.** (1) Mathlib has no `continuousAt_finset_sum`/`ContinuousAt.fun_sum` — use
`tendsto_finsetSum` (the `_finset_sum` spelling is deprecated), which applies directly because
`ContinuousAt f x` is definitionally the right `Tendsto`. (2) After `Summable.congr` the goal
carries unreduced beta redexes `(fun n ↦ …) n`, so `rw [q0Residue_zero_one]` fails to find its
pattern; `simp only [mixHSterm, q0Residue_zero_one]` beta-reduces and closes it.

**Status.** ✓ **DONE (2026-07-24), axiom-clean.** Term (II) is now fully concrete. MML.8's residual
content is exactly the real-space identification (below), unchanged.

---

### Task MML.12 — the collapse *region*: a scoping correction, and what the ML series can never reach

**Trigger.** `MixRDFInnerCollapse` quantifies `∀ r, 0 < r → r < R_ij`, but term (II)'s convergence is
established only for `r > max(σ₀/2, (σ₁−σ₀)/2)` (MML.5's gate exponent
`p(r) = max((σ₀−σ₁−2r)/σ₁, (−σ₀−2r)/σ₁)` is `< −1` exactly there). The two ranges were never
reconciled.

**(1) Scoping correction — state the collapse on the annulus.** Below the threshold there is no
summability result, and the evidence points the wrong way: the scalar precedent (`Kterm`, `OZFIX.12`)
is genuinely **divergent** for `u ≤ σ/2`, and MML.5's own numerics measured `p(0.45) = −0.867 > −1`
at `σ = [0.8, 2.3]`. Lean's `tsum` of a non-summable family is the junk value `0`, so
`mixHS_series2` becomes `0` there and the predicate silently degenerates into `base r + p0 = r·h₁(r)`
— a *different* claim, with no reason to hold. **This is the `Kterm` vacuity trap the MML.8 notes
warned about (Crux #2, item 4), reaching MML.8 through the quantifier range rather than through the
summand** — which is why the earlier check ("add antiderivatives until the decay exponent is `< −1`")
did not catch it: the summand is fine, the *interval* is not.

⚠ **Honest disposition: this does not prove the `(0, R_ij)` form false.** It shows its content below
the threshold is unsupported and junk-valued. The fix is to state the identity where term (II)
converges — `MixRDFInnerCollapseAnnulus` — and `threshold_lt_contact` shows that region is **never
empty** (`max(σ₀/2, (σ₁−σ₀)/2) < (σ₀+σ₁)/2` for every physical pair, both branches strict from
`0 < σ₁` and `0 < σ₀`), so the restriction costs no generality.

**(2) Structural — the ML series only ever reaches the OUTER inner-core piece.** The threshold's
second branch is *exactly* the inner-core knot:

    (σ₁ − σ₀)/2  =  Mix.lam 0 1  =  λ₀₁ .

Hence `λ₀₁ ≤ max(σ₀/2, λ₀₁) = threshold` (`lam01_le_threshold`), and the entire collapse region lies
inside `(λ₀₁, R₀₁)` — the **outer** of the two pieces into which the unlike-pair inner core splits
(IB.4 / MPOLY.5: `(0,λ)` degree 1, `(λ,R)` degree 4). ⇒ **the HS-pole Mittag-Leffler series can never
certify the inner piece `(0, λ₀₁)`, whatever happens to MML.8's real-space step**; that piece must
come from Group MRS's finite closed form. The coincidence is not accidental in the other direction
either: MML.5 recorded that the `(σ₁−σ₀)/2` branch "binds only when `2σ₀ < σ₁`", and
`σ₀/2 ≥ λ₀₁ ⟺ 2σ₀ ≥ σ₁` — the same condition, now with a geometric reading.

This also sharpens the DCF/RDF division of labour: Group MRS covers the whole inner core with a
finite closed form; the RDF's ML series covers only its outer piece. They are not two routes to the
same interval.

**Depends on.** MML.5 (the threshold and its numerics), MML.11 (the concrete family), IB.4/MPOLY.5
(the `λ₀₁` split), `Mix.lam`/`Mix.R` (`InnerDecomp.lean`).

**Lean.** `YukawaOZMix/MixtureRDFPoleData.lean`, axiom-clean, full build green: `rdfCollapseThreshold`,
`contactR01`, `lam01`, `lam01_le_threshold`, `lam01_lt_of_threshold_lt`, `threshold_lt_contact`,
`threshold_pos`, `exists_mem_collapse_region`, `MixRDFInnerCollapseAnnulus`,
`mixRDFInnerCollapseAnnulus_of_collapse` (the `(0,R)` form implies the annulus form; the converse
fails, and the difference is precisely the junk-valued region).

**Status.** ✓ **DONE (2026-07-24), axiom-clean.** MML.8's target is now stated on the interval where
its own term (II) converges, and its reach is bounded below by `λ₀₁` for good.

---

### Task MML.13 — the `n = 1` soundness bridge for MML.9–MML.12

**Why.** MML.8's collapse is unproved and MML.9–MML.12 are matrix statements with **no consumer
yet**. The one mechanical test such a body of statements admits is the degenerate case: instantiate
at a single component and check it reproduces the *known* scalar theory rather than something new.
Same test MRS.0b ran on the consumer-less physics axiom `pyhs_mixture_no_spinodal`
(`MixtureNoSpinodalN1.lean`), and the project's record says it earns its keep — the statement bugs in
MA.5 (junk-valued zero set), MA.2 (partial-sum grouping) and `baxter_exterior_regularity` clause 6a
(a jump at `σ`) were all caught by confronting a case whose answer was independently known.

**Check 1 — the collapse factor.** MML.10's `R_k = R_k·Ĉ₀(s_k)` at `Fin 1` yields `Ĉ₀(s_k) = 1`, the
scalar `ρĈ(kₙ) = 1` behind `OZFIX.11` (`cmix_eq_one_fin_one`, routed through the matrix identity,
cancelling the nonzero `det′` via `hsResidueMatrix_fin_one`: `adj = 1` so `R = det′⁻¹ • I`).

⚠ **Read this correctly — it is a consistency check, not independent confirmation.** At `Fin 1` the
conclusion is already forced by `det T₀(s_k) = 0` alone (`cmix_eq_one_fin_one_of_det`, via
`Matrix.det_fin_one`, no residue matrix in sight). So the two routes are not independent evidence.
What the test rules out is a **sign slip, a transposition error, or a wrong `det′` power** in
`hsResidue_eq_mul_cmix` — any of those would land the first route somewhere else and contradict the
second. That is what a degenerate-case test can check, and all it can check; overstating it as
"two independent confirmations" would be wrong.

**Check 2 — the pole order.** `hhat1_fin_one_entry`: Y1.6's `Ĥ₁` at one component is the scalar
`B₁/(det Q̂₀)²`, a genuine **double** pole at a simple zero — matching the `Q̂₀⁻¹`-count reading (two
inverse factors ⇒ order 2) that MML.8's Crux #1 rests on.

**Check 3 — the term-(II) coefficient.** `hhat1_double_pole_fin_one`: MML.11's residue-matrix
sandwich `β_k = (R̃ᵀ·B₁(s_k)·R̃) i j` degenerates to the elementary scalar double-pole coefficient
`β_k = B₁(s_k)/det′(s_k)²`. **No matrix artifact survives** — the outcome the general formula had to
produce and did not have to.

**Non-vacuity certificate.** A degenerate-case test proves nothing if its own case is empty, and this
repo has produced true-but-vacuous statements before (`b4_origin_bc_abstract`,
`b9_d_ij_nonzero_example`). So the witness is recorded as a Lean `example`: `Q̂₀(z) = !![z − 1]` has a
simple determinant zero at `s_k = 1` with `det′ = 1 ≠ 0`, and a constant `B₁` is continuous — all
four hypotheses of `hhat1_double_pole_fin_one` (hence of `hhat1_double_pole`) simultaneously
satisfied.

**Lean.** `YukawaOZMix/MixtureRDFPoleData.lean`, axiom-clean, full build green:
`hsResidueMatrix_fin_one`, `cmix_eq_one_fin_one`, `cmix_eq_one_fin_one_of_det`,
`hhat1_fin_one_entry`, `hhat1_double_pole_fin_one`, + the non-vacuity `example`.
Mathlib inputs: `Matrix.adjugate_fin_one` (`adj A = 1`), `Matrix.det_fin_one`, `Matrix.one_apply_eq`.

**Status.** ✓ **DONE (2026-07-24), axiom-clean. All three checks pass, no statement bug found.**
Unlike MA.5/MA.2/clause-6a, this bridge did **not** turn up a defect — a clean pass, recorded so that
a future session does not re-run it. It does not advance the collapse itself.

---

### Task MML.14 — matrix real-space infrastructure I: the antiderivative tower of term (II)

**The step past scaffolding.** MML.9–MML.13 characterised MML.8's remaining obligation; MML.14 begins
**building** the infrastructure that obligation needs. The scalar `hcollapse` (`OZFIX.11`/`OZFIX.12`)
runs on an **antiderivative tower** over the per-pole Fourier residue —
`residue_term → Hterm → Kterm` (`OzCollapseInner.lean`) — each rung one integration in `r` and one
power of `1/‖k‖` better in summability, so that `Kterm` (two rungs) is summable at **every** `u > 0`
and the inner region (sampled down toward `r = 0`) can be reached. MML.14 is the mixture counterpart.

**The key structural fact (proved).** The mixture per-pole term is already in hand as
`mixHSterm2 α β s r = (α + β·r)·e^{−s·r}` (the double pole's envelope, MML.8/MML.9/MML.11). Its tower
needs **no new function shapes**:

> the family `{(a + b·r)·e^{−s·r} : a, b ∈ ℂ}` (`expLinTerm`) is **closed under antidifferentiation
> in `r`**, with coefficient map `antiCoeff s (a,b) = (−a/s − b/s², −b/s)`.

`expLinTerm_antideriv_hasDerivAt` (`s ≠ 0`) proves `expLinTerm (antiCoeff s a b) s` is an
antiderivative of `expLinTerm a b s` — the mixture analog of `Kterm_hasDerivAt`. Iterating gives the
two concrete rungs `mixHSAntideriv1` (matrix `Hterm`) and `mixHSAntideriv2` (matrix `Kterm`), with the
`HasDerivAt` chain `mixHSAntideriv2 → mixHSAntideriv1 → mixHSterm2`.

**Why the tower buys summability, made precise.** `expLinTerm_norm`:
`‖(a+b·r)·e^{−s·r}‖ = ‖a+b·r‖·e^{−r·Re s}`, so on the reflected family (`Re s_n > 0`) the exponential
is `≤ 1` for `r ≥ 0` (`expLinTerm_norm_le_of_re_nonneg`) and the size is set by the coefficient. Each
`antiCoeff` divides by `s`: `antiCoeff_snd_norm` (`‖B‖ = ‖b‖/‖s‖`) and `antiCoeff_fst_norm_le`
(`‖A‖ ≤ ‖a‖/‖s‖ + ‖b‖/‖s‖²`). **Two rungs ⇒ two spare powers of `1/‖s_n‖`**, which should push the
summability exponent below `−1` *without* the `rdist > max(σ₀/2, λ₀₁)` threshold the untowered series
(MML.5) needs — the mixture form of `Kterm`'s all-`u>0` summability, and the mechanism that reaches
the inner core.

**Summability, reduced to one coefficient bound.** `mixHSAntideriv2_eq_mixHSterm` writes the `Kterm`
rung as a plain `mixHSterm` at its `r`-absorbed coefficient, and `mixHSAntideriv2_summable_of_growth`
then gives `Summable` from linear pole growth + a `‖s_n‖^p` bound (`p < −1`) on that coefficient
(reusing `mixHS_summable_of_growth`). **The one remaining analysis obligation is isolated as the
hypothesis `hbound`**: magnitude bounds on the double-pole coefficients `α_n`, `β_n` in `‖s_n‖` — the
mixture analog of the scalar `residue_term_norm_bound`, which MML.5's `detF_family_magnitude_bound`
did for the *simple*-pole residue `B_k = −q01/det′` but not yet for the double-pole `α, β`.

**Roadmap — the remaining rungs of the infrastructure.**
1. ✅ **Rung 1 DONE (2026-07-24) — the coefficient step is discharged.** See the Rung 1 note below.
   What remains of it is only the concrete `α, β` bounds (the mixture `residue_term_norm_bound`).
2. **The collapse predicate** — a matrix `CoreSeriesClosure`: an explicit, always-summable series
   identity (over the `Kterm` rung) equal to a polynomial in `r`, carried as a hypothesis exactly as
   the scalar `CoreSeriesClosure` is (⚠ the `Kterm`-form, not `Hterm`, to dodge the vacuity trap —
   this is the MML.12 lesson at the series level).
3. **The reduction** — a matrix `oz_collapse_inner_of_star`: per-pole integration by parts
   (`mixHSAntideriv2′ = mixHSAntideriv1`, `mixHSAntideriv1′ = mixHSterm2`, both proved here) converts
   the convolution over the annulus into `Kterm`-values at endpoints + one interval integral, which
   the collapse identity then closes by polynomial algebra.

**Depends on.** `mixHSterm2` (MML.8), `mixHS_summable_of_growth` (MML.5 infra). Mathlib:
`HasDerivAt.cexp`, `Complex.ofRealCLM.hasDerivAt`, `Complex.norm_exp`.

**Lean.** New file `YukawaOZMix/MixtureRDFAntideriv.lean` (ns `FMSA.MixtureRDF`), axiom-clean, full
build green: `expLinTerm`, `mixHSterm2_eq_expLinTerm`, `expLinTerm_hasDerivAt`, `expLinTerm_deriv_eq`,
`antiCoeff`, `expLinTerm_antideriv_hasDerivAt`, `mixHSAntideriv1`/`2` + their `hasDerivAt` chain,
`expLinTerm_norm`, `expLinTerm_norm_le_of_re_nonneg`, `antiCoeff_snd_norm`, `antiCoeff_fst_norm_le`,
`mixHSAntideriv2Coeff`, `mixHSAntideriv2_eq_mixHSterm`, `mixHSAntideriv2_summable_of_growth`.

**Lean pitfall.** `once-/twice` in prose closes a `/-! -/` docstring early (the `-/`); write
`once- or twice-`. The `expLinTerm` derivative is cleanest via `rw [show <deriv-value> = <product-rule
form> from by ring]; exact hlin.mul hexp` rather than `convert … ; ring` (which leaves a non-ring
`HasDerivAt` goal fragment).

**Status.** ◑ **Tower + decay mechanism DONE (2026-07-24), axiom-clean.** Summability reduced to one
explicit coefficient bound, then Rung 1 (below) discharges that bound down to the concrete `α, β`
estimate. Roadmap rungs 2–3 remain.

---

### Task MML.14 Rung 1 — threshold-free summability of the `Kterm` tower

**What it delivers.** The `hbound` hypothesis left open by `mixHSAntideriv2_summable_of_growth` is now
proved from the inputs a concrete pole family actually supplies. Given a **common `‖s_n‖^q` bound**
(`q < 1`) on the two double-pole coefficients `α_n`, `β_n`, plus reflected positivity `Re s_n ≥ 0`,
`‖s_n‖ ≥ 1`, and linear pole growth, the `Kterm`-rung series `Σ_n mixHSAntideriv2` is `Summable` at
**every** `r ≥ 0` (`mixHSAntideriv2_summable_of_coeff_bounds`). The two `antiCoeff` divisions turn `q`
into the summability exponent `p = q − 2 < −1`, **with no `rdist > max(σ₀/2, λ₀₁)` threshold** — this
is exactly the mixture form of the scalar `Kterm`'s all-`u>0` summability (`Kterm_summable_of_pole_family`),
and it is what lets the tower reach arbitrarily close to `r = 0` (the inner-core sampling).

**The arithmetic, done once.**
- `mixHSAntideriv2Coeff_eq` — the `Kterm`-rung coefficient in closed form: `α/s² + 2β/s³ + (β/s²)·r`
  (`field_simp; ring` at `s ≠ 0`), exhibiting the two spare `1/s` powers concretely.
- `mixHSAntideriv2Coeff_norm_le` — `‖coeff‖ ≤ (‖α_n‖ + (2+r)·‖β_n‖) / ‖s_n‖²`, folding the `1/‖s‖³`
  term into `1/‖s‖²` via `‖s‖ ≥ 1`.
- `mixHSAntideriv2_summable_of_coeff_bounds` — assembles: on the reflected family
  `‖mixHSterm coeff‖ = ‖coeff‖·e^{−r·Re s} ≤ ‖coeff‖` (the exp is a genuine decay), then the coeff
  bound + the `‖s_n‖^q` inputs land `‖·‖ ≤ Cc(3+r)·‖s_n‖^{q−2}`, and `mixHS_summable_of_growth`
  closes it. The `‖s‖^q/‖s‖² = ‖s‖^{q−2}` step is `Real.rpow_sub` + `Real.rpow_two`.

**The remaining concrete input — reduced twice, then validated.** The `α, β` bounds are the mixture
analog of the scalar `residue_term_norm_bound`. From MML.11, `β_n = N(s_n)/det′(s_n)²` and
`α_n = N′(s_n)/det′(s_n)² − N(s_n)·det″(s_n)/det′(s_n)³`, with `N = ((adj Q̂₀)ᵀ·B₁·adj Q̂₀)ᵢⱼ`. Rung 1
(below) discharges this down to **component** magnitudes and then confirms `q < 1` genuinely holds.
Isolated as `hα`, `hβ`.

**Reduction to component magnitudes (`mixHSAntideriv2_summable_of_component_bounds`).** The `α, β`
bounds reduce, by pure algebra, to component magnitudes on the RDF numerator: `coeff_div_sq_norm_le`
gives `‖β‖ = ‖N/det′²‖ ≤ ‖N‖/c₀²` and `coeff_alpha_norm_le` gives
`‖α‖ ≤ ‖N′‖/c₀² + ‖N‖·‖det″‖/c₀³`, from a constant `det′` lower bound `c₀` (MML.5's `disk_facts` f3).
So the tower is summable given common `‖s_n‖^q` (`q < 1`) bounds on `‖N‖`, `‖N′‖`, and the *product*
`‖N‖·‖det″‖`.

**⚠ A live scoping question — resolved in the tower's favour (`bMulti_norm_le`).** Whether `q < 1`
actually holds turns on the growth of the Yukawa numerator `B₁` along the pole family. Earlier worry:
if `B₁` carried the outer DCF's `e^{−ikR}` it could grow like `‖s_n‖^{2R/σ₁}` at the raw zeros
(`Re s_n < 0`), forcing `q ≥ 1` and reinstating the MML.5 `rdist` threshold (the tower buying nothing
past MML.12's annulus). **It does not.** The WH-projected `B₁` is the spectral amplitude
`bMulti = Σ_{m,p} c_{mp}/(s + z_{mp})` — a **pure sum of simple poles, no exponential** (the `e^{−ikR}`
lives in the *outer* transform `U₁` and is absorbed into the residues by the causal projection,
`outer_residue_eq_spectralAmp_residue`). `bMulti_norm_le` (`SpectralAmplitude.lean`, axiom-clean)
proves `‖B₁(s)‖ ≤ C·N²/‖s‖` past the pole radius: **`B₁` decays like `1/‖s‖`.** With the adjugate
entries bounded (`q0_entry_c → δ`) and `det Q̂₀ → 1` (`Q0_det_c_tendsto_one`, so `det′, det″` bounded),
all three component bounds hold with `q < 1` (in fact strongly negative). The tower is genuinely
threshold-free.

**The numerator assembly (`triple_transpose_entry_norm_le`, `tower_summable_of_matrix_bounds`).**
The RDF numerator `N = ((adj Q̂₀)ᵀ·B₁·adj Q̂₀)ᵢⱼ` bound is now **assembled from entry-level primitives**:
`triple_transpose_entry_norm_le` gives `‖(Aᵀ·B·A)ᵢⱼ‖ ≤ NN²·Ca²·Cb` from `‖A_pq‖ ≤ Ca`, `‖B_pq‖ ≤ Cb`
(via the proved `triple_entry_transpose_eq` + finite triangle inequality). Feeding the adjugate entry
bound `Ca` and the Yukawa entry bound `Cb·‖s_n‖^q` (which `bMulti_norm_le` supplies at `q = −1`) gives
`‖N(s_n)‖ ≤ K·‖s_n‖^q`, and `‖N·det″‖ ≤ K·CDpp·‖s_n‖^q` (`det″` bounded). `tower_summable_of_matrix_bounds`
then closes tower summability from these plus the `det′` lower bound `c₀` and the `N′` bound — the
`N`- and `N·det″`-sides are assembled internally; only `N′` is an input.

**What is left of Rung 1.** Two mechanical pieces, no open obstacle:
1. **The `N′` assembly** — the same triple-product pattern applied to `N′ = (adj′ᵀ·B₁·adj + adjᵀ·B₁′·adj
   + adjᵀ·B₁·adj′)ᵢⱼ`, needing the adjugate/`B₁` *derivative* entry bounds (a `bMulti′` decay `~1/‖s‖²`
   and `q0_entry_c′` bounds). Taken as the input `hNd` for now.
2. **The raw per-entry primitives** — `‖adj Q̂₀(s_n)‖ ≤ Ca`, `‖B₁‖ ≤ Cb/‖s_n‖` (`bMulti_norm_le`, done),
   `‖det″‖ ≤ CDpp`, `c₀ ≤ ‖det′‖` (`disk_facts` f3) — standard magnitude estimates on the *explicit*
   Baxter matrix and its determinant, i.e. the mixture `residue_term_norm_bound`; the `adj` bound is a
   `q01_norm_le`-style estimate on the pole disks, `det″` bounded from `det Q̂₀ → 1`. Cofinite-to-`∀n`
   bookkeeping (`bMulti_norm_le` needs `‖s‖` past the pole radius) is the only wiring subtlety.
The crux (`B₁` growth) is settled and the numerator assembly is complete; what remains is the
per-entry magnitude grind, not new structure.

**Depends on.** MML.14 tower; `bMulti` (Y1.5, `SpectralAmplitude.lean`); MML.11 coefficient formulas;
`Q0_det_c_tendsto_one`, `disk_facts` f3. Mathlib: `Real.rpow_sub`, `Real.rpow_two`, `div_le_div₀`,
`pow_le_pow_left₀`, `Complex.norm_real` (⚠ → real `‖r‖`, then `Real.norm_eq_abs`).

**Lean.** `YukawaOZMix/MixtureRDFAntideriv.lean` (`mixHSAntideriv2Coeff_eq`,
`mixHSAntideriv2Coeff_norm_le`, `mixHSAntideriv2_summable_of_coeff_bounds`, `coeff_div_sq_norm_le`,
`coeff_alpha_norm_le`, `mixHSAntideriv2_summable_of_component_bounds`);
`YukawaOZMix/SpectralAmplitude.lean` (`bMulti_norm_le`); `YukawaOZMix/MixtureRDFPoleData.lean`
(`triple_transpose_entry_norm_le`, `tower_summable_of_matrix_bounds`) — all axiom-clean, full build green.

**Lean pitfalls.** A binder `∀ n, … (n:ℝ) … sfam n …` makes Lean infer `n : ℝ` from the cast —
annotate `∀ n : ℕ`. `Complex.norm_real` rewrites `‖(r:ℂ)‖` to the *real* norm `‖r‖`, not `|r|` (follow
with `Real.norm_eq_abs`). `div_le_div` is renamed `div_le_div₀`.

**Status.** ✅ **DONE (2026-07-24), axiom-clean.** The tower is summable threshold-free; the full
reduction chain is built (tower ← coefficient ← component ← matrix-primitive bounds); the RDF
numerator `N` and `N·det″` are **assembled** from entry bounds (`tower_summable_of_matrix_bounds`); and
the crux (`B₁` decays like `1/‖s‖`, `bMulti_norm_le`) is proved, so `q < 1` genuinely holds and the
tower approach is validated. What remains is purely the per-entry magnitude grind — the `N′` assembly
(same triple-product pattern) and the standard `adj`/`det″` bounds on the explicit Baxter matrix (the
mixture `residue_term_norm_bound`), no new structure. Roadmap rung 2 (matrix `CoreSeriesClosure`)
remains; rung 3 (the integration-by-parts toolkit) is done — see below.

---

### Task MML.14 Rung 3 — the per-pole integration-by-parts toolkit

**What it delivers.** The scalar `hcollapse` reduction (`OZFIX.12`, `oz_collapse_of_two_sigma_le`) runs
on **per-pole integration by parts** — the antiderivative tower `Kterm′ = Hterm`,
`Hterm′ = h_explicit_term` turns the collapse's outer `t`-integral into endpoint antiderivative values
plus a lower-order integral, which the core series identity then closes. Rung 3 is the mixture analog,
built directly on MML.14's proved `HasDerivAt` chain `mixHSAntideriv2 → mixHSAntideriv1 → mixHSterm2`,
all axiom-clean:

* `expLinTerm_continuous` — the `(a+b·r)e^{−s·r}` shape is continuous in `r` (⇒ interval-integrable).
* `mixHSterm2_integral` / `mixHSAntideriv1_integral` — **per-pole FTC** on the two rungs:
  `∫_a^b mixHSterm2 = [mixHSAntideriv1]_a^b`, `∫_a^b mixHSAntideriv1 = [mixHSAntideriv2]_a^b`
  (`integral_eq_sub_of_hasDerivAt` + the chain).
* `mixHSterm2_weighted_ibp` — **integration by parts against a weight** `w`:
  `∫_a^b w·mixHSterm2 = [w·mixHSAntideriv1]_a^b − ∫_a^b w′·mixHSAntideriv1`
  (`integral_mul_deriv_eq_deriv_mul`). This is the step that moves the derivative off the per-pole
  term onto the weight, lowering the integrand's `r`-order — the mechanism the collapse's outer
  integral needs.
* `mixHSterm2_integral_tsum` — **termwise integration of the series**:
  `∫_a^b (∑ₙ mixHSterm2 · n) = ∑ₙ [mixHSAntideriv1 n]_a^b`, from `MeasureTheory.integral_tsum`
  (each summand continuous ⇒ `AEStronglyMeasurable`) + the per-pole FTC. The `L¹` hypothesis
  `∑ₙ ∫⁻ ‖·‖ₑ ≠ ∞` holds on the annulus, where the term series is summable (MML.5). This carries the
  collapse from `r·h₁ = r·(∑ …)` to a per-pole endpoint sum.

**What the full reduction still needs (not this task).** Rung 3 is the *plumbing*; the full matrix
`oz_collapse_of_two_sigma_le` additionally requires (i) Rung 2's matrix `CoreSeriesClosure` — the
series identity that closes the endpoint terms — and (ii) the **matrix OZ★** real-space convolution
that exhibits the collapse as such an integral identity in the first place (the mixture
`baxterPsi_eq_phi_add_rho_conv`, still unbuilt). Rung 3 gives the calculus that consumes those two;
it does not supply them.

**Depends on.** MML.14 tower `HasDerivAt` chain (`mixHSAntideriv1_hasDerivAt`,
`mixHSAntideriv2_hasDerivAt`). Mathlib: `integral_eq_sub_of_hasDerivAt`,
`integral_mul_deriv_eq_deriv_mul`, `MeasureTheory.integral_tsum`.

**Lean.** `YukawaOZMix/MixtureRDFAntideriv.lean` (§ Rung 3): `expLinTerm_continuous`,
`mixHSterm2_integral`, `mixHSAntideriv1_integral`, `mixHSterm2_weighted_ibp`,
`mixHSterm2_integral_tsum` — all axiom-clean, full build green.

**Lean pitfall.** The enorm notation `‖·‖ₑ` (needed for `integral_tsum`'s hypothesis) requires
`open ENNReal` (or `open scoped ENNReal`) — without it, `‖x‖ₑ` fails to parse ("expected token"),
even under `open MeasureTheory`. `Continuous.intervalIntegrable`/`.aestronglyMeasurable.restrict` take
the endpoints/measure explicitly.

**Status.** ✅ **DONE (2026-07-24), axiom-clean.** The per-pole IBP/FTC toolkit is complete. The full
collapse reduction is gated on Rung 2 (`CoreSeriesClosure`) and the matrix OZ★ — neither of which is
Rung 3.

---

### Task MML.14 Rung 2 — the matrix `CoreSeriesClosure` predicate and its non-vacuity

**What it delivers.** The scalar collapse reduces to a single series identity `CoreSeriesClosure`
(`OzCollapseInner.lean`): the twice-antidifferentiated (`Kterm`-form), always-summable residue
series, corrected by its first-order Taylor data at the anchor `σ`, equals an explicit polynomial in
`u` (content: *the exterior residue series, continued into the core, reproduces the inner value*).
Rung 2 is the matrix analog — the predicate plus its non-vacuity.

* `MixCoreSeriesClosure alpha beta sfam anchor poly` — the predicate: on `(0, anchor]`,
  `∑ₙ [mixHSAntideriv2(r) − mixHSAntideriv2(anchor) − (r−anchor)·mixHSAntideriv1(anchor)] = poly r`.
  The bracket is the **first-order Taylor remainder** of `mixHSAntideriv2` at `anchor` (since
  `mixHSAntideriv2′ = mixHSAntideriv1`, MML.14 chain). `poly : ℝ → ℂ` is general (the matrix analog
  of the scalar's `π(σ²(u−σ) − (u³−σ³)/3)`; its concrete value comes from the inner core via the
  unbuilt matrix OZ★).
* `mixCoreSeriesClosure_summand_summable` — **non-vacuity**: the summand is `Summable` from the three
  Rung-1 summabilities (`mixHSAntideriv2` at `r`, at `anchor`; `mixHSAntideriv1` at `anchor`), so the
  predicate is about a *convergent* `tsum` — exactly the scalar `coreSeriesClosure_summand_summable`.
* `mixHSAntideriv1_summable_of_coeff_bounds` — the `Hterm`-rung summability that discharges the
  `mixHSAntideriv1` hypothesis: one `antiCoeff` gain ⇒ exponent `q − 1`, so it needs `q < 0` (vs the
  `Kterm` rung's `q < 1`); the RDF's `q ≈ −1` clears it. Plumbing: `mixHSAntideriv1Coeff`,
  `_eq_mixHSterm`, `mixHSAntideriv1Coeff_norm_le` (one `1/‖s‖` gain).

⚠ **The `Kterm`-form is essential — MML.12's vacuity lesson at the series level.** The `Hterm`-form
(`mixHSAntideriv1`) series is summable only for `q < 0` at a fixed point and (raw) only above the
MML.5 threshold, so a predicate stated on it would be false/vacuous near `r = 0`. The `Kterm`-form
(`mixHSAntideriv2`) is summable at every `r ≥ 0` (Rung 1), and the *remainder* combination is
genuinely summable — this is why the predicate uses `mixHSAntideriv2` with the first-order correction,
not a bare series.

**Held as a `Prop`, not an axiom** — identical discipline to the scalar `CoreSeriesClosure`: a naive
series-value axiom is satisfiable by sub-families summing to the wrong value (`MZERO.1`-infinitude ≠
pole-exhaustion). It is discharged only by a genuine pole-enumerating family, and the concrete `poly`
needs the matrix OZ★ real-space identity — the one input Rung 2 does not (and should not) supply.

**Depends on.** MML.14 tower (`mixHSAntideriv1`/`2`, `mixHS_summable_of_growth`); Rung 1 summabilities.

**Lean.** `YukawaOZMix/MixtureRDFAntideriv.lean` (§ Rung 2): `mixHSAntideriv1Coeff`,
`mixHSAntideriv1_eq_mixHSterm`, `mixHSAntideriv1Coeff_eq`, `mixHSAntideriv1Coeff_norm_le`,
`mixHSAntideriv1_summable_of_coeff_bounds`, `MixCoreSeriesClosure`,
`mixCoreSeriesClosure_summand_summable` — all axiom-clean, full build green.

**Status.** ✅ **DONE (2026-07-24), axiom-clean.** The predicate is defined and proved non-vacuous.
What remains for the full collapse is discharging `MixCoreSeriesClosure` for the genuine pole family —
which needs the **matrix OZ★** (the concrete `poly` from the inner value) — plus the matrix
`oz_fixed_pt_unique` bridge, i.e. the mixture real-space Baxter core (`OZFIX.15–20` analog), started
below (MML.15).

---

### Task MML.15 — matrix OZ★: the mixture real-space OZ identity (foundation / START)

**The last unbuilt piece of MML.8's infrastructure, launched.** The three calculus rungs (Rung 1
summability, Rung 2 `CoreSeriesClosure`, Rung 3 IBP) are complete; they all **consume** the matrix
OZ★ — the real-space matrix Ornstein–Zernike identity that (i) exhibits the collapse as an integral
identity and (ii) supplies `MixCoreSeriesClosure`'s concrete `poly` from the inner value. The scalar
OZ★ `baxterPsi_ozstar` (`BaxterOzStar.lean`, unconditional) is
`baxterPsi(r) = r·c_HS(r) + ρ·r·radial3d_conv(c_HS, baxterPsi/·)(r)`; the general-`N` matrix analog is
the mixture version of the *entire* `BaxterRenewal.lean` + `BaxterOzStar.lean` apparatus
(`OZFIX.15–20`) — large. MML.15 lays the **structural foundation** and validates the target shape.

* `matRadialConv` — the entrywise matrix radial convolution `(A ⋆ B)ᵢⱼ = ∑ₖ radial3d_conv(Aᵢₖ, Bₖⱼ)`,
  reducing the matrix OZ convolution to the *scalar* `radial3d_conv` machinery per entry, with a
  **species-coupling sum** over the intermediate `k`.
* `MatOZStar Ψ Φ ρ` — the matrix OZ★ predicate: `Ψᵢⱼ(r) = r·Φᵢⱼ(r) + ρ·r·(matRadialConv Φ (Ψ/·))ᵢⱼ(r)`
  for `r > 0`. Held as a `Prop` — the concrete `Ψ, Φ` and the proof are the matrix-Baxter construction
  (the research-scale remainder); this fixes the *target shape*.
* `matOZStar_entry` — the explicit coupled entry equation, exhibiting the `∑ₖ radial3d_conv(Φᵢₖ, Ψₖⱼ/·)`
  species coupling that makes the matrix OZ★ genuinely more than `N` independent scalar problems.
* `matOZStar_fin_one_of_scalar` — **the `n = 1` soundness bridge**: at one component `MatOZStar`
  (`Ψ = baxterPsi`, `Φ = c_HS`) is *exactly* the proved scalar `baxterPsi_ozstar`. The framework
  specializes correctly to the known scalar theory (MML.13 / MRS.0b discipline) and this doubles as a
  non-vacuity witness — `MatOZStar` is instantiable, not a vacuous `Prop`.

**The real-space factorization foundation (started 2026-07-24).** The scalar OZ★ is *built on* the
real-space Baxter factorization (`OZFIX.18` KDEF, `rho_baxterK_eq_q0_self_conv`):
`ρ·K(v) = q0(v) − ∫_v^σ q0(t)·q0(t−v)dt`, the real-space content of `1 − ρĈ = Q̂(k)·Q̂(−k)`. The
mixture factorization `I − Ĉ₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` (MRS.6 `Cmix0_factorization`, Fourier) inverse-
transforms with the same second foundational layer, now built:
* `matSelfConv` — the matrix self-convolution `(Q ⋆ Qᵀ)ᵢⱼ(v) = ∑ₖ ∫_v^σ Qᵢₖ(t)·Qⱼₖ(t−v) dt`, the
  real-space image of `Q̂₀(k)·Q̂₀ᵀ(−k)` (the `ᵀ` gives the species-summed `∑ₖ`; the `−k` makes it a
  correlation), reducing to the scalar self-convolution per entry-pair.
* `MatBaxterFactorization` — the matrix real-space KDEF `ρ·Kᵢⱼ(v) = qᵢⱼ(v) − (matSelfConv q)ᵢⱼ(v)` on
  `(0, σ)`, held as a `Prop`.
* `matBaxterFactorization_fin_one_of_scalar` — the **`n = 1` bridge**: at one component
  (`K = baxterK`, `q = q0_poly`) it is *exactly* the scalar `rho_baxterK_eq_q0_self_conv`.

**The shell-conv = K-conv bridge — third layer (`OZFIX.19` analog, 2026-07-24).** The scalar
`radial3d_conv_eq_baxterK_shell` ties the 3D radial convolution (the OZ★ shape) to a 1D convolution
with the Baxter shell kernel `K` (the factorization): `r·radial3d_conv(c_HS, g)(r) = ∫₀^σ baxterK(u)·
(oddExt g(r−u) + oddExt g(r+u)) du`. **The matrix analog is that scalar identity summed over the
intermediate species `k`** — no new analysis, since `matRadialConv` is a sum of scalar
`radial3d_conv`s and `r` pulls inside the sum:
* `matShellConv` — the 1D Baxter-kernel form `∑ₖ ∫₀^σ Kᵢₖ(u)·(oddExt Gₖⱼ(r−u) + oddExt Gₖⱼ(r+u)) du`.
* `matRadialConv_eq_matShellConv` — the bridge `r·(matRadialConv C G)ᵢⱼ = (matShellConv K G)ᵢⱼ` from
  the per-`(i,k)` scalar shell identity (`hentry`); pure assembly (`Finset.mul_sum` + `sum_congr`).
* `matShellBridge_fin_one_of_scalar` — the **`n = 1` bridge**: the per-entry `hentry` is exactly the
  proved scalar `radial3d_conv_eq_baxterK_shell` (carrying its two integrability hypotheses,
  discharged unconditionally in `BaxterOzStar.lean` for `g = baxterPsi/·`). This layer connects the
  OZ★ shape (layer 1, `matRadialConv`) to the factorization (layer 2, `matSelfConv`/`K`).

**The general-`c` shell identity — the per-entry analytic input, now proved (2026-07-24).** The
mixture entries `C₀ᵢₖ` are each a different `c`-shape at their own `σ_ik`, not the single `c_HS`, so
the shell bridge's `hentry` needed the shell identity for an *arbitrary* kernel. `ShellKernel.lean`
supplies it: `shellKernel c σ v = 2π ∫_|v|^σ s·c(s) ds` (the general Baxter shell kernel), and
`radial3d_conv_eq_shellKernel` proves `r·radial3d_conv(c, g)(r) = ∫₀^σ shellKernel(c)(u)·(oddExt
g(r−u)+oddExt g(r+u)) du` for **any** `c` supported in `[0,σ]`. The proof is a transcription of the
scalar `radial3d_conv_eq_baxterK_shell` with `c_HS → c`, `baxterK → shellKernel c`, `c_HS_outer →
hc_outer` — `c_HS` was used only through its support and `baxterK`'s definition; everything else
(`radial3d_conv_eq_oddExt`, `intervalIntegral_triangle_swap`, the inner shell reassembly) is generic.
`shellKernel_c_HS` confirms it reduces to `baxterK`. **Consumed by**
`matRadialConv_eq_matShellConv_of_shellKernel` (`MixtureOzStar.lean`): the matrix shell bridge with
the kernel *built from the entries* `Kᵢₖ = shellKernel(C₀ᵢₖ)`, discharging `hentry` per entry — the
general-`N` form the assembly consumes, with only per-entry support + integrability as hypotheses.

**The matrix `baxterPsi` construction — shape + renewal equation (2026-07-24).** The scalar
`baxterPsi` is the three-branch glued solution (outer Volterra `baxterPsiOuter` on `[σ,∞)`, odd
reflection, definitional core `−v`), satisfying `baxterPsiOuter_spec`. The matrix analog now has the
same shape:
* `matBaxterPsi Ψouter Ψcore σ` — the glued matrix solution; `matBaxterPsi_core` / `_outer` /
  `_reflect` the branch equations.
* `MatRenewalEq Ψouter F Q σ` — the matrix renewal equation `Ψouterᵢⱼ(r) = Fᵢⱼ(r) + ∑ₖ ∫_σ^r
  Qᵢₖ(r−t)·Ψouterₖⱼ(t) dt` (`r ≥ σ`), the **coupled** Volterra system across species `k` (the
  coupling that distinguishes it from `N` scalar renewals).
* `matBaxterPsi_fin_one_of_scalar` / `matRenewalEq_fin_one_of_scalar` — the **`n = 1` bridges**: the
  matrix `baxterPsi` core is the scalar `baxterPsi`, and `MatRenewalEq` is the proved scalar
  `baxterPsiOuter_spec`.
**`Ψouter` is now constructed (2026-07-24) — the coupled matrix Volterra is solvable.** The mixture
renewal `Ψ(r) = F(r) + ∫_σ^r Q(r−t)·Ψ(t) dt` is a **matrix product** — the species-coupling sum
`∑ₖ Qᵢₖ·Ψₖⱼ` *is* `(Q·Ψ)ᵢⱼ` — so it is a Volterra equation on the complete normed ring
`E = Matrix (Fin N) (Fin N) ℝ`. Two pieces:
* **`Analysis/VolterraBanach.lean` — the Banach generalization of `MA.10`.** For any complete normed
  ring `E` (`NormedRing`, `NormedAlgebra ℝ`, `CompleteSpace`) and continuous convolution kernel
  `q : ℝ → E`, `volterra_convolution_existsUniqueE` gives a unique continuous `E`-valued solution of
  `u(r) = g(r) + ∫_a^r q(r−t)·u(t) dt`. The proof is the *identical* iterate-contraction argument as
  the scalar `MA.10`; the only change is `|K·u| ≤ M·|u|` becoming `‖q·u‖ ≤ ‖q‖·‖u‖` via `norm_mul_le`
  (submultiplicativity). Axiom-clean — a mechanical generalization, not new mathematics.
* **`matVolterra_convolution_existsUnique`** (`MixtureOzStar.lean`) — the instantiation at
  `E = Matrix (Fin N) (Fin N) ℝ` under the submultiplicative `Matrix.linftyOp` norm: the matrix
  renewal has a unique continuous matrix solution `Ψouter`. The entrywise `MatRenewalEq` form follows
  by matrix-entry evaluation commuting with the integral (`Matrix.mul_apply` +
  `ContinuousLinearMap.intervalIntegral_comp_comm`), a mechanical step.

**Entry-extraction is complete — the matrix-norm plumbing is solved (2026-07-24).** The entrywise
`MatRenewalEq` (`∑ₖ ∫ Qᵢₖ·Ψₖⱼ`) from the matrix-product solution needs `(∫ f)ᵢⱼ = ∫ fᵢⱼ` (entry
evaluation commuting with the matrix Bochner integral), through
`ContinuousLinearMap.intervalIntegral_comp_comm` at the entry CLM, hence through
`IntervalIntegrable (f : ℝ → Matrix ℝ)`.

⚠ **The instance-diamond fix.** That predicate does not elaborate on its own under the `letI`'d
`Matrix.linftyOp` norm — `ENormedAddMonoid (Matrix ℝ)` is not synthesized, because the default
`Matrix` product topology competes with the norm's and
`NormedAddCommGroup.toENormedAddCommMonoid`'s topology does not unify (it *is* synthesized for an
abstract `[NormedAddCommGroup E]`, so a Matrix-topology-diamond, not a gap). **The one-line fix:
`letI : ENormedAddCommMonoid (Matrix ℝ) := NormedAddCommGroup.toENormedAddCommMonoid`**, which pins
the norm-induced topology. Three lemmas then close the extraction:
* `matrix_intervalIntegral_apply` — `(∫ f)ᵢⱼ = ∫ fᵢⱼ` (via the entry CLM + the fix).
* `matrix_mul_intervalIntegral_entry` — `(∫ Q·U)ᵢⱼ = ∑ₖ ∫ Qᵢₖ·Uₖⱼ` (`matrix_intervalIntegral_apply`
  + `Matrix.mul_apply` + `intervalIntegral.integral_finsetSum`).
* `matRenewalEq_of_matrixProduct` — **end-to-end**: a matrix-product renewal `Ψ(r) = F(r) + ∫ Q(r−t)·
  Ψ(t) dt` (the `matVolterra_convolution_existsUnique` form) *is* `MatRenewalEq` for the entry
  families. So `Ψouter` is now constructed in the exact `∑ₖ` form the matrix `baxterPsi` consumes.

**Matrix `F[K]=Ĉ` DONE (2026-07-24, `OZFIX.18` F-part).** The scalar `baxterK_cos_eq_radial_fourier`
matches the Fourier transform of the Baxter shell kernel with the DCF `radial_fourier`. Its
matrix form is that identity per entry, so the genuine content is the **general-`c` version**, now
proved in `HardSphere/ShellKernel.lean` (like the shell identity, `c_HS`-independent):
* `shellKernel_hasDerivAt` — `shellKernel(c)′(v) = −2π·v·c(v)` on `(0,σ)` (FTC-1, the general-`c`
  `hasDerivAt_baxterK`); `shellKernel_apply_sigma` (`K(σ)=0`), `shellKernel_continuousOn` (primitive).
* `radial_fourier_eq_intervalIntegral_of_support` — `radial_fourier(c) = (4π/k)∫₀^σ r·c(r)·sin`
  for `c` supported in `[0,σ]`.
* `shellKernel_cos_eq_radial_fourier` — `2∫₀^σ shellKernel(c)·cos(kv) = radial_fourier(c)(k)`, one
  integration by parts (boundary killed by `K(σ)=0`), for `c` supported in `[0,σ]`, continuous on the
  open core, `s·c(s)` interval-integrable.
`MixtureOzStar.lean`: `matShellKernel_cos_eq_radial_fourier` (per entry `C₀ᵢⱼ`) +
`matShellKernel_cos_eq_radial_fourier_fin_one_of_scalar` (the `n = 1` bridge to
`baxterK_cos_eq_radial_fourier`).

**Matrix 2D reindex DONE (2026-07-27, `OZFIX.20`).** The scalar `dbl_conv_reindex` uses the *same*
`q0` for both Baxter factors; the matrix self-convolution `matSelfConv i j = ∑ₖ Qᵢₖ⋆Qⱼₖ` couples
*different* factors `Qᵢₖ, Qⱼₖ` (off-diagonal), so the genuine content is a **two-function** reindex:
* `dbl_conv_reindex_two` (`BaxterRenewal.lean`) — for two distinct factors `q0a, q0b`,
  `∫ q0a(t)∫ q0b(s)ψ(r+t−s) = ∫_u [(∫_u^σ q0a·q0b(·−u))·ψ(r+u) + (∫_u^σ q0b·q0a(·−u))·ψ(r−u)]`.
  Both sides route through the *asymmetric* triangle-split double integral
  `∫ t ∫_{s<t} [q0a(t)q0b(s)ψ(r+t−s) + q0a(s)q0b(t)ψ(r+s−t)]` (the scalar's symmetrized `ψ(r±u)`
  splits because the two factors no longer commute across the diagonal). Same
  `intervalIntegral_triangle_swap_gen` + `integral_comp_sub_left` change of variable as the scalar;
  9 fine-grained integrability hypotheses. For `q0a = q0b` it collapses to `dbl_conv_reindex`.
* `matDblConv_reindex` (`MixtureOzStar.lean`) — sums the two-function reindex over the intermediate
  species `k` (`intervalIntegral.integral_finsetSum` + `Finset.sum_mul` regroup), giving
  `∑ₖ (Qᵢₖ⋆Qⱼₖ)⋆ψ = ∫_u [matSelfConv Q σ u i j · ψ(r+u) + matSelfConv Q σ u j i · ψ(r−u)]`
  (the second kernel is the `i↔j` transpose). `matDblConv_reindex_fin_one` = the `n = 1` bridge.

**Integrability side-conditions DONE (2026-07-27, `OZFIX.20` discharge).** The matrix reindex is
stated with nine per-species integrability hypotheses; `MixtureOzStarIntegrable.lean` discharges all
nine from the **natural regularity** of the Baxter data (factors `Q i j` continuous, `psi` measurable
+ `|psi|` `uIcc`-bounded), exactly the regularity the scalar `ozstar_h…` (`BaxterOzStar.lean`) exploit
for `q0_poly`/`baxterPsi`. Generic engine:
* `bddOn_uIcc_of_continuous`, `psiComp_bddOn` — compact-interval bounds from continuity (via
  `isCompact_uIcc.exists_isMaxOn`);
* `swap_indicator_integrable` — the shared Fubini `(Ioi ·).indicator` engine, factoring the three
  product-measure side-conditions (`integrable_prod_restrict_of_measurable_bddOn` + indicator
  boundedness); `swapPM_integrable` / `swapA_integrable` specialise it to the `ga(t)·gb(t−u)·ψ(w u)`
  and `ga(t)·gb(s)·ψ(r+t−s)` shapes;
* `constMul_psi_intervalIntegrable` — the slice side-conditions;
* `paramLo_/paramHi_/paramKernel_mul_intervalIntegrable` — the parametric inner-integral
  side-conditions (`measurable_intervalIntegral_param` + `norm_integral_le_of_norm_le_const`).
`matDblConv_reindex_of_regular` assembles them: the matrix reindex conditional only on
`(∀ a b, Continuous (Q a b))`, `Measurable psi`, and `psi`'s `uIcc`-boundedness — the matrix analog of
the way `baxterPsi_ozstar` is unconditional.

**Matrix OZ★ ASSEMBLED (2026-07-28, `OZFIX.15/19/20` combined) — axiom-clean, no decay axiom.**
`matOzStar_of_shellClaims` (`MixtureOzStar.lean`) derives the matrix real-space OZ identity
`MatOZStar Ψ Φ ρ` from four inputs, exactly mirroring the scalar `baxterPsi_eq_phi_add_rho_conv`:
* `hfact` — `MatBaxterFactorization` (matrix KDEF `ρKᵢₖ = Qᵢₖ − matSelfConv(i,k)`);
* `hbridge` — `matRadialConv_eq_matShellConv` (matrix `OZFIX.19` shell-conv bridge);
* `hQint`/`hSint` — shell integrability (dischargeable via `MixtureOzStarIntegrable.lean`);
* `hclaimA` — the **matrix renewal identity in shell form** (`OZFIX.15` analog of
  `baxter_psi_conv_eq_phi`): `Ψᵢⱼ(r) = r·Φᵢⱼ(r) + (shell-Q − self-conv-shell)`.
The load-bearing algebra is `matShellConv_kdef_split` (KDEF substituted a.e. on the open core splits
`ρ·matShellConv` into shell-`Q` minus self-conv-shell). `claimA` supplies `Ψ − r·Φ`, and
`ρ·matShellConv` (bridge + KDEF split) supplies the *same* shell expression ⇒ `MatOZStar`.
Validated at `N = 1` by the pre-existing `matOZStar_fin_one_of_scalar` (= unconditional scalar
`baxterPsi_ozstar`). **The assembly needed NO matrix decay axiom** — the hard content lives entirely
in the three `constructed-solution` Prop inputs (`hfact`/`hbridge`/`hclaimA`).

**Assembly integrability plumbing FINISHED (2026-07-30, `MixtureOzStarIntegrable.lean`, axiom-clean).**
`matOzStar_of_shellClaims` still carried its two shell-integrability side-conditions (`hQint`, the
linear `Q`-shell; `hSint`, the self-conv shell) as *bare* hypotheses — the last un-plumbed integral in
the matrix assembly, the analog of the reindex's nine that `matDblConv_reindex_of_regular` already
discharged. Now closed by the capstone **`matOzStar_of_regular`**, which discharges both from the same
natural regularity (`Q` continuous, `oddExt (Psi·/·)` measurable + `uIcc`-bounded per entry) and keeps
only the genuine constructed-solution inputs `hfact`/`hbridge`/`hclaimA` — so the matrix assembly now
needs *no* integrability hypotheses, exactly mirroring the unconditional scalar
`baxterPsi_eq_phi_add_rho_conv`. Two reused engine lemmas: `shellQ_intervalIntegrable`
(`g·(psi(r−u)+psi(r+u))` = two `mulCont_psi_intervalIntegrable`, the `c=1` slice of
`constMul_psi_intervalIntegrable`) and `shellS_intervalIntegrable` (expand `matSelfConv` into the
species sum of `paramKernel_mul_intervalIntegrable` shapes, close by `IntervalIntegrable.sum` +
`Finset.sum_mul`). `#print axioms` on all four = standard three only, **no new axiom, ledger unchanged**.

**`Ψouter` CONSTRUCTED — no longer a parameter (2026-07-31, axiom-clean).**  The renewal scaffolding
took `Ψouter` (the coupled matrix Volterra outer solution) as a *parameter*; the note "constructing it
is the remaining analytic core" is now discharged.  Built by lifting the proved scalar global-gluing
chain (`volterraSol`→`volterraGlobal`→`volterraGlobal_spec`, `BaxterRenewal.lean`) to **any complete
normed ring** in `Analysis/VolterraBanach.lean` — `volterraSolE`/`volterraSolE_spec`/`_unique`,
`volterraSolE_compat` (overlap agreement from uniqueness), `volterraGlobalE` (`if a≤r then sol(b:=r) at
r else 0`), `volterraGlobalE_eq_sol`/`_spec`/`_continuousOn`/`_continuousOn_Ici` (half-line continuity by
`mono_of_mem_nhdsWithin` gluing).  Instantiated at `E = Matrix (Fin N) (Fin N) ℝ` (`linftyOp` ring) in
`MixtureOzStar.lean`: `matBaxterPsiOuterFun` = `volterraGlobalE` precomposed with `max σ ·` (globally
continuous, agrees with the solution on `[σ,∞)`; `matBaxterPsiOuterFun_continuous` via
`ContinuousOn.comp_continuous`, `_renewal` via `volterraGlobalE_spec` + `integral_congr`).  Capstone
**`matBaxterPsiOuter_matRenewalEq`**: for *any* continuous matrix Baxter data `Q, F`, the entries of
`matBaxterPsiOuterFun` satisfy the entrywise `∑ₖ` `MatRenewalEq` (via `matRenewalEq_of_matrixProduct`).
`#print axioms` = standard three, **no new axiom, ledger unchanged**.  **Still open for the full
`hclaimA`:** (i) instantiate `Q, F` with the concrete real-space matrix Baxter kernel + forcing (the
momentum→real-space `Q0_mat_c` data), and (ii) the **matrix seed identity** — the analog of
`baxter_psi_conv_eq_phi` converting `MatRenewalEq` (the `∫_σ^r` renewal) to the OZ★ shell form (the
`oddExt`/`∫_0^σ` shell).  The existence/renewal half of the construction is now done; the seed identity
is the remaining research-scale piece.

**Matrix seed — claim (A) + outer half BUILT (2026-07-31, `MixtureBaxterSeed.lean`, axiom-clean).**
The scalar seed `baxter_psi_conv_eq_phi` (`Ψ⋆Q₊⋆Q₋ = r·c_HS`) rests on `baxter_u_outer` (claim (A):
`u := Ψ⋆Q₊ ≡ 0` on `[σ,∞)`) + `baxter_core_seed` (the Wertheim–Thiele affine algebra on the core).
Built for the matrix:
* `intervalConv_sub_open` — the reusable analytic heart: `∫_0^σ q(t)ψ(r−t) = ∫_0^r q(r−s)ψ(s)` for any
  continuous `q` supported in `[0,σ]` (substitute `s=r−t`, then the `[0,r−σ]` tail vanishes since
  `q(r−s)=0` there).  Carries NO core/forcing content — the general form of the scalar reduction.
* `matBaxterU` (`uᵢⱼ = Ψᵢⱼ − ∑ₖ ∫_0^σ Qᵢₖ·Ψₖⱼ(r−·)`) + **`matBaxterU_outer`** — matrix claim (A):
  the coupled `MatRenewalEq` (with forcing `Fᵢⱼ(r)=∑ₖ∫_0^σ Qᵢₖ(r−s)·Ψcoreₖⱼ(s)`) is equivalent on
  `[σ,∞)` to `Ψᵢⱼ(r)=∑ₖ∫_0^σ Qᵢₖ(t)·Ψₖⱼ(r−t)`.  Proof = `intervalConv_sub_open` **summed over species
  `k`** (`Finset.sum_congr`), `[0,r]` split at `σ` (`integral_add_adjacent_intervals`), the `[0,σ]`
  piece matched to the forcing via core values a.e. (jump at `σ` null).  Integrability per `k` from
  core-continuous on `[0,σ]` (a.e.) + outer-`ContinuousOn` on `[σ,r]` — the glued-solution regularity.
* `matBaxterUQm` (second convolution `⋆Q₋`) + **`matBaxterUQm_zero_of_uOuter`** — the **outer half of
  the seed**: `Ψ⋆Q₊⋆Q₋ ≡ 0` on `[σ,∞)` (both `uᵢⱼ(r)` and `uₖⱼ(r+t)` vanish; matches `r·c_HS(r)=0`
  since `c_HS` supported in `[0,σ]`), reduced abstractly to the claim-(A) conclusion `hUouter`.
`#print axioms` all three = std 3.  **Still open (the CORE half, `0<r<σ`):** `matBaxterU_core` (affine
`u = r·(M₀−1)−M₁`) + matrix `baxter_core_seed` (the WT/PY moment algebra tying it to `c_HS`) — both
need the concrete real-space matrix moments/DCF, i.e. piece (i).  Claim (A) is the renewal-side half
and is now unconditional (given the glued-solution regularity); the core half is the concrete-data half.

**⚠️ RETRACTED (2026-07-31) — the "piece (i)" real-space kernel below was a DUPLICATE, file removed.**
The real-space matrix Baxter factor **already exists**: `WHSupports.q0MixEntry` ("[LN] Eq. 56/10") =
`X.Q0·(r−Rᵢⱼ) + X.Qpp·(r−Rᵢⱼ)²/2` windowed on `Icc λᵢⱼ Rᵢⱼ` (`Rᵢⱼ = σ̄ᵢⱼ`), from the `Mix` struct —
**with the causal lower-cut** that my `q0MatReal` lacked (mine was continuous / no cut / `ρ_geo`-bundled ⇒
wrong for unlike pairs: misses the `λᵢⱼ` jump and the separate `λᵢⱼ`-delta).  The momentum factorization
is also long-standing (`Cmix0 = I − Q̂₀(k)Q̂₀ᵀ(−k)`, MRS.6 `Cmix0_factorization`; `Q0_mat_c`).
`MixtureBaxterRealSpace.lean` (q0MatReal + moments + transform) deleted; **`matBaxterU_core` kept** (it is
abstract / Q-agnostic).  The paragraphs below are the retracted account; see the gap map after them.

**Claim (B) `matBaxterU_core` BUILT (2026-07-31, `MixtureBaxterSeed.lean`, axiom-clean).**  Matrix analog of
scalar `baxter_u_core`: for `Ψ` with core value `Ψₖⱼ(v)=−v` on `(−σ,σ)`, on `0<r<σ` the whole sample range
`r−t` stays in the core, so `matBaxterU Psi Q σ i j r = r·(∑ₖ M₀ᵢₖ − 1) − ∑ₖ M₁ᵢₖ` with `M₀ᵢₖ=∫_0^σ Qᵢₖ`,
`M₁ᵢₖ=∫_0^σ t·Qᵢₖ` (the scalar computation summed over `k`).  **Stated with integrability (`hQ0`/`hQ1`),
not continuity**, so it accepts the discontinuous physical `q0MixEntry`.  The `−1` is the single
`Ψᵢⱼ(r)=−r` term (Baxter identity part), not summed.

**GAP MAP toward concrete `hclaimA` (2026-07-31).**  (1) **Matrix Wertheim core seed** `matBaxterUQm_ij(r)
= r·c_HS_ij(r)` on the core — needs a real-space matrix PY DCF `c_HS_ij(r)` and the WT/PY algebra (matrix
analog of `baxter_core_seed`).  **The crux.**  **⚠ Verified 2026-07-31: the real-space matrix PY DCF closed
form exists NOWHERE in the project** (not a forgotten formula).  The matrix PY DCF is present only in
**momentum** space (`Cmix0 = I − Q̂₀Q̂₀ᵀ`, MRS.6); the **real-space** HS DCF the project uses is the **FMT**
form (`cHS_FMT`/`CHSKink`; Python `get_HS_FMT` in every route).  A real-space PY closed form = the inverse
transform of `Cmix0` = the **Lebowitz/Wertheim** result, which `MixtureRealSpace.lean` explicitly **defers as
MRS.8** ("`Ĉ₀` equals the physical HS DCF transform").  So gap #1's two halves collapse: defining `c_HS_ij`
real-space **is** the Wertheim derivation, not a transcription — the project deliberately sidesteps it (FMT
real-space + `Cmix0` momentum).  **✅ ADDRESSED 2026-07-31 (`YukawaOZMix/MixtureHSDCF.lean`, axiom-clean):
zeroth-order HS DCF built REUSING the existing `q0MixEntry`/`pMixEntry`/`⋆` machinery.**  Key structural
fact: `Cmix0 = I − Q̂₀(k)Q̂₀ᵀ(−k)` is **forward × reflected**, so `qpConv = qFwd ⋆ pMixEntry` (`qFwd` = the
forward `2π√ρ·q0MixEntry`), support `[−Rᵢⱼ,Rᵢⱼ]` with `σₙ` cancelling (`λᵢₙ−Rⱼₙ=−Rᵢⱼ`, exactly like
`bConvP`; both-reflected `P⋆P` would keep `σₙ`).  `cHSmixRaw_ij = qFwd_ij + pMixEntry_ji − ∑ₗ qpConv_ilj`
= the real-space non-delta part of `[Cmix0]_ij` (verified by the `Cmix0` expansion), supported on
`[−Rᵢⱼ,Rᵢⱼ]`.  Remaining: the inverse-transform theorem `cHSmixRaw = [Cmix0]_ij` (parallel to `(★)`), the
`2π√ρ·t` normalization + odd part, then `matBaxterUQm = r·c_HS`.
**✅✅ Steps 1–2 (finite closed form + smoothness) COMPLETE for N=1 (2026-07-31, `MixtureHSDCF.lean`,
axiom-clean, no sorries).**  Mirrors the first-order `innerDCF_N1_contDiffOn`.  `qpConv_N1_contDiffOn`
(the self-conv is `ContDiffOn (0,R₀₀)`): on the core the overlap resolves (`∫_0^R = ∫_0^x[≡0] + ∫_x^R`,
`pMixEntry → quad` on `[x,R]`), the integrand becomes `(quad)(quad)`, and the `∫` equals the closed-form
atom `integral_quad_mul_quad` — got `ContDiff` **without writing the degree-5 polynomial** via
`funext (fun x => integral_quad_mul_quad …) ⇒ (fun x => ∫…) = (fun x => ⟨atom RHS⟩)`, then `fun_prop`.
Plus `qpConv_N1_contDiffOn_neg` (`(−R,0)`, overlap `[0,x+R]`), `cHSmixRaw_N1_contDiffOn`(`_neg`)
(`= qFwd + pMixEntry − qpConv`), and the headline **`cHSodd_N1_contDiffOn`** (the DCF `2π√ρ·r·c^HS` is
`ContDiffOn (0,R₀₀)`, via `cHSmixRaw(0,R) − cHSmixRaw∘neg`).  New reusable atoms: `pMixEntry_bounded`,
`qpConv_integrand_intervalIntegrable`, `integral_quad_mul_quad`.  Remaining DCF-side: general-N (the
`λᵢⱼ` knot ⇒ two pieces, like `dcfOdd_contDiffOn_upper/lower`); then the core-seed/Wertheim.
**✅ `cHSodd` done + MML.8 trace (2026-07-31).**  The normalization/odd-part (#2) was **not a theorem but a
def-pattern**: the first-order DCF is *defined* as the odd part `dcfOdd = fun x => Wmix x − Wmix (−x)`
(`= 2π√ρ·r·c^(1)`); mirrored as `cHSodd = fun x => cHSmixRaw x − cHSmixRaw (−x)` (`= 2π√ρ·r·c^HS`, since
`r·c` is odd), with `cHSodd_odd` + `cHSodd_support_subset [−Rᵢⱼ,Rᵢⱼ]`.  **Trace conclusion — the c_HS/seed
line is on the critical path, not redundant:** `Ĥ₁ = S₀Ĉ₁S₀`, `S₀ = I+Ĥ₀`, dressing (done) ⇒
`h₁ = c₁ + h₀⋆c₁ + c₁⋆h₀ + h₀⋆c₁⋆h₀`, and since `Ĉ₁` is HS-pole-free **every HS pole of `h₁` is in the
three `h₀`-dressed terms** ⇒ MML.8's residual is `h₀` (the zeroth-order HS RDF) = the OZ★ solution
`matBaxterPsi`.  The momentum route to `h₀` (`(I−Cmix0)⁻¹−I`) is the *circular* ML-collapse; the chosen
non-circular route is `matOzStar_unique` (uniqueness, done, **abstract `Phi`**) + a **concrete
`matBaxterPsi` existence** (= `hclaimA`, needs concrete `Phi = c_HS`).  So the single missing MML.8 input
is `h₀ = matBaxterPsi` as a concrete `MatOZStar` solution — `c₁`/dressing/uniqueness are all done.

**✅✅✅ DCF-side smoothness COMPLETE — general-N `cHSodd` two-piece (2026-07-31, axiom-clean, build 8717,
30 defs/theorems in `MixtureHSDCF.lean`).**  For `σⱼ≥σᵢ` (`λᵢⱼ≥0`) the knot `λᵢⱼ` splits the physical
core `(0,Rᵢⱼ)`; `cHSodd` needs `cHSmixRaw` on the reflected core `(−Rᵢⱼ,0)` too.  Reflected pieces
mirror the forward ones with k-free edges: **`qpConv_contDiffOn_upper_neg`** on `(−Rᵢⱼ,−λᵢⱼ)` [window
splits at the **top** `x+Rⱼₖ`, above which `pMixEntry(x−t)=0`; resolved `∫_{λᵢₖ}^{x+Rⱼₖ}`; new edge
`λᵢₖ−Rⱼₖ=−Rᵢⱼ`; `hvanish` via `ae_of_all` — the `Ioc` left-open endpoint gives the strict `x+Rⱼₖ<t`
for free, no `∀ᵐ y≠…` trick] + **`qpConv_contDiffOn_lower_neg`** on `(−λᵢⱼ,0)` [FULL window, no split;
`hlam` **redundant→`_hlam`**: domain nonempty ⟹ `−λᵢⱼ<x<0` ⟹ `λᵢⱼ>0` for free].  Both reflected
`cHSmixRaw` pieces (`cHSmixRaw_contDiffOn_upper_neg`/`_lower_neg`): `qFwd_ij=0`, `pMixEntry_ji`=quad ⇒
`= pMixEntry − ∑ₖ qpConv`.  Then **`cHSodd_contDiffOn_upper`** `(λᵢⱼ,Rᵢⱼ)` + **`cHSodd_contDiffOn_lower`**
`(0,λᵢⱼ)` via `cHSmixRaw(x)−cHSmixRaw(−x)`, `.comp contDiff_neg.contDiffOn` mapping each physical piece
into its reflection (same shape as `cHSodd_N1_contDiffOn`).  ⇒ **`cHSodd = 2π√ρ·r·c^HS` is `ContDiffOn`
the whole physical core for all N.**  The finite-closed-form/smoothness DCF side is now closed; what
remains for MML.8 is the core-seed/Wertheim (`h₀=matBaxterPsi` concrete) + the `cHSmixRaw↔Cmix0`
inverse-transform, NOT any further smoothness.

**✅✅ SECOND-CONVOLUTION SEED CHAIN (2026-08-01, `MixtureBaxterSeed.lean`, axiom-clean, build 8717).**
The MML.8 seed crux `h₀=matBaxterPsi` needs `Ψ⋆Q₊⋆Q₋ = r·c_HS` (scalar `baxter_psi_conv_eq_phi`).
Claims (A) [`matBaxterU_outer`, u≡0 outer] and (B) [`matBaxterU_core`, u affine on core] were already
done; I connected them to the full seed, isolating the ONE remaining gap to a pure moment identity.
Five theorems mirroring the scalar `baxter_seed_at_psi`/`baxter_psi_conv_eq_phi`/`baxter_core_seed`:
* **`matBaxterUQm_core_reduce`** — on `0<r<σ`, the 2nd-conv `∫₀^σ` collapses to `∫₀^{σ−r}`; the
  `[σ−r,σ]` tail vanishes **exactly** (`r+t≥σ ⟹ uₖⱼ(r+t)=0` by claim A). Support + integrability only.
* **`matBaxterUQm_eq_rPhi_of_seed`** — `matBaxterUQm = r·Φ` on ALL `r>0` from an abstract core-seed
  hyp; core = reduce + seed, outer = `matBaxterUQm_zero_of_uOuter` (done) + `Φ` outer-vanishing.
* **`matBaxterUQm_coreSeed_moment`** — substitutes claim (B) (a.e. — the endpoint `t=σ−r` samples
  `r+t=σ`, outside the open core) to rewrite the seed LHS into the explicit **row-moment** form
  `(r·(∑ₖM₀ᵢₖ−1)−∑ₖM₁ᵢₖ) − ∑ₖ∫₀^{σ−r}Qᵢₖ·((r+t)(∑ₗM₀ₖₗ−1)−∑ₗM₁ₖₗ)`, `M₀ᵢₖ=∫₀^σQᵢₖ`, `M₁ᵢₖ=∫₀^σtQᵢₖ`.
* **`matBaxterUQm_eq_rPhi_of_momentSeed`** — the **MML.8-ready** form: `matBaxterUQm ≡ r·Φ` given ONLY
  the pure moment identity `hMomentSeed`; ALL support/integrability/(A)/(B)-substitution/regime-split
  discharged here. Supply `hMomentSeed` (equal-diameter, delta-free) ⇒ `matBaxterUQm ≡ r·c_HS`.
* **`matBaxterUQm_momentSeed_fin_one_of_scalar`** — N=1 non-vacuity: `hMomentSeed` **is** the proved
  scalar `baxter_core_seed` (`Fin.sum_univ_one` + `baxterM0_eq`/`baxterM1_eq`) ⇒ the hypothesis is
  DISCHARGEABLE, the seed-side analog of `matOZStar_fin_one_of_scalar`.
The remaining seed gap is now exactly the **general-N matrix Wertheim–Thiele moment identity** (row
moments of the concrete `WHSupports.q0MixEntry` matched to `c_HS`), rigorous for **equal diameters**.

**✅✅✅ GENERAL-N EQUAL-DIAMETER matrix `baxter_core_seed` PROVEN (2026-08-01, axiom-clean, build 8717).**
The `hMomentSeed` gap is CLOSED for equal diameters at general `N`.  **Physics:** the Lebowitz PY
coefficients `Q0phys i j`, `Qppphys j` (`MatrixQ0.lean`) depend on `σᵢ,σⱼ` only, so for a common
diameter they are constant across species and the Baxter-factor **rows collapse** to the one-component
scalar factor at the total density: `∑ₖ Qᵢₖ(u) = q0_poly η σ ρ(u)`, `ρ = ∑ₖρₖ`, `η = πρσ³/6`.  Two
theorems:
* **`matBaxterUQm_momentSeed_of_rowSum`** — under `hrow : ∀ i, ∀ u ∈ [0,σ], ∑ₖ Qᵢₖ u = q0_poly η σ ρ u`,
  the matrix moment identity **is** the scalar `baxter_core_seed`.  Proof: `∑ₖM₀ᵢₖ = M₀`, `∑ₖM₁ᵢₖ = M₁`
  (`integral_finsetSum` + `integral_congr`·`hrow` + `baxterM0_eq`/`baxterM1_eq`); the affine factor is
  then `k`-independent (`simp only [hM0,hM1]`); the coupling `∑ₖ ∫ Qᵢₖ·A` pulls the row-sum inside
  (`Finset.sum_mul`) to `∫ q0_poly·A`; `exact baxter_core_seed`.  `Φ = c_HS` is the SINGLE one-component
  PY DCF (equal-diameter species = colour labels — the classical same-size-additive result).
* **`matBaxterUQm_eq_rcHS_of_rowSum`** (capstone) — the full `matBaxterUQm = Ψ ⋆ Q₊ ⋆ Q₋ ≡ r·c_HS` on
  ALL `r>0`, general-`N` equal-diameter, feeding the row-sum seed to `matBaxterUQm_eq_rPhi_of_momentSeed`
  (Φ = `fun _ _ => c_HS`, outer-vanishing = `c_HS_outer`).  **The matrix OZFIX.15 seed at general N,
  delta-free, is DONE** — no remaining hypothesis beyond `hrow` + claim-(A)/core-value regularity.
Pitfalls: `integral_finsetSum` takes `s` **implicit** (no `_`); row-sum must be `Icc 0 σ`-restricted
(q0_poly ≠ 0 off the support); unused `∀`-binder ⇒ `_j`.

**✅ `hrow` DISCHARGED for the concrete `q0MixEntry` (2026-08-01, `MixtureRowSum.lean`, axiom-clean,
build 8718).**  `q0MixEntry_rowSum_eq_q0_poly`: for a common diameter (`X.σ k = σ`) with the
**non-symmetric density-weighted** PY coefficients `X.Q0 i k = ρₖ·q_prime_py η σ`,
`X.Qpp k = ρₖ·q_doubleprime_py η` (the convention matching the seed's bare core value `Ψₖⱼ = −v`), the
row-sum of the concrete kernel is `∑ₖ q0MixEntry X i k u = q0_poly η σ (∑ₖρₖ) u` on `[0,σ]`.  Since
`λᵢₖ = 0`, `Rᵢₖ = σ`, each entry collapses to `ρₖ·(q'(u−σ)+q''(u−σ)²/2)`, and `Finset.sum_mul` +
`q0_poly_inner` give the one-component factor at total density.  **Physics:** the density sits on the
**column** `ρₖ` (not the symmetric `√(ρᵢρₖ)`, which would not collapse); this is consistent with
`Q0phys` reducing to exactly `q_prime_py` at a single equal-diameter species.  It **plugs directly** as
the `hrow` argument of `matBaxterUQm_momentSeed_of_rowSum` (verified), so with only
`IntervalIntegrable (q0MixEntry X i k) 0 σ` the matrix core seed holds for the concrete kernel.
Pitfall: apply `indicator_of_mem` **before** rewriting `R i k → σ` (else the indicator's *set* changes
and `indicator_of_mem` no longer matches).

**✅✅ CONCRETE `q0MixEntry` matrix core seed UNCONDITIONAL (2026-08-01, `MixtureRowSum.lean`, build 8718).**
Added the two integrability lemmas — **`q0MixEntry_intervalIntegrable`** (bounded measurable
indicator-quadratic ⇒ interval-integrable, via `Measurable.indicator` + `exists_bound_of_continuousOn`
+ `integrableOn_of_bounded`) and **`q0MixEntry_mul_id_intervalIntegrable`** (`t·q0MixEntry` via
`.continuousOn_mul`) — and the capstone **`matBaxterUQm_momentSeed_q0MixEntry`**: the equal-diameter
matrix Wertheim–Thiele moment identity `= r·c_HS` for `Q = q0MixEntry`, with **no integrability
side-condition left**.  `matBaxterUQm_momentSeed_of_rowSum` is now fully discharged for the physical
kernel — `hMomentSeed` is unconditionally proven for the concrete `q0MixEntry` at equal diameters.
**Remaining for MML.8:** the Ψ-side hypotheses `hUouter` (claim A) / `hint` / `hcore` for the concrete
`matBaxterPsi`, then the KDEF `hfact` and shell bridge `hbridge`, to feed `matOzStar_of_regular`.

**✅ `hcore` + `hUouter` DONE for the constructed `matBaxterPsi` (2026-08-02, `MixtureRowSum.lean`,
axiom-clean, build 8718).**  `matBaxterPsi_hcore`: `Ψcore = fun _ _ v => −v` ⇒ `matBaxterPsi … k j v = −v`
on `(−σ,σ)` (one-liner off `matBaxterPsi_core`).  **`matBaxterPsi_hUouter`** (claim A): for **continuous**
matrix Baxter data `Qm,Fm` (`Qm` vanishing above `σ`, `Fm` = core-convolution forcing), the glued
`Ψ = matBaxterPsi (matBaxterPsiOuterFun σ Qm Fm) (fun _ _ v => −v) σ` satisfies `matBaxterUᵢⱼ(r) = 0` on
`[σ,∞)`.  Wires `matBaxterU_outer` — `hQcont`/`hQsupp` entrywise, `hcore` = `matBaxterPsi_core`,
`houter_cont` = `matBaxterPsiOuterFun_continuous` + `matBaxterPsi_outer` (`ContinuousOn.congr`), and
`hrenewal` from `matBaxterPsiOuter_matRenewalEq` (Banach global Volterra) with `Ψouter → Ψ` rewritten by
`matBaxterPsi_outer` on `[σ,r]`.  **Kernel note:** the renewal is built by Banach Volterra, which needs
`Continuous Qm`, so the **seed kernel is the continuous `q0_poly`-matrix, not the truncated
`q0MixEntry`** (which jumps at `0`).  They agree on `[0,σ]` — all that `matBaxterU`/`matBaxterUQm`
sample — so the moment seed is identical; the **final assembly should use one continuous `Q`** (the
density-weighted `q0_poly`-matrix) and re-derive `hrow`/`hMomentSeed`/integrability for it (same `[0,σ]`
argument, integrability *easier* since continuous).

**✅ `hint` DONE for the constructed `matBaxterPsi` (2026-08-02, `MixtureRowSum.lean`, axiom-clean,
build 8718).**  Seven theorems — a genuine measure-theory chain.  `matBaxterPsi_hint` gives
`IntervalIntegrable (fun t => (Qm t)ᵢₖ · matBaxterU Ψ Qₑ σ ₖⱼ(r+t)) 0 σ`.  Chain: `convWindow_measurable`
(`x ↦ ∫₀^σ Q(t)·Psi(x−t)` measurable via `StronglyMeasurable.integral_prod_right` after rewriting the
interval integral as an `Ioc`-indicator) → `matBaxterU_measurable` (`Psi − ∑ₗ` convWindow) →
`matBaxterU_bddOn` on `Icc a b` (`|Psi| + ∑ₗ`conv-bounds, each via `norm_integral_le_of_norm_le_const`;
`choose` + `abs_sum_le_sum_abs` + `gcongr`) → `matBaxterU_hint_of_regular` (general: `Q` continuous +
`Psi` measurable + bddOn ⇒ hint, via `integrableOn_of_bounded` then `.continuousOn_mul`).  Glued-`Ψ`
regularity: `matBaxterPsi_entry_measurable` (`Measurable.ite` on `Ici σ` / `Iic (−σ)`) +
`matBaxterPsi_entry_bddOn` (three cases; `exists_bound_of_continuousOn` on the compact `uIcc`, reflected
branch via `−x ∈ uIcc (−b) (−a)`).  The glued `Ψ` is only bounded-measurable (may jump at `±σ`) — fine
for integrability.  **The Ψ-side is now complete: `hcore` + `hUouter` + `hint` all discharged.**

**✅ KDEF `hfact` DONE for equal diameters (2026-08-02, `MixtureRowSum.lean`, axiom-clean, build 8718).**
Key algebra: with `Qᵢₖ = wᵢₖ·q0_poly`, `Kᵢⱼ = wᵢⱼ·baxterK`, the matrix self-convolution factors as
`matSelfConvᵢⱼ = (∑ₖ wᵢₖwⱼₖ)·(q0⋆q0)`, so `ρK = Q − matSelfConv` reduces to the scalar
`rho_baxterK_eq_q0_self_conv` **iff `W` is idempotent** (`∑ₖ wᵢₖwⱼₖ = wᵢⱼ`).
`matBaxterFactorization_of_idempotent` (general idempotent `W`) + `physWeight_idempotent` (the physical
symmetric `wᵢⱼ = √(ρᵢρⱼ)/ρ` is idempotent, `ρ = ∑ₖρₖ`) + `matBaxterFactorization_equalDiam` (concrete
`Q = √(ρᵢρⱼ)/ρ·q0_poly`, `K = √(ρᵢρⱼ)/ρ·baxterK`).

**⚠️ Convention caveat (surfaced here).**  The KDEF wants `W` **idempotent** (the symmetric
`√(ρᵢρⱼ)/ρ` qualifies), whereas the moment-seed `hrow` wants **row-sums 1** (`∑ₖ wᵢₖ = 1`).  Both hold
for the same `Q` **only when `W = J/N`, i.e. equal densities** (`ρₖ = ρ/N` ⇒ `√(ρᵢρⱼ)/ρ = 1/N`).  The
root cause is the abstract machinery's design — bare `hcore` (`Ψ = −v`, not `√`-weighted) and a single
scalar `ρ` in `MatOZStar` (not per-species `ρₖ`) — which is physically consistent only for equal
densities.  (My earlier `q0MixEntry` `hrow` used the column `X.Q0 = ρₖq'`; at equal densities that
equals `q0/N`, so everything reconciles.)  **Net: full MML.8 closure via seed + KDEF + bridge is
rigorous for equal diameters *and equal densities* (`W = J/N`); `hfact` itself holds for any idempotent
`W`.**

**✅ `hbridge` (matrix OZFIX.19) DONE for the weighted kernel (2026-08-02, `MixtureRowSum.lean`,
axiom-clean, build 8718).**  `radial3d_conv_const_mul` (`radial3d_conv (c·f) g r = c·radial3d_conv f g r`,
the constant pulls through both nested integrals) + `matBridge_weighted`: with `Φᵢₖ = wᵢₖ·c_HS`,
`Kᵢₖ = wᵢₖ·baxterK` (the **same** weight as the KDEF), `r·matRadialConv Φ G = matShellConv K G` holds —
via `matRadialConv_eq_matShellConv`, pulling `wᵢₖ` out of `radial3d_conv` and the shell integral, each
per-entry identity being the scalar `radial3d_conv_eq_baxterK_shell` (taking the per-entry
`hshell`/`hjoint` integrability, exactly as `matShellBridge_fin_one_of_scalar`).  **Remaining for full
`matOzStar_of_regular`:** `hQ` (Q continuous — easy for the weighted `q0_poly` kernel), `hpm`/`hpb`
(`oddExt(Ψ/x)` measurable + bounded — the analog of `matBaxterPsi_entry_measurable`/`_bddOn`), and
**`hclaimA`** — the shell-form renewal `Ψ = rΦ + (Q-shell − selfConv-shell)`, the connective piece
linking the seed `matBaxterUQm = r·Φ` to the shell form (the last substantial step).

**✅✅✅ EQUAL-DIAMETER MATRIX OZ★ COMPLETE — direct reduction (2026-08-02, `MixtureRowSum.lean`,
axiom-clean, build 8718).  This SUPERSEDES the `hclaimA`/seed/KDEF/bridge route for equal diameters.**
Key insight: for the physical **symmetric** weight `wᵢⱼ = √(ρᵢρⱼ)/ρ`, the *whole* solution is
`wᵢⱼ·(scalar)` — `Ψᵢⱼ = wᵢⱼ·baxterPsi`, `Φᵢⱼ = wᵢⱼ·c_HS` — so `MatOZStar` reduces **directly** to the
proved (axiom-free) scalar `baxterPsi_ozstar`, with no seed/claimA/KDEF/bridge at all.
* `radial3d_conv_const_mul_right` (linearity in the 2nd argument) — with `radial3d_conv_const_mul`
  (1st argument, from `hbridge`), both weights pull out of `radial3d_conv`.
* `matOzStar_equalDiam` — for a chained-idempotent `W` (`∑ₖ wᵢₖwₖⱼ = wᵢⱼ`): the `matRadialConv` species
  sum collapses (`← Finset.sum_mul` + `W·W = W`), each entry `= wᵢⱼ·baxterPsi_ozstar`.
* `physWeight_idempotent_chained` (the physical `√(ρᵢρⱼ)/ρ` is chained-idempotent) +
  `matOzStar_equalDiam_phys` — the concrete `MatOZStar (√(ρᵢρⱼ)/ρ·baxterPsi) (√(ρᵢρⱼ)/ρ·c_HS) ρ`: **the
  equal-diameter mixture Ornstein–Zernike identity, at *any* densities.**
**Resolves the convention caveat:** the symmetric `Ψ = w·baxterPsi` has core `−wᵢⱼv` (not the bare
`−v`), so it is the *symmetric-convention* physical solution — self-consistent for **unequal
densities** (the bare-`hcore` seed route needed equal densities; the direct route needs neither).  The
seed machinery (all six hypotheses discharged) remains the route for the general unequal-**diameter**
case and for connecting `Ψ` to `matBaxterPsiOuterFun` via Volterra uniqueness.  **Equal-diameter MML.8
core: DONE.**

**Unequal-diameter direction — odd structure + shell→flat (2026-08-03, `MixtureRowSum.lean`,
axiom-clean, build 8718).**  For unequal diameters the `wᵢⱼ·scalar` factorization *fails* (each pair
`(i,j)` has its own `σ_ij`, `λ_ij`, DCF shape), so the coupled seed route is genuinely needed.  The
*diameter-agnostic* building blocks of the shell form: `matBaxterPsi_odd` (the glued `Ψ` is odd when the
core is odd — the reflection branch `−Ψouter(−v)` makes it so), `oddExt_div_self_of_odd`
(`oddExt(ψ/·) = ψ` for odd `ψ`, `v ≠ 0`), and `shell_eq_flat_of_odd` (the OZ★/`hclaimA` shell integrand
collapses a.e. to the flat renewal form).  **Genuine open obstructions for unequal diameters:** (a) the
flat matrix Wertheim–Thiele seed `matBaxterUQm = r·c_HS,ij` with a *per-pair* DCF — the moment-seed
`hrow` reduction needs a single `q0_poly` and fails; (b) the `matSelfConv` reindex inside `hclaimA`
needs a **symmetric** `Q`, but the unequal-diameter Baxter factor is *not* symmetric
(`λ_ij = −λ_ji`, different `Qpp`), which the equal-diameter symmetric weight sidesteps.  `hbridge` *is*
unequal-diameter-ready (`matRadialConv_eq_matShellConv_of_shellKernel`, per-entry `c`-shapes).  These
remaining pieces are research-scale.

**Obstruction (b) pinned (2026-08-03, `matSelfConv_shift`, axiom-clean, build 8718) — a precise negative
finding.**  The seed→`hclaimA` gap: `matBaxterUQm` uses `Q i k` (not the transpose `Q k i`) in its second
convolution, so the double term expands to the *chained* `∑ₖ∑ₘ Qᵢₖ(t)Qₖₘ(s)Ψₘⱼ(r+t−s)` (`= Q·Q·Ψ`).
Reindexing (`matDblConv_reindex`, which additionally needs `Q` symmetric to make both factors share the
second index) yields `∑ₘ ∫ (matSelfConvᵢₘ·Ψₘⱼ(r+u) + matSelfConvₘᵢ·Ψₘⱼ(r−u))`.  But `hclaimA` weights
*both* `r±u` terms by `matSelfConvᵢₖ`, so discharging it requires **`matSelfConv` symmetric**.
`matSelfConv_shift` proves it is *not*: `matSelfConvᵢⱼ(u) = ∑ₖ ∫₀^{σ−u} Qᵢₖ(τ+u)Qⱼₖ(τ)` puts the `+u`
shift on the `i`-factor, `(j,i)` on the `j`-factor — unequal for a non-symmetric `Q`.  For the
equal-diameter symmetric factor it works; for the unequal-diameter one (`λ_ij = −λ_ji`, `Qpp_j ≠ Qpp_i`)
it genuinely blocks.  **Resolution needs a symmetrised matrix seed (transpose `Q k i` in the second
Baxter convolution, giving `Q·Qᵀ·Ψ = matSelfConv` correctly) or a new reindex — i.e. a real redefinition
of the matrix seed for `N ≥ 2`, research-scale.**

**Symmetrised seed prototyped (2026-08-03, `MixtureRowSum.lean`, axiom-clean, build 8718) — the
constructive fix for (b).**  The transpose goes in the *inner* factor of the second convolution:
`matBaxterUt i j r = Ψᵢⱼ(r) − ∑ₘ ∫ Qₘᵢ(s)·Ψₘⱼ(r−s)` (transpose `Qₘᵢ`), and
`matBaxterUQmSym = matBaxterU − ∑ₖ ∫ Qᵢₖ(t)·matBaxterUt(k,j)(r+t)`.  `matBaxterUQmSym_unfold` (`rfl`)
exhibits the double term `∑ₖ ∫ Qᵢₖ(t)·(Ψₖⱼ(r+t) − ∑ₘ ∫ Qₘₖ(s)·Ψₘⱼ(r+t−s))` — both `Qᵢₖ` and `Qₘₖ`
carry the **second** index `k`, exactly the `matSelfConv` correlation shape (vs the current seed's
chained `Qₖₘ`).  `matBaxterUQmSym_of_symm` proves it coincides with `matBaxterUQm` for symmetric `Q`
(so it is a faithful generalization: identical at `N = 1` and for the equal-diameter factor, differing
only in the asymmetric unequal-diameter case).  By hand, `matBaxterUQmSym`'s double term reindexes (via
`matDblConv_reindex`) to `∑ₘ ∫ (matSelfConvᵢₘ·Ψₘⱼ(r+u) + matSelfConvₘᵢ·Ψₘⱼ(r−u))`.  **Full closure still
needs restating `hclaimA`/`matShellConv` with this *asymmetric* `matSelfConv` split (`matSelfConv_shift`
shows the symmetric form is wrong for `N ≥ 2`) and discharging the reindex's integrability — but the
seed *object* is now correct for `N ≥ 2`.**

**Asymmetric assembly refactored + reframing (2026-08-03, `MixtureRowSum.lean`, axiom-clean, build 8718).**
`matShellConvAsym Kp Km G` (`Kp` on `r+u`, `Km` on `r−u`; `matShellConv` = the diagonal `Kp = Km`),
`matShellConvAsym_kdef_split` (two-kernel KDEF `ρKp = Q − matSelfConv`, `ρKm = Q − matSelfConvᵀ`, splits
into the `Q`-shell minus the *asymmetric* `matSelfConv`-shell), and `matShellConvAsym_diag`
(`Kp = Km` collapses to `matShellConv`).  **Key reframing (`matSelfConv_shell_symm`):** `matSelfConv`
symmetry `matSelfConvᵢₖ = matSelfConvₖᵢ` is a **physical** property — `Q̂(k)·Q̂ᵀ(−k) = I − Ĉ` is symmetric
because the DCF `Ĉ` is (`cᵢⱼ = cⱼᵢ`), holding for *any* diameters, not an algebraic one (`matSelfConv_shift`
shows it fails for arbitrary `Q`).  Under it, the corrected seed's asymmetric shell term equals the
symmetric term the *current* `matOzStar_of_shellClaims` consumes.  **So the unequal-diameter route is
now precise:** corrected seed (`matBaxterUQmSym`) + `matSelfConv` symmetry ⇒ symmetric `hclaimA` ⇒ the
existing assembly, verbatim, all diameters.  Obstruction (b) reduces to a **single physical theorem**:
`matSelfConv` symmetry for the physical Baxter factor (`∑ₗ ∫ Qᵢₗ(τ+u)Qₖₗ(τ) = ∑ₗ ∫ Qₖₗ(τ+u)Qᵢₗ(τ)`, from
the WH factorization of the symmetric PY DCF) — no longer a mysterious block.  The asymmetric machinery
is the fallback if that symmetry proves hard.

**`matSelfConv` symmetry proven from the DCF-symmetry hypothesis (2026-08-03, `MixtureRowSum.lean`,
axiom-clean, build 8718) — obstruction (b) reduced to one clean hypothesis.**  The DCF symmetry in
real-space form is `hMsym : ∀ i k t s, ∑ₗ Qᵢₗ(t)Qₖₗ(s) = ∑ₗ Qᵢₗ(s)Qₖₗ(t)` (the two-time self-correlation
kernel is symmetric in `(t, s)`; `= Q̂Q̂ᵀ(−k) = I − Ĉ` symmetric, not algebraic).
`matSelfConv_symm_of_corrSymm`: `hMsym` + integrability ⇒ `matSelfConvᵢₖ = matSelfConvₖᵢ` (move the sum
inside via `integral_finsetSum`, swap `(t, t−u)` with `hMsym`, `mul_comm`).
`matSelfConv_shell_symm_of_corrSymm` (capstone): `hMsym` ⇒ the corrected seed's asymmetric shell term
equals the symmetric term the existing assembly consumes.  **Full unequal-diameter chain:** corrected
seed (`matBaxterUQmSym`, correlation double term) → reindex → asymmetric `matSelfConv` → `hMsym` →
symmetric `hclaimA` → existing `matOzStar_of_shellClaims`.  **So obstruction (b) collapses entirely to
`hMsym`** — a named, provable-in-principle physical hypothesis.  Remaining: prove `hMsym` for the
concrete `q0MixEntry` (from the WH factorization of the symmetric PY DCF, or a direct computation),
discharge the reindex integrability, and wire `matBaxterUQmSym` through the seed chain.

**`hMsym` proven for the concrete `q0MixEntry`, separable / equal-diameter case (2026-08-03,
`MixtureRowSum.lean`, axiom-clean, build 8718).**  `hMsym` holds for any **separable** factor
`Qᵢₗ = wᵢₗ·q̂` (one common profile) — the two-time kernel `wᵢₗwₖₗ·q̂(t)q̂(s)` commutes term by term, no
factorization needed (`hMsym_of_separable`).  `q0MixEntry_hMsym_equalDiam`: for a common diameter with
the column-weighted coefficients (`X.Q0 i l = ρₗ·a`, `X.Qpp l = ρₗ·b` — the same hypotheses as
`q0MixEntry_rowSum_eq_q0_poly`), every entry is `ρₗ·(indicator quadratic)`, separable, so `hMsym` holds.
This **discharges `matSelfConv_symm_of_corrSymm`'s hypothesis for the concrete equal-diameter kernel**,
making the whole seed → `hMsym` → assembly chain concrete at equal diameters.  **For *unequal* diameters
`q0MixEntry` is not separable** (each pair has its own `σ_il`, `λ_il` profile), so `hMsym` there
genuinely needs the WH factorization of the symmetric PY DCF — the last physical open step.  Net:
equal-diameter is now closed by *two* independent routes (the direct `matOzStar_equalDiam_phys` and the
seed → `hMsym` chain); the unequal-diameter case is gated solely on the non-separable `hMsym`.

**Corrected route: `matSelfConv` symmetry from the WH factorization, not `hMsym` (2026-08-03,
`MixtureRowSum.lean`, axiom-clean, build 8718).**  Attempting the non-separable `hMsym` revealed it is
*stronger* than the WH factorization supplies: `hMsym`'s Fourier content is `∑ₗ Q̂ᵢₗ(ω)Q̂ₖₗ(ν)` symmetric
in `ω ↔ ν` (two-variable), whereas the WH factorization only gives `Q̂(k)·Q̂ᵀ(−k) = I − Ĉ` symmetric
(single-variable).  So for a non-separable (unequal-diameter) `Q`, `hMsym` need not hold — but
`matSelfConv` symmetry (the object actually needed) still does, from the factorization.
`matSelfConv_symm_of_dcf`: DCF symmetry (`hCsym`) + the WH factorization on the core (`hfact`:
`matSelfConv = C`, the real-space content of `Cmix0 = I − Q̂₀Q̂₀ᵀ(−k)`, MRS.6) ⇒ `matSelfConv` symmetric.
`matSelfConv_shell_symm_of_dcf`: same hypotheses ⇒ the asymmetric shell term equals the symmetric one
(a.e. on the core).  **So obstruction (b) is discharged for *any* diameters, modulo casting the
already-proven Fourier `Cmix0_factorization` to its real-space core form `matSelfConv = C`.**  The
`hMsym` route stays valid for the separable / equal-diameter case; the `_of_dcf` route is the general
one, and it grounds the last step in an *existing* codebase result rather than a new physical theorem.

**Cast scoped (2026-08-03, `matSelfConv_symm_of_transform`, axiom-clean, build 8718).**  The
`Cmix0_factorization → matSelfConv` cast factors into exactly two inputs:
* **(A) momentum symmetry — already proved.**  `Tfun z = Q̂₀(z)Q̂₀ᵀ(−z)` is symmetric for the physical
  N=2 factor: `MixtureRealSpace.swap_offdiag_of_keys` (MRS.7, from the two PY key relations
  `Q0phys_key_relation`/`Qppphys_key_relation`) + `T0_isSymm_of_swap` + `fin2_transpose_eq_iff_offdiag`.
  (`Cmix0_factorization` itself is *definitional*, `Cmix0 := 1 − Q̂Q̂ᵀ(−k)`.)
* **(B) the transform bridge — the sole gap.**  `matSelfConvᵢₖ(·) = InvLaplace(z ↦ (Tfun z)ᵢₖ)`,
  decomposing into: B1 `q̂ᵢₗ(z) = ∫ e^{−zt}q0MixEntry` (Baxter-factor Laplace = `q0_entry_c`); B2 the
  product↔correlation theorem `q̂ᵢₗ(z)q̂ₖₗ(−z) = ∫ e^{−zu}(Qᵢₗ ⋆̃ Qₖₗ)(u) du`; B3 the `∑ₗ` and the causal
  `∫ᵤ^σ` truncation (compact support of `q0MixEntry`); B4 transform injectivity.
`matSelfConv_symm_of_transform` proves `A + B ⇒ matSelfConv` symmetry, hence — via
`matSelfConv_symm_of_dcf` — obstruction (b) for any diameters.  **So the whole unequal-diameter program
reduces to (B) alone**, the analysis of a *known* Laplace correspondence, with everything else (the
corrected seed, the reindex, the asymmetric shell assembly, the momentum symmetry) already built and
axiom-clean.  This is the endpoint of the unequal-diameter scoping.

**B1 done — the Laplace transform of `q0MixEntry` (2026-08-03, `MixtureRowSum.lean`, axiom-clean,
build 8718).**  `laplace_baxter_quad`: `∫_λ^{λ+σ} e^{−zr}(Q0(r−R)+Q''(r−R)²/2) dr =
e^{−zλ}(Q0·p₁(σ,z)+Q''·p₂(σ,z))` with `p₁=(1−zσ−e^{−zσ})/z²`, `p₂=(1−zσ+(zσ)²/2−e^{−zσ})/z³`, by FTC
against the explicit antiderivative (`integral_eq_sub_of_hasDerivAt` + `exp_add` for the endpoint).
`q0MixEntry_laplace`: the indicator collapses on `[λᵢⱼ, Rᵢⱼ]` and `Rᵢⱼ = λᵢⱼ + σᵢ`, so
`∫ e^{−zt} q0MixEntry X i j t = e^{−zλᵢⱼ}(Q0ᵢⱼ·p₁(σᵢ,z)+Q''ⱼ·p₂(σᵢ,z))`.  **`p₁`, `p₂` match the momentum
`MatrixQ0.q0_entry`'s function part exactly** (`q0_entry = δ − rho_geo·e^{−λz}(Qp·p₁+Q''·p₂)`), so
`Laplace(q0MixEntry) = −(q0_entry non-delta)/rho_geo` — the density-normalization convention.  So **B1,
the real↔momentum Baxter-factor correspondence, is established.**
Pitfall: `(hasDerivAt_id r).const_mul z |>.neg` hits an instance diamond — use `.const_mul (-z)` +
`simpa [neg_mul]`.

**B2 done — the Laplace product↔correlation theorem (2026-08-03, `MixtureRowSum.lean`, axiom-clean,
build 8590).**  `laplace_product_eq_corr`:
`(∫ f(t)e^{−zt} dt)·(∫ g(s)e^{zs} ds) = ∫ (∫ f(t)g(t−u) dt)·e^{−zu} du` — the product of the two
one-sided Laplace transforms `q̂ᵢₗ(z)`, `q̂ₖₗ(−z)` equals the Laplace transform of the cross-correlation
`(f ⋆̃ g)(u) = ∫ f(t)g(t−u) dt` (which is exactly the full-line `matSelfConv` summand).  Proof chain:
product → double integral (`← integral_prod_mul`), `∫→∫∫` (`integral_prod hjoint1`), **per-`t` inner
reflection** `s = t−u` (helper `integral_reflect_sub : ∫ s, H(t−s) = ∫ s, H s`, via
`integral_neg_eq_self` + `integral_add_right_eq_self` — note `integral_comp_sub_left` exists only for
interval integrals, not full-line), which turns `e^{−zt}e^{zs} = e^{−z(t−s)}` into `e^{−zu}`; then Fubini
swap `∫∫→∫∫` (`integral_integral_swap hjoint2`) and pull out `e^{−zu}` (`integral_mul_const`).  Takes two
joint-integrability hypotheses (`hjoint1` for the original product integrand, `hjoint2` for the reflected
`(t,u) ↦ f(t)g(t−u)e^{−zu}`) — both hold for the compactly-supported `q0MixEntry` (bounded × compact
support ⇒ `Integrable` on the product, to be discharged at the use site in B3).  With B1, this gives
`q̂ᵢₗ(z)·q̂ₖₗ(−z) = Laplace((Qᵢₗ ⋆̃ Qₖₗ))`.

**⚠⚠ B3 SCOPING — STRUCTURAL FINDING: the windowed `matSelfConv` is the WRONG (asymmetric) object; the
FULL-LINE correlation `R` is the symmetric one (2026-08-03).**  Scoping B3's truncation exposed that
`matSelfConv Q σ v i j = ∑ₖ ∫ᵥ^σ Qᵢₖ(t)Qⱼₖ(t−v) dt` does NOT equal the full-line correlation
`Rᵢⱼ(v) = ∑ₖ ∫_ℝ Qᵢₖ(t)Qⱼₖ(t−v) dt` for unequal diameters.  Substituting `t = s+v` (checked in Lean,
`intervalIntegral.integral_comp_add_right`) puts both orderings on the common window `[0,σ−v]`:
`matSelfConv(i,j)(v) = ∑ₖ ∫₀^{σ−v} Qᵢₖ(s+v)Qⱼₖ(s) ds`, `matSelfConv(j,i)(v) = ∑ₖ ∫₀^{σ−v} Qᵢₖ(s)Qⱼₖ(s+v) ds`
— differing only in the direction of the `+v` shift.  The upper cut `s>σ−v` contributes nothing (`σ ≥ Rᵢₖ`),
but the lower cut `s<0` DROPS a genuine causal tail: `Qⱼₖ(s) ≠ 0` on `s ∈ [λⱼₖ, 0)` whenever `λⱼₖ=(σₖ−σⱼ)/2 < 0`
(`σⱼ > σₖ`).  That dropped tail is governed by `λⱼₖ` for `(i,j)` but by `λᵢₖ` for `(j,i)` — **different tails ⇒
the windowed `matSelfConv` is genuinely asymmetric** (consistent with the already-proved `matSelfConv_shift`
non-symmetry).  The FULL-LINE `R` keeps both tails and IS symmetric: `𝓕(Rᵢⱼ)(k) = [Q̂(k)Q̂(−k)ᵀ]ᵢⱼ`
(B2 summed over `l`), symmetric in `(i,j)` by `swap_offdiag_of_keys`/MRS.7 (`I−Ĉ` symmetric) ⇒ by Fourier
injectivity `Rᵢⱼ = Rⱼᵢ`.  (Note `R` is additionally even, `Rᵢⱼ(v)=Rᵢⱼ(−v)`, since `Rⱼᵢ(v)=Rᵢⱼ(−v)`
algebraically.)  **Consequence for the unequal-diameter seed:** the seed's second convolution must be the
FULL-LINE correlation `R` (equivalently, a *pair-dependent* lower limit `v+λⱼₖ`, matching Baxter's actual
mixture causal limits `∫_{v+λⱼₖ}^{…}`), NOT the uniform-lower-limit-`v` `matSelfConv`.  For EQUAL diameters
`λ=0` there is no tail, `matSelfConv = R`, and both closed routes already hold — the uniform window was an
equal-diameter simplification.  **So B3 done right = ∑ₗ of B2 into the full-line `R`** (trivial, no truncation
subtlety); **B4 = Fourier injectivity, which Mathlib HAS** — `Continuous.fourierInv_fourier_eq`
(`𝓕⁻(𝓕 f)=f` for continuous integrable `f` with integrable `𝓕 f`) ⇒ injectivity axiom-clean, **no new axiom**.
The remaining engineering: (a) redo B1/B2 in the COMPLEX/Fourier convention `e^{−2πikt}` (mechanical — the
B2 proof is character-agnostic; `swap_offdiag` is already Fourier-side and Fourier inversion needs the
imaginary axis), (b) rebuild the KDEF `hfact` on the full-line correlation `R`, (c) discharge the
integrability side-conditions (compact support ⇒ `Integrable f`, `Integrable 𝓕f` from the piecewise-poly
decay).  **Net: the transform bridge closes obstruction (b) axiom-clean, but proving the FULL-LINE `R`
symmetric — the seed must be re-based on `R`, not the windowed `matSelfConv`.**

**B1/B2 complex (Fourier convention) DONE, axiom-clean (2026-08-03, `MixtureRowSum.lean`, build 8590).**
The `_c` variants carry a complex transform variable `z : ℂ` (Fourier transform at `z = 2πi·w`), matching
the imaginary-axis home of `swap_offdiag_of_keys` and enabling Mathlib Fourier inversion for B4:
* `laplace_baxter_quad_c (z : ℂ) (lam sigma Q0 Qpp : ℝ) (hz : z ≠ 0)` — same FTC proof as the real B1, with
  `Complex.exp`/`ofReal` casts.  Antiderivative deriv via `Complex.ofRealCLM.hasDerivAt` (deriv of `↑· : ℝ→ℂ`
  is `1`) + `.cexp`; the same `.const_mul (-z)` + `simpa [neg_mul]` dodge for the diamond; endpoint via
  `← Complex.exp_add` + `push_cast; ring_nf`; final `push_cast; field_simp; ring`.
* `integral_reflect_sub_c` (ℂ-valued reflection) + `laplace_product_eq_corr_c (f g : ℝ → ℂ) (z : ℂ)` — the B2
  proof is **character-agnostic**: identical Fubini chain (`integral_prod_mul`/`integral_prod`/
  `integral_integral_swap`/`integral_mul_const` all fire for `𝕜=ℂ`), only `Real.exp→Complex.exp` and casts.
* `q0MixEntry_laplace_c (X) (i j) (z : ℂ)` — the concrete entry's complex transform (indicator collapse +
  `push_cast; ring` + `laplace_baxter_quad_c`); at `z=2πi·w` this is the momentum `Q̂ᵢⱼ(w)` of MRS.7.
Remaining for `hbridge`: (B3) `∑ₗ` of `laplace_product_eq_corr_c` into the full-line correlation `R` +
discharge the two `Integrable` product hyps (compact support); (B4) specialize `z=2πi·w`, identify with
Mathlib `𝓕`, and apply `Continuous.fourierInv_fourier_eq` to `R(i,j)−R(j,i)` (transform `≡0` by MRS.7 ⇒
`R` symmetric); then re-base the seed/KDEF on `R`.

**B3 DONE — `∑ₗ` into the full-line correlation, fully UNCONDITIONAL (2026-08-03, `MixtureRowSum.lean`,
axiom-clean, build 8590).**  `matCorr X i j v := ∑ₗ ∫_ℝ (q0MixEntry X i l t)·(q0MixEntry X j l (t−v))`
(the symmetric full-line object) and `matCorr_laplace`:
`∑ₗ Q̂ᵢₗ(z)·Q̂ⱼₗ(−z) = ∫_ℝ matCorrᵢⱼ(v)·e^{−zv} dv` for every `z : ℂ`, **all integrability discharged**.
Structure:
* `laplace_sum_eq_corr_c` — the ALGEBRA (generic `Finset`/families): per-index `laplace_product_eq_corr_c`
  via `Finset.sum_congr`, then `← integral_finsetSum` (swap `∑`/`∫`), then `Finset.sum_mul` (pull `e^{−zv}`
  out of the row sum).  Takes the three integrability families as hypotheses.
* Integrability primitives for `q0MixEntry` (compact support `[λ,R]`, so bounded × finite-measure ⇒
  `Integrable` via `integrableOn_iff_integrable_of_support_subset` + `Measure.integrableOn_of_bounded`):
  `q0MixEntry_measurable`, `q0MixEntry_mul_exp_integrable` (1-D `(entry)·e^{wt}`, any `w:ℂ`),
  `q0MixEntry_abs_le` (global `|entry|≤C`), `q0MixEntry_corr_exp_prod_integrable` (**h2**, the 2-D box
  `Bt×ˢBu` bound: support in a box from both entries' cores, bounded by `Ci·Cj·E` with `E` bounding
  `‖e^{−zu}‖` on the compact `u`-range).
* Wiring in `matCorr_laplace`: **h1** = `Integrable.mul_prod` of two 1-D primitives (`w=−z`, `w=+z`;
  `simpa [neg_mul]` to match `e^{−(z·)}`); **h2** = the box lemma; **h3** = `h2.integral_prod_right`
  (integrate `t`, keep the lag `v`) `.congr` a pointwise `integral_mul_const` pulling `e^{−zv}` out.
  Pitfalls: `integral_prod_left` keeps first/integrates second — need `integral_prod_right`;
  `Complex.norm_ofReal` doesn't exist (use `Complex.norm_real`+`Real.norm_eq_abs`); disambiguate the
  Bochner `MeasureTheory.integral_mul_const` from the interval one by giving `r` explicitly.
**B4 DONE (up to 2 isolated inputs) — Fourier-inversion symmetry (2026-08-03, `MixtureRowSum.lean`,
axiom-clean, build 8590).**  `matCorr_symm`: `matCorr X i j = matCorr X j i`, reduced to exactly two
remaining inputs.  Pieces:
* **Fourier injectivity core** (general `ℝ→ℂ`, reusable): `fourierInv_zero_real` (`𝓕⁻ 0 = 0` via
  `Real.fourierInv_eq`+`simp`); `fourier_sub_real` (`𝓕(f−g)=𝓕f−𝓕g` via `Real.fourier_eq` inner-product
  form + `integral_sub`, integrand integrability from `Real.fourierIntegral_convergent_iff`);
  **`eq_zero_of_fourier_eq_zero`** — a continuous integrable `f` with `𝓕 f = 0` is `0` (the KEY economy:
  `Integrable (𝓕 f)` is FREE since `𝓕 f = 0` is the integrable zero function ⇒ **no decay estimate on
  `matCorr` needed**, only `Continuous.fourierInv_fourier_eq`); `eq_of_fourier_eq` (equal-transform
  injectivity, via the zero form on `f−g`).
* **`matCorr_integrable`** — `matCorr` integrable (`integrable_finsetSum` of the `z=0` case of h2 through
  `integral_prod_right`).
* **`zOfW w := 2πi·w`** + **`matCorr_fourier_eq`** — the CONVENTION BRIDGE `𝓕(matCorr i j) w = ∑ₗ Q̂ᵢₗ(z)·Q̂ⱼₗ(−z)`
  at `z=zOfW w` (Mathlib `𝓕` via `Real.fourier_eq`/`Circle.smul_def`/`Real.fourierChar_apply`, matching
  exponents with `Real.inner_apply` `⟪v,w⟫=v·w` + `push_cast; ring_nf`, then `matCorr_laplace`).
* **`matCorr_symm`** — `eq_of_fourier_eq` (`matCorr_continuous` + `matCorr_integrable` + the bridge on
  both sides) + the momentum symmetry `hmom`; now takes ONLY `hmom` (continuity discharged internally).

**B4 input (1) `matCorr` CONTINUITY — DISCHARGED via the L² route (2026-08-03, axiom-clean, build 8718).**
Dominated convergence does NOT apply (the integrand `v ↦ Qⱼₗ(t−v)` jumps at `λ` for every `t`); the
continuity is L²-smoothing.  `cₗ(v) = ∫ Qᵢₗ(t)Qⱼₗ(t−v)dt = ⟪(Qᵢₗ)_L², τᵥ(Qⱼₗ)_L²⟫` and:
* `q0MixEntry_memLp` — `(q0MixEntry:ℂ) ∈ Lᵖ` (bounded × compact support; `MemLp.mono'` vs
  `memLp_indicator_const`).
* `q0MixEntry_corr_continuous` — `v ↦ cₗ(v)` continuous: translation `T v = (·−v)` is a continuous
  `C(ℝ,ℝ)`-family (`ContinuousMap.continuous_of_continuous_uncurry`) that is measure-preserving
  (`measurePreserving_sub_right`); `v ↦ Lp.compMeasurePreserving (T v) gLp` is continuous
  (`Lp.compMeasurePreserving_continuous`), the inner product `⟪fLp, ·⟫` is continuous, and
  `⟪fLp, gv v⟫ = cₗ(v)` via `L2.inner_def` + `integral_congr_ae` with the two representative `ae`-eqs
  (`MemLp.coeFn_toLp`, `Lp.coeFn_compMeasurePreserving` composed through
  `MeasurePreserving.quasiMeasurePreserving.ae_eq_comp`; `Complex.conj_ofReal` kills the conjugate).
* `matCorr_continuous` — finite sum (`continuous_finsetSum`).

**⚠⚠ `hmom` is FALSE — `matCorr` is NOT the symmetric object (2026-08-03, numerically settled; corrects
the B3-scoping/B4 claim).**  The intended input (2) was `hmom`: `∑ₗ Q̂ᵢₗ(z)Q̂ⱼₗ(−z) = ∑ₗ Q̂ⱼₗ(z)Q̂ᵢₗ(−z)` (the
UNWEIGHTED function-part product = `matCorr`'s transform), to come from `swap_offdiag_of_keys`/MRS.7.  But
MRS.7 proves the FULL momentum product `[Q̂₀(k)Q̂₀(−k)ᵀ]` symmetric, and `Q̂₀ᵢⱼ = δᵢⱼ − ρ_geoᵢⱼ·Q̂ᵢⱼ` carries
the identity `δ` AND the `ρ_geo` weights.  **Test** (`scratchpad/hmom_test.py`, physical PY params satisfying
the MRS.7 key relations): full product symmetric to **3e-16**; unweighted (=`matCorr`) product diff **0.024**;
`ρ_geo`-weighted-but-no-identity product diff **1.6e-3** (so the `δ` terms are ESSENTIAL, not just the
weights).  Real-space: `matCorr(j,i)(v)=matCorr(i,j)(−v)` (algebraic subst) ⇒ `matCorr` symmetric ⟺ each entry
EVEN; the off-diagonal `matCorr(0,1)` is a cross-correlation of DIFFERENT functions, NOT even
(`matCorr(0,1)(±0.3)` = 0.285 vs 0.400, diff 0.115).  **So `matCorr` is genuinely not symmetric, `hmom` cannot
be discharged, and `matCorr_symm` (a valid implication) does NOT close obstruction (b).**  The physical
symmetric object is the FULL `Q̂₀` self-product — real-space distributional (`δ(v)` at the origin), so plain
function-space Fourier inversion does not apply.  **Redirect:** obstruction (b) must use the full Baxter factor
(with identity δᵢⱼδ(r)), OR be discharged directly in MOMENTUM space via `swap_offdiag_of_keys` (proven N=2)
without the real-space `matCorr` detour.  All B1–B4 machinery (`matCorr_fourier_eq`, injectivity lemmas,
`matCorr_continuous`, `matCorr_integrable`, the `_c` transforms) is CORRECT and reusable — only the target
object (`matCorr`) was the wrong one.

**Obstruction (b) DISCHARGED in momentum space via `swap_offdiag` (2026-08-03, `MixtureRealSpace.lean`,
axiom-clean, build 8719).**  The correct symmetric object is the momentum DCF `Cmix0 = I − Q̂₀(k)Q̂₀(−k)ᵀ`
(NOT the function-part `matSelfConv`/`matCorr`).  Shipped in `FMSA.MRS`:
* `Cmix0_symm_of_swap` — general: the swap identity `Q̂₀(−k)Q̂₀ᵀ(k) = Q̂₀(k)Q̂₀ᵀ(−k)` ⇒ `Ĉ₀ᵀ = Ĉ₀`
  (one direction of `Cmix0_isSymm_iff`).
* `Qphys_Cmix0_symm` — physical N=2: `Ĉ₀ᵀ = Ĉ₀` from `Qphys_T0_isSymm` (`transpose_mul`+`transpose_transpose`
  turn T0-symmetry into the swap identity).
* `Qphys_Cmix0_entry_symm` — the entrywise `Ĉ₀(k)ᵢⱼ = Ĉ₀(k)ⱼᵢ`, i.e. the exact `hCsym` (`cᵢⱼ = cⱼᵢ`)
  input shape, for any physical density/diameter pair.
**Why this is the right object, not `matSelfConv`:** `matSelfConv_symm_of_transform` is a VALID implication
but UNSATISFIABLE for the bare `Q = q0MixEntry` — `hTsym` needs the FULL product `Q̂₀=I−ρ_geo·q̂` (identity +
weights), `hbridge` needs the function-part product, and these two `Tfun` choices are different (numerically
the function-part product's asymmetry is ~0.02).  The DCF `Ĉ₀` off-diagonal IS a genuine function (the `δ`
sits only on the diagonal), so `Ĉ₀ᵢₖ = q̂ᵢₖ(z) + q̂ₖᵢ(−z) − matCorrᵢₖ(z)` (i≠k) is symmetric via
`Qphys_Cmix0_entry_symm`.  **Momentum side now fully done; the remaining real-space work is the CORRECTED
`hfact` — the seed must produce `Ĉ₀` (linear `q̂` terms included), NOT `matSelfConv` alone.**

**Corrected `hfact` — `Ĉ₀ = linear − self-conv` (2026-08-04, axiom-clean, build 8719).**  The precise
decomposition, in momentum space (`MixtureRealSpace.lean`, `FMSA.MRS`):
* `Cmix0_linear_selfconv` — `Ĉ₀(k) = W(k) + W(−k)ᵀ − W(k)·W(−k)ᵀ` with `W = I − Q̂₀` (the weighted Baxter
  function transform `ρ_geo·q̂`); pure matrix algebra `1−(1−A)(1−B)=A+B−AB` (`noncomm_ring`).  So the
  seed's target `Ĉ₀` carries the **linear `q̂` terms** `W(k)+W(−k)ᵀ`; the bare self-conv `W(k)W(−k)ᵀ` (≈
  `matCorr`) alone is not it.  With `Qphys_Cmix0_symm` this is the complete momentum-space discharge.
* Real-space transform bridges (`MixtureRowSum.lean`): `fourier_eq_zOfW` (reusable — `𝓕 g w = ∫ g(v)e^{−(2πiw)v}`,
  the general convention bridge, and `matCorr_fourier_eq` now factors through it), `q0MixEntry_fourier_eq`
  (`𝓕(q0MixEntry i j) = q̂ᵢⱼ(z)` — a linear term), `q0MixEntry_refl_fourier_eq` (`𝓕(v↦q0MixEntry j i (−v)) = q̂ⱼᵢ(−z)`
  — the reflected linear term, via `integral_neg_eq_self`).

**⚠ Real-space `matDCF = q0(i,j) + q0(j,i)(−·) − ρ-weighted-matCorr` is DISCONTINUOUS** (the linear `q0`
terms jump at `λ`, unlike the continuous `matCorr`), so real-space Fourier inversion (`eq_of_fourier_eq`,
which needs continuity) gives only a.e. equality — the global-continuity route used for `matCorr` does NOT
transfer to the DCF.  **This is WHY the discharge is cleanest in momentum space** (`Cmix0_linear_selfconv` +
`Qphys_Cmix0_symm`, no continuity needed); a real-space `matDCF` symmetry would need the `ContinuousAt`/a.e.
inversion (jump set is measure-zero) or Fourier a.e.-injectivity (absent in Mathlib).  Net: **momentum-space
corrected `hfact` COMPLETE; the seed reformulation to consume `Ĉ₀` (momentum) rather than real-space
`matSelfConv` is the remaining architectural step.**

**Seed reformulated to consume `Ĉ₀` — the corrected assembly (2026-08-04, `MixtureRowSum.lean`, axiom-clean,
build 8719).**  Key realization from the KDEF comment (`MixtureOzStar` L122): `ρK = Q − matSelfConv`, and the
DCF kernel `K` **carries the linear `q̂` term `Q`** — so `K` (not `matSelfConv`) is the symmetric object.
* `matBaxterK_symm_of_dcf` — `Kᵢₖ = Kₖᵢ` from the DCF symmetry `hCsym` (`Qᵢₖ−matSelfConvᵢₖ = Qₖᵢ−matSelfConvₖᵢ`,
  the real-space content of `Cmix0` symmetric, `Qphys_Cmix0_entry_symm`), via `hfact` + `mul_left_cancel₀` —
  **even though `matSelfConv` alone is NOT symmetric** (the linear `Q` compensates).
* `matOzStar_of_shellClaims_K` — the UNSPLIT assembly: `Ψ = r·Φ + ρ·matShellConv K` (with the symmetric `K`)
  + the shell-conv bridge `hbridge` ⇒ `MatOZStar`, in TWO lines (`rw [hclaimA, ← hbridge]`).  **No
  `matSelfConv` symmetry, no KDEF split, no integrability** — the asymmetric function-part self-conv never
  appears because the linear `q̂` terms live inside `K`.  Contrast the original `matOzStar_of_shellClaims`,
  which splits `ρ·matShellConv K = ∑Q·shell − ∑matSelfConv·shell` and so needs the false symmetry.
**Net:** the assembly now consumes `K = Ĉ₀/ρ` (symmetric via `swap_offdiag`, momentum), sidestepping the
false `matSelfConv` symmetry entirely.

**Seed → unsplit `K`-form `hclaimA` — the asymmetric-`K` closure (2026-08-04, `MixtureRowSum.lean`,
axiom-clean, build 8719).**  The corrected seed produces `matShellConvAsym K Kᵀ`: `K(i,k)` on `r+u` (linear
`q̂ᵢₖ(z)`) and the REFLECTED `K(k,i)` on `r−u` (linear `q̂ₖᵢ(−z)`) — the two linear `q̂` terms of `Ĉ₀`, with
the reflected index `k,i` supplied by the transposed seed (`matBaxterUQmSym`).
* `matShellConvAsym_symm_of_K` — `matShellConvAsym K Kᵀ = matShellConv K` given `K` symmetric (`Kᵀ = K`);
  `Finset.sum_congr` + `integral_congr` + `rw [hKsym k i u]` + `ring`.  The correct analog of the (false)
  `matSelfConv_shell_symm`.
* `matOzStar_of_asymK` — **CLOSES obstruction (b) for ANY diameters**: seed's asymmetric-`K` `hclaimA` +
  `K` symmetry (`hKsym`) + `hbridge` ⇒ `MatOZStar` (`matShellConvAsym_symm_of_K` then
  `matOzStar_of_shellClaims_K`).  Uses ONLY the proven momentum-space DCF symmetry.
**So the assembly is COMPLETE.**  Its three hypotheses: `hbridge` = `matRadialConv_eq_matShellConv` (exists);
`hKsym` = `matBaxterK_symm_of_dcf` ⟸ `hCsym` (real-space DCF symmetry) ⟸ `Cmix0` symmetric (`Qphys_Cmix0_entry_symm`,
proven, momentum) via the DCF transform bridge; `hclaimA` = the seed (`matBaxterUQmSym`) producing the
asymmetric-`K` renewal.  Remaining to fully instantiate: (i) confirm `matBaxterUQmSym` outputs exactly
`ρ·matShellConvAsym K Kᵀ` (the reflected `Q(k,i)` on `r−u`), and (ii) the real-space `hCsym` ⟸ momentum
`Cmix0` transform bridge (a.e., given the `matDCF` discontinuity).  The obstruction-(b) LOGIC is now fully
in place; only these two concrete instantiations remain.

**⚠⚠ NEGATIVE FINDING (i): `matBaxterUQmSym` does NOT output `ρ·matShellConvAsym K Kᵀ` for unequal
diameters (2026-08-04, `MixtureRowSum.lean`, axiom-clean, build 8719).**  Tracing `matBaxterUQmSym_unfold`
+ `matBaxterU`: BOTH linear terms carry the UN-reflected `Qᵢₖ` — `matBaxterU` gives `Qᵢₖ` on the `r−t` arm,
the second convolution gives `Qᵢₖ` on `r+t`.  Via `matDblConv_reindex` the SELF-CONV part IS correctly
reflected (`matSelfConvᵢₖ` on `r+u`, `matSelfConvₖᵢ` on `r−u`), so per-arm after the KDEF: `r+u` coeff =
`Qᵢₖ − matSelfConvᵢₖ = ρK(i,k)` ✓, but `r−u` coeff = `Qᵢₖ − matSelfConvₖᵢ` — which is `ρKᵀ(i,k)` (=
`Qₖᵢ − matSelfConvₖᵢ`) **iff `Qᵢₖ = Qₖᵢ`** (`seed_rMinus_eq_KKt_iff`, `sub_left_inj`) — equal diameters only.
So for unequal diameters an uncompensated `(Qᵢₖ−Qₖᵢ)·Ψₖⱼ(r−u)` term survives, and `matOzStar_of_asymK`
(which needs `K Kᵀ`) does NOT apply to the current seed.  **The self-conv reflection is right; the LINEAR
reflection is missing.**  Fix = the transposed FIRST convolution (`Qₖᵢ` on `r−t`), but that changes the
renewal (`matBaxterU_outer` fixes `Qᵢₖ` via `MatRenewalEq`) — so the reflected-linear seed needs a
transposed renewal, a genuinely different construction.  This is the real remaining seed-level obstacle;
the assembly (`matOzStar_of_asymK`), `K`-symmetry, momentum discharge, and `Ĉ₀` decomposition are all done.

**⚠⚠⚠ DEEPER FINDING — `K` symmetry is ALSO FALSE; the transposed renewal is a DEAD END (2026-08-04,
`scratchpad/k_symm_test.py`).**  Before building the transposed renewal, I tested whether `K = (Q −
matSelfConv)/ρ` is even symmetric — **it is NOT**: `Q(i,k)−matSelfConv(i,k) ≠ Q(k,i)−matSelfConv(k,i)`,
diff **~3e-3** at every `v`.  So `matBaxterK_symm_of_dcf`'s `hCsym` and `matOzStar_of_asymK`'s `hKsym` are
**FALSE** (the same `hmom`/`matSelfConv` trap): `K` has only ONE linear term `Q` + the WINDOWED
`matSelfConv` `[v,σ]`.  Even a reflected-linear seed producing `K Kᵀ` would NOT collapse
(`matShellConvAsym_symm_of_K` needs `K` symmetric).  The genuinely symmetric object is the FULL-LINE DCF
`matDCFᵢₖ(v) = q0(i,k)(v) + q0(k,i)(−v) − matCorrᵢₖ(v)` (TWO linear terms + full-line `matCorr`), tested
symmetric to **1e-11..1e-15 A.E.** — but its symmetry diff **jumps to ~0.19 AT `v = ±λ`** (`λ(1,0)=0.2`,
where `q0` jumps).  **So `matDCF` is symmetric A.E. and discontinuous exactly at `v=λ`.**  ROOT CAUSE
(recurring ALL session): every windowed / single-linear object (`matSelfConv`, `K`) is asymmetric; only the
full-line, two-linear-term `matDCF`/`Cmix0` is symmetric, and only A.E.  **The whole `K`-shell reformulation
rests on a false premise; the correct route is the a.e. Fourier-inversion framework on the DISCONTINUOUS
`matDCF` — a genuine research-scale obstacle, not a seed reindex.**  The momentum-space facts
(`Cmix0_linear_selfconv`, `Qphys_Cmix0_symm`) remain correct and are the anchor; it is the real-space/a.e.
transfer that is hard.  The `K`-shell lemmas stay as VALID implications (docstrings flag their false
premises), like `matCorr_symm`/`hmom`.

**✅ STALE-BLOCKER REFUTED — "Fourier a.e.-injectivity absent in Mathlib" is now available (2026-08-06,
`Analysis/FourierAEInjective.lean`, axiom-clean std-3).**  The a.e.-transfer above (`Cmix0`
momentum-symmetry ⇒ `matDCF` real-space a.e.-symmetry) was blocked on Fourier a.e.-injectivity, flagged
throughout the 08-04 work as absent from Mathlib.  It is now **derivable** from Mathlib's new
`MeasureTheory.Integrable.fourierInv_fourier_eq` (`Analysis/Fourier/Inversion.lean`).  The trick that
makes it work despite the mixture-DCF transform NOT being `L¹`: apply it to the **symmetry difference**
`d = matDCF(i,k) − matDCF(k,i)`, whose transform `𝓕 d = Cmix0(i,k) − Cmix0(k,i) = 0` — and `𝓕 d = 0`
is trivially integrable, so `fourierInv_fourier_eq` applies with `integrable_zero`, giving `𝓕⁻(𝓕 d) = d`
at continuity points; with `𝓕⁻ 0 = 0` this reads `d = 0` at every continuity point, hence a.e. (the DCF
jumps only on the measure-zero `{v = λᵢⱼ}`).  Built: **`ae_eq_zero_of_fourier_eq_zero`** (`Integrable f`,
`𝓕 f = 0`, `f` cont. a.e. ⟹ `f = 0` a.e.) and **`ae_eq_of_fourier_eq`** (the difference form the DCF
symmetry consumes, via `Real.fourier_eq` + `integral_sub` for `𝓕(f−g)=𝓕f−𝓕g`).  Both general (any
finite-dim real inner product space `V`, any `ℂ`-Banach `E`), std-3.  **This unblocks option 4's core.**
Remaining for the unequal-diameter transfer: (a) the convention bridge `radial_fourier ↔ Mathlib 𝓕` on
radial functions (so the momentum symmetry stated via `radial_fourier`/`Cmix0` feeds `𝓕 d = 0`), and
(b) `matDCF` integrability + a.e.-continuity (compact support + finitely many jumps ⇒ both routine); then
`ae_eq_of_fourier_eq` discharges `hCsym`.  The "genuine research-scale obstacle" was a stale Mathlib gap.

**✅ STEP (a) DONE — the `radial_fourier ↔ 𝓕` bridge (2026-08-06, `HardSphere/RadialFourierInjective.lean`,
axiom-clean std-3, build 8744).**  The DCF symmetry is stated via the project's 3-D radial transform
`radial_fourier`, not Mathlib's `𝓕`; this bridges them and delivers **radial-Fourier a.e.-injectivity**.
Reduction: `radial_fourier f k = (4π/k)·∫₀^∞ r·f(r)·sin(kr) dr` is the sine transform of `r·f(r)`, and
Mathlib's `𝓕` of the **odd extension** `ψ_f : v ↦ v·f|v|` is `−2i·(that sine integral)`
(`RadialFourierInversion.fourier_of_odd`, MA.9, already in the project).  So `radial_fourier f =
radial_fourier g` ⇒ `𝓕 ψ_f = 𝓕 ψ_g` ⇒ (via the new `ae_eq_of_fourier_eq`, whose `𝓕 d = 0` route needs
**no** `Integrable(𝓕·)` — the point that makes it apply to the non-`L¹`-transform DCF) ⇒ `ψ_f = ψ_g` a.e.
⇒ dividing the `v` factor, `f = g` a.e. on `(0,∞)`.  Built: **`ae_eq_oddExt_of_radial_fourier_eq`** (odd
extensions equal a.e. on `ℝ`), **`ae_eq_of_radial_fourier_eq`** (`f =ᵐ g` on `Ioi 0` — the form the DCF
symmetry consumes), + helper `oddExt_fourier_integral_eq` (the fourier_of_odd integral = cast real radial
integral; the `sin(2πvw)`↔`sin(2πwv)` reorder handled by a `ring`-inside-`sin` `rw`).  Hypotheses on
`f`/`g`: only odd-extension `Integrable` + a.e.-`ContinuousAt`.  **Only step (b) remains** for the
unequal-diameter `hCsym`: instantiate `f := matDCF i k`, `g := matDCF k i`, discharge those two routine
regularity facts (compact support + finitely many jumps) and `hFeq` from `Qphys_Cmix0_symm` via the
radial-transform def — then `matOzStar_of_asymK` closes the unequal-diameter general-N OZ★ core.

**⚠ CORRECTION + ✅ the RIGHT step (b) enabler (2026-08-06, `YukawaOZMix/MixtureDCFAEInjective.lean`,
axiom-clean std-3, build 8745).**  Tracing the actual consumer: obstruction (b)'s DCF symmetry uses the
**1-D** transform `matCorr_laplace`/`fourier_eq_zOfW` (`∫·e^{−zv}` at `z = 2πi·w`), **not** `radial_fourier`
— the radial bridge above is for the RDF `g(r)`, a different object.  The relevant existing lemma
`MixtureRowSum.eq_of_fourier_eq` needs **full continuity** and so does NOT apply to the real-space DCF,
which is discontinuous (the `q0MixEntry` linear terms jump at `v=λᵢₖ`; `matCorr` itself is continuous).
That discontinuity is exactly what the new a.e.-version fixes: **`ae_eq_of_zOfW_transform_eq`** — integrable
+ a.e.-continuous `f,g` with equal `zOfW` transforms agree a.e. (= `ae_eq_of_fourier_eq` ∘ `fourier_eq_zOfW`,
no full continuity, no `Integrable(𝓕·)`).  **Remaining for full (b) — the object-level bookkeeping (2026-08-03
subtlety):** `matCorr`'s transform is the *unweighted* function-part product `∑ₗ q̂ᵢₗ(z)q̂ₖₗ(−z)`, but
`Cmix0 = I − Q̂₀(k)Q̂₀(−k)ᵀ` uses the `ρ_geo`-**weighted** product (`δ`/`I` terms cancel ⇒ `Cmix0` is a pure
function `ρq̂ᵢₖ + ρq̂ₖᵢ(−·) − ρ²·(weighted matCorr)`).  So the correctly-weighted full-line DCF must be built
and its `zOfW` transform proved `= Cmix0ᵢₖ`; then `Qphys_Cmix0_symm` + `ae_eq_of_zOfW_transform_eq` give
`hCsym`.  That is mechanical `ρ_geo`-scalar bookkeeping on the existing `q0MixEntry_fourier_eq`/
`matCorr_fourier_eq`, not a new obstacle — the continuity blocker (the genuinely hard part) is removed.

**✅ the algebraic core of the weighted construction (2026-08-06, same file, std-3, build 8745).**
**`Cmix0_entry_of_id_sub`** — for any Baxter matrix of the `q0_entry_c` shape `Q(s)ᵢⱼ = δᵢⱼ −
ρ_geoᵢⱼ·B(s)ᵢⱼ` (which `Qphys` has *by definition* of `q0_entry_c`, `B = e^{−λs}(Q0·p₁ + Qpp·p₂)`),
`Cmix0(Q)(k)ᵢⱼ = ρ_geoᵢⱼ·B(k)ᵢⱼ + ρ_geoⱼᵢ·B(−k)ⱼᵢ − ∑ₗ ρ_geoᵢₗρ_geoⱼₗ·B(k)ᵢₗ·B(−k)ⱼₗ`.  Proof: expand
`1 − Q(k)·Q(−k)ᵀ` entrywise, `ite_mul`+`Finset.sum_ite_eq` collapse the four `δ`-sums, `rcases i=j`
+`ring` — the **`δᵢⱼ` and identity cross-terms cancel**, leaving the pure function (the fact the
2026-08-03 note called "the identity δ terms are essential" — they cancel *in `Cmix0`*, so `Cmix0` is a
genuine function even though `Q̂₀Q̂₀ᵀ` is distributional).  This is the momentum-side target the weighted
real-space DCF must transform to.  **Remaining for full (b):** (i) instantiate at `Qphys` (`hQ` is a
direct `q0_entry_c` unfold), (ii) identify `B(s)ᵢⱼ = ∫ q0MixEntry(i,j)·e^{−st}` (`q0MixEntry_laplace_c`,
needs the physical `Mix X`↔`Qphys` data match), (iii) build the `ρ_geo`-weighted `matCorr` + its
transform, (iv) assemble `matDCFfull` with `𝓕 = Cmix0ᵢₖ`, (v) `Qphys_Cmix0_symm` +
`ae_eq_of_zOfW_transform_eq` (+ routine integrability/a.e.-continuity) ⇒ `hCsym`.  Steps (i)–(v) are
mechanical bookkeeping on the now-assembled algebraic core + the two a.e.-injectivity enablers.

**✅ steps (i)+(ii) DONE (2026-08-06, same file, std-3, build 8745).**  **(i)** `BbarePhys` (the bare
bracket `e^{−λs}(Q0phys·p₁ + Qppphys·p₂)`) + `Qphys_id_sub` (`Qphys(s)ᵢⱼ = δᵢⱼ − ρ_geoᵢⱼ·B(s)ᵢⱼ`, a
one-line `q0_entry_c` unfold + `ring`) + **`Cmix0_Qphys_eq`** (the physical momentum-side closed form
`Cmix0(Qphys)(k)ᵢⱼ = ρ_geoᵢⱼ·B(k)ᵢⱼ + ρ_geoⱼᵢ·B(−k)ⱼᵢ − ∑ₗ ρ_geoᵢₗρ_geoⱼₗ·B(k)ᵢₗ·B(−k)ⱼₗ`, =
`Cmix0_entry_of_id_sub` at `Qphys_id_sub`).  **(ii)** verified the `Mix↔Qphys` bridge: no instance
existed, but `Mix 2 M` has only 7 fields + `hσ`, so **`physMix ρ σ hσ : Mix 2 0`** (M=0, no Yukawa
tails) is trivial, and **`q0MixEntry_physMix_laplace`** proves the window Laplace
`∫_{[λ,R]} e^{−st}·q0MixEntry(physMix)ᵢⱼ = BbarePhys(s)ᵢⱼ` (via `q0MixEntry_laplace_c` + physical field
values; `Qpp` row-independence by `fin_cases`; the `s·λ` vs `λ·s` inside `cexp` handled by a `hexparg`
rewrite).  **Remaining:** (ii-full) the full-line `∫_ℝ = ∫_{[λ,R]}` support bridge ⇒
`𝓕(q0MixEntry physMix)ᵢⱼ w = BbarePhys(zOfW w)`; (iii) `ρ_geo`-weighted `matCorr` + its transform;
(iv) assemble `matDCFfull = ρ·q0(i,j) + ρ·q0(j,i)(−·) − (weighted matCorr)` with `𝓕 = Cmix0(Qphys)ᵢⱼ`;
(v) `Qphys_Cmix0_symm` + `ae_eq_of_zOfW_transform_eq` (+ routine integrability/a.e.-continuity) ⇒
`hCsym`.  The momentum side is now fully closed-form; what's left is real-space assembly.

**✅ step (iii) DONE (2026-08-06, same file, std-3, build 8745).**  **`matCorrW`** (the `ρ_geo`-weighted
full-line correlation `∑ₗ ∫ (ρᵢₗ·q0(i,l)(t))·(ρⱼₗ·q0(j,l)(t−v)) dt`) + **`matCorrW_laplace`**:
`∫ matCorrW·e^{−zv} = ∑ₗ ρᵢₗρⱼₗ·(∫ q0(i,l)e^{−zt})·(∫ q0(j,l)e^{zs})`.  The weight can't be absorbed into a
`Mix` (per-pair `ρ_geoᵢⱼ` vs per-single-index `Qpp`), so instead it's absorbed into the general
`laplace_sum_eq_corr_c` at `F l = ρᵢₗ·q0(i,l)`, `G l = ρⱼₗ·q0(j,l)`; the 3 integrability side-conditions
come from the unweighted `q0MixEntry_corr_exp_prod_integrable`/`q0MixEntry_mul_exp_integrable` via
`Integrable.const_mul` + `.congr` (ring), then the constants factor out (`integral_const_mul` per `l`).
The RHS is exactly the `Cmix0_Qphys_eq` double-product term once each `∫ q0·e^{−st} = BbarePhys(s)`.
**Remaining:** (ii-full) full-line `∫_ℝ = ∫_{[λ,R]}` support bridge ⇒ `∫_ℝ q0MixEntry(physMix)·e^{−st} =
BbarePhys(s)`; (iv) `matDCFfull = ρ·q0(i,j) + ρ·q0(j,i)(−·) − matCorrW` with `𝓕 = Cmix0(Qphys)ᵢⱼ`
(assemble ii-full + iii + `Cmix0_Qphys_eq`); (v) `Qphys_Cmix0_symm` + `ae_eq_of_zOfW_transform_eq` (+
integrability/a.e.-continuity of `matDCFfull`) ⇒ `hCsym`.  (i)+(ii-window)+(iii) all closed-form.

**✅ steps (ii-full)+(iv) DONE (2026-08-06, same file, std-3, build 8745).**  **(ii-full)**
**`q0MixEntry_physMix_fullline`** — `∫_ℝ e^{−st}·q0MixEntry(physMix)ᵢⱼ = BbarePhys(s)ᵢⱼ`, from the
window form + compact support (`setIntegral_eq_integral_of_forall_compl_eq_zero` +
`integral_Icc_eq_integral_Ioc` + `intervalIntegral.integral_of_le`).  **(iv)** **`matDCFfull`** =
`ρ_geoᵢⱼ·q0(i,j)(v) + ρ_geoⱼᵢ·q0(j,i)(−v) − matCorrW(v)` + **`matDCFfull_laplace`**: `∫_ℝ matDCFfull·e^{−zv}
= Cmix0(Qphys)(z)ᵢⱼ` for `z≠0`.  Proof assembles: `integral_sub`/`integral_add` split (3 integrabilities
via `const_mul`/`comp_neg`/`integrable_finsetSum`), t1 = linear term (ii-full + const factor), t2 =
reflected term (`integral_neg_eq_self` shifts `q0(j,i,−v)` to `BbarePhys(−z)`), t3 = matCorrW
(`matCorrW_laplace` + ii-full at `±z`), then `Cmix0_Qphys_eq`.  So the weighted real-space DCF is exactly
the inverse transform of the momentum `Cmix0`.  **Remaining — (v) only:** `matDCFfull i j =ᵐ matDCFfull j i`
via `Cmix0(Qphys)(zOfW w)ᵢⱼ = Cmix0(Qphys)(zOfW w)ⱼᵢ` (`Qphys_Cmix0_symm`, `k≠0`) + `matDCFfull_laplace`
(at `z = zOfW w ≠ 0`, i.e. `w ≠ 0`) fed to `ae_eq_of_zOfW_transform_eq`.  ⚠ **the `w=0` edge:**
`matDCFfull_laplace` needs `z≠0`, so the `zOfW 0 = 0` (total-integral / `k=0` compressibility) point isn't
covered directly — needs either continuity of `𝓕(matDCFfull)` (dense `w≠0` ⇒ all `w`) or a direct total-mass
symmetry.  That + the routine `matDCFfull` integrability + a.e.-continuity (compact support + finite jumps)
is all that's left of MML.15 obstruction (b).

**✅ step (v) DONE — obstruction (b) DISCHARGED (2026-08-07, `MixtureDCFAEInjective.lean`, std-3, build
8600).**  **`matDCF_ae_symm`**: `matDCFfull rho sigma hsig i j =ᵐ[volume] matDCFfull … j i` — the full-line
real-space zeroth-order mixture DCF is **a.e.-symmetric** (`Ĉ₀ᵢⱼ(v) = Ĉ₀ⱼᵢ(v)` a.e.), the exact `hCsym`
object the notes at `MixtureRowSum.lean:941-953` flagged (the *everywhere*-`hCsym` route is documented
FALSE — the DCF jumps at `v = λ`; only the full-line object is symmetric, and only a.e.).  Fed to
`ae_eq_of_zOfW_transform_eq` (needs the `zOfW` transform equal at **every** `w`).  Four supporting lemmas,
all std-3:
- **`q0MixEntry_continuousAt`** — `q0MixEntry(i,j)` (→ℂ) is `ContinuousAt v` off the two endpoints
  `{λᵢⱼ, Rᵢⱼ}` (`lt_trichotomy` × the indicator's three pieces, `Iio/Ioo/Ioi_mem_nhds` + `ContinuousAt.congr`).
- **`matDCFfull_integrable`** / **`matDCFfull_ae_continuous`** — routine regularity: integrable (`memLp_one`
  + `comp_neg` + `integrable_finsetSum`), and `ContinuousAt` off the *finite* set
  `{λᵢⱼ, Rᵢⱼ, −λⱼᵢ, −Rⱼᵢ}` (`measure_mono_null` + `Set.toFinite.measure_zero`).
- **`zOfW_transform_continuous`** — `w ↦ ∫ f·e^{−(2πiw)v}` is continuous for integrable `f`
  (`continuous_of_dominated`, bound `‖f‖`, kernel unit-modulus via `Complex.norm_exp_ofReal_mul_I`).  This is
  the tool that closes the **`w=0` edge**: `matDCFfull_transform_offdiag` gives the transform equality off
  `w=0` (via `matDCFfull_laplace` + `Qphys_Cmix0_entry_symm`, `k = zOfW w ≠ 0`), and `Continuous.ext_on
  (dense_compl_singleton 0)` extends it to **all** `w` — no separate total-mass computation needed.

**MML.15 obstruction (b) is now CLOSED at N=2.**  The a.e.-inversion framework (`ae_eq_of_fourier_eq` via
Mathlib's `Integrable.fourierInv_fourier_eq`, `Layer 0 FourierAEInjective.lean`) that this needed refuted the
"Fourier a.e.-injectivity absent" stale blocker.  **Follow-on (NOT part of (b)):** the shell assembly
(`matSelfConv_shell_symm_of_dcf`, `matOzStar_of_shellClaims_K`) still consumes an *everywhere* `hCsym`; to
run on `matDCF_ae_symm` it needs an **a.e.-consuming** variant (symmetry used inside
`intervalIntegral.integral_congr_ae`) **plus the corrected `hfact`** (seed-output = `Ĉ₀`, the real-space
core identity `matSelfConv → Ĉ₀` with the two linear `q̂` terms included — the "remaining real-space work"
of `MixtureRowSum.lean:926-927`).  Those two are the last pieces of MML.8's collapse for unequal diameters.

**✅ a.e.-consuming shell assembly + corrected `hfact` DONE (2026-08-07, `MixtureDCFAEInjective.lean`, std-3,
build 8600).**  The two follow-on pieces above, both closed:
- **a.e.-consuming shell variant** — `matShellConvAsym_symm_of_K_ae` (the a.e. twin of
  `matShellConvAsym_symm_of_K`: uses `intervalIntegral.integral_congr_ae` so a null exception set — the DCF
  jump at `v=λ` — is harmless; consumes `hKsym_ae : ∀ i k, ∀ᵐ u, u∈Ioc 0 σ → K i k u = K k i u`) +
  `matOzStar_of_asymK_ae` (the a.e. twin of `matOzStar_of_asymK`: `MatOZStar` from `hbridge` + `hclaimA` +
  the **a.e.** `hKsym_ae`).
- **corrected `hfact`** — `matDCFreCore := (matDCFfull …).re` is the correct DCF core `Ĉ₀` (two linear `q̂`
  terms INCLUDED, NOT the false windowed `matSelfConv`); `matDCFreCore_ae_symm` inherits its a.e. symmetry
  straight from `matDCF_ae_symm` (take `.re`).
- **capstone** — `matOzStar_of_matDCF_ae`: `MatOZStar` from the corrected `hfact` (`hKdcf : ρK = Ĉ₀ =
  matDCFreCore` a.e. on the shell) + `hbridge` + `hclaimA`, **with the kernel-symmetry hypothesis discharged
  internally** (from `matDCFreCore_ae_symm` + `mul_left_cancel₀`).  `matOzStar_of_matDCF_ae_canonical` takes
  the natural kernel `K := Ĉ₀/ρ`, discharging `hKdcf` by `ρ·(Ĉ₀/ρ)=Ĉ₀` ⇒ the ONLY surviving inputs to the
  unequal-diameter `MatOZStar` are `hbridge` (the provable `matRadialConv_eq_matShellConv`) and `hclaimA`
  (the corrected seed).

So the **symmetry obstruction (b) is entirely removed from the assembly** — no `matSelfConv`/windowed-`K`
symmetry (both false) and no *everywhere* DCF symmetry (false, jumps at `v=λ`) anywhere in the chain.  What
remains for the full unequal-diameter MML.8 collapse is exactly the **seed** `hclaimA` (`MixtureRowSum.lean:
1026-1035` — the current `matBaxterUQmSym` outputs the asym-`K` form only for equal diameters; the reflected
linear term needs the transposed first convolution, changing the renewal) + the ML-series collapse
`MixRDFInnerCollapse` (a `Prop`, pole-exhaustion, not axiomatizable).  `hbridge` is `matRadialConv_eq_matShellConv`.

**✅ corrected seed BUILT — the "changes the renewal" obstacle DISSOLVED (2026-08-07,
`MixtureCorrectedSeed.lean`, std-3, build 8601).**  The reflected-`r−u`-linear seed, closed to a single
moment hypothesis.  **Key observation** `matBaxterUt_eq_transpose`: the transposed first convolution
`matBaxterUt Psi Q = matBaxterU Psi Qᵀ` (`Qᵀ a b = Q b a`) — pure `rfl` after renaming the species sum.  So
the transposed claim-`(A)`/`(B)` are the EXISTING `matBaxterU_outer`/`matBaxterU_core` **at `Qᵀ`**
(`matBaxterUt_outer`, `matBaxterUt_core`) — the "changed renewal" (`Ψ` solves the transposed Volterra,
kernel `Qₖᵢ`) is fully constructible (the Volterra Banach machinery is kernel-agnostic), NOT a blocker.
Built the fully-corrected seed **`matBaxterUQmSymFull`** = `matBaxterUt − ∑ₖ∫₀^σ Qᵢₖ·matBaxterUt(k,j,r+t)`
(the leading arm is now `matBaxterUt`, so the `r−u` linear is the reflected `Qₖᵢ`; the `r+u` linear is
`Qᵢₖ` — exactly the `K`/`Kᵀ` pair `matShellConvAsym K Kᵀ` needs, any diameters), then its seed identity
`matBaxterUQmSymFull ≡ r·Φ` on `(0,∞)` reduced (mirroring `matBaxterUQm_*`): **`_zero_of_utOuter`** (outer
half), **`_core_reduce`** (`[0,σ]→[0,σ−r]` truncation), **`_eq_rPhi_of_seed`** (capstone) — leaving the
SINGLE remaining input `hseed`, the reflected-arm Wertheim–Thiele moment identity (the corrected analog of
`baxter_core_seed`; delta-free and provable by the row/column-collapse for equal diameters, as the existing
`matBaxterUQm_momentSeed_of_rowSum` does).  So MML.8's unequal-diameter collapse now has **both** the
symmetry side (obstruction (b), fully closed) and the corrected seed (reduced to one delta-free moment
identity) in hand; what remains is the seed→shell reindex plumbing (`matDblConv_reindex` + KDEF into the
exact `matShellConvAsym K Kᵀ` form, mechanical) and `hseed`'s unequal-diameter case (a genuine physical
moment identity), plus the separate `MixRDFInnerCollapse` ML-series `Prop`.

**✅ seed→shell reindex plumbing DONE (2026-08-07, `MixtureCorrectedSeed.lean`, std-3, build 8601) — and it
EXPOSES the real remaining gap.**  Seven lemmas connecting `matBaxterUQmSymFull` to the shell form:
- **`oddExt_div_self_eq_of_odd`** — general oddExt bridge (`oddExt (g/·) = g` for odd `g`, `g 0 = 0`;
  generalizes `oddExt_div_self_eq_baxterPsi`) + **`matShellConvAsym_transpose_raw`** (removes `oddExt` given
  `Ψ` odd) + **`rho_matShellConvAsym_transpose_kdef`** (`ρ·matShellConvAsym K Kᵀ` in raw KDEF form
  `∑ₖ∫((Qᵢₖ−mSCᵢₖ)Ψ(r+u) + (Qₖᵢ−mSCₖᵢ)Ψ(r−u))`).
- **`matDbl_eq_selfConvShell`** — the reindex: pull the inner species sum out, `Finset.sum_comm`, apply
  `matDblConv_reindex` per outer species `m` ⇒ the seed's double conv = reflected self-conv shell
  `∑ₘ∫(mSCᵢₘΨ(r+u) + mSCₘᵢΨ(r−u))`.
- **`matBaxterUQmSymFull_eq_psi_sub_rawShell`**/**`_eq_psi_sub_shell`** + capstone **`correctedSeed_hclaimA`**:
  combining with the seed identity `≡ r·Φ` gives `Ψᵢⱼ(r) = r·Φᵢⱼ(r) + ρ·matShellConvAsym K Kᵀ (Ψ/·)ᵢⱼ(r)` —
  the **exact `hclaimA`** shape `matOzStar_of_asymK_ae` consumes.

**⚠ KEY FINDING the plumbing surfaces:** the `K` in `correctedSeed_hclaimA` is the **windowed** Baxter kernel
(`ρK = Q − matSelfConv`, `matSelfConv` = `[u,σ]`-windowed self-conv), NOT the full-line DCF `matDCFreCore`.
Feeding `matOzStar_of_asymK_ae` needs `K` a.e.-symmetric on `(0,σ)`, i.e. `Qᵢₖ − matSelfConvᵢₖ =ᵐ Qₖᵢ −
matSelfConvₖᵢ` — the **windowed** DCF symmetry, which `MixtureRowSum.lean:947` records as numerically FALSE
(~3e-3) for unequal diameters.  This is a **different object** from `matDCF_ae_symm` (full-line, two linear terms
+ full-line `matCorr`): the seed's windowed `matSelfConv` (∫ over `[u,σ]`) differs from the full-line `matCorr`
(∫ over ℝ) exactly on the reflected-support piece `[u+λₖₗ, u]` when `σₗ<σₖ`.  So the last gap is NOT "mechanical"
as the notes assumed — it is the **windowed↔full-line reconciliation**: either prove the windowed asymmetric
shell `matShellConvAsym K Kᵀ` equals the symmetric full-line shell `matShellConv Kfl` (so the two-linear
full-line DCF's a.e. symmetry closes it under the integral), or produce a seed whose convolutions are full-line.
The plumbing's value is precisely isolating this: everything up to `hclaimA` is now axiom-clean, and the residual
is one concrete analytic identity (windowed self-conv shell = full-line DCF shell), no longer a vague "plumbing".

**✅ windowed↔full-line: the folding step + the PRECISE gap (2026-08-07, `MixtureCorrectedSeed.lean`, std-3, build
8601).**  Two lemmas that reduce the reconciliation to its irreducible core:
- **`matShellConvAsym_fold`** — the seed's two-armed windowed shell IS a single full-line `[−σ,σ]` convolution:
  `matShellConvAsym K Kᵀ (Ψ/·)ᵢⱼ(r) = ∑ₖ ∫_{−σ}^σ foldKernel K i k v · Ψₖⱼ(r+v) dv`, where the `r−u` arm folds to
  the `v<0` half by `u ↦ −v` (`intervalIntegral.integral_comp_neg`), and `foldKernel K i k v = Kᵢₖ(v)` for `v>0`,
  `Kₖᵢ(−v)` for `v≤0`.  No symmetry used — pure substitution + additivity.
- **`foldKernel_transpose_odd`** — `foldKernel K i k (−v) = foldKernel K k i v` **automatically** (no hypothesis on
  `K`).  So the fold is **transpose-odd**; OZ★'s symmetric shell `matShellConv Kfl` folds to an **EVEN** kernel
  (`Kfl(i,k)(|v|)`).  `foldKernel K` is even ⟺ `Kᵢₖ = Kₖᵢ` (windowed symmetry) — the false input.

**⇒ The residual is now pinned to ONE statement:** `∑ₖ∫_{−σ}^σ foldKernel K i k v · Ψₖⱼ(r+v) = ∑ₖ∫_{−σ}^σ (even
full-line DCF kernel)(i,k,v) · Ψₖⱼ(r+v)` — i.e. the transpose-odd windowed fold and the even full-line DCF give
the SAME convolution against the (odd) Baxter solution `Ψ`.  This is not an algebraic kernel identity (the kernels
differ pointwise, `transpose-odd ≠ even`); it holds only under the integral against the specific solution, which is
exactly the **Baxter-factorization ⟹ OZ** content (`Q̂Q̂ᵀ(−k) = I − Ĉ` ⟹ `Ĥ = Ĉ + ρĈĤ`).  So it is the genuine
MML.8 crux for unequal diameters and needs the **Fourier/factorization route** (the momentum `Cmix0_factorization`
+ `matDCF_ae_symm` symmetry transported to real space against `Ψ`), NOT a short real-space rewrite.  Everything up
to and including the fold is axiom-clean; the reconciliation core is now a single, precisely-stated identity.

**✅ Fourier/factorization route — the momentum linchpin DISSOLVES the gap at the transform level (2026-08-07,
`MixtureDCFAEInjective.lean`, std-3, build 8601).**  **`Qphys_prod_eq_one_sub_dcf_transform`**:
`(Q̂₀(z)·Q̂₀(−z)ᵀ)ᵢⱼ = δᵢⱼ − ∫_ℝ matDCFfullᵢⱼ(v)·e^{−zv} dv` — the Baxter-factor product `T₀` equals `I` minus
the transform of the full-line DCF.  Proof: `Cmix0_factorization` (`Q̂₀(z)·Q̂₀ᵀ(−z) = I − Ĉ₀`, momentum) +
`matDCFfull_laplace` (`∫ matDCFfull·e^{−zv} = Ĉ₀ = Cmix0`, step (iv)) — two existing lemmas composed.

**Why this resolves what the fold exposed:** the seed's operator is `Ψ ⋆ Q₊ ⋆ Q₋`, whose momentum symbol is
`Q̂₀(z)·Q̂₀ᵀ(−z) = I − (matDCFfull transform)`.  So `Ψ ⋆ Q₊ ⋆ Q₋ = Ψ − Ψ ⋆ matDCFfull`, i.e. the seed IS OZ★
with the **full-line, a.e.-symmetric** DCF `matDCFfull` (`matDCF_ae_symm`).  The apparent windowed asymmetry —
the transpose-odd fold `foldKernel K`, the false windowed-`K` symmetry — is a **real-space artifact of the
`[u,σ]` windowing that vanishes at the transform level**: windowed `matSelfConv` and full-line `matCorr` carry
the SAME symbol `Q̂₀Q̂₀ᵀ(−z)` acting on `Ψ̂`, because the reindex `matDbl_eq_selfConvShell` + the two linear arms
reconstruct exactly `T₀ = I − Ĉ₀`.  So `matShellConvAsym K Kᵀ (Ψ) = Ψ ⋆ matDCFfull` holds as OPERATORS even
though the kernels differ pointwise (transpose-odd ≠ even) — the "kernels must be equal" obstruction was an
artifact of comparing real-space kernels instead of symbols.

**Remaining (now CONCRETE, not vague):** transport the momentum identity to the real-space operator identity
`Q₊ ⋆ Q₋ = δ·I − matDCFfull` via FT injectivity (`ae_eq_of_zOfW_transform_eq`, in hand) + the convolution
theorem for the matrix shell operators (`𝓕(A ⋆ B) = 𝓕A·𝓕B` for these `[0,σ]`-supported kernels).  That
convolution theorem is the one remaining piece of formalization; the momentum content — the crux the notes said
"needs the Fourier route" — is now PROVED (`Qphys_prod_eq_one_sub_dcf_transform`).  Plus, still: `hseed`'s
unequal-diameter moment identity and the `MixRDFInnerCollapse` ML-series `Prop`.

**✅ convolution theorem for the shell operators DONE (2026-08-07, `MixtureDCFAEInjective.lean`, std-3, build
8600).**  Three lemmas — the transport machinery:
- **`laplace_shift`** — the translation theorem `∫_ℝ g(r+u)·e^{−zr} dr = e^{zu}·∫_ℝ g(r)·e^{−zr} dr` (pure
  change of variables, `integral_add_right_eq_self`; no integrability needed) + **`laplace_shift_neg`** (the
  `r−u` arm, `e^{−zu}` factor).  THE core: each `r±u` sample in a shell operator contributes an `e^{±zu}` symbol
  factor.
- **`foldShell_laplace`** — the shell-operator transform: `𝓕_r[∑ₖ ∫_ℝ Dₖ(v)·Ψₖ(r+v) dv] = ∑ₖ (∫_ℝ Dₖ(v)·e^{zv}
  dv)·Ψ̂ₖ(z)` (Fubini via `integral_integral_swap` + `laplace_shift` per `v`).  The shell operator becomes a
  **multiplication operator on `Ψ̂`** whose symbol is `∑ₖ ∫ Dₖ·e^{zv}` — exactly the object the momentum linchpin
  controls.

**⇒ The reconciliation is now a finite assembly of proved lemmas:** apply `foldShell_laplace` to BOTH the seed's
shell (`matShellConvAsym_fold` → kernel `foldKernel K`) and the OZ★ shell (`matShellConv Kfl` → even kernel);
both transforms are `(symbol)·Ψ̂`; the two symbols coincide because `∫ foldKernel K·e^{zv}` and the DCF symbol
both equal `T₀ = I − Ĉ₀` by `Qphys_prod_eq_one_sub_dcf_transform`; then `ae_eq_of_zOfW_transform_eq` (FT
injectivity) gives the real-space operator equality.  Still-open (now all bookkeeping): (1) the symbol identity
`∫_{−σ}^σ foldKernel K i k v·e^{zv} = Ĉ₀(i,k)` (unfolds via `foldKernel = K/Kᵀ` on `v≷0` to `∫₀^σ K(i,k)e^{zv} +
∫₀^σ K(k,i)e^{−zv}` = the factorization `Q̂₀Q̂₀ᵀ(−z)`), (2) `foldShell_laplace`'s joint-integrability side-conditions
for the concrete kernels (compact support of `q0MixEntry`), (3) `hseed` + `MixRDFInnerCollapse`.  **The genuinely
hard analytic content — the transform machinery + the momentum factorization — is now ALL axiom-clean; what
remains is assembly bookkeeping.**

**◑ symbol identity — fold-split DONE + a precise obstruction PINNED (2026-08-07, `MixtureCorrectedSeed.lean`,
std-3, build 8600).**  **`foldKernel_laplace_split`**: the fold symbol `∫_{−σ}^σ foldKernel K i k v·e^{zv}`
splits into the two one-sided Baxter-kernel transforms `∫₀^σ K(i,k)·e^{zv} + ∫₀^σ K(k,i)·e^{−zv}` (the `v<0`
half reflects to `e^{−zv}` on the transposed `K(k,i)` by `u↦−v`, `integral_comp_neg`).  So the symbol identity
`= Cmix0` reduces, via the KDEF `ρK = Q − matSelfConv`, to (a) the **linear** part `∫₀^σ Q(i,k)e^{zv} + ∫₀^σ
Q(k,i)e^{−zv}` and (b) the **self-conv** part `∫₀^σ mSC(i,k)e^{zv} + ∫₀^σ mSC(k,i)e^{−zv}`.

**Self-conv symbol identity (derived, provable by square-splitting):** `∫₀^σ mSC(i,k)(v)e^{zv} + ∫₀^σ
mSC(k,i)(v)e^{−zv} = ∑ₗ (∫₀^σ Q(i,l)(t)e^{zt})·(∫₀^σ Q(k,l)(s)e^{−zs})`.  The two windowed self-conv terms are
exactly the lower/upper triangles of the `[0,σ]²` square `(∫₀^σ Q(i,l)e^{zt})(∫₀^σ Q(k,l)e^{−zs})` (substitute
`v = t−s`; `mSC`'s `∫_v^σ` window = the `t≥v` triangle) — a clean Fubini identity, no support assumption.

**⚠ THE PRECISE OBSTRUCTION (why unequal diameters are hard, now pinned):** the self-conv symbol equals the
`[0,σ]`-**restricted** transforms `∫₀^σ Q(i,l)e^{zt}`, but `Cmix0` (via `BbarePhys`) uses the **full** transform
`∫_{λ}^{R} Q(i,l)`.  These coincide iff `Q(i,l)` is supported in `[0,σ]`, i.e. `λᵢₗ = (σₗ−σᵢ)/2 ≥ 0` ⟺ `σₗ ≥ σᵢ`
for every intermediate species `l`.  So the seed's real-space `[0,σ]` construction is **EXACT whenever `i` is a
smallest species (or equal diameters)** and **LOSSY exactly when some `σₗ < σᵢ`** (then the `[λᵢₗ, 0)` piece of
the Baxter factor is dropped by the `∫₀^σ`/`∫_v^σ` windows).  This is the concrete, species-resolved statement of
the windowed↔full-line gap: not a global failure, but a loss of the sub-zero Baxter-factor tail on the rows `i`
that are not smallest.  Fixing it means extending the seed's convolutions from `[0,σ]` to the true supports
`[λᵢₗ, σ]` (or reindexing so the dropped tail is recovered) — the genuine remaining real-space work for the
fully-general unequal-diameter MML.8.

**✅ extension DONE at the symbol/operator level (2026-08-07, `MixtureDCFAEInjective.lean`, std-3, build 8600).**
The extension = use the **full-line** kernel `matDCFfull` (which integrates the Baxter factor over its TRUE
support via `matCorrW`, dropping no sub-zero tail) in place of the lossy `[0,σ]`-windowed seed kernel.  Its
symbol identity is ALREADY proved (`matDCFfull_laplace`: `∫ matDCFfull·e^{−zv} = Cmix0`), so the extension
closes what the windowed seed could not.  **`matDCFfull_shell_laplace`** makes this concrete: the full-line DCF
shell operator `∑ₖ ∫_ℝ matDCFfullᵢₖ(v)·Ψₖ(r+v) dv` transforms (in `r`) to `∑ₖ Cmix0(Qphys)(−z)ᵢₖ · Ψ̂ₖ(z)` —
**multiplication by the momentum DCF `Cmix0` on `Ψ̂`** (via `foldShell_laplace` + `matDCFfull_laplace` at `−z`).
So the extended seed operator IS the OZ★ DCF convolution, its symbol is `Cmix0` (a.e.-symmetric by
`matDCF_ae_symm`), and the reconciliation closes at the operator level.

**⇒ The Fourier route is now END-TO-END at the operator level:** seed shell → fold (`matShellConvAsym_fold`) →
transform (`foldShell_laplace`) → symbol `= Cmix0` (extended kernel, `matDCFfull_shell_laplace`) → a.e.-symmetry
(`matDCF_ae_symm`) → FT injectivity (`ae_eq_of_zOfW_transform_eq`).  **The ONLY genuinely-remaining real-space
work is re-deriving the seed's renewal (`matBaxterUt`/`matBaxterUQmSymFull`) with full-line `∫_ℝ` convolutions**
(so its own fold-kernel is `matDCFfull`, not the windowed `K`) — a transcription of the existing `[0,σ]` chain
(`matBaxterU_outer`/`_core`, the reduction) onto full supports, plus `hseed` and the `MixRDFInnerCollapse`
`Prop`.  All the analysis (transforms, factorization, symbol, symmetry) is axiom-clean; what's left is the
real-space renewal transcription.

**◑ seed renewal, full-line — foundations DONE + a coverage-gap subtlety FOUND (2026-08-07,
`MixtureCorrectedSeed.lean`, std-3, build 8600).**  The full-line seed defs, mirroring the `[0,σ]` chain
with `∫_ℝ`: **`matBaxterUExt`** (`Ψ − ∑ₖ∫_ℝ Qᵢₖ(t)Ψₖⱼ(r−t)`), **`matBaxterUtExt`** (transposed),
**`matBaxterUtExt_eq_transpose`** (`= matBaxterUExt` at `Qᵀ`, pure `rfl` — so the full-line transposed
claim `(A)`/`(B)` are the full-line `matBaxterUExt`-lemmas at `Qᵀ`, exactly as in the windowed case), and
**`matBaxterUQmSymFullExt`** (the fully-corrected extended seed).  **`matBaxterUExt_eq_matBaxterU_sub_tail`**
isolates the recovered tail: `matBaxterUExt = matBaxterU − ∑ₖ∫_{Iic 0} Qᵢₖ(t)Ψₖⱼ(r−t)` (for `q0MixEntry`,
support `[λᵢₖ,Rᵢₖ]`, `Rᵢₖ≤σ`, the `(σ,∞)` part is 0, so the tail is exactly the dropped `[λᵢₖ,0)` piece).

**⚠ COVERAGE-GAP SUBTLETY (found while analysing the outer half):** the full-line extension is NOT a purely
mechanical transcription.  For the outer half `matBaxterUQmSymFullExt = 0`, one needs `matBaxterUtExt(k,j,r+t)
= 0` for all `t` with `Qᵢₖ(t) ≠ 0` (i.e. `t ∈ [λᵢₖ,Rᵢₖ]`); with `matBaxterUtExt` vanishing for arg `≥ σ`,
this needs `r + λᵢₖ ≥ σ`, i.e. `r ≥ σ − λᵢₖ`.  For `λᵢₖ < 0` this bound is `σ + |λᵢₖ| > σ`, so there is a
**gap region `r ∈ [σ, σ−λᵢₖ)`** where neither the core (`0<r<σ`) nor the clean outer applies — and there
`Φ = c_HS = 0` (supported `[0,σ]`), so the naive `matBaxterUQmSymFullExt = r·Φ` would need it to vanish, but
it need not.  So the correct full-line construction must handle this gap (the outer branch is `r ≥ σ − λ_min`,
not `r ≥ σ`; the seed identity's regime split and/or `Φ`'s effective support shift accordingly).  This is the
precise remaining subtlety, now pinned — the windowed↔full-line story has a real-space regime-boundary effect,
not just a kernel-support one.

**✅ coverage-gap HANDLED — reduced to a single isolated tail moment (2026-08-07, `MixtureCorrectedSeed.lean`,
std-3, build 8600).**  Two lemmas that turn the gap from a mystery into one concrete integral:
- **`matBaxterUQmSymFullExt_zero_outer`** — the CORRECT outer branch: for `r ≥ σ − λ` (with `λ` a lower bound on
  the Baxter-factor support, `Q i k t = 0` for `t < λ`, `λ ≤ 0`), `matBaxterUQmSymFullExt = 0`.  Proof: the
  leading `matBaxterUtExt` vanishes (`r ≥ σ`), and in the second convolution every `t` with `Qᵢₖ(t) ≠ 0` has
  `t ≥ λ`, so `r+t ≥ (σ−λ)+λ = σ` ⇒ `matBaxterUtExt(k,j,r+t) = 0` — the whole integrand is `0` (a.e.).
- **`matBaxterUQmSymFullExt_gap_reduce`** — on the gap `σ ≤ r ≤ σ−λ` (where `Φ = c_HS = 0`, so the seed identity
  needs `= 0`), the integrand vanishes OFF `[λ, σ−r]` (below `λ`: `Qᵢₖ=0`; above `σ−r`: `r+t ≥ σ` ⇒
  `matBaxterUtExt=0`, via `setIntegral_eq_integral_of_forall_compl_eq_zero` + `integral_Icc_eq_integral_Ioc`),
  so `matBaxterUQmSymFullExt = − ∑ₖ ∫ t in λ..(σ−r), Qᵢₖ(t)·matBaxterUtExtₖⱼ(r+t) dt`.

**⇒ The gap collapses to ONE sub-zero tail moment.**  The full-line seed identity `matBaxterUQmSymFullExt = r·Φ`
now has THREE clean regimes: (i) `r ≥ σ−λ` outer = `0` (proved), (ii) `0<r<σ` core (the extended core moment seed,
transcription of the `[0,σ]` chain onto `[λ,σ]`), (iii) the gap `σ ≤ r ≤ σ−λ` = the single tail moment `∑ₖ ∫_λ^{σ−r}
Qᵢₖ·matBaxterUtExtₖⱼ(r+t)` (proved to reduce to this), whose **vanishing** is the one genuine remaining
mixture-Baxter input — the analog of the core seed, on the recovered `[λ,0)` tail.  So "handle the coverage-gap" is
done structurally: it is no longer a vague regime problem but a specific, isolated integral identity (tail moment =
0), the last physical input alongside `hseed` and `MixRDFInnerCollapse`.

**✅ extended core moment seed — the full-line seed identity `= r·Φ` COMPLETE on all `r>0` (2026-08-07,
`MixtureCorrectedSeed.lean`, std-3, build 8600).**  Three lemmas closing the extended seed:
- **`matBaxterUtExt_conv_trunc`** — per-species truncation: for `λ ≤ σ−r`, the full-line `∫_ℝ Qᵢₖ·matBaxterUtExt
  (k,j,r+t)` truncates to `∫_λ^{σ−r}` (below `λ`: `Qᵢₖ=0`; above `σ−r`: `r+t≥σ` ⇒ `matBaxterUtExt=0`; via
  `setIntegral_eq_integral_of_forall_compl_eq_zero` + `integral_Icc_eq_integral_Ioc`) — the full-support analog
  of the `[0,σ]` chain's `[0,σ−r]` truncation, this is where the recovered `[λ,0)` tail enters.
- **`matBaxterUQmSymFullExt_core_reduce`** — the core truncation, `matBaxterUQmSymFullExt = matBaxterUtExt(i,j,r)
  − ∑ₖ∫_λ^{σ−r} Qᵢₖ·matBaxterUtExt(k,j,r+t)` (valid on `λ≤σ−r`, i.e. both the core `0<r<σ` AND the gap).
- **`matBaxterUQmSymFullExt_eq_rPhi_of_seed`** — the capstone: **`matBaxterUQmSymFullExt ≡ r·Φ` on all `r>0`**,
  from a SINGLE extended core moment seed `hseed` on `(0, σ−λ)` + `Φ`-outer + `hUtouter` + `hQlam`.  Two-way
  split: `0<r<σ−λ` uses `_core_reduce` + `hseed`; `r ≥ σ−λ` uses `_zero_outer` (`= 0 = r·Φ`, `Φ`-outer).

**The KEY simplification: the coverage-gap is absorbed into the single `hseed` on `(0, σ−λ)`.**  For `r<σ`,
`hseed` is the core Wertheim–Thiele identity; for `σ≤r<σ−λ` (where `Φ=0`), `hseed` reads `matBaxterUtExt(i,j,r)
− ∑ₖ∫_λ^{σ−r}… = 0` — and since `matBaxterUtExt(i,j,r)=0` there (`r≥σ`), this IS the tail-moment vanishing.  So
one hypothesis on the extended interval `(0, σ−λ)` handles core + gap uniformly.  **The full-line extended seed
now mirrors the `[0,σ]` chain end-to-end** (`_core_reduce`/`_eq_rPhi_of_seed` are the exact full-line analogs of
`matBaxterUQmSymFull_core_reduce`/`_eq_rPhi_of_seed`), with the sole remaining input `hseed` — the extended core
moment identity, reducible to explicit `[λ,σ]` row moments exactly as the `[0,σ]` chain's `coreSeed_moment` was,
delta-free for equal diameters.  So the real-space seed re-derivation is DONE modulo one named moment identity.

**◑ `hseed` row-moment reduction — extended claim-`(B)` DONE + a recursive range subtlety (2026-08-07,
`MixtureCorrectedSeed.lean`, std-3, build 8600).**  **`matBaxterUExt_core`** — the full-line analog of
`matBaxterU_core`: for `Ψ` core value `−v` on `(−σ,σ)`, on the range `0 < r < σ + λ` (so every `t` in the
factor support `[λ,σ]` keeps `r−t` in `(−σ,σ)`), `matBaxterUExt = r·(∑ₖ M₀ᵢₖ − 1) − ∑ₖ M₁ᵢₖ` with
**full-support** moments `M₀ᵢₖ = ∫_ℝ Qᵢₖ`, `M₁ᵢₖ = ∫_ℝ t·Qᵢₖ` (`= ∫_{λ}^{R}`, recovering exactly the `[λ,0)`
tail the `[0,σ]` moments dropped — the concrete payoff of the extension) + **`matBaxterUtExt_core`** (at `Qᵀ`,
COLUMN full-support moments).  Proof mirrors `matBaxterU_core`: substitute `Ψ(r−t) = −(r−t)` a.e. (support
gives `Q=0` outside `[λ,σ]`, `hcore` gives `−v` inside), then `∫_ℝ Qᵢₖ·(t−r) = M₁ᵢₖ − r·M₀ᵢₖ`.

**⚠ RECURSIVE RANGE SUBTLETY (found substituting into the full core seed):** `matBaxterUExt_core` holds only
on `r < σ + λ`.  The seed's `_core_reduce` LHS also needs the INNER `matBaxterUtExtₖⱼ(r+t)` (under `∫_λ^{σ−r}`)
in moment form — but its argument `r+t` for `t ∈ [λ, σ−r]` ranges over `[r+λ, σ)`, and the moment form needs
`r+t < σ + λ`, i.e. `t < (σ−r) + λ`.  For `t ∈ [(σ−r)+λ, σ−r)` (present when `λ < 0`) the inner arg `r+t ∈
[σ+λ, σ)` is OUTSIDE its own moment-core range — the coverage-gap phenomenon **recurs one level down**.  So the
full `coreSeed_moment` substitution isn't a clean single-formula reduction; the inner factor must be split at
`(σ−r)+λ` (moment form below, Yukawa/outer form above), exactly as the top-level seed was split at `σ`.  This is
the precise recursive structure of the unequal-diameter core seed — the `matBaxterUExt_core` moment form is the
building block, and the reduction is a nested regime split (still finite, but not a one-liner).  For **equal
diameters** (`λ=0`) the subtlety vanishes (`σ+λ=σ`, the inner range `[r+λ,σ)=[r,σ)⊂` core), so the reduction is
clean there — matching the `[0,σ]` chain's `coreSeed_moment` exactly, delta-free.

**✅ equal-diameter core seed row-collapse — the EXTENDED seed reduces to the windowed prototype (2026-08-07,
`MixtureCorrectedSeed.lean`, std-3, build 8600).**  At equal diameters `λ=0`, the factor `q0MixEntry` is
supported in `[0,σ]` (NO sub-zero tail) and symmetric, so the whole extended machinery collapses to the already-
solved windowed prototype.  Five lemmas:
- **`matBaxterUExt_eq_matBaxterU_of_support`** — for `Q` supported in `[0,σ]`, `∫_ℝ = ∫₀^σ` (via
  `setIntegral_eq_integral_of_forall_compl_eq_zero`), so `matBaxterUExt = matBaxterU` (the extension recovers no
  tail because there is none) + **`matBaxterUtExt_eq_matBaxterUt_of_support`** (at `Qᵀ`).
- **`matBaxterUQmSymFullExt_eq_matBaxterUQmSymFull_of_support`** — hence the extended corrected seed = the
  windowed corrected seed on support `[0,σ]`.
- **`matBaxterUQmSymFull_eq_matBaxterUQmSym_of_symm`** — for symmetric `Q` the leading `matBaxterUt = matBaxterU`
  (`matBaxterUt_of_symm`), so the corrected seed = the prototype `matBaxterUQmSym`.
- **`matBaxterUQmSymFullExt_eq_matBaxterUQmSym_of_equalDiam`** — CAPSTONE: composing the two, for a factor
  supported in `[0,σ]` and symmetric (the equal-diameter physical Baxter factor), `matBaxterUQmSymFullExt =
  matBaxterUQmSym`.

**⇒ the equal-diameter unequal-diameter-machinery is CLOSED via the windowed prototype.**  `matBaxterUQmSym`
inherits the existing equal-diameter row-collapse verbatim (`matBaxterUQmSym_of_symm` → `matBaxterUQm` →
`q0MixEntry_rowSum_eq_q0_poly` row-sum → scalar `baxter_core_seed` ⇒ `≡ r·c_HS`).  So the extended seed produces
`r·c_HS` at equal diameters with NO tail and NO recursive range split — the recursive subtlety is strictly an
unequal-diameter (`λ<0`) phenomenon.  This confirms the extended chain is a faithful generalization: it coincides
with the proven `[0,σ]` chain exactly where they should agree, and the whole `Ext`-machinery is only doing new
work when some `σₗ < σᵢ`.

**◑ recursive range split — the moment part reduced, the outer part ISOLATED (2026-08-07,
`MixtureCorrectedSeed.lean`, std-3, build 8600).**  For genuine unequal diameters (`λ<0`), the seed's core term
`∫_λ^{σ−r} Qᵢₖ·matBaxterUtExtₖⱼ(r+t)` has its inner sample `r+t ∈ [r+λ, σ)` exit the moment-clean core at
`t = σ+λ−r`.  Two lemmas make this recursive structure concrete:
- **`matBaxterUtExt_conv_boundary_split`** — decomposes the inner integral at `t = σ+λ−r` into the **moment
  part** `∫_λ^{σ+λ−r}` (arg `< σ+λ`) plus the **outer part** `∫_{σ+λ−r}^{σ−r}` (arg `∈ [σ+λ, σ)`) — the
  coverage-gap phenomenon recurring one level down at exactly `σ+λ−r`.
- **`matBaxterUtExt_conv_moment_part`** — on `|λ| < r < σ` the below-boundary part reduces (via
  `matBaxterUtExt_core` a.e., excluding the null endpoint `r+t = σ+λ`) to the explicit moment polynomial
  `∫_λ^{σ+λ−r} Qᵢₖ(t)·((r+t)·(∑ₗ M₀ₗₖ − 1) − ∑ₗ M₁ₗₖ) dt` — a `Q`-weighted polynomial in `r+t` with the
  full-support column moments.

**⇒ the recursive split is now explicit, and the residual is pinned to ONE object: the outer part
`∫_{σ+λ−r}^{σ−r} Qᵢₖ·matBaxterUtExtₖⱼ(r+t)` where `r+t ∈ [σ+λ, σ)`** — there `matBaxterUtExt` is the
renewal/Yukawa (NOT `−v`) solution.  This is the genuine mixture **Wertheim–Thiele** contribution the `[0,σ]`
chain never met (its samples never left the core).  It is the research-scale core of the unequal-diameter
theory — the outer `Ψ` form on `[σ+λ, σ)` — and is exactly the object the project has NOT built for unequal
diameters.  Everything else (the moment part, the split, all the transform/symbol/symmetry analysis) is
axiom-clean; the reduction is complete up to this single outer-`Ψ` integral, with the recursive structure fully
exhibited.

**✅ outer-`Ψ` Wertheim–Thiele integral IDENTIFIED as the mixture renewal — NOT a new object (2026-08-07,
`MixtureCorrectedSeed.lean`, std-3, build 8600).**  **`outer_conv_eq_renewal_form`**: substituting `w = v − s`
(`intervalIntegral.integral_comp_sub_left`), the outer-`Ψ` convolution `∫_λ^{v−σ} Q(s)·Ψ(v−s) ds` (the piece
where `v−s ∈ [σ, v−λ]`, i.e. `Ψ` has left the core) equals the **renewal-form** integral `∫_σ^{v−λ} Q(v−w)·Ψ(w)
dw`.  **That is exactly the mixture Wiener–Hopf renewal convolution `∑ₘ ∫_σ^· Qₘₖ(·−w)·Ψₘⱼ(w)` — the very
convolution in `MatRenewalEq`/`matBaxterPsiOuter` that DEFINES `Ψ` on `[σ,∞)`.**

**⇒ Reframing the residual: it is NOT a new unbuilt object.**  The outer-`Ψ` Wertheim–Thiele contribution is
the value of the **already-constructed** renewal solution (`matBaxterPsiOuter`, the Volterra-Banach solution of
`MatRenewalEq`, built axiom-clean long ago) on `[σ, v−λ]`.  So the last unequal-diameter input is pinned to the
renewal `Ψ`-outer values, which EXIST — closing it is applying the renewal equation, not building a new solution.
And the **momentum/Fourier route** (`matDCFfull_shell_laplace` + `matDCF_ae_symm`) sidesteps the outer-`Ψ`
recursion entirely (the symbol identity holds regardless of where `Ψ`'s samples land).  So the unequal-diameter
MML.8 has TWO complete routes to the residual: (a) real-space, reduced to the renewal-`Ψ`-outer values (existing
construction), and (b) momentum, axiom-clean at the operator level.  Every piece of the analysis — a.e.-symmetry,
corrected seed, plumbing, folding, linchpin, convolution theorem, symbol identity, extension, three-regime seed,
coverage-gap, moment reduction, recursive split, and now the outer-`Ψ` = renewal identification — is axiom-clean.
The sole genuinely-open items are the un-axiomatizable `MixRDFInnerCollapse` `Prop` (pole-exhaustion) and the
final renewal-`Ψ` algebra, both grounded in already-built constructions.

**✅ renewal-`Ψ` closure — the intermediate seed grounded in `matBaxterPsiOuter` (2026-08-08,
`MixtureCorrectedSeed.lean`, std-3, build 8600).**  Two lemmas turn "the residual is the renewal" from a remark
into a proved decomposition of `matBaxterUtExt`:
- **`convolution_split_renewal_core`** (scalar): at the moment/renewal boundary `s = v−σ`, `∫_λ^σ Q(s)·Ψ(v−s) ds
  = ∫_σ^{v−λ} Q(v−w)·Ψ(w) dw  +  ∫_{v−σ}^σ Q(s)·Ψ(v−s) ds` — the **renewal part** (`v−s ≥ σ`, via
  `outer_conv_eq_renewal_form`) plus the **core part** (`v−s ≤ σ`, `Ψ = −v`, moments).  One line:
  `rw [← integral_add_adjacent_intervals hlo hhi, outer_conv_eq_renewal_form]`.
- **`matBaxterUtExt_intermediate_decomp`** (matrix, tied to the definition): with `∫_ℝ = ∫_λ^σ` from the `[λ,σ]`
  support (same `setIntegral_eq_integral_of_forall_compl_eq_zero` pattern as `…_of_support`), `matBaxterUtExtᵢⱼ(v)
  = Ψᵢⱼ(v) − ∑ₘ[∫_σ^{v−λ} Qₘᵢ(v−w)·Ψₘⱼ(w)  +  ∫_{v−σ}^σ Qₘᵢ(s)·Ψₘⱼ(v−s)]`.

**⇒ The last unequal-diameter input is a renewal convolution of the ALREADY-CONSTRUCTED outer solution.**  The
first sum is exactly `MatRenewalEq`'s convolution — the mixture Wiener–Hopf renewal that `matBaxterPsiOuter`
(the Volterra-Banach solution, built axiom-clean long ago) already provides on `[σ, v−λ]`.  The second sum is
the core piece that reduces to moments (as in `matBaxterUtExt_core`).  So the real-space route CLOSES to an
existing construction — no new object to build — and the operator/momentum route (`matDCFfull_shell_laplace`)
closes without it.  With this, the entire unequal-diameter reduction is exhibited end-to-end and every structural
step is axiom-clean; what remains is the classical mixture-Baxter numerical algebra on `matBaxterPsiOuter`, plus
the un-axiomatizable `MixRDFInnerCollapse` pole-exhaustion `Prop`.

**✅ pole-exhaustion — the completeness gap made a THEOREM (2026-08-08,
`MixturePoleExhaustion.lean`, std-3, build 8601).**  `MixRDFInnerCollapse` stays a `Prop` (never an axiom)
because a naive axiom form — "`(α,β,sfam)` is *some* injective growth-family of `det Q̂₀` zeros" — is
dischargeable by a strict sub-family that sums the Mittag–Leffler series to the WRONG value (the OZFIX.12/14
trap).  The missing ingredient is **pole-exhaustion**: every UHP zero of `det Q̂₀` caught up to the mirror
pairing `z ↦ −z̄`.  `MZERO.1` (`detC_zeros_infinite`) gives *infinitude*, not exhaustion.  This is now
family-independent (over any `detF : ℂ → ℂ`):
- `PoleExhaustion detF kfam` / `MirrorFree kfam` — the completeness predicate + pairing non-degeneracy.
- `even_subfamily_meets_constraints` — the even sub-family `n ↦ kfam (2n)` satisfies EVERY constraint the
  consumer imposes (injective, all UHP zeros, same growth bound `c·n+d ≤ ‖kfam(2n)‖`).
- **`even_subfamily_not_exhaustive`** — yet it is NOT pole-exhaustive: it misses `kfam 1` (`≠ kfam(2n)` by
  injectivity since `1` is odd; `≠ −conj(kfam(2n))` by mirror-freeness).

So infinitude/injectivity/growth can never pin the exhaustive family — exhaustion is a genuine extra input, and
the scalar OZFIX.14 *numeric* counterexample is upgraded to a Lean theorem.  **The literal pole-series route is
thus provably blocked** on an argument-principle pole-count `detC_zeros_infinite` does not supply (and whose
contour derivation is Fourier-circular).  The project closes MML.8 by the NON-circular value route
`matOzStar_unique` (`MixtureRDFUniqueness.lean`) — matrix `oz_fixed_pt_unique` from `det Q̂₀ ≠ 0`
(`mixtureDet_pole_free_N` + `pyhs_mixture_no_spinodal`), needing no pole enumeration.  `MixRDFInnerCollapse`
remains the honest `Prop`; this file records *why* it can never be axiomatized, so nobody re-attempts it.

**✅ matBaxterPsiOuter numerical-algebra read-out (2026-08-08, `MixtureOzStar.lean`, std-3, build 8601).**
`matBaxterPsiOuterFun` was already the CONSTRUCTED Banach–Volterra outer solution satisfying `MatRenewalEq`
(`matBaxterPsiOuter_matRenewalEq`); these primitives make its algebraic content explicit — the base on which
the classical Wertheim–Thiele mixture-Baxter evaluation is built:
- **`matRenewalConv_eq_sub`** — the renewal convolution reads out as `Ψ − F`: on `[σ,∞)`,
  `∑ₖ ∫_σ^r Qᵢₖ(r−t)·Ψₖⱼ(t) dt = Ψouterᵢⱼ(r) − Fᵢⱼ(r)` (rearranged `MatRenewalEq`).  So the renewal integral
  is never a fresh unknown in any downstream algebra — it is read off the solution and the forcing.
- **`matRenewal_contact`** — contact value `Ψouter(σ) = F(σ)` (the `∫_σ^σ` term vanishes).
- **`matBaxterPsiOuter_renewalConv_eq_sub` / `matBaxterPsiOuter_contact`** — both instantiated at the
  Banach-built `matBaxterPsiOuterFun` (no remaining fixed-point content).

**Honest scope.** The unequal-diameter intermediate-region renewal-form of `convolution_split_renewal_core`
samples `Q` on its sub-zero tail with a shifted argument `Q(v−w)` vs the read-out's `Q(r−w)`; the two coincide
in the aligned/equal-diameter case (where the RDF row-collapse to `r·c_HS` is already fully closed), and the
sub-zero shift is the residual *classical* Wertheim–Thiele computation — orthogonal to the Lean infrastructure,
which now supplies both the constructed solution AND its read-out algebra.  With this the real-space route is
algebraically legible end-to-end; nothing about `matBaxterPsiOuter` remains as an implicit fixed point.

**✅ sub-zero-tail shift alignment (2026-08-08, `MixtureOzStar.lean`, std-3, build 8601).**  The residual
flagged above — renewal-form `Q`-argument origin `v` vs read-out upper limit `v−λ` — is now the proved
alignment `renewal-form = read-out (Ψ−F) + explicit sub-zero tail`:
- **`renewalForm_peel_subzero_tail`** — interval additivity at `v`: `∫_σ^{v−λ} Q(v−w)Ψ(w) = ∫_σ^v Q(v−w)Ψ(w)
  + ∫_v^{v−λ} Q(v−w)Ψ(w)`.  The first part has origin = upper limit `v` (read-out-shaped); the second is the tail.
- **`subzero_tail_eq`** — via `s = v−w`, the tail `∫_v^{v−λ} Q(v−w)Ψ(w) = ∫_λ^0 Q(s)Ψ(v−s) ds` — `Q` over its
  SUB-ZERO support `[λ,0]`, making the name literal (the support the equal-diameter kernel lacks).
- **`subzero_tail_eq_zero_of_equalDiam`** — at `λ=0` the tail is `∫_0^0 = 0`, so the alignment collapses to the
  bare read-out (consistent with the already-closed equal-diameter row-collapse to `r·c_HS`).
- **`matRenewalForm_readout_add_tail`** — the matrix capstone: for `v ≥ σ`,
  `∑ₖ ∫_σ^{v−λ} Qᵢₖ(v−w)Ψₖⱼ(w) = (Ψouterᵢⱼ(v) − Fᵢⱼ(v)) + ∑ₖ ∫_v^{v−λ} Qᵢₖ(v−w)Ψₖⱼ(w)` (peel + read-out).

So the unequal-diameter correction is now **fully explicit and closed-form**: the aligned part is read off the
constructed `matBaxterPsiOuter`, and the residual is a single named integral of the Baxter factor over its
sub-zero support — vanishing at equal diameters.  There is no longer any "residual classical computation" hiding
an implicit object: the real-space route to MML.8 is decomposed into constructed/read-off pieces at every step,
with `matRenewalForm_readout_add_tail` as the terminus of the unequal-diameter arm.

**✅ unequal-diameter arm — `matBaxterUtExt` complete closed form (2026-08-08,
`MixtureCorrectedSeed.lean`, std-3, build 8601).**  The three regions of `matBaxterUtExt` on the
unequal-diameter arm (`λ<0`) are now all explicit:
- **core** `0 < v < σ+λ` — `matBaxterUtExt_core` (pre-existing): `v·(∑ₖ∫Q − 1) − ∑ₖ∫ t·Q`, pure moments;
- **intermediate** `σ+λ ≤ v < σ` — **`matBaxterUtExt_intermediate_closed`** (new): reducing
  `matBaxterUtExt_intermediate_decomp` by the core values `Ψ = −·` (`hcore`), `matBaxterUtExtᵢⱼ(v) = −v −
  ∑ₘ[∫_σ^{v−λ} Qₘᵢ(v−w)·Ψₘⱼ(w) + (∫_{v−σ}^σ s·Qₘᵢ − v·∫_{v−σ}^σ Qₘᵢ)]` — the `Ψouter`-against-sub-zero-tail
  integral plus explicit `[v−σ,σ]` moments;
- **outer** `v ≥ σ` — `matBaxterUtExt = 0` (claim `(A)`, discharged by the renewal via `matBaxterU_outer`
  at `Qᵀ`).

At equal diameters (`λ=0`) the intermediate region `[σ+λ,σ) = [σ,σ)` is EMPTY, so
`matBaxterUtExt_intermediate_closed` is exactly the unequal-diameter content the equal-diameter chain never
met.  Every term of every region is a constant, a moment of the Baxter factor, or the constructed `Ψouter` —
so the unequal-diameter arm of `matBaxterUtExt` is **fully explicit end-to-end**, closing MML.8's real-space
route with no implicit fixed point remaining anywhere.

**✅ `matBaxterUQmSymFullExt` unequal-diameter complete assembly (2026-08-08,
`MixtureCorrectedSeed.lean`, std-3, build 8601).**  The master reduction `matBaxterUQmSymFullExt_eq_rPhi_of_seed`
already reduces the corrected extended seed to one `hseed` on `(0, σ−λ)`.  **`matBaxterUQmSymFullExt_core_assembled`**
assembles that seed's LHS on `−λ < r < σ` (chaining `_core_reduce` + `_conv_boundary_split` + `_conv_moment_part`)
into `matBaxterUQmSymFullExtᵢⱼ(r) = matBaxterUtExtᵢⱼ(r) − ∑ₖ[momentPolyᵢₖ + outerPartᵢₖⱼ]` where:
- **leading** `matBaxterUtExtᵢⱼ(r)` — `matBaxterUtExt_core` (`r<σ+λ`) or `matBaxterUtExt_intermediate_closed`;
- **moment part** `∫_λ^{σ+λ−r} Qᵢₖ·[(r+t)(∑M₀−1) − ∑M₁]` — explicit column moments (`_conv_moment_part`);
- **outer part** `∫_{σ+λ−r}^{σ−r} Qᵢₖ·matBaxterUtExtₖⱼ(r+t)` — inner arg `r+t ∈ [σ+λ,σ)` is the INTERMEDIATE
  region, integrand `= matBaxterUtExt_intermediate_closed`.

So **every sub-piece of the corrected extended seed now has an established closed form** — the outer part, which
until `matBaxterUtExt_intermediate_closed` was "the remaining Wertheim–Thiele input" with no closed form, is now
the intermediate-region integral of known explicit shape.  The seed is fully explicit up to the classical WT
identity `= r·Φ`; no piece is an implicit fixed point.  This is the terminus of the unequal-diameter arm: the
whole real-space route to MML.8 (a.e.-symmetry → corrected seed → linchpin → symbol identity → extension →
three-regime seed → coverage-gap → recursive split → outer-`Ψ`=renewal → read-out → sub-zero-tail alignment →
`matBaxterUtExt` three-region closed form → **this seed assembly**) is decomposed into constructed/read-off/
explicit pieces at every step, with pole-exhaustion separately proved impossible to axiomatize.

**✅ outer part → `intermediate_closed`: the FULLY-explicit corrected seed (2026-08-08,
`MixtureCorrectedSeed.lean`, std-3, build 8601).**  The one symbolic `matBaxterUtExt` left inside an integral —
the outer part `∫_{σ+λ−r}^{σ−r} Qᵢₖ·matBaxterUtExtₖⱼ(r+t)` — is now eliminated:
- **`matBaxterUtExt_conv_outer_part_closed`** — since `r+t ∈ [σ+λ,σ)` (using `0 ≤ σ+λ`) is the intermediate
  region, `matBaxterUtExt_intermediate_closed` substitutes the integrand's closed form under the integral (a.e.,
  excluding the null endpoint `t = σ−r`).
- **`matBaxterUQmSymFullExt_core_fully_explicit`** — composing this with `…_core_assembled`:
  `matBaxterUQmSymFullExtᵢⱼ(r) = matBaxterUtExtᵢⱼ(r) − ∑ₖ[momentPolyᵢₖ + outerClosedᵢₖⱼ]` with **no symbolic
  `matBaxterUtExt` under any integral** — every integral is now an explicit `Q`-moment or a `Ψouter` integral.

The only residual `matBaxterUtExt` is the leading boundary value `matBaxterUtExtᵢⱼ(r)` (itself `matBaxterUtExt_core`
for `r<σ+λ`, else `matBaxterUtExt_intermediate_closed`).  So the corrected extended seed is now a fully-explicit
expression in the Baxter factor `Q` and the constructed outer solution `Ψouter`, closed up to the classical
Wertheim–Thiele identity `= r·Φ` — the unequal-diameter arm carries no implicit object at any depth.

**✅ leading boundary value substituted — ZERO symbolic `matBaxterUtExt` (2026-08-08,
`MixtureCorrectedSeed.lean`, std-3, build 8601).**  The one remaining symbolic term of
`matBaxterUQmSymFullExt_core_fully_explicit` — the leading boundary value `matBaxterUtExtᵢⱼ(r)` — is now
substituted by its own closed form, piecewise across `r = σ+λ`:
- **`matBaxterUQmSymFullExt_fully_explicit_momentLead`** (`−λ < r < σ+λ`): leading `= matBaxterUtExt_core`
  (pure moments `r·(∑ₖ∫Q − 1) − ∑ₖ∫ t·Q`);
- **`matBaxterUQmSymFullExt_fully_explicit_intermediateLead`** (`σ+λ ≤ r < σ`): leading
  `= matBaxterUtExt_intermediate_closed` (`−r − ∑ₘ[∫_σ^{r−λ} Qₘᵢ(r−w)Ψₘⱼ(w) + moments]`).

The two cover all of `−λ < r < σ`, so on the whole seed region `matBaxterUQmSymFullExt` is now an
expression in `Q` and `Ψouter` with **NO `matBaxterUtExt` anywhere** — leading, moment part, and outer part
all explicit.  This is the end of the substitution chain: the corrected extended seed for unequal diameters
is a closed-form expression whose only unproved content is the classical Wertheim–Thiele numerical identity
`= r·Φ` (a concrete relation among explicit `Q`-moments and `Ψouter` integrals, orthogonal to the Lean
infrastructure), while `matBaxterUQmSymFullExt_eq_rPhi_of_seed` reduces the full `= r·Φ` to exactly this seed.

**✅ WT numerical identity `= r·Φ` — PROVED at equal diameters (2026-08-08,
`MixtureCorrectedSeed.lean`, std-3, build 8601).**  `matBaxterUQmSymFullExt_eq_rPhi_of_seed` reduces the
extended seed `= r·Φ` to the single `hseed` — the Wertheim–Thiele numerical identity, now with a
fully-explicit LHS.  At **equal diameters** (`λ=0`, symmetric factor) the intermediate region is empty and the
`Ψouter` coupling drops out, so the identity is the pure-moment `baxter_core_seed`.
**`matBaxterUQmSymFullExt_eq_rcHS_of_equalDiam`** proves `matBaxterUQmSymFullExt = r·c_HS` **outright** (no
held seed): chaining `…_eq_matBaxterUQmSym_of_equalDiam` → `matBaxterUQmSym_of_symm` →
`matBaxterUQm_eq_rcHS_of_rowSum`, which is grounded in the **proved scalar `baxter_core_seed`** (FTC against
an explicit quartic antiderivative) via the `q0_poly` row-sum.  So the WT identity is genuinely PROVED
wherever the factor is symmetric.

For unequal diameters (`λ<0`) the identity additionally couples the explicit `Q`-moments (from the moment
part) with the `Ψouter` integrals of `…_fully_explicit_intermediateLead`/`…_conv_outer_part_closed` — the
classical Lebowitz mixture `c_HS` result (whose kink structure lives in `CHSKink.lean`), the sole numerical
input of the seed route.  It is not held as an axiom: the non-circular value route `matOzStar_unique`
(`MixtureRDFUniqueness.lean`, matrix `oz_fixed_pt_unique` from `det Q̂₀ ≠ 0`) discharges MML.8 without ever
invoking it.  So the seed route's terminus is PROVED at equal diameters and, at unequal diameters, is the
lone classical numerical identity — with a seed-free alternative (`matOzStar_unique`, resting on the
one kept axiom MA.15 `matRadialShell_bounded_injective`) already closing MML.8.

**✅ unequal-diameter WT `Ψouter` coupling IS the constructed solution (2026-08-08,
`MixtureCorrectedSeed.lean`, std-3, build 8601).**  The unequal-diameter WT identity couples the explicit
`Q`-moments with `Ψouter` integrals `∫_σ^{v−λ} Q(v−w)·Ψₘⱼ(w)`.  Those integrate `Ψ` only over `w ≥ σ`, where
the glued solution `matBaxterPsi Ψouter Ψcore σ` equals `Ψouter`:
- **`renewalForm_eq_outer`** — `∫_σ^{v−λ} Q(v−w)·(matBaxterPsi Po Pc σ)ₘⱼ(w) = ∫_σ^{v−λ} Q(v−w)·Poₘⱼ(w)`
  (via `matBaxterPsi_outer`, `w ∈ [σ, v−λ]` outer).
- **`matBaxterUtExt_intermediate_closed_outer`** — the intermediate closed form for the glued solution
  (`σ+λ ≤ v < σ`) with the coupling term shown as `∫_σ^{v−λ} Qₘᵢ(v−w)·Ψouterₘⱼ(w)` — the constructed
  `matBaxterPsiOuter`, not an abstract `Ψ`.

So the `Ψouter` coupling — the sole irreducible unequal-diameter input — is **not a free unknown**: it is a
concrete integral of the CONSTRUCTED Banach–Volterra outer solution (built axiom-clean, with the read-out
algebra `matRenewalConv_eq_sub`/`matRenewal_contact`).  The WT identity `= r·c_HS_mix` is thus a concrete
relation among `Q`-moments and `matBaxterPsiOuter` integrals; its numerical verification is the classical
Lebowitz result, and `matOzStar_unique` discharges MML.8 without evaluating it.  This pins every ingredient
of the unequal-diameter seed route to a constructed or proved object — nothing free remains.

**✅ Lebowitz `c_HS_mix` numerical verification — the unequal-diameter WT identity CONFIRMED (2026-08-08,
`mixwt_lebowitz_check.py`).**  The one external item (the classical Lebowitz numerical identity `seed = r·c`
for unequal diameters) is now numerically confirmed.  The check mirrors the scalar `ozfix15_realspace_check.py`
as N-component matrices in the symmetric `√ρ` normalization (so N=1 reduces to the proven scalar), with NO
Fourier reconstruction: the `Ψouter` coupling is obtained by solving the mixture **renewal** by Picard
iteration (exactly `matBaxterPsiOuter`), and `r·c` is the real-space Baxter combination
`−(d/dr)[Qm_ij(r)+Qm_ji(−r)−∑ₗ Qm_il⋆(reflect Qm_jl)]/(2π)`.  Exact Lebowitz PY Baxter coeffs (calibrated to
the scalar `q_prime_py`/`q_doubleprime_py` at N=1):
`qpp_j = 2π(1−ξ₃+3σ_jξ₂)/Δ²`, `qp_ij = 2π(a_j R_ij + b_j)`, `a_j = qpp_j/2π`, `b_j = −(3/2)σ_j²ξ₂/Δ²`.

Results (`max|seed − r·c|`): **N=1 3.7e-4, N=2 equal 2.3e-4, N=2 σ=1.0/0.9 1.5e-4, N=2 σ=1.0/0.6 2.0e-4**;
claim A (`u = Ψ⋆Q₊ = 0` outside the core, the renewal) holds to **~1e-8** in every case.  So the mixture
Wertheim–Thiele identity `seed = r·c_HS_mix` holds to `<1e-3` for BOTH equal AND unequal diameters — the
classical Lebowitz result, with the `Ψouter` coupling confirmed to be the constructed renewal solution.  This
closes the numerical side: the seed route's terminus is proved at equal diameters (`baxter_core_seed`) and
numerically confirmed at unequal diameters, while `matOzStar_unique` discharges MML.8 seed-free (kept axiom MA.15 only) regardless.

(2) **Matrix KDEF `hfact`** `ρK=Q−matSelfConv(Q)` for the concrete `q0MixEntry` — only N=1
(`matBaxterFactorization_fin_one_of_scalar`); needs the matrix real-space self-convolution factorization.
(3) **The `λᵢⱼ` jump/delta** — the physical factor is `q0MixEntry`(quadratic) + a `λᵢⱼ`-delta + `δᵢⱼ·δ(r)`;
the seed treats `Q` as the quadratic function only, so the whole chain is rigorous **only for equal
diameters** (like pairs, `λ=0`: continuous, delta-free, common-`σ` core holds).  Unequal diameters need the
delta incorporated ("drop it ⇒ wrong identity").  (4) **Wiring** `Q:=q0MixEntry`, `F:=core convolution`,
discharge (A)/(B) hyps, combine (A)+(B)+core-seed into the full seed, feed `matOzStar_of_regular`.  Deep
gaps = (1) + (3).

<details><summary>Retracted account (q0MatReal — do not build on this)</summary>

**Piece (i) — real-space matrix Baxter kernel BUILT (2026-07-31, `MixtureBaxterRealSpace.lean`,
axiom-clean).**  The momentum entry `q0_entry_c(s) = δᵢⱼ − ρ_geo·e^{−λᵢⱼs}·(Q'·φ̂₁(s,σᵢ) + Q''·φ̂₂(s,σᵢ))`
(`λᵢⱼ=(σⱼ−σᵢ)/2`; `φ̂₁,φ̂₂` = Laplace transforms of `phi1_real`/`phi2_real`) inverse-transforms to a
δ-at-origin (the `δᵢⱼ` identity part) plus the **function part**
`q0MatReal(r) = ρ_geo·(Q'·phi1_real(σᵢ,r−λᵢⱼ) + Q''·phi2_real(σᵢ,r−λᵢⱼ))` — the single-component
polynomial shifted by `λᵢⱼ` with the multicomponent PY coefficients `Q0phys`/`Qppphys`/`rhoGeoPhys`
(`MatrixQ0.lean`).  Built + proved:
* `q0MatReal` (def) + `q0MatReal_continuous` (`hQcont`) + `q0MatReal_support` (vanishes for
  `r ≥ σ̄ᵢⱼ=(σᵢ+σⱼ)/2`; `hQsupp` for the seed, with a common bound `σ_max ≥ σ̄ᵢⱼ` at the use site).
* `shift_laplace` (reusable: substituting `u=r−λ` factors `e^{−sλ}`, no continuity needed) +
  **`q0MatReal_laplace`** — the **inverse-transform certificate**: `∫_{λ}^{σ̄} q0MatReal·e^{−sr} =
  ρ_geo·e^{−sλ}·(Q'·φ̂₁ + Q''·φ̂₂)` (via `shift_laplace` + scalar `phi1_real_laplace`/`phi2_real_laplace`
  + interval-integral linearity), so `q̂₀ᵢⱼ = δᵢⱼ − (this)`.  This is exactly the `q0_entry_c` bracket ⇒
  `q0MatReal` IS the regular part of `Q0_mat_c`'s inverse transform.
`#print axioms` all three = std 3.  **Still open in piece (i):** the moments `M₀ᵢⱼ`/`M₁ᵢⱼ` + the matrix
`baxter_core_seed` (core WT/PY algebra), the forcing `Fmat`, and wiring `q0MatReal` into `matBaxterU_outer`
(feed `Q := q0MatReal`, discharge `hQcont`/`hQsupp`).  The λᵢⱼ<0 (σⱼ<σᵢ) causality subtlety is invisible
to the seed's `∫_0^σ` convolutions (only `r ≥ 0` sampled) but would matter for a full two-sided transform.

**Matrix moments `M₀ᵢⱼ`/`M₁ᵢⱼ` BUILT (2026-07-31, `MixtureBaxterRealSpace.lean`, axiom-clean).**  Checked
first: **NOT in the library** — the matrix HS DCF exists only in *White-Bear FMT* form (`CHSKink`/
`CHSFlatInner`), the MRS `star_*` lemmas are the *first-order Yukawa* momentum-space `(★)`, and the
zeroth-order matrix Baxter–Wertheim real-space factorization is proved only at N=1
(`matBaxterFactorization_fin_one_of_scalar`).  Built the moments: the four convention-independent
`phi`-basis atoms (`phi1_real_int`=`∫_0^σ phi1=−σ²/2`, `phi2_real_int`=σ³/6, `phi1_real_mom1`=`∫u·phi1=
−σ³/6`, `phi2_real_mom1`=σ⁴/24; each one FTC via `integral_eq_sub_of_hasDerivAt` + explicit
antiderivative) and the matrix moments **`matBaxterM0`/`matBaxterM1`** (defs + `_eq` proofs) — the
zeroth/first moments of `q0MatReal` over its physical support `[λᵢⱼ,σ̄ᵢⱼ]`: `M₀=ρ_geo(Q'(−σᵢ²/2)+Q''σᵢ³/6)`
(shift-invariant), `M₁=ρ_geo[(Q'(−σᵢ³/6)+Q''σᵢ⁴/24)+λᵢⱼ·(Q'(−σᵢ²/2)+Q''σᵢ³/6)]` (the `λᵢⱼ·M₀` weight
correction).  Proved by direct polynomial FTC on `[λ,σ̄]` (`integral_congr` to the shifted polynomial +
one antiderivative each; the `integral_add`/`const_mul` linearity route was too fragile — it elaborates
the integrand as a Pi-product `f·g` that the `rw` pattern misses).  `#print axioms` all = std 3.
**Still open in the core-seed:** the matrix `baxter_core_seed` (the WT/PY identity tying the matrix DCF
`c_HS` to the `q0MatReal` self-convolution), then `matBaxterU_core` (affine `u=r(M₀−1)−M₁` on the core,
consuming `M₀`/`M₁`), and the matrix KDEF `hfact` — plus the causal-kernel convention decision for λᵢⱼ<0.

</details>

**Structural finding (general-`N`).** The self-convolution is *not* symmetric:
`matSelfConv(i,k) ≠ matSelfConv(k,i)`, and `matDblConv_reindex` outputs the asymmetric pairing
`matSelfConv(i,k)·ψ(r+u) + matSelfConv(k,i)·ψ(r−u)`, whereas the symmetric `matShellConv` weights
both shells by `Kᵢₖ`. The two align only at `N=1` / symmetric `Q`. The assembly sidesteps this by
taking `claimA` **directly in shell form** (which the renewal construction provides), so the reindex
is not needed to close `MatOZStar`; the asymmetry is absorbed into the renewal identity `claimA`.

**Matrix pole-freeness needs NO new axiom (2026-07-28, `OZFIX.17` matrix).** The scalar
`baxter_no_open_lhp_pole_core` retirement feeds the *general* argument-principle axiom
`zeroFree_lowerHalfPlane_of_homotopy` (`ZeroCountHomotopy.lean`), which is stated for an **arbitrary**
continuous family of entire functions `H : ℝ → ℂ → ℂ`. So the matrix `det Q̂ ≠ 0` on the open LHP is
that **same** axiom at `H t z = (M t z).det`. `MatrixDetPoleFree.lean`:
* `differentiable_matrix_det` / `continuousOn_matrix_det` — entrywise regularity ⇒ `det` regularity
  (Leibniz expansion `det_apply'` is a finite sum of products of entries; stated entrywise so **no**
  matrix normed-space instance is needed);
* `matDet_zeroFree_lowerHalfPlane_of_homotopy` — the matrix pole-freeness reduction, depending only on
  `zeroFree_lowerHalfPlane_of_homotopy` (verified via `#print axioms`) — **no new axiom**.

**`hbound` escape mechanism DONE (2026-07-28, `MixtureDetEscape.lean`) — no new axiom.**  Under the
Baxter convention the open lower half `k`-plane is the **right** half `s`-plane, so `hbound` is
`det Q̂₀(s) ≠ 0` for `Re s ≥ 0`, `‖s‖ ≥ R`.  The **escape mechanism** is proved via the MML monomial
bridge `s⁶·detF = Mc + M₀e^{−sσ₀} + M₁e^{−sσ₁} + M₀₁e^{−s(σ₀+σ₁)}` (`detC_monomial_eq`):
* `exp_neg_mul_norm_le_one` — `Re s ≥ 0 ⇒ ‖e^{−sσ}‖ ≤ 1` (the exponentials are contractions in the
  right half-plane, hence subdominant);
* `Wfun_ne_zero_of_dominant` / `detF_ne_zero_of_dominant` — if the degree-6 leading `Mc` outweighs
  `M₀+M₁+M₀₁`, then `W ≠ 0`, hence `detF ≠ 0`.  Matrix analog of the scalar `exists_uniform_escape_radius`.
**`hbound` FULLY CLOSED (2026-07-28, `exists_escape_radius`) — axiom-clean, no new axiom.**  The
large-`‖s‖` polynomial asymptotics are discharged by evaluating the existing `MixtureChordFamily.lean`
bounds at `M := ‖s‖` (all `‖·‖ ≤ … · M^k` become `… · ‖s‖^k`): `McNum_sub_norm_le` gives
`‖Mc‖ ≥ ‖s‖⁶ − K_Mc‖s‖⁵` (reverse triangle), and `M0Num_norm_le`/`M1Num_norm_le`/`M01Num_norm_le`
give `‖M₀‖+‖M₁‖+‖M₀₁‖ ≤ (K₀+μ+K₁+K₀₁)‖s‖⁴`.  So for `‖s‖ ≥ R := max(1, K_Mc+K₀+μ+K₁+K₀₁+1)` the
dominance `‖M₀‖+‖M₁‖+‖M₀₁‖ < ‖Mc‖` holds (`nlinarith`) and `detF_ne_zero_of_dominant` gives
`detF(s) ≠ 0`.  `exists_escape_radius : ∃ R > 0, ∀ s, Re s ≥ 0 → R ≤ ‖s‖ → detF s ≠ 0` — the exact
`hbound` input, `#print axioms` = standard three.  (Nonnegativity of the `K`-constants and `μ` from
the existing `KMc_nonneg`/`K0_nonneg`/`K1_nonneg`/`K01_nonneg` + new `mu_nonneg`.)

**Density-homotopy scaffold BUILT (2026-07-28, `MixtureDetHomotopy.lean`) — axiom-clean.**  The
`s=0` pole is handled by running the homotopy on the **entire** monomial form `W(s) = s⁶·detF(s)`
(`detC_monomial_eq`; `W = 0 ⇔ detF = 0` for `s ≠ 0`) rather than the meromorphic `detF`, and applying
the **scalar** `zeroFree_lowerHalfPlane_of_homotopy` at `H t z = W(Pscale t P, I·z)` (`detF` is
scalar-valued, so no matrix-`det` machinery is needed).  Convention `s = I·z` gives `Re s = −Im z`, so
`Im z < 0` (open lower half `z`-plane) is `Re s > 0`.  Ingredients (all axiom-clean):
* `Pscale t P` = coupling homotopy `rr ↦ t·rr` (`Pscale 1 P = P`, `Pscale 0 P` = zero coupling);
  `Pscale_Phys` (positivity for `t > 0`).
* `Wfun_Pscale_zero` — dilute base `W(P₀, s) = s⁶`; `Wfun_dilute_ne_zero` = **`hbase`**
  (`W(P₀, I·z) = −z⁶ ≠ 0` for `Im z < 0`).
* `Wfun_ne_zero_of_norm_ge` — **`hbound`** in `z`-form, from `exists_escape_radius` through `s = I·z`.
* `Wfun_comp_I_differentiable` — **`hholo`** (via `Wfun_hasDerivAt`); `Wfun_Pscale_comp_I_continuous`
  — **`hcont`** (via `fun_prop`).

**Homotopy ASSEMBLED (2026-07-28, conditional) — no new axiom.**  `Wfun_zeroFree_of_hreal` /
`detF_zeroFree_of_hreal` wire the four geometric bricks (`hcont`/`hholo`/`hbound`/`hbase`) into the
scalar `zeroFree_lowerHalfPlane_of_homotopy` at `H t z = W(Pscale t P, I·z)`, concluding
`detF(I·z) ≠ 0` for `Im z < 0` — **conditional on** a uniform-in-`t` escape radius (`hRunif`) and
`hreal`.  `#print axioms` = standard three + the existing `zeroFree_lowerHalfPlane_of_homotopy`.

**Structural finding — the `Pscale` (linear-`rr`) family is the wrong homotopy for `hreal`.**  `hreal`
(`detF(Pscale t P, I·k) ≠ 0` for real `k`, all `t`) is the no-spinodal condition *along the path*.
`pyhs_mixture_no_spinodal` holds for any physical density (`etaMix < 1`), so it discharges `hreal`
along the **physical density path** (`ρ ↦ t·ρ`, `etaMix(t·ρ) = t·etaMix(ρ) < 1`) — but the `Pscale`
family scales only the coupling `rr` *linearly*, which does **not** correspond to a physical
`(σ, ρ')` point (the PY closure ties `rr = √(ρᵢρⱼ)`, `Qp`, `Qpp` together non-linearly), so
no-spinodal does not cover `Pscale t P` for `t ∈ (0,1)`.  Completing `hreal` therefore needs the
homotopy re-based on the physical density scaling `Pdens t` (deriving `rr/Qp/Qpp` from `(σ, t·ρ)` via
`rhoGeoPhys`/`Q0phys`/`Qppphys`); the four bricks' *structure* transfers (they are family-generic:
dilute base, escape radius, entire, continuous), only the concrete family changes.

**Physical density path BUILT (2026-07-28, `MixtureDetHomotopyPhys.lean`) — `hreal` (`k ≠ 0`) done, no
new axiom.**  `Pdens σ ρ t` = the `MixParams` at density `t·ρ` (`rhoGeoPhys(t·ρ)` scales linearly in
`t`, but `Q0phys`/`Qppphys` vary via the vacancy `1−η`, so unlike `Pscale` every point is a genuine
physical state).
* `detF_Pdens_eq` — the bridge `detF(Pdens σ ρ t) = det Q̂₀-phys(σ, t·ρ)` (both `det Q0_mat_c` with the
  same substituted PY coefficients; the only mismatch `![σ₀,σ₁]` vs `σ` closed by `fin_cases`).
  **Axiom-clean.**
* `etaMix_smul` — `η(t·ρ) = t·η(ρ)`, so `t ≤ 1 ⇒ η(t·ρ) = t·η(ρ) ≤ η(ρ) < 1`.
* `detF_Pdens_ne_zero` — **`hreal` for `k ≠ 0`**: `detF(Pdens σ ρ t, I·k) ≠ 0` for real `k ≠ 0`,
  `t ∈ (0,1]`, directly from the existing `pyhs_mixture_no_spinodal` at density `t·ρ`.  (HS has no
  spinodal at any density ⇒ the physical path is singularity-free.)  Depends only on the existing
  physics axiom — no new axiom.

**Remaining subtlety found — run the homotopy on the ENTIRE `detF`, not `W`.**  `W(P₀, 0) = 0` (the
dilute base `W = z⁶` has a zero at the origin), which breaks `hreal` at `z = 0`; the scalar track
avoided this by using `1−Q̂` (entire, nonzero at origin).  The matrix analog is `detF` itself, which is
**entire** — each `q0_entry_c` has a *removable* singularity at `s = 0` (`q0_entry_c_differentiableAt`
only records `s ≠ 0`).  So completing the assembly needs: (i) `detF` entire; (ii) the `z = 0` value
`detF(Pdens t, 0) = det Q̂₀(0) ≠ 0`; (iii) a uniform-in-`t` escape radius.  All three are transcription,
**not** new axioms.

**`detF` entire DONE (2026-07-28, `MixtureDetEntire.lean`) — axiom-clean.**  The Lean `detF` is
`0/0`-junk at `s = 0` but analytic away from `0` (`Q0_det_c_differentiableAt`) with a finite removable
limit (`detC_tendsto`, from the already-proved `q0_entry_c_tendsto`: `φ₁(0)=−σ²/2`, `φ₂(0)=σ³/6`).
* `detF_update_differentiable` — `Function.update detF 0 c` is **entire** for the limit `c`, by
  Riemann's removable-singularity theorem `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
  (differentiable on the punctured `𝓝` since `update = detF` off `0`; `ContinuousAt 0` via
  `nhdsNE_sup_pure` + the limit).
* `detF_tendsto` / `detF_ext_differentiable` — package the limit with the entire extension.
This is the entire object the homotopy runs on (`hholo`), the matrix analog of the scalar `1−Q̂`.
**Dilute base of the extension DONE (2026-07-28) — `hbase` for `detF_ext`.**  `Pdens_zero_rr`
(`rr(Pdens σ ρ 0) = 0`, since `rhoGeoPhys(0·ρ) = √0 = 0`) + `Q0_mat_c_rho_geo_zero`
(`Q0_mat_c` at zero coupling `= I`) ⇒ `detF_Pdens_zero` (`detF(Pdens σ ρ 0) ≡ 1`, no `0/0` issue) and
`detF_ext_Pdens_zero` (`update (detF(Pdens 0)) 0 1 ≡ 1`, nonzero everywhere incl. `z = 0`).
Axiom-clean.

**Precise remaining accounting for the concrete pole-freeness theorem** (all no-new-axiom):
* **`hholo`** = `detF_ext_differentiable` ✓; **`hbase`** = `detF_ext_Pdens_zero` ✓;
  **`hreal` (`k ≠ 0`)** = `detF_Pdens_ne_zero` ✓ (existing no-spinodal); **`hbound`** = lift
  `exists_escape_radius` to `detF_ext` in `z`-form ✓ (mechanical).
* **`hreal` at `z = 0` — the origin value `detF_ext(Pdens t, 0) = c_t ≠ 0`** — is the genuine remaining
  physical sub-fact, characterised precisely (2026-07-28):
  - `c_t` = `det` of the removable **moment matrix** `Mᵢⱼ = δᵢⱼ − ρ_geoᵢⱼ(Qpᵢⱼ(−σᵢ²/2) + Qppᵢⱼ(σᵢ³/6))`
    (the `q0_entry_c_tendsto` values) — **not** the Lean `0/0`-junk value `1`; physically it is the
    `k = 0` structure factor = **compressibility**.
  - **`pyhs_mixture_no_spinodal` does not cover it** (it is stated with `k ≠ 0`, precisely to dodge the
    `s = 0` removable value); `Q0_moment_det_pos` gives `det > 0` for real `z > 0`, hence only
    `c_t = lim_{z→0⁺} ≥ 0`, **not** strict.
  - **`c_t ≠ 0` is NOT derivable from the axis non-vanishing** (`detF ≠ 0` on the real-positive axis
    via `Q0_mat_phys_isUnit_det`, and on the imaginary axis via no-spinodal): if `c_t = 0` then the
    entire `detF_ext ~ a·zⁿ` near `0`, which is consistent with non-vanishing on **both** axes
    (`a·zⁿ > 0` for `z > 0`; `a·iⁿyⁿ ≠ 0`) — no contradiction.  So `c_t > 0` is genuine `k = 0`
    compressibility content.
  - **✅ CLOSED (2026-07-28, `Q0MomentGeOne.lean` + `MixtureDetOrigin.lean`) — AXIOM-CLEAN, no physics
    axiom.**  Route 1 (explicit moment determinant): `moment_key` gives not just `det > 0` but
    `ad − bc ≥ a + d`, hence `det = 1 − (a+d) + (ad−bc) ≥ 1` (`Q0_moment_det_ge_one`,
    `Q0_mat_phys_det_ge_one`) — a **strict-with-margin** bound.  It survives the `z → 0` limit: at real
    `z > 0`, `detF(Pdens σ ρ t, z) = det Q0_mat_phys(z, σ, t·ρ) ≥ 1` (`detF_Pdens_ofReal` +
    `Q0_mat_phys_det_ge_one`), so `Re(c) = lim_{z→0⁺} det ≥ 1 > 0` (`ge_of_tendsto`), hence `c ≠ 0`
    (`detF_Pdens_origin_ne_zero`; `hreal` at `z=0` = `detF_ext_Pdens_origin_ne_zero`).  `#print axioms`
    = standard three — the `k = 0` compressibility positivity is **proved**, not a companion axiom
    (`moment_key` is proved algebra; `pyhs_mixture_no_spinodal` is not even used).  Bonus: real
    removable values `p1 → −σ²/2`, `p2 → σ³/6` (`p1_tendsto_zero_nhds`, `p2_tendsto_zero_nhds`).
* **`hcont`** (joint continuity of the family extension) and **uniform-`t` escape radius**
  (`K`-constants `rr`-monotone) — mechanical.

**Concrete pole-freeness theorem ASSEMBLED (2026-07-28, `MixtureDetOrigin.lean`) — no new axiom.**
`mixtureDet_pole_free_of_regular` : for the physical mixture `(σ, ρ)`, `detF(Pdens σ ρ 1, I·z) ≠ 0`
throughout the open lower half `z`-plane — the LHP pole-freeness of `det Q̂₀`.  It runs the density
homotopy on the entire removable extension via `zeroFree_lowerHalfPlane_of_homotopy`, discharging
**every** pointwise input from the proved lemmas: `hholo` (`detF_update_differentiable`), `hbase`
(dilute `detF ≡ 1`), `hreal` for `k ≠ 0` (`Pdens_detF_imag_ne_zero`, no-spinodal) and `k = 0`
(`cf_ne_zero`, the axiom-clean compressibility), `hbound` (uniform escape).  `#print axioms` = the two
**existing** axioms only (`zeroFree_lowerHalfPlane_of_homotopy` + `pyhs_mixture_no_spinodal`) — no new
axiom.  Conditional only on the two **family-regularity** hypotheses `hcont` (joint continuity of the
`(t,z) ↦ detF_ext(Pdens t)(I·z)` family) and `hRunif` (uniform-in-`t` escape radius) — both purely
mechanical (continuity of a parametrised analytic family; `K`-bound over the compact `[0,1]`), the
last remainder.

**Progress on the remainder (2026-07-28).**  `detF_ne_zero_of_Kbound` (`MixtureDetEscape.lean`) — the
**uniform escape mechanism** for `hRunif`: from a common bound `K_Mc,K₀,μ,K₁,K₀₁ ≤ B`, `detF(P,s) ≠ 0`
for `Re s ≥ 0`, `‖s‖ ≥ max(1,5B+1)` (axiom-clean).  Building blocks for the uniform `B`:
`vacMix`/`xi2` continuous in `t` on `[0,1]` (`fun_prop`), `vac > 0` there (`etaMix(t·ρ)=t·etaMix(ρ)<1`).
**`hRunif` DONE (2026-07-29, `MixtureDetUniform.lean`) — axiom-clean.**  `hRunif_Pdens` : a single
`R = max(1, 5B+1)` works for all `t ∈ [0,1]`.  The five `K`-constants of `Pdens t` are continuous in
`t` (`Ksum_cont` — `vacMix`/`xi2` continuous via `fun_prop`, `vac(t)=1−t·η(ρ)>0`, so `Q0phys`/`Qppphys`
= `…/vac` continuous by `ContinuousOn.div`, then `cB`/`K`s are polynomials in the fields), hence their
sum is bounded on the compact `[0,1]` (`isCompact_Icc.exists_bound_of_continuousOn`); `Pdens_Phys`
(physicality for `t > 0`, from `Q0phys_pos`/`Qppphys_pos`/`rhoGeoPhys_pos`) + `detF_ne_zero_of_Kbound`
close it (`t = 0` is dilute `detF ≡ 1`).

**`hcont` DONE ⇒ UNCONDITIONAL theorem (2026-07-29, `MixtureDetHcont.lean`).**  The `0/0`-junk of
`detF` at `s = 0` comes only from `φ₁,φ₂ = num/sⁿ`, which depend on `s`/`σ` **not** on `t`.  Replacing
them with continuous removable extensions `psi1`,`psi2` (`psi{1,2}_continuous` via `phi{1,2}_tendsto` +
`nhdsNE_sup_pure`) gives the `ψ`-form det `detFpsi` — **manifestly jointly continuous**
(`detFpsi_continuous`; fields of `Pdens t` continuous in `t`, `ψ` continuous in `s`) and `= detF` away
from `0` (`detFpsi_eq_detF`).  Since `cf t = detFpsi(Pdens t) 0` (`cf_eq_detFpsi_zero`), the
update-based `detF_ext = detFpsi`, so `hcont` follows by `ContinuousOn.congr` (`hcont_Pdens`).  No
parametrised removable-singularity theorem was needed — the `t`-independence of `φ` sidesteps it.

**`mixtureDet_pole_free`** : `detF(Pdens σ ρ 1, I·z) ≠ 0` on the open lower half `z`-plane for every
physical `N=2` hard-sphere mixture — **fully unconditional**.  `hcont`/`hRunif`/`cf` all discharged;
`#print axioms` = the two **existing** axioms only (`zeroFree_lowerHalfPlane_of_homotopy` +
`pyhs_mixture_no_spinodal`).  The matrix `pole-in-LHP ⇔ decay` obstacle (`OZFIX.17`) is fully resolved
for `N=2` — no new axiom, everything else proved (including the axiom-clean `k=0` compressibility).

**Answer to "does the matrix track need a NEW math axiom?" — NO.**  Pole-freeness reuses the existing
`zeroFree_lowerHalfPlane_of_homotopy` (`matDet_zeroFree_lowerHalfPlane_of_homotopy`); `hreal` is the
existing `pyhs_mixture_no_spinodal`; `hbase` = `det Q̂₀(0)=1` (MML `Q0_mat_c_at_zero`); `hbound`'s
mechanism is now proved (this file). The matrix Baxter factorization is **explicit**
(`Q0_mat_phys_eq_one_sub_mul`, proved) — no abstract Wiener–Hopf existence gap. What remains
(`hfact`/`hbridge`/`hclaimA` for the concrete mixture, the poly asymptotics, the homotopy scaffold,
`s=0` pole) is **transcription work, not new axioms** — the matrix track can reach the scalar track's
standard modulo only the *existing* kept math axioms.

**Depends on.** Scalar `baxterPsi_ozstar`, `rho_baxterK_eq_q0_self_conv`, `baxterK`, `q0_poly`
(`BaxterOzStar.lean`/`BaxterRenewal.lean`); `radial3d_conv` (`RadialLaplace.lean`).

**Lean.** `HSMixture/MixtureOzStar.lean` (ns `FMSA.MixtureOzStar`): `matRadialConv`,
`matRadialConv_apply`, `matRadialConv_fin_one`, `MatOZStar`, `matOZStar_entry`,
`matOZStar_fin_one_of_scalar`; `matSelfConv`, `matSelfConv_apply`, `matSelfConv_fin_one`,
`MatBaxterFactorization`, `matBaxterFactorization_fin_one_of_scalar`; `matShellConv`,
`matShellConv_apply`, `matRadialConv_eq_matShellConv`, `matShellBridge_fin_one_of_scalar`,
`matRadialConv_eq_matShellConv_of_shellKernel`; `matBaxterPsi`, `matBaxterPsi_core`/`_outer`/`_reflect`,
`MatRenewalEq`, `matBaxterPsi_fin_one_of_scalar`, `matRenewalEq_fin_one_of_scalar`;
`matShellConv_kdef_split`, `matOzStar_of_shellClaims` — all axiom-clean.  `HSMixture/MixtureOzStarIntegrable.lean`
discharges every integral side-condition of the assembly: the reindex's nine
(`matDblConv_reindex_of_regular`) and the assembly's two shell conditions
(`mulCont_psi_intervalIntegrable`, `shellQ_intervalIntegrable`, `shellS_intervalIntegrable`,
capstone `matOzStar_of_regular`) — all axiom-clean.
`matVolterra_convolution_existsUnique`. Plus `HardSphere/ShellKernel.lean` (`shellKernel`,
`radial3d_conv_eq_shellKernel`, `shellKernel_c_HS`) and `Analysis/VolterraBanach.lean` (the Banach
`MA.10`: `volterraTE`, `volterra_iterate_boundE`, `volterra_existsUniqueE`,
`volterra_convolution_existsUniqueE`). Full build green.

**Status.** ◑ **STARTED (2026-07-24), axiom-clean foundation — four layers, `Ψouter` constructed.** (1) The OZ★ target
shape (`MatOZStar`, entrywise reduction to scalar `radial3d_conv`); (2) its real-space factorization
foundation (`MatBaxterFactorization`, `matSelfConv`); (3) the shell-conv = K-conv bridge
(`matRadialConv_eq_matShellConv`, general-`c` via `ShellKernel.lean`) connecting (1) to (2); (4) the
matrix `baxterPsi` construction shape + renewal equation (`matBaxterPsi`, `MatRenewalEq`). Each has an
`n = 1` bridge to a proved scalar theorem (`baxterPsi_ozstar`, `rho_baxterK_eq_q0_self_conv`,
`radial3d_conv_eq_baxterK_shell`, `baxterPsi_core`/`baxterPsiOuter_spec`). The
general-`N` analytic construction (matrix `baxterPsi`, `OZFIX.18` F-part + `OZFIX.20` reindex,
renewal + integrability, modulo the matrix decay axiom) is the remaining research-scale work — the
last unbuilt piece of MML.8. **The general-`c` shell identity (`radial3d_conv_eq_shellKernel`,
`ShellKernel.lean`) is now proved**, so the shell-bridge layer is complete for arbitrary mixture
entries, not just `c_HS`.  **UPDATE 2026-07-31 — the assembly integrability and the `Ψouter`
existence/renewal are now BUILT** (`matOzStar_of_regular`; `matBaxterPsiOuter_matRenewalEq` via the
Banach global Volterra chain `VolterraBanach.volterraGlobalE`), so what remains of MML.8's construction
narrows to: (a) the concrete real-space matrix Baxter data `Q, F` (momentum→real-space `Q0_mat_c`),
and (b) the **matrix seed identity** (analog of `baxter_psi_conv_eq_phi`, `MatRenewalEq` → OZ★ shell
form).  See the "`Ψouter` CONSTRUCTED" note above.

---

## Group MZERO — Mixture `det(Q̂₀)` Zero Family (HS-pole existence)

**Scope.** `det(Q̂₀(s))` has **infinitely many** complex zeros `s_k` (the "HS poles" whose
residues feed MML.4/MML.8's Mittag-Leffler series). **MZERO.1** is the foundational statement;
**MZERO.2–MZERO.11** decompose it across two independent routes (Banach contraction / Jensen
zero-counting), either of which alone closes MZERO.1. The route overview precedes the numbered
tasks below.

**✅ GROUP CLOSED — audited 2026-07-24, no open item.** The audit was mechanical rather than a
re-read of recorded statuses: every named deliverable of MZERO.1–MZERO.11 was `#print axioms`-checked
and returns the standard three only (`detC_zeros_infinite_unconditional`, `chordPoleFamily_detC_exists`,
`chord_zero_exists_of_bounds`, `chordPhi_fixedPt_iff`, `chordPhi_lipschitzOnWith`,
`mapsTo_closedBall_of_lipschitzOnWith_of_dist_le`, `Q0_det_c_zeros_infinite`,
`Q0_det_c_pole_family_growth`, `det_meromorphicOn`, `det_divisor_nonneg`, `detC_jensen_log_bound`,
`detBoundaryGrowth_of_linear`, `detC_boundaryGrowth_iff_infinite_zeros`,
`detC_zeros_infinite_of_boundaryGrowth`). ⚠ **Namespace note for future audits:** the MZERO.3/4/6
Banach machinery lives in `FMSA.BanachPoleFamily` and MZERO.10's growth predicate in
`FMSA.BoundaryGrowth` — **not** in `FMSA.MixtureHSPoles`, because the generic layer was migrated to
`Analysis/` (MRS.9b). Looking them up under the mixture namespace reports "unknown constant" and
looks like a missing proof.

#### Re-audit 2026-07-31 — the 07-24 audit still holds, plus three findings

**Re-measured, not re-read.** All 20 MZERO constants (the 14 above plus `Q0_det_c_tendsto_one`,
`Q0_det_c_not_identically_zero`, `Q0_det_c_differentiableAt`, `detC_boundaryGrowth_of_infinite_zeros`,
`infinite_zeros_of_growth`, `detC_zeros_infinite_of_growth`) `#print axioms` = **standard three**.
Nothing moved under MZERO's feet in the `be70ac4` "General N" rewrite or the MRS.9d file shuffle.

**1. Split the group's status honestly: the machinery is load-bearing, the headline is
consumer-less.** These are different facts and the group note ran them together.

| MZERO artifact | Lean consumers outside its own file |
|---|---|
| **`detF_family_magnitude_bound`** (the MZERO.5 magnitude/growth work) | **`MixtureMLBound.lean` (MML.5), `MixtureInnerDCF.lean` (MML.8), `MixtureRDFPoleData.lean` (MML.11)** — genuinely load-bearing |
| **`ChordPoleFamily` / `zeros_infinite_of_chordPoleFamily`** (MZERO.3/4/6/7's abstraction) | **`HardSphere/BaxterChordFamily.lean`, `HardSphere/BaxterPoles.lean`** — the **scalar** track reuses it, so the `Analysis/` migration paid off outside the mixture |
| **`detC_zeros_infinite_unconditional`, `detF_zeros_infinite`, `Q0_det_c_zeros_infinite`** (MZERO.1, Route A) | **none** — every hit is a docstring |
| **`detC_zeros_infinite_of_boundaryGrowth`, `detC_zeros_infinite_of_growth`** (MZERO.11, Route B) | **none** — every hit is a docstring |

So "infinitely many HS poles" is currently **proved and unconsumed**. That is *expected*, not a
defect: **MRS.3** removed the DCF consumer outright (the `det Q̂₀` zeros never enter `Ĉ₁`), and the
only remaining consumer is **MML.8**, which is open. Worth stating because this project treats
consumer-less statements as a hazard class (cf. MRS.0b, written precisely to test a consumer-less
axiom; four axioms here were false *as stated* and every one was caught by a proof attempt, never by
`#print axioms`). MZERO's headline has had no such test — but unlike an axiom it is *proved*, so the
exposure is only to a mis-*statement*, and finding 3 below is the check that closes that.

**2. ⚠ Naming trap: `MixParams.Phys` does NOT mean "the physical Lebowitz coefficients".** Its own
docstring is accurate — "ordered positive diameters and entrywise positive matrices" — but
`chordPoleFamily_detF_exists P hP` with `hP : P.Phys` reads, at a glance, as though MZERO had been
instantiated at the actual PY mixture. It has not: `rr`, `Qp`, `Qpp` are **free** matrices
constrained only by positivity. `Q0phys` / `Qppphys` / `rhoGeoPhys` **appear nowhere** in
`MixtureChordFamily.lean`, `MixtureHSZeros.lean`, or `MixtureHSCounting.lean`.

**3. The physical bridge is available, favourable, and unwritten — this is the one actionable item.**
Reading the definitions in `MatrixQ0.lean`, the Lebowitz coefficients are *manifestly* entrywise
positive whenever `vac = 1−η > 0`, `σ > 0`, `ρ ≥ 0`:

```
Q0phys  = (2π/vac)·( (σᵢ+σⱼ)/2 + π·ξ₂·σᵢσⱼ/(4·vac) )     every summand > 0
Qppphys = (2π/vac)·( 1 + π·ξ₂·σⱼ/(2·vac) )                every summand > 0
rhoGeo  = √(ρᵢρⱼ) > 0,      ξ₂ = Σ ρᵢσᵢ² ≥ 0
```

Confirmed numerically at the reference mixture (σ=[1,2], x=[0.25,0.75], ρ*=0.139 ⇒ η=0.4549,
vac=0.5451): `min Q0phys = 19.03`, `min Qppphys = 26.53`, `min rhoGeo = 0.0348`, `0<σ₀<σ₁` — so
**`MixParams.Phys` holds for the physical mixture** and `detC_zeros_infinite_unconditional` applies
to it. End-to-end non-vacuity re-checked by locating the zeros themselves at those *physical*
coefficients (Newton from MZERO.5's anchor `i·2πn/σ₁`): 8 distinct zeros,
`s = −0.417+3.389i, −0.946+6.291i, …, −2.362+25.075i`, `|detC| ≤ 3.4e-15`, mean `Im` spacing
**3.098** against the predicted `2π/σ₁ = 3.1416` — reproducing MZERO.2's recorded "Δ Im ≈ π" GO gate.

### ✅ MZERO.12 — the physical instantiation, WRITTEN (2026-07-31)

**`LeanCode/HSMixture/MixtureZerosPhys.lean`** (ns `FMSA.MixtureHSPoles`), axiom-clean, full build
green (8716 jobs). A **new file**, so `MixtureChordFamily.lean` and its neighbours — the MML.8
working set — are untouched.

| theorem | statement |
|---|---|
| `Pdens_one` | `Pdens sigma rho 1` **is** the physical pack (`1 • rho = rho`) — the bridge between the homotopy packaging and the plain coefficients |
| **`detC_zeros_infinite_phys`** | `0 < σᵢ`, `σ₀ < σ₁`, `0 < ρᵢ`, `η < 1` ⇒ `{s : ℂ \| detC ![σ₀,σ₁] (↑rhoGeoPhys) (↑Q0phys) (↑Qppphys) s = 0}.Infinite` |
| **`Q0_mat_c_phys_det_zeros_infinite`** | the same on the matrix itself — `(Q0_mat_c s σ ↑rhoGeoPhys ↑Q0phys ↑Qppphys).det`, i.e. **definitionally MRS.7's `Qphys`**. The form a consumer wants |
| `example` (non-vacuity) | the four hypotheses hold simultaneously at the project's reference mixture `σ=[1,2]`, `ρ=[0.03475,0.10425]` (`η ≈ 0.4549`); the `η < 1` step needs only `π < 4` |

⚠ **It proves nothing new — and the reason is the finding.** The three `MixParams.Phys` positivity
obligations were **already theorems**: `Q0phys_pos`, `Qppphys_pos`, `rhoGeoPhys_pos`, and even the
packaged **`Pdens_Phys`**, all in `MixtureDetUniform.lean`. They were built for the **density
homotopy** of the physics-axiom-retirement track (`MatrixDetPoleFree` / `MixtureDetHomotopyPhys`),
whose consumer is `hRunif_Pdens` — and **nobody ever pointed them at `detF_zeros_infinite`**. So the
whole corollary is `Pdens_Phys … 1` plus `1 • rho = rho`. My first draft re-proved all three from
scratch and the build caught it as a name clash (`environment already contains
'FMSA.MixtureHSPoles.Qppphys_pos'`) — `feedback_stale_blockers` again, in its purest form: the
missing fact was already in the tree, merely never exported to the group that needed it. **Two
tracks had each done half of this and neither knew.**

Layering respected (`HSMixture/` may not import `YukawaDCF/`), so the statement stops at the
`Q0_mat_c` level; an `FMSA.MRS`-side restatement in terms of the literal `Qphys` alias is a one-liner
whenever someone wants it.

---

### ⚠ Layering violation in `MixtureRDFUniqueness.lean` — found and repaired 2026-07-31

Checking that layering claim turned up a real back-edge, present since `c8efdc4`:
**`HSMixture/MixtureRDFUniqueness.lean` imported `YukawaOZMix/MixtureRDFStructureFactor.lean`**, so
`CONVENTIONS.md`'s first self-check grep had been non-empty. All three greps print nothing again.

**The dependency was one declaration out of 26** — `det_eq_of_wienerHopf_factorization`, i.e.
`T₀ = Qp·Qmᵀ ⇒ det T₀ = det Qp · det Qm`, whose proof is `Matrix.det_mul` then
`Matrix.det_transpose`. No Baxter, Yukawa or mixture content whatsoever; it was in `YukawaDCF/`
only because MML.9 happened to be where it was first needed.

**Repair (not a file move).** The generic core is now
**`Analysis/MatrixIdentity.det_mul_transpose`** — `(A * Bᵀ).det = A.det * B.det`, stated without the
factorization hypothesis so it is a plain rewrite rule, generic in ring and index type. Both sides
cite it: `MixtureRDFUniqueness.matStructureFactor_isUnit_of_det_ne_zero` now does
`rw [Matrix.isUnit_iff_isUnit_det, hfact, det_mul_transpose]` and dropped the `YukawaDCF` import;
`MixtureRDF.det_eq_of_wienerHopf_factorization` keeps its name, its physics-facing docstring and all
four of its in-file uses, and became a one-line consequence.

**Moving the file up would have been wrong.** `MixtureRDFUniqueness` is matrix OZ★ uniqueness — a
**hard-sphere** statement (MML.9 itself established that the residual collapse content is `Ĥ₀`, the
Yukawa factor `Ĉ₁` between the two `S₀`'s being pole-free). Relocating it to `YukawaDCF/` would have
encoded the false claim that it needs a Yukawa tail. Push the generic lemma **down**; do not move the
specific file **up**.

**Ledger unchanged** — verified, not assumed: `#print axioms` after the repair gives
`det_mul_transpose`, `det_eq_of_wienerHopf_factorization`,
`matStructureFactor_isUnit_of_det_ne_zero`, `rdf_entry_star_eq`, `rdf_entry_double_pole` = standard
three, and **`matOzStar_unique` still carries exactly `FMSA.matRadialShell_bounded_injective`** and
nothing new. Full build green (8716 jobs).

---

### Task MZERO.1 — Infinitely many HS poles for N=2

**Statement.** `det(Q0_mat_c s) = 0` has infinitely many distinct complex solutions.

**Strategy.** The 2×2 determinant det(Q̂₀(s)) is an entire function of s (each entry of
Q̂₀ is entire by Y1.1, determinant of entire matrix is entire). It is not identically
zero (det → 1 as s → ∞ by Y1.1's entry formulas). For a non-constant entire function,
the zeros are either finite in number or form a discrete infinite sequence.

The non-constancy + "not eventually large" argument:
- As Re(s) → +∞: the off-diagonal entries Q̂₀₀₁, Q̂₀₁₀ → 0 (GA.2 mechanism), so
  det(Q̂₀) → Q̂₀₀₀·Q̂₀₁₁ → 1 (bounded away from 0 for large real s).
- On the imaginary axis: behavior like N=1 `Qhat_complex` (periodic structure from
  e^{−is·σ} terms); Rouché applied on large circles shows zeros accumulate.

Alternatively, extend POLE.3's Banach-contraction strategy to det(Q̂₀):
- Parameterize zeros of det(Q̂₀(s)) by solving `s = F_n(s)` for a family of maps F_n
  derived from the quasi-polynomial structure of det(Q̂₀).
- Show the contraction bound holds for each n (numerically: run the analog of POLE.2
  for the N=2 det).

**Depends on.** MML.1 (det formula), Y1.1 (entries entire), M.4 (det ≠ 0 on real axis),
POLE.3 proof strategy.
**File.** `HSMixture/MixtureHSZeros.lean` (foundation) / `MixtureHSPoles.lean`.

**Foundation — DONE (2026-07-15), axiom-clean, `HSMixture/MixtureHSZeros.lean`** (namespace
`FMSA.MixtureHSPoles`).  The non-constancy every infinitely-many-zeros argument starts from:
- `Q0_det_c_tendsto_one` — `det(Q0_mat_c (t:ℂ) …) → 1` as real `t → +∞` (via `Matrix.det_fin_two`):
  diagonal Baxter entries → 1 (`q0_diag_c_tendsto_one`) and the off-diagonal *product* → 0
  (`q0_offdiag_prod_tendsto_zero` — the two `λ`-shifts are opposite, `λ_{01}+λ_{10}=0`, so the
  exponentials cancel and each Baxter bracket `φ₁,φ₂ → 0`).
- `Q0_mat_c_at_zero` (`Q0_mat_c 0 = I`, Lean `0/0=0` value) + `Q0_det_c_not_identically_zero`
  (`∃ s, det ≠ 0`).
- `q0_entry_c_differentiableAt` / `Q0_det_c_differentiableAt` — **holomorphy away from `s=0`**: each
  Baxter entry, and (for `N=2`, via `Matrix.det_fin_two`) `det(Q̂₀)`, is `DifferentiableAt ℂ` at every
  `s₀ ≠ 0` (`fun_prop (disch := assumption)` on the `s^{2,3} ≠ 0` div side-goals).  With the
  non-constancy above, this is the holomorphic-and-non-constant setup a zero-counting argument needs.
- Helpers: `cofReal_inv_tendsto_zero`, `cexp_neg_mul_tendsto_zero`, `phi1c_tendsto`/`phi2c_tendsto`,
  `bracket_tendsto_zero`, `offdiag_prod_eq`.
- *Note:* this file imports only `Q0Complex` (uses `Matrix.det_fin_two` directly, not MML.1's
  `Q0_det_fin_two`), so it builds independently of the currently-in-progress `BaxterResidue` import
  that `MixtureHSPoles` (MML.1/MML.2) transitively pulls.

**Status.** ◑ **foundation DONE** (non-constancy / `det → 1`); the full *infinitely many zeros*
(zero family) is decomposed into **MZERO.2–MZERO.11** below.

---

### MZERO.2–MZERO.11 — MZERO.1 zero-family decomposition (routes overview)

The "`det(Q̂₀(s))` has infinitely many complex zeros" core (= MZERO.1), split into numbered tasks
MZERO.2–MZERO.11 across **two independent routes** (either alone closes MZERO.1). Foundation done
(`Q0_det_c_tendsto_one` non-constancy + `Q0_det_c_differentiableAt` holomorphy off `s=0`,
`MixtureHSZeros.lean`).

- **Route A — Banach contraction (MZERO.2–MZERO.7)**, POLE.3-style, mirrors `BaxterPoles.lean`. ✓ DONE
  (2026-07-15), axiom-clean & `sorry`-free, **conditional on the MZERO.5 magnitude bounds**. **Unified with
  POLE.3:** the generic chord engine + shared **`ChordPoleFamily F`** predicate +
  `zeros_infinite_of_chordPoleFamily` live in `Analysis/BanachPoleFamily.lean`; `Q0_det_c_zeros_infinite`
  (mixture) and `G_baxter_zeros_infinite_of_chordPoleFamily` (Baxter) both consume it ⇒ **MZERO.5 ≡ POLE.3's
  open `hstep`** (one asymptotic-family lemma closes both). `#print axioms` on all three →
  `[propext, Classical.choice, Quot.sound]`.
- **Route B — Rouché / zero-counting (MZERO.8–MZERO.11)**. *Mathlib has no ready Rouché or argument principle,
  but zero-counting routes through Jensen's formula + the divisor:* `MeromorphicOn.circleAverage_log_norm`
  (`Analysis/Complex/JensenFormula.lean`) gives `circleAverage (log‖f·‖) c R = ∑ᶠ u, divisor f
  (closedBall c |R|) u · log(R‖c−u‖⁻¹) + … + log‖trailingCoeff‖`, and `divisor f (closedBall c R)` counts
  zeros for analytic `f` (no poles). *Contradiction route:* finitely many zeros ⇒ `divisor det
  (closedBall 0 R)` stabilizes ⇒ RHS ~ `(const)·log R`; but the boundary average grows `≥ c·R` (the
  `e^{−sσ}` growth) ⇒ `R ≫ log R` ⇒ contradiction ⇒ ∞ many zeros. MZERO.8 done, MZERO.10/MZERO.11 structural
  capstones done, MZERO.9 `divisor ≥ 0` unconditional, **`hJensen` NOW PROVED** (2026-07-16,
  `detC_jensen_log_bound`) — so **Route B is fully closed modulo only MZERO.10** (`DetBoundaryGrowth`),
  the `e^{−sσ}` boundary-growth input (`detC_zeros_infinite_of_boundaryGrowth`).

---

### Task MZERO.2 — feasibility gate (Python, POLE.2 analog: GO/NO-GO)

*(Route A.)* Feasibility check. ✓ **DONE — GO** (`verify_mixture_hs_poles.py`, σ=[1,2], ρ=[0.2,0.05],
η=0.314). Found a **quasi-periodic zero family** (Δ Im ≈ π, 22 zeros up to Im≈239, `Re(s_n)` growing
~`log(Im)`), and a **chord-Newton** map `g(s)=s−F(s)/F′(s1)` on a disk `r=0.15` satisfies **both** Banach
conditions for **all** of them with margin: Lipschitz `K ≈ 0.30–0.35` — critically **uniform** across the
whole family (does *not* drift to 1 as `n→∞`, unlike BAXTER's plain-Newton concern), self-map gap
~`1e-40 ≪ r(1−K)≈0.10`. ⇒ the Banach path (MZERO.3–MZERO.7) is viable with **chord-Newton**; each zero is
simple (`F′≠0`). Also confirms the quasi-periodic structure Route B's boundary-growth estimate (MZERO.10)
relies on.

---

### Task MZERO.3 — generic chord-Newton Banach existence wrapper

*(Route A, Lean.)* `chord_zero_exists_of_bounds (F : ℂ → ℂ) …` (Lipschitz self-map `chordPhi F Fp1` of a
`Metric.closedBall` ⇒ `∃ s ∈ ball, F s = 0`), from `ContractingWith.exists_fixedPoint'`. Map-independent.
✓ **DONE (axiom-clean)**, shared `Analysis/BanachPoleFamily.lean`. Cleaner than
`G_baxter_pole_exists_of_bounds`: the `fp ⟹ zero` direction folds in (no `hFixedImpliesRoot` hyp),
because chord-Newton's `fp ⟺ F = 0` is unconditional.

---

### Task MZERO.4 — chord-Newton map + fixed-point ⟺ zero

*(Route A, Lean.)* `chordPhi F Fp1 s := s − F s / Fp1` + `chordPhi_fixedPt_iff` (`IsFixedPt ⟺ F s = 0`,
given `Fp1 ≠ 0`). ✓ **DONE (axiom-clean).** One-line (`sub_eq_self` + `div_eq_zero_iff`); **simpler than
the log-map** `baxterPhi_fixedPt_implies_zero` (no `Complex.log`, `Complex.exp_log`, `2π`-periodicity, or
branch-safety) — the payoff of the MZERO.2 chord-Newton choice.

---

### Task MZERO.5 — magnitude bounds (`ChordPoleFamily det_c`) — the residual gap

*(Route A, the one remaining piece — now UNIFIED with POLE.3.)* Construct a `ChordPoleFamily det_c`: the
chord-Lipschitz bound `∀ s ∈ ball, ‖1 − det′(s)/Fp1‖ ≤ K` (`K<1`) + the good-guess
`hstep : ‖det(s₁)/Fp1‖ ≤ r(1−K)` + the asymptotic pole locations. ◑ Two things pin it down:
- **Shared predicate** `ChordPoleFamily F` (`Analysis/BanachPoleFamily.lean`) — the *same* obligation
  `G_baxter` (POLE.3) carries; `Q0_det_c_zeros_infinite` and `G_baxter_zeros_infinite_of_chordPoleFamily`
  both consume it. So MZERO.5 ≡ POLE.3-`hstep`, and one asymptotic-family lemma closes **both**. (**POLE.5 is
  DONE** — the `n^{1−2r/σ}` summability bound; its magnitude machinery
  `abs_exp_neg_ikn_sigma_*`/`G_baxter_deriv_lower_bound_of_zero` is the reusable *technique* for the
  mixture bounds, transposed to 2 frequencies.)
- **MZERO.5a bridge** `detC_lam_free` (`MixtureHSZeros.lean`, ✓ DONE axiom-clean) — `det_c` has **no
  `e^{±λs}` blow-up** (off-diag shifts cancel), so `det_c = (diag₀)(diag₁) − ρ₀₁ρ₁₀(bracket₀)(bracket₁)`
  is a **2-frequency exp-polynomial in the same Baxter brackets as `G_baxter`** — the structural reason
  the two share the class.

What remains: the *quantitative* `‖det″‖`-upper/`‖det′‖`-lower bounds + the asymptotic Im-quantized zero
locations (the 2-freq analog of POLE.5's `Im(k_n)=Θ(ln n)`). `det` differentiability on the disk **is**
proved (`Q0_det_c_differentiableAt`); no branch-safety (unlike BaxterPoles' `R_mem_slitPlane`).


**✅ 2026-07-17 — MZERO.5 CLOSED (⇒ MZERO.1 CLOSED).** `HSMixture/MixtureChordFamily.lean`
(3497 lines, axiom-clean, no `sorry`, full `lake build` green 8646 jobs). Headline:

```
detC_zeros_infinite_unconditional {sig0 sig1 : ℝ} (h0 : 0 < sig0) (h01 : sig0 < sig1)
    {rr Qp Qpp : Fin 2 → Fin 2 → ℝ} (hrr : ∀ i j, 0 < rr i j) (hQp : ∀ i j, 0 < Qp i j)
    (hQpp : ∀ i j, 0 < Qpp i j) :
    {s : ℂ | detC ![sig0, sig1] (fun i j => (rr i j : ℂ)) (fun i j => (Qp i j : ℂ))
      (fun i j => (Qpp i j : ℂ)) s = 0}.Infinite
```

— **hypotheses are parameter positivity/ordering ONLY**; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`. Also `chordPoleFamily_detC_exists` (the
`ChordPoleFamily detC` value the shared engine consumes), plus the `MixParams`-form siblings
`chordPoleFamily_detF_exists` / `detF_zeros_infinite` / `chord_conditions_eventually`
(`MixParams.detF P = detC ![P.sig0,P.sig1] … ` is `rfl`). This **retires the `hbound`/`hstep`
hypotheses of `Q0_det_c_zeros_infinite`** — that conditional theorem is superseded for the
existence question (kept as the ∀-parameterised layer). **Route A is now the completed genuine
route** (Route B remains a reformulation of MZERO.1, per `detC_boundaryGrowth_iff_infinite_zeros`).

Construction (2-freq transposition of `POLE.9`'s template): parameters packed as `MixParams` +
`Phys`; the **monomial polynomialisation** `Wfun P s = s⁶·detC s = McNum + M0Num·e^{−sσ₀} +
M1Num·e^{−sσ₁} + M01Num·e^{−s(σ₀+σ₁)}` (from `detC_lam_free`, clearing `s⁶`; all four `*Num`
explicit polynomials); anchor `aₙ = i·2πn/σ₁` with **exact phase kill** of the σ₁-frequency;
the **derived guess** `sGuess P n = −(1/σ₁)·log t + i·2πn/σ₁`, `t = ‖McNum(aₙ)‖/‖M1Num(aₙ)‖`
(note `Re < 0` — the log-lift is NEGATIVE here, opposite to Baxter); anchor envelopes
(`McNum_two_point_le`, `M1Num_two_point_le`, `tRat_upper/lower`), derivative `derivF` +
`detF_hasDerivAt` (quotient rule off `Wfun`), `WD_at_sGuess_lower`, `Wfun_on_disk_le`,
`WD_var_on_disk_le`, `Ag_lower_and_step`, `chord_bound_at`, and `chord_conditions_eventually`
(threshold bundle + push along `n ↦ 2πn/σ₁`). Constants: radius `rc = 1/(20σ₁)`, `K = 3/4`;
separation from the **exact** `Im(sGuess P n) = 2πn/σ₁` (gap `2π/σ₁ > 2rc`, `Real.pi_gt_three`).
Reused verbatim: `FMSA.HardSphere.norm_sub_ratio_mul_le` (generic phase-difference bound),
`eventually_log_cap`. Lean lessons: `field_simp`+`ring` on the chord split fails in a fat
context — extract the pure-algebra lemma `chord_algebra_split`
(`1 − (B/x⁶)/(A/y⁶) = (A−B)/A + (B/A)(1 − y⁶/x⁶)`) and `exact` it; inserting a lemma between
`set_option maxHeartbeats … in` and its theorem silently detaches the option (spurious `whnf`
timeout); `rpow` avoided throughout in favour of `Real.exp (δ·log t)` + `Real.add_one_le_exp`.

**2026-07-16 — POLE-session takeover + numerical scoping (GO).** With `POLE.9`'s 1-freq chord
template complete (`HardSphere/BaxterChordFamily.lean`), this session is closing MZERO.5 in a
new file `HSMixture/MixtureChordFamily.lean` (MixtureHSZeros/Counting/MLSeries untouched).
Scoping (`mzero5_scoping.py`, σ∈{[1,2],[1,1.5],[0.8,2.3]}, n→5000, mpmath): **(i) dominant
balance identified** — at every zero, `|Mc| ≈ |M₁E₁| ≈ 1` while `|M₀E₀|, |M₀₁E₀E₁| → 0`
(monomial split `detC = Mc + M₀e^{−sσ₀} + M₁e^{−sσ₁} + M₀₁e^{−s(σ₀+σ₁)}` from `detC_lam_free`);
the zero family balances the constant term against the **larger-diameter** frequency `σ₁`,
spacing `Δ Im = 2π/σ₁` (the recorded `π` was `2π/σ₁` at `σ₁=2`); **(ii) `Re s_k` is NEGATIVE**,
`≈ −(2/σ₁)·ln|s_k|` (MZERO.2's scan window `re∈[−6,1]` already said so); (iii) the **derived
guess** `s_guess(n) = −(1/σ₁)ln|Mc(aₙ)/M₁(aₙ)| + i·(2πn − arg(−Mc/M₁)(aₙ))/σ₁`, anchor
`aₙ = i·2πn/σ₁`, converges to the true zeros (`|g−s*|: 0.33 → 0.0014` over `n=2→2000`), chord
step → 0, `K(r=0.15) ≈ 0.29–0.41` uniform, `|det′(s_k)|/(σ₁|Mc|) → 1.000`; chord-OK from
`n ≈ 10–20` at all three σ sets. Same construction shape as `POLE.9` (phase kill at the anchor
is exact for the σ₁-frequency since `σ₁·Im aₙ = 2πn`).
---

### Task MZERO.6 — chord-map Lipschitz + MapsTo (disk into itself)

*(Route A, Lean.)* `chordPhi_lipschitzOnWith` (from `HasDerivAt F F′` + the MZERO.5 bound, via
`Convex.lipschitzOnWith_of_nnnorm_deriv_le`) + generic `mapsTo_closedBall_of_lipschitzOnWith_of_dist_le`.
✓ **DONE (axiom-clean)** — now in the shared `Analysis/BanachPoleFamily.lean`.

---

### Task MZERO.7 — infinitude engine + `det` instantiation

*(Route A, Lean.)* The generic **`zeros_infinite_of_chordPoleFamily`** (`BanachPoleFamily.lean`, per-`n`
chord existence → `choose` → injective via `hsep` → `Set.infinite_of_injective_forall_mem`) is the shared
infinitude engine; **`Q0_det_c_zeros_infinite`** (`MixtureHSZeros.lean`) is a thin instantiation packaging
the det-family data (Im-spacing ⇒ `hsep`, differentiability off `0`) into a `ChordPoleFamily det_c`. ✓
**DONE (axiom-clean), conditional on MZERO.5** — exact parity with, and now sharing the predicate of,
`G_baxter_zeros_infinite_of_chordPoleFamily`.

---

### Task MZERO.8 — `det(Q̂₀)` meromorphic (for Jensen)

*(Route B, Lean.)* ✓ **DONE**, axiom-clean (`det_meromorphicAt`, `det_meromorphicOn`,
`MixtureHSZeros.lean`). **Much easier than planned — no analytic continuation needed:** each
`φ₁,φ₂ = (entire)/s^{2,3}` is `MeromorphicAt` everywhere as a *ratio of entire functions*, meromorphic is
closed under `+,−,×,÷`, and `fun_prop` (MeromorphicAt closure lemmas are `@[fun_prop]`) discharges the
whole `det_fin_two` combination. The Lean `0/0` value at `s=0` is irrelevant (`MeromorphicAt` only sees a
punctured nbhd) ⇒ **Route B's `s=0` "hard part" dissolves**; only the MZERO.10 boundary-growth estimate
remains hard.

---

### Task MZERO.9 — `divisor det ≥ 0` + `hJensen` Jensen-counting bound

*(Route B, Lean, `MixtureHSCounting.lean`.)* The bound: `MeromorphicOn.circleAverage_log_norm` (Jensen) +
`divisor det ≥ 0` (`det` poleless — each `φ=num/sⁿ` has `meromorphicOrderAt φ 0 = 0`, `num` vanishing to
order `n`) + finite support ⇒ finite zeros give the `O(log R)` bound. ✓ **DONE (2026-07-16, axiom-clean).**
- **`divisor det ≥ 0` is now UNCONDITIONAL** (`det_divisor_nonneg`, axiom-clean, 2026-07-15). The "det has
  a limit at `0`" hyp of `det_divisor_nonneg_of_tendsto` (reduced via
  `tendsto_nhds_iff_meromorphicOrderAt_nonneg`) is discharged by the **Baxter removable values at `s=0`**:
  `φ₁(0)=−σ²/2` (`phi1_tendsto`), `φ₂(0)=σ³/6` (`phi2_tendsto`).
- Mechanism: exp-Taylor limits `(eʷ−1−w)/w²→½` (`expTaylor2`), `(eʷ−1−w−w²/2)/w³→⅙` (`expTaylor3`), proved
  via `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` (order of the Taylor remainder from vanishing
  derivatives) + the reusable `remainder_div_tendsto_zero` (`f w/wⁿ→0` when `analyticOrderAt f 0 ≥ n+1`).
  Substitution `w=−sσ` (`neg_mul_tendsto_punctured`) gives the `φ` limits; **the `s³` odd power flips the
  sign** so the `φ₂` multiplier is `+σ³` (not `−σ³`).
- Chain: `q0_entry_c_tendsto` (entry limit `δ − ρ·(Qp·(−σ²/2)+Qpp·(σ³/6))`, `e^{−λs}→1`) → `detC_tendsto`
  (`det_fin_two` combination) → `det_divisor_nonneg`. **The `φ₁(0)=−σ²/2`, `φ₂(0)=σ³/6` are the `s=0`
  Taylor coefficients of the Baxter entries — reusable for the inner-core polynomial / numerical
  construction (cf. MPOLY, GAP.9).**
- **`hJensen` NOW PROVED** ✓ (2026-07-16, axiom-clean): `detC_jensen_log_bound` (`MixtureHSCounting.lean`)
  discharges it by citing the abstract MA.5 `circleAverage_log_norm_le_of_finite_zeros`
  (`Analysis/JensenCounting.lean`) + a `detC`-specific **bridge** (finite *literal* zeros ⇒ finite
  *divisor* support): every point of nonzero order is either `s=0` (the removable point, whose Lean junk
  value need not vanish) or — being analytic there (`Q0_det_c_differentiableAt`, `u≠0`) with positive
  order — a genuine zero (`AnalyticAt.analyticOrderAt_ne_zero`), so the support sits in `{0} ∪ zeros`,
  finite. **⇒ Route B now closes `Set.Infinite {detC=0}` modulo ONLY MZERO.10** (`DetBoundaryGrowth`),
  via `detC_zeros_infinite_of_boundaryGrowth` — the `hJensen` hypothesis is gone.

---

### Task MZERO.10 — boundary growth hypothesis

*(Route B, Lean; the `detC` half in `HSMixture/MixtureHSCounting.lean`, the generic predicate and
`detBoundaryGrowth_of_linear` in **`Analysis/BoundaryGrowth.lean`** ns `FMSA.BoundaryGrowth` — migrated
by MRS.9b, checked 2026-07-31.)* ✓ **DONE** as the input hypothesis `DetBoundaryGrowth f`
(`circleAverage (Real.log‖f·‖) 0 R` beats every `M·log R + C`) + `detBoundaryGrowth_of_linear` (a
`≥ c·R − C₀` estimate implies it, via `Real.isLittleO_log_id_atTop`). Axiom-clean.

**⚠ MZERO.10 for `detC` is EQUIVALENT to MZERO.1 — not an independent analytic input (2026-07-16,
PROVED).** By the integrated Jensen identity `circleAverage(log‖detC·‖) 0 R = ∫₀ᴿ n(t)/t dt + const`
(no poles ⇒ `divisor ≥ 0`), super-log growth of the boundary average ⟺ `n(t)→∞` ⟺ **infinitely many
zeros = MZERO.1**. The theorem **`detC_boundaryGrowth_iff_infinite_zeros`** (axiom-clean,
`MixtureHSCounting.lean`, `0<σᵢ`) proves this equivalence: `⟸` is `detC_zeros_infinite_of_boundaryGrowth`
(= `hJensen`'s contrapositive), `⟹` is `detC_boundaryGrowth_of_infinite_zeros` (Jensen LOWER bound —
`K` zeros in the ball give `circleAverage ≥ K·log R − const`; rules out `detC` locally-zero via the
identity theorem on `ℂ∖{0}` + the non-vanishing witness `Q0_det_c_tendsto_one`). **Correction to the
earlier note:** the growth is NOT "from `e^{−sσ}` magnitude" — a zero-*free* exponential `e^{−sτ}` has
circle-average `0` (`∫cos θ = 0`); the linear log-average growth comes **entirely from the (linearly
dense) zeros**. So Route B is a Jensen *reformulation* of MZERO.1, not an independent closure of it —
proving MZERO.10 from analytic structure alone is exactly as hard as the whole result. The genuine
independent route is **Route A (MZERO.5/hstep)**.

---

### Task MZERO.11 — Jensen capstone ⇒ ∞ many zeros

*(Route B, Lean; `infinite_zeros_of_growth` now in **`Analysis/BoundaryGrowth.lean`**, the `detC`
capstones in `HSMixture/MixtureHSCounting.lean` — checked 2026-07-31.)* ✓ **structural capstone DONE** (`infinite_zeros_of_growth`: a
Jensen log-bound for the finite-zeros case + `DetBoundaryGrowth` ⇒ `Set.Infinite {f=0}`; pure
contradiction) and `detC_zeros_infinite_of_growth` (**independent Route-B proof** of
`Set.Infinite {detC=0}`, matching Route A's `Q0_det_c_zeros_infinite`). Axiom-clean. Reuses
`det_meromorphicOn` (MZERO.8) for Jensen's hypothesis. **With MZERO.9's `hJensen` now proved (2026-07-16),
the hJensen hypothesis is discharged**: `detC_zeros_infinite_of_boundaryGrowth` gives the Route-B
infinitude conditional on **only** `DetBoundaryGrowth` (MZERO.10) — full parity with Route A (which rests
on the MZERO.5 magnitude bounds).


### Task MRS.0b — the `n = 1` bridge: `pyhs_mixture_no_spinodal` at one component is a THEOREM

**✓ DONE 2026-07-19, full build green (8678 jobs), no `sorry`, `#print axioms` = STANDARD THREE
ONLY.** New file `HSMixture/MixtureNoSpinodalN1.lean`; the axiom's own file is untouched except for
a docstring correction.

**Why this was worth doing before any consumer exists.** `pyhs_mixture_no_spinodal` (MRS.0) is
pre-placed with **no consumer**. That is a specific hazard, not a neutral state: a consumer-less
axiom has no downstream use that could ever expose a mis-statement, and this project has had **four**
axioms that were false *as stated* (MA.5 literal-zero-set, MA.2 ordered-vs-circle-grouped, MA.4,
clause 6a's jump at σ) — every one caught **only** by a proof attempt, never by `#print axioms`, the
build, or review. The `n = 1` slice is the one mechanically checkable soundness test such an axiom
admits, because there the mixture claim *must* reduce to the already-proven scalar `pyhs_no_spinodal`.

**Result — stronger than "consistent".** `pyhs_mixture_no_spinodal_n1` has the **same statement as
the axiom specialised to `Fin 1`** and is proved **without** the axiom, depending on nothing but
`[propext, Classical.choice, Quot.sound]`. Not even MA.13/MA.14 appear, because the scalar
`pyhs_no_spinodal` is itself axiom-clean via the `k⁶` route. **So at `n = 1` the axiom is redundant,
and its entire content lives in `n ≥ 2`** — consistent with the numerics, where every certificate
that succeeds at `N = 1` (term-wise dominance) fails from `N = 2` onward.

**The chain (four steps).**

1. **Moments.** `xi2_n1 : ξ₂ = ρ₀σ₀²`, `etaMix_n1 : η = πρ₀σ₀³/6` — the latter is *literally* the
   `heta_def` hypothesis `pyhs_no_spinodal` requires, so the coupling conventions agree exactly.
2. **Coefficients.** `Q0phys_n1 : Q0phys ρ σ 0 0 = q_prime_py η σ₀` and
   `Qppphys_n1 : Qppphys ρ σ 0 0 = q_doubleprime_py η`. Proof: substitute `ρ₀ = 6η/(πσ₀³)` and
   `field_simp`/`ring`. **This closes a loop** — `q_doubleprime_py`'s docstring *derives* it from the
   multicomponent formula `(2π/Δ)(1+πR_jξ₂/(2Δ))`, so the scalar and mixture coefficients were two
   hand-transcriptions of one paper; they are now a machine-checked identity.
   Also `rhoGeoPhys_n1 : √(ρ₀ρ₀) = ρ₀`.
3. **Kernels.** `qhat_complex_eq_mixture_kernel` — the mixture's two Laplace kernels reassemble the
   scalar transform. The observation that makes it easy: with `s = ik`,
   `(1−sσ−e^{−sσ})/s² = −∫₀^σ(σ−r)e^{−sr}dr` and `(1−sσ+(sσ)²/2−e^{−sσ})/s³ = ∫₀^σ(σ−r)²/2·e^{−sr}dr`,
   which is **exactly** the shape of `q0_poly r = ρ(Q'(r−σ) + Q''(r−σ)²/2)`. So no integration is
   needed: `Qhat_complex_formula` (POLE.1) already supplies the closed form, and both sides are
   rational in `s` and `e^{−sσ}` ⇒ `field_simp; ring`. ⚠ **`Complex.I` never needs `I² = −1`** — the
   identity holds treating `I` as a formal atom, which is why `ring` closes it.
4. **Determinant.** `Q0_mat_c_phys_n1_det` via `Matrix.det_fin_one`; the off-diagonal shift
   `λ₀₀ = (σ₀−σ₀)/2` vanishes and `δ₀₀ = 1`.

Assembly: `det Q̂₀(ik) = 1 − Q̂(k)`, then `qhat_complex_ne_one_of_real`.

**Prior art check:** the bridge did not exist in any form. The only `Fin 1` lemma touching `Q0_mat`
was `Q0_mat_n1_entry` (`MatrixQ0.lean:254`), which terminates in an unfolded `q0_entry`, never a
named scalar object; `MatrixN1.lean` proves the `Fin 1` collapse only for *abstract constant* 1×1
matrices, so it does not compose with `Q0_mat_phys`. None of `etaMix`/`Q0phys`/`Qppphys` had an
`n = 1` reduction, and `Matrix.det_fin_one` appeared nowhere in `LeanCode/`.

**What this does NOT do.** It does not make the general axiom any more provable. The `k⁶` route is
still dead for `N ≥ 2` (term-wise dominance fails 300/300, even at diameter ratio ≈ 1.00 — a phase
artifact, not a weakness of the claim), so MRS.0 remains MA.14-class, needing a winding argument.
The bridge is a *validation*, not a step toward the proof.


### Task MRS.9 — `HSMixture/` library reorganization

**✓ Overall COMPLETE: 9a–9c DONE 2026-07-19, 9d DONE 2026-07-27.**  The library reorganization is **one** task —
create the `HSMixture/` layer, re-home misfiled files, split straddlers into `Analysis/`, normalize
the species binder — so it is recorded here as `MRS.9` with four sub-parts, **not** as four letter
suffixes of the physics axiom `MRS.0`.  Consolidated from the ex-`MRS.0c/0d/0e/0f` records
2026-07-19 (`MRS.0`/`MRS.0b` remain the physics-axiom cluster above).  The layering invariant it
establishes — `Analysis/ ← HardSphere/ ← HSMixture/ ← YukawaDCF/`, imports leftward only — is in
`CONVENTIONS.md`.

#### MRS.9a — `LeanCode/HSMixture/` — the N-component hard-sphere layer

**✓ DONE 2026-07-19, build green (8683 jobs, identical to the pre-move baseline ⇒ pure move,
no declaration added or removed), all four invariants re-verified.**

**Motivation.** `pyhs_mixture_no_spinodal` sat in `YukawaDCF/` although it is a pure hard-sphere
statement. Chasing that revealed a structural problem: `HardSphere/` (66 files) was *already* the
home of the mixture Baxter matrix `MatrixQ0`, `Q0DetRankTwo`, and the whole FMT cluster, so
"HardSphere = single-component" was simply not true. The scalar/mixture line is the same one
`MRS.0b`'s `n = 1` bridge just made precise (scalar proven, mixture axiomatized), so it is worth
making visible in the directory structure.

**Layering invariant** (now recorded in `CONVENTIONS.md` with copy-pasteable greps):
`Analysis/ ← HardSphere/ ← HSMixture/ ← YukawaDCF/`, imports pointing leftward only.

**Moved — 14 files into `HSMixture/`.**
* Baxter mixture core, from `HardSphere/` (6): `MatrixQ0` (with `etaMix`/`xi2`/`Q0phys`/`Qppphys`/
  `rhoGeoPhys`), `Q0Complex`, `Q0DetRankTwo`, `Q0DetLimit`, `MixtureNoSpinodal`,
  `MixtureNoSpinodalN1`.
* FMT mixture cluster, from `HardSphere/` (4): `WhiteBearFMT`, `CHSKink`, `CHSKinkWB`,
  `CHSFlatInner` — species-indexed and predicated on unlike radii `Ri ≠ Rj`. The cluster is fully
  self-contained (imports only each other; `CHSKinkWB`/`CHSFlatInner` have no external consumer), so
  it moves as a unit with zero back-edges.
* From `YukawaDCF/` (4): `MixtureHSZeros`, `MixtureHSPoles`, `MixtureChordFamily` (`MixParams`),
  `MixtureHSCounting` — none has any Yukawa content outside its copyright line.

**Also re-homed:** `SingleCompReduction` `YukawaDCF/ → HardSphere/` (entirely scalar signatures
`(S M z : ℝ)` despite the directory); `MatrixIdentity` `HardSphere/ → Analysis/` (abstract identity
over arbitrary `Matrix (Fin n) (Fin n) ℝ`, imports no LeanCode module).

**Namespaces needed no change** — `FMSA.MatrixQ0`, `FMSA.Q0Complex`, … encode content, not
directory (the content-descriptive naming convention), so a directory move is free.

⚠ **Classification-method lesson — the narrow grep lies.** The species-index binder is *not*
uniform across the library: `Fin n` (Baxter), `Fin N` (`WhiteBearFMT`), `Fin M` (`CHSKinkWB`).
Screening on `Fin n` alone reported "0 hits" for `CHSKinkWB` and **misfiled the entire FMT cluster as
scalar**; it surfaced only after re-sweeping with `Fin [A-Za-z]+ → (ℝ|ℂ)` plus the mixture-only
concept `Ri ≠ Rj`. Two further traps: `Mixture*` prefixes are unreliable in *both* directions
(`MixtureHSCounting` is abstract complex analysis; `SingleCompReduction` is scalar), and the
`Mix N M` structure is **not** pure HS — its `zp`/`cb` fields are Yukawa pole residues, which is why
`WHSupports`/`MixtureClosedForm`/`MixtureConvolution`/`MixtureDCFSmooth`/`InnerDecomp` all stayed
put. All recorded in `CONVENTIONS.md`.

**Deliberately NOT moved (blocked by a genuine back-edge, → the split task below):**
`MixtureLaurent` and `MixtureMLBound` import `MixturePolyCoeffs` / `MixtureMLSeries`, which do carry
real Yukawa content; moving them would create `HSMixture → YukawaDCF`. Likewise `MatrixN1` cannot go
to `Analysis/` while it imports `HardSphere/SingleCompIdentity`+`BaxterFactor`.

**Verified:** (1) `lake build` green at 8683 jobs, equal to baseline; (2) all three layering greps
empty; (3) the axiom ledger is **byte-identical** before/after — 8 axioms (7 math + 1 physics), the
physics one now under the `HSMixture` bucket; (4) `#print axioms pyhs_mixture_no_spinodal_n1` still
`[propext, Classical.choice, Quot.sound]`.

**Continued as `MRS.9b` (below):** split the three straddling files, general half leftward —
`MatrixN1` (4 abstract lemmas → `Analysis/`, `m2_identity_baxter` stays), `MixtureHSCounting`
(`DetBoundaryGrowth`/`infinite_zeros_of_growth`/`expTaylor2,3`/… → `Analysis/`), `MixtureLaurent`
(`taylor4_*` generic calculus → `Analysis/`). That also unblocks the two moves above.


#### MRS.9b — splitting the straddling files: general math moved into `Analysis/`

**✓ DONE 2026-07-19, build green (8688 jobs), no `sorry`, all four invariants re-verified.**
Directory counts `Analysis 18→23`, `HardSphere 56`, `HSMixture 14→15`, `YukawaDCF 23→22`.

Stage 2 of the `HSMixture/` reorganisation (`MRS.9a`): a file that straddles the layering boundary
is **split**, not filed by majority vote — the general half moves left, per Group MA admissibility
rule (c) and the `BanachPoleFamily` / `radialShell_bounded_injective` precedents.

**Five new `Analysis/` files, all imports = Mathlib only (except `BoundaryGrowth`).**

| new file | extracted from | contents |
|---|---|---|
| `MatrixFin1.lean` | `HardSphere/MatrixN1` | `1×1` matrix mul/inv = scalar mul/div; unconditional (`D = 0` ⇒ both sides `0`) |
| `ExpTaylorLimits.lean` | `HSMixture/MixtureHSCounting` | `remainder_div_tendsto_zero`, `expTaylor2/3`, `phi1/phi2_tendsto` — removable singularities at `s = 0` for arbitrary `σ ≠ 0` |
| `BoundaryGrowth.lean` | same | `DetBoundaryGrowth`, `detBoundaryGrowth_of_linear`, `infinite_zeros_of_growth`, `finset_sum_le_finsum_of_nonneg` — abstract `f : ℂ → ℂ` |
| `Taylor4Calculus.lean` | `HSMixture/MixtureLaurent` | the order-4 Taylor germ algebra: `taylor4_mul/sub/neg/recip`, `poly4_eq_zero_of_littleO`, `taylor4_coeff_unique` — arbitrary `f g : ℝ → ℝ` |
| `PoleSeriesSummable.lean` | `YukawaOZMix/MixtureMLSeries` | `mixHSterm`, `mixHS_summable`, `mixHS_summable_of_growth` — arbitrary `Bcoef sfam : ℕ → ℂ` |

**A 4th split was needed and was not in the plan.** `MixtureMLBound` was blocked by
`MixtureMLSeries`, which I had classified as "genuinely Yukawa" from keyword counts. That was
right about the *file* (it defines `yukawaCoupling`, the Laplace-space propagator factor) but wrong
about the *dependency*: `MixtureMLBound` uses only `mixHSterm` / `mixHS_summable_of_growth`, both
fully abstract. Splitting those out unblocked it, and **`MixtureMLBound` is now in `HSMixture/`**.

**⚠ `MixtureLaurent` is still blocked — the plan's claim that stage 2 would unblock it was wrong.**
Its residual three theorems need `q0_entry_taylor3`, `p1_limit`, `p2_limit`, `p1/p2_cubic_coeff`,
`exp_neg_cubic_rem` from `MixturePolyCoeffs`, which imports `InnerOriginBC` + `ContactMatching`
(real Yukawa). Those six lemmas do **not** themselves touch the Yukawa imports, so a 5th split is
*feasible* — but `MixturePolyCoeffs` is 1300+ lines and currently carries ~390 lines of uncommitted
edits from another session, so it was left alone. Recorded as `MRS.9d`.

**Extraction-method notes** (all three hazards actually bit):
* Blocks were located by script (declaration + its preceding `/--` docstring) rather than by hand,
  and re-inserted verbatim — no proof was retyped.
* ⚠ The extractor matched `/--` but not `/-!`, so **section headers were orphaned**: `MixtureLaurent`
  kept a `/-! ### Well-definedness …` header whose theorem had moved. Check `^/-! ###` after any
  extraction.
* ⚠ The last block of a file swallows its `end Namespace` line. `MixtureLaurent` lost its `end` and
  **still built** — Lean auto-closes at EOF and only emits a `linter.style.missingEnd` warning.
  Green build ⇏ balanced namespaces; grep `^namespace` vs `^end ` counts.
* `open` does not propagate through `import`: every downstream consumer of a moved declaration needs
  its own `open` (`MixtureInnerDCF`, `MixtureMLBound` both did).

**Deliberate non-goal.** `PoleSeriesSummable`'s `mixHS*` names are historical and now live in
`Analysis/` despite the domain-flavoured prefix. Renaming them to content-descriptive names is a
follow-up (`MRS.9d`), deferred to keep this split's blast radius small while other sessions have
uncommitted work in the same files.


#### MRS.9c — species binder normalised to `N`

**✓ DONE 2026-07-19, build green (8683 jobs, unchanged), convention recorded in `CONVENTIONS.md`.**

Species count is now uniformly `N` (`sigma rho : Fin N → ℝ`). Renamed in 9 files — `n → N` in
`MatrixQ0`, `Q0Complex`, `Q0DetRankTwo`, `Q0DetLimit`, `MixtureNoSpinodal`, `MixtureHSZeros`,
`MixtureRealSpace`, `SpectralAmplitude`; `M → N` in `CHSKinkWB`. `WhiteBearFMT`, `BijReduction` and
the `Mix N M` structure already conformed. **Reserved:** `M` = Yukawa poles per residue expansion
(`Mix`'s `zp`/`cb` third index), bare `n` = anything unindexed (pole/branch number, iteration count,
chord index, Taylor order).

**The scope was 9 files, not the ~24 an initial `Fin _ → ℝ` sweep suggested.** ⚠ **`Fin _ → ℝ` does
NOT mean "species"** — it is equally the *Yukawa tail* index: `FMSAPoly/*`, `FreeEnergy/*`,
`ContactMatching`, `YukawaInnerCore`, `MixtureInnerDCF` all bind `(A z : Fin n → ℝ)` = tail
amplitudes and decay rates. Renaming those would have been actively wrong. The correct discriminator
is **what is indexed**: `sigma`/`rho`/`d` ⇒ species; `A`/`z`/`K`/`Amp` ⇒ tails. Caught by inspecting
`variable {n : ℕ} (A z : Fin n → ℝ)` lines before editing.

`CHSKinkWB`'s `M` was the one genuine defect: `M` means *pole count* in `Mix N M`, so the same letter
carried two meanings. Binder names are implicit, so this could never surface as an error — only a
reader would ever notice.

⚠ **Method lesson — `lake build` cannot validate a binder rename.** Renaming a bound variable is
alpha-equivalent: a *local* `n` (a `∀ n`, an `intro n`) wrongly swept into `N` compiles perfectly and
is silently wrong. Green build ⇏ correct rename. The actual verification was (i) per-declaration
scoping in the rewrite (only blocks matching `Fin n → (ℝ|ℂ)` or `Matrix (Fin n)`), (ii) a guard
skipping any block that already bound `N` (relevant: `MixtureHSZeros` uses `N` for a summation count
in *other* declarations), and (iii) a post-hoc grep of all 9 files for `∀ N`/`intro N`/`fun N`/
`induction N` — all empty, so no local was captured.


#### MRS.9d — split `MixturePolyCoeffs`, move `MixtureLaurent`, rename `mixHS*` (ex-`0f`)

**✓ DONE 2026-07-27, build green (8699 jobs), layering invariant re-verified, axiom ledger
byte-identical (pure reorg).**  The deferral blocker is gone — the other session's `MixturePolyCoeffs`
edits landed in commits `93f10f6`/`b3896eb`, so the tree is clean.

**⚠ The 2026-07-19 dependency list above was STALE — re-derived before acting** (per
`feedback_stale_blockers`).  The recorded back-edge was six lemmas; the *current* `MixtureLaurent`
needed **only `p1_limit` + `p2_limit`** from `MixturePolyCoeffs`.  The other four (`q0_entry_taylor3`,
`p1_cubic_coeff`, `p2_cubic_coeff`, `exp_neg_cubic_rem`) had dropped out of `MixtureLaurent`'s
dependency set — `q0_entry_taylor4` now uses the already-extracted `p1_quartic_coeff` /
`exp_neg_quartic_rem` (`Taylor4Calculus`), so only the two order-0 limits remained.  A `grep` of the
actual references, not the note, is what caught this.

**What was done.**
1. **Extracted to `Analysis/Taylor4Calculus.lean`** (namespace `FMSA.Taylor4`, its established home for
   the p1/p2 block-coefficient lemmas — `p1_quartic_coeff`/`exp_neg_quartic_rem` were already there):
   `p2_limit`, `p1_limit` (from `MixturePolyCoeffs`; `p1_limit` uses `p2_limit`, kept in that order)
   and `p2_quartic_coeff` (from `MixtureLaurent` itself — pure real-analysis, its only consumer was
   `q0_entry_taylor4` in the same file, so it left with the general lemmas rather than riding along to
   `HSMixture/`).  All three are `#print axioms = {std three}`.  Names kept (`p1`/`p2` is the
   file's existing convention, not a domain leak).  `MixturePolyCoeffs` now `import`s
   `Analysis/Taylor4Calculus` + `open FMSA.Taylor4` for its three internal `p1_limit`/`p2_limit`
   call sites; nothing else references them externally.
2. **Moved `MixtureLaurent` `YukawaDCF/ → HSMixture/`** (`git mv`, namespace `FMSA.MixtureLaurent`
   unchanged — content-descriptive).  Imports are now `Mathlib` + `Analysis.Taylor4Calculus` +
   `HSMixture.MatrixQ0` (the `q0_entry` it uses, previously pulled in transitively via
   `MixturePolyCoeffs`, now imported directly).  `p1_limit`/`p2_limit`/`p2_quartic_coeff` resolve via
   its existing `open FMSA.Taylor4`.  Its theorems (`q0_entry_taylor4`, `taylor4_inv_entry`) have no
   code consumers, so the move is a leaf relocation.  `LeanCode.lean` import path updated.
3. **Renamed the four generic `mixHS*` in `Analysis/PoleSeriesSummable`** to content-descriptive
   names (word-boundary `sed`, 70 occurrences across 7 files):
   `mixHSterm → poleExpTerm`, `mixHS_series → poleExpSeriesRe`,
   `mixHS_summable → poleExpTerm_summable_of_decay`,
   `mixHS_summable_of_growth → poleExpTerm_summable_of_growth`.
   **Scope = only the generics in `Analysis/`.**  The domain-layer *derived* objects
   (`mixHSterm2`, `mixHS_series2`, `mixHSAntideriv*`, `detF_mixHS_summable`) keep their `mixHS*`
   names — they are genuinely mixture-HS specific and live in `YukawaDCF/`/`HSMixture/`, where a
   domain prefix is correct.  ⚠ The rename must be `\b`-anchored: `mixHSterm` is a substring of the
   preserved `mixHSterm2` (digit-suffixed) and `detF_mixHS_summable` / `…_eq_mixHSterm` (`_`-prefixed);
   the word boundary protects all of them, verified by before/after counts
   (`mixHSterm2` 34→34, `detF_mixHS_summable` 8→8).
4. **Re-verified the layering invariant** (`MRS.9a`'s three greps): `Analysis/ ⊬ higher`,
   `HardSphere/ ⊬ {HSMixture,YukawaDCF}`, **`HSMixture/ ⊬ YukawaDCF`** — all empty.  Directory counts
   now `Analysis 27, HardSphere 59, HSMixture 17, YukawaDCF 24`.

**MRS.9 (`9a`–`9d`) is now COMPLETE.**  Follow-up (2026-07-27): the order-3 p1/p2 lemmas
(`p1_cubic_coeff`, `p2_cubic_coeff`, `exp_neg_cubic_rem`) — verified genuinely physics-independent
(they take only `(σ : ℝ)`/`(λ : ℝ)` and prove via `Real.exp_bound`; NO `q0_entry`/`MatrixQ0`/Yukawa
in the *code*, only in motivating prose) — were **also moved to `Analysis/Taylor4Calculus.lean`**,
completing the p1/p2/exp Baxter-block Taylor family there (orders 0, 3, 4 now all in `Analysis/`).
Their sole consumers were `MixturePolyCoeffs`-internal (`q0_entry_taylor3`), which resolve via the
`open FMSA.Taylor4` already added in `MRS.9d`; verbose GAP.9/`D_ij` docstrings trimmed to the
domain-neutral house style.  Build green 8699, all three `#print axioms = {std three}`.  ⚠ A crude
"references a domain object?" grep suggests a few remaining `p1_num*`/`p2_num*` numerator-derivative
helpers *may* also be general, but the classifier split sibling lemmas inconsistently, so migrating
those needs per-lemma reading and is left as a genuinely-optional future pass — not started.


**GENERAL-`N` — UNCONDITIONAL (2026-07-29, `MixtureDetGeneralN.lean`).**  The `N=2`
`mixtureDet_pole_free` generalises to arbitrary `N`, `mixtureDet_pole_free_N` : `det Q̂₀(I·z) ≠ 0`
on the open lower half `z`-plane for every physical `N`-component mixture, **fully unconditional**,
`#print axioms` = the same two existing axioms (`zeroFree_lowerHalfPlane_of_homotopy`,
`pyhs_mixture_no_spinodal`) — no new axiom.  Route: the already-`N`-general framework
`matDet_zeroFree_lowerHalfPlane_of_homotopy` applied to the entire `ψ`-matrix `Mdens` (physical `Q̂₀`
with each `φ = num/sⁿ` replaced by its entire removable extension `ψ`, so every entry is entire
(`hholo`, `Mdens_hholo`) and jointly continuous (`hcont`, `Mdens_hcont`)).  `hbase` = dilute `Mdens 0
= I`.  `hreal` = `k≠0` no-spinodal (`{N}`) + `k=0` compressibility `detMdens_origin_ne_zero`
(axiom-clean, `det ≥ 1` via `Q0_mat_phys_det_ge_one_N` = rank-2 reduction + `moment_key`, which is
`{N}`).

**The escape `hbound` (the crux `N`-general obstacle) — SOLVED cleanly via a diagonal similarity.**
Individual `Q̂₀` entries blow up as `Re s → ∞` (`e^{−λ_{ij}s}`, `λ_{ij}<0`), but the phase
`e^{−λ_{ij}s} = e^{σᵢs/2}·e^{−σⱼs/2}` **is** a diagonal similarity `D(·)D⁻¹`, so
`det Q̂₀ = det Mgauge` (`det_Q0_eq_det_gauge`, via `det_mul` + `det_diagonal`, `∏e^{σᵢs/2}·∏e^{−σⱼs/2}
= e^0 = 1`) where `Mgauge` has the phase stripped (`lam=0`, entries bounded).  Then `Mgauge = 1 − A`,
`‖A‖_{L∞ op} ≤ Abnd/‖s‖ → 0` (kernel bounds `‖φ₁‖ ≤ (2+σ)/‖s‖`, `‖φ₂‖ ≤ (2+σ+σ²/2)/‖s‖` from
`‖e^{−sσ}‖ = e^{−σ Re s} ≤ 1`; `linfty_opNorm_le_row`), uniformly in `t` (`Abnd_cont` + compact
`[0,1]`), so `1 − A = Mgauge` is a unit (`isUnit_one_sub_of_norm_lt_one`) and `det ≠ 0` for `‖s‖ ≥ R`
(`exists_uniform_escape`, axiom-clean).  This is **cleaner than the `N=2` monomial bridge** and needed
no complex VU factorisation.  **`OZFIX.17` matrix pole↔decay is now RESOLVED for ALL `N`.**

---

### Task MML.16 — the RDF **parity partner** is annihilated exactly (the "even pseudo-trace" question)

**Origin (2026-08-03).** A reading question: the first-order RDF is built from the **unilateral**
transform `Ĥ₁`, while the physical object is the **sine** transform `H̃₁` (the transform of the *odd*
extension of `r·h₁`). One-sided ≠ two-sided, so an *even-function pseudo-trace* could in principle
contaminate `B₁`. Does Tang & Lu's derivation handle it — or does it merely happen to be small?

**Checked against the original** (`pdf/sources_paywall/Analytical solution of the Ornstein-Zernike
equation for mixtures.pdf` = Tang & Lu, *Mol. Phys.* **84**, 89–103 (1995)), journal pp. 91–94:

* **p. 91 / p. 92 — both transforms are defined**, and the exact link is stated:
  `H̃(k) = [Ĥ(−k) − Ĥ(k)]/(ik)`, `C̃(k) = [Ĉ(−k) − Ĉ(k)]/(ik)`. So `H̃` is (up to `1/(ik)`) the **odd
  part** of `Ĥ`; Tang & Lu **never** identify the two.
* **p. 92, Eq. (9) / p. 93, Eq. (10) — the parity partners are written explicitly**: substituting the
  link produces `Q̂₀ᵀ(k)Ĥ₁(−k)Q̂₀(k)` (RDF partner) and `−[Q̂₀(−k)]⁻¹Ĉ₁(−k)[Q̂₀ᵀ(−k)]⁻¹` (DCF partner)
  alongside the `U₁` and `S₁` terms.
* **p. 93 — the space analysis** puts "the first, the third, and the fourth terms on the right-hand
  side of equation (10)" in `[−∞,R]`; only `U₁` reaches `[R,∞)`.
* **p. 94 — the Wiener-Hopf conclusion**: "The left-hand side … is in `[R,∞)` space, while the
  right-hand side … belongs to `[−∞,R]` space. Both sides should vanish." ⇒ Eq. (14)/(15),
  `Q̂₀ᵀ(k)Ĥ₁(k)Q̂₀(k) = {T_U}^{[R,∞)}`, `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹`.

**Answer.** The artifact is **confronted and annihilated exactly** — it is not small, it is
*elsewhere*: it lives on the reflected half-line, which the causal projection discards. Nothing here
is asymptotic.

**⚠ [LN] deviates from the original at exactly this step — a transcription seam.**
`pdf/lecture_notes_OZ_Yukawa.tex` writes, in the derivation of `eq:OZ1_Baxter`, "*note that the
half-line transforms satisfy `H̃₁(k) = Ĥ₁(k)` (since `h^{(1)}(r)=0` for `r<0` …)*". In the notes' own
normalization that is **false** (the tilde carries a `1/k` and is the odd part), and its stated reason
is not the operative one. Consequently the notes' `eq:rearranged` has a vacuous `− L(k) + L(k)` where
the original has the two genuinely different reflected terms — while the notes' **Proof 2 still
discusses `Ĥ₁(−k)`**, betraying its descent from the original. The *conclusion* (Eq. 62/68) is
unaffected, which is why nothing downstream broke. **Read the original, not the notes, for this step.**

**Lean — DONE (2026-08-03, axiom-clean),** `LeanCode/YukawaOZMix/ReflectedTermSupports.lean`
(namespace `FMSA.ReflectedSupports`), wired into `LeanCode.lean`:

* `support_comp_neg`, `reflected_support_Iic` — reflection reverses the support: `h₁` on `[R,∞)`
  (the exact hard-core condition, every order) ⇒ the time-reversed `h₁` on `(−∞,−R]`;
* `Icc_add_Iic_subset`, `Iic_add_Icc_subset`, `Iic_add_Iic_subset` — the Minkowski arithmetic that
  `support_convolution_subset` reduces the space analysis to (mirrors `MixtureConvolution.lean`'s
  `Ici`/`Icc` helpers, opposite orientation);
* **`reflected_rdf_conj_support`** — *Proof 2, RDF half*: `Q̂₀ᵀ ⋆ h₁(−·) ⋆ Q̂₀` is supported on
  `(−∞,−λ_ij]`;
* **`antiCausal_triple_support`** — *Proof 2, conjugation half*: a triple convolution of anti-causal
  factors stays anti-causal — covers the inner-core `S₁` term (`b := R`) **and** the DCF parity
  partner (`b := 0`) in one lemma;
* **`parity_partners_causal_projection_zero`** — the headline: the causal projection of a
  `(−∞,R)`-supported term is **identically `0`**;
* `causal_projection_with_reflection` (+ `_open`) — Y1.3b's `causal_projection_real` with the two
  partners **present** in the equation: the conclusion `L = {T_U}^{[R,∞)}` is unchanged. The `_open`
  form concludes on `(R,∞)` and needs no strictness, which matters because for **like pairs**
  (`λ_ii = 0`) the `S₁` term's support bound is exactly `(−∞,R]` — Tang & Lu's two spaces are both
  closed and overlap in the single point `r = R`;
* closing `example` — non-vacuity **with `Wrefl ≠ 0`**: the annihilation is about *where* the partner
  lives, not its size. (Contrast the DCF side, where the analogous reflected term is `O(1)`: the C++
  port's `reflection` razor moves **107 %** when it is dropped, and MRS.5's `oddPart_reduction` keeps
  `𝒲(r) − 𝒲(−r)` explicitly.)

**Atomic supports — now discharged too (2026-08-03, same file).**  The first cut left "the concrete
`Q̂₀`, `h₁`, `S₁` satisfy the atomic supports" to Y1.3a.  That gap is closed:

* **`q0MixEntryRefl` / `q0MixEntryRefl_support_subset`** — the **transposed** Baxter factor
  `{Q̂₀ᵀ}_{ij}` on `[−R_ij, −λ_ij]`.  This was the atom Y1.3a genuinely lacked (`WHSupports` has only
  the untransposed `q0MixEntry`); transposition is `r → −r`, so it follows from Y1.3a + reflection.
* **`support_subset_Ici_of_hardCore`**, **`support_subset_Icc_of_window`** — the physics ⇒ support
  bridges: the exact hard-core condition `h^{(γ)}(r) = 0` for `r < R` (Tang & Lu p. 91, every order)
  and the definitional `[0,R]` window of `S₁`.
* **`reflected_rdf_edge_eq`** — the mixed-index edge identity `−λ_im + (−R_mn) + R_nj = R_ij − σ_m`:
  the intermediate species `n` **cancels completely**, `m` survives only as a margin.  (Same
  cancellation pattern as `MixtureConvolution.pbp_edge_eq`.)
* **`reflected_rdf_conj_support_physical`** — hence `supp ⊆ (−∞, R_ij − σ_m]` **from physics only**,
  and **`reflected_rdf_conj_eq_zero_of_contact_le`** — the partner vanishes on the **closed**
  `[R_ij, ∞)`, endpoint included, because `σ_m > 0` (`Mix.hσ`, the structure's only physical axiom).
  So for the parity partner the endpoint caveat above is **void**; only the inner-core `S₁` term
  touches `r = R`.
* **`convIter_support_subset`** — every Neumann term of `I + A + A⋆A + ⋯` is anti-causal with the
  *same* bound when `A` is (`a ≤ 0` keeps the edge from moving right).

**⚠ The fourth atom does NOT need MA.13 — finding of 2026-08-03.**  The Neumann series genuinely
diverges in the physical regime (`‖q‖₁ > 1`, the very reason `wiener_causal_resolvent` is a kept
axiom), so the series route stalls.  But **the support question is local**, and locally the renewal
equation is unconditionally solvable:

* `renewalResolvent` := `VolterraBanach.volterraGlobalE 0 q q` — the solution of `R = q + q ⋆ R`
  supplied by **MA.10** (`Analysis/Volterra.lean` / `VolterraBanach.lean`, *proved, axiom-free*).
  MA.10 gives existence **and uniqueness on every window** `[0,b]` with **no smallness hypothesis**:
  the factorial iterate bound `Mⁿ(b−a)ⁿ/n!` beats any `‖q‖₁`, and `volterraGlobalE` glues the windows.
* **`renewalResolvent_support`** — the resolvent is **causal by construction** (`volterraGlobalE` is
  literally `0` off `[0,∞)`), with `renewalResolvent_spec` pinning it by its equation;
  **`renewalResolventRefl_support`** mirrors it to the anti-causal orientation `[Q̂₀(−k)]⁻¹` has.
* **`antiCausal_conj_delta_support`** — conjugation by `δ + (anti-causal)` preserves `(−∞,b]`: the
  four-term expansion `(δ+A) ⋆ f ⋆ (δ+B)` stays anti-causal.
* **`eq10_antiCausal_side`** — hence *both* remaining terms of Eq. (10) (the inner-core `S₁` term,
  `b := R_ij`; the DCF parity partner, `b := 0`) are supported in `(−∞,R_ij]`.
  `#print axioms` on all of these: the **standard three only** — MA.13 does not appear.

**So MA.13 is off this path.**  What it *is* needed for is the **global `L¹`** resolvent — the decay
and pole statements of POLE.11 — which is strictly stronger than "supported on a half-line".  The two
questions were conflated; they are now separated.

**What genuinely remains is a dictionary item, not analysis:** that the physical `[Q̂₀(−k)]⁻¹` *is*
`δ + R` with `R` the renewal solution.  That is the real-space reading of `Q̂₀·Q̂₀⁻¹ = I` (algebra plus
the transform correspondence), carried as the hypothesis shape of `antiCausal_conj_delta_support`.

**Status.** ✓ DONE (axiom-clean), atomic supports included, **and free of MA.13**. Companion
write-up: `FMSA_dp_output/md/rdf_parity_no_pseudotrace.md`.

### Task MML.17 — Tang & Lu momentum-side first-order mixture RDF (the residue expansion)

Reference: `pdf/sources_paywall/Analytical solution of the Ornstein-Zernike equation for mixtures.pdf`
= **Tang & Lu, *Mol. Phys.* 84, 89–103 (1995)**, §2–3.  The mixture first-order RDF is solved in
**momentum space** via the closed-form inverse `[Q̂₀]⁻¹`, *not* the real-space renewal seed of MML.15/16
(that whole seed saga — `matBaxterUQm`, K-shell, `matShellConvAsym`, reflected-linear, transposed
renewal — was the wrong method; its lemmas survive as valid implications with flagged-false premises).
My `Cmix0 / Q̂₀ / swap_offdiag / det / q0_entry_c` objects match the paper's eqs (7)–(13) exactly.

The paper's chain (eq numbers are Tang & Lu's):

* **(4) HS contact baseline (eq 25)** — `LeanCode/YukawaOZMix/MixtureRDFContact.lean`,
  `FMSA.MatrixQ0.gHS_contact` + `gHS_contact_equalDiam` (reduces to `(1+η/2)/(1−η)²`). Axiom-clean.
* **(1) closed-form inverse (Appendix, eq before 15)** — `LeanCode/HSMixture/MixtureQ0Inverse.lean`,
  `Q0_mat_phys_inv_closed_form` / `Q0_mat_phys_inv_eq`: `[Q̂₀]⁻¹ = I + U(I−VU)⁻¹V` via
  Sherman–Morrison–Woodbury on the existing rank-2 `Q̂₀ = I − UV` (`I−VU` is 2×2, `det = det Q̂₀ ≥ 1`).
  This IS Tang & Lu's Appendix inverse `{[Q̂₀]⁻¹}ᵢⱼ = δᵢⱼ + 2π(ρᵢρⱼ)^{1/2}Wᵢⱼ(ik)/(Δ det(ik))·e^{−ikλᵢⱼ}`,
  i.e. the `Aᵢⱼ(t) = 2π(ρᵢρⱼ)^{1/2}Wᵢⱼ(t)/(Δ det(t))` amplitudes of eq (20). Axiom-clean.
* **eq (15) assembly** — same file, `H1_eq_of_transformed` / `H1_eq_phys`:
  `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` from the transformed first-order OZ `Q̂₀ᵀĤ₁Q̂₀ = B₁`. Axiom-clean.
* **(2)=(18) one-Yukawa `U₁` transform** — `LeanCode/YukawaOZ/MixtureYukawaTransform.lean`,
  `laplace_yukawa` + `yukawa_U1_entry`: `∫_R^∞ (βRε e^{−z(r−R)})e^{−sr}dr = βRε e^{−sR}/(s+z)`, i.e.
  `U₁ᵢⱼ = Kᵢⱼ e^{−ikRᵢⱼ}/(ik+zᵢⱼ)`, `Kᵢⱼ = 2π(ρᵢρⱼ)^{1/2}Rβε`. The `1/r` of the MSA tail cancels the
  radial `r` weight ⇒ a pure exponential integral. Axiom-clean.
* **(3) residue extraction (eq 20→21)** — `LeanCode/YukawaOZ/MixtureYukawaResidue.lean` (NEW,
  2026-08-04). Eq (19) turns `B₁(k)` into `−E(k) Res_{y(s)}(E(−y)[Q̂₀(−y)]⁻¹U₁(y)[Q̂₀ᵀ(−y)]⁻¹E(−y)/(y−k))E(k)`,
  the residue taken **at the Yukawa poles of `U₁`**. Substituting eq (18) + `[Q̂₀(−y)]⁻¹ = I + A(−iy)`
  makes every entry of the eq (20) integrand a finite sum of terms of the *one* shape
  `g(y)/((y−k)(iy+z))`, `g` analytic (products of `K` and `A(−iy)`), with a **simple** pole at `y = iz`
  because `iy+z = i(y−iz)`. The single lemma
  - **`residue_yukawa_pole_general`** : `Res_{y=iz}[g(y)/((y−k)(iy+z))] = −g(iz)/(ik+z)`
    (proved as the punctured-limit `(y−iz)·f(y)`: on `𝓝[≠](iz)` the pole cancels to `g(y)/((y−k)i)`,
    continuous at `iz`; value rewritten via `(iz−k)i = −(ik+z)`)

  captures **all four** eq (20) term-types at once, supplying uniformly (i) the Yukawa denominator
  `1/(ik+z_{αβ})` of eq (21), (ii) the argument evaluation `A(−iy)|_{y=iz} = A(z)` (`neg_I_mul_I_mul`:
  `−i·(iz)=z`) that turns `A(−iy)` into `Aⱼₙ(zᵢₙ)`, `Aᵢₘ(zₘⱼ)`, `Aᵢₘ(zₘₙ)Aⱼₙ(zₘₙ)`, and (iii) the
  `−E(k)…E(k)` sign flip. Corollaries `residue_yukawa_pole` (`g≡1 ⇒ −1/(ik+z)`) and
  `residue_yukawa_first_term` (`−K·Res ⇒ +K/(ik+z)`, the diagonal `bᵢⱼ` leading term of eq 21).

  **Sole hypothesis `iz ≠ k`** (physically `z=z_{ij}>0` real, `k` real ⇒ automatic), which by itself
  already forces `ik+z ≠ 0` (since `(iz−k)i = −(ik+z)` and `iz−k ≠ 0`, `i ≠ 0`) — no separate
  non-vanishing assumption on the Yukawa denominator. **No contour axiom**: a *single* simple pole's
  residue is just a punctured limit, so this is ordinary `Tendsto` complex analysis. Axiom-clean
  (`propext, Classical.choice, Quot.sound`).

* **(3, contour-sum step) done** — `LeanCode/Analysis/ContourSumUpperHalfPlane.lean` (NEW,
  2026-08-04, namespace `FMSA.MixtureRDF`). The other half of eq (19): the `∫dy/(y−k)` inversion
  equals the finite **sum** of the per-pole residues. **`improper_integral_eq_sum_residues_upperHalfPlane`**
  — the general engine: for any `f` with finitely many simple poles `c' i` strictly in the *open* UHP
  (residue factor `g i`, `f = g i/(·−c' i)` near `c' i`), holomorphic on the rest of the closed UHP off
  a countable `s`, with a vanishing upper-arc integral (`harc`, Jordan-type), `∫_{−R}^{R} f → Σᵢ 2πi·g i (c' i)`.
  Proof mirrors `fourier_kernel_one_pole`'s tail: `∫ = Σ − arc(R)` eventually (from the half-disk residue
  formula `halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles`, with the R-dependent
  `hinside`/`hc`/`hd` discharged for `R` large via `eventually_gt_atTop` + `‖z‖≤‖z−c'i‖+‖c'i‖<R` +
  `|z.im−(c'i).im|≤‖z−c'i‖<r'i<(c'i).im`), arc → 0, so `∫ → Σ`. **This GENERALIZES the project's
  single-kernel `fourier_kernel_one_pole`/`fourier_kernel_finite_poles`** (which were fixed to
  `e^{ixr}/(x−k)`) to an arbitrary integrand.  **`improper_integral_eq_sum_yukawa_residues`** — the
  bridge: specializes `c' i = i·zᵢ` with the Yukawa factor shape `g i w = ĝ i w/((w−k)·i)` and rewrites
  the conclusion into `Σᵢ 2πi·(−ĝᵢ(i zᵢ)/(i k + zᵢ))` — i.e. `2πi` times *exactly* the residue **value**
  `residue_yukawa_pole_general` computes, via `(i zᵢ−k)·i = −(i k + zᵢ)`.  So the two halves of task
  (3) — residue **value** + contour **sum** — are now explicitly composed.  **`#print axioms` on both =
  `halfDiskBoundary_eq_sum_of_small_circles` + std-3** — only the ONE accepted contour axiom (the same
  one `fourier_kernel_one_pole` and the argument principle already use), **no new axiom**.

  **Why only the Yukawa poles are enclosed** (justifying eq 19's "residue w.r.t. each element of `U₁`"):
  `[Q̂₀(−y)]⁻¹` is **pole-free in the UHP** — `mixtureDet_pole_free_N`, proved for all `N` — so closing
  the contour upward encloses exactly the simple poles `y = i zᵢⱼ` of `U₁(y)`.  This is fed to the engine
  as `hc`/`hd` (holomorphy off the Yukawa balls).

* **(3a, leading term hc/hd/harc) done** — `LeanCode/YukawaOZ/MixtureYukawaContourTerm.lean` (NEW,
  2026-08-04). Discharges the engine's *integrand-specific* inputs for the **leading eq (20) term** of a
  fixed RDF entry `{Ĥ₁(k)}ᵢⱼ` (the `[Q̂₀]⁻¹ ≈ I` contribution) — a complete, end-to-end contour sum with
  NO remaining hypotheses beyond state-point positivity.  **KEY: the leading term is exponential-free.**
  With `E(−y)ₘₘ = e^{iyRₘ/2}`, `U₁(y)ᵢⱼ = Kᵢⱼ e^{−iyRᵢⱼ}/(iy+zᵢⱼ)`, and the **additive-diameter identity**
  `Rᵢⱼ = Rᵢ/2 + Rⱼ/2`, the outer `E`'s cancel `U₁`'s exponential exactly:
  `E(−y)ᵢᵢ·U₁ᵢⱼ·E(−y)ⱼⱼ = Kᵢⱼ/(iy+zᵢⱼ)` — a **single** simple Yukawa pole, **no exponential** ⇒ `O(1/y²)`
  decay ⇒ the arc bound is elementary (arc length `πR` × `O(1/R²)` → 0), **no Jordan lemma needed**.
  **`contourSum_leading_term`** (hyps `0<r0`, `r0 < Im(iz)`, `Im k < 0`) proves
  `∫_{−R}^{R} K/((y−k)(iy+z)) dy → 2πi·(−K/(ik+z))` (= eq 21's leading `bᵢⱼ` term after the `−E(k)…E(k)`
  sign) by discharging: **hc** (`ContinuousOn.div`, denom `≠0` since `iy+z = i(y−iz) ≠0` off the pole ball
  and `y≠k` as `Im y ≥ 0 > Im k`), **hd** (`DifferentiableAt.div`, same), **harc** (`squeeze_zero_norm'`
  by the `4‖K‖/R` bound: `‖(iR e^{iθ})•f‖ = R‖f‖ ≤ R·4‖K‖/R² = 4‖K‖/R`, using `‖w−k‖,‖iw+z‖ ≥ R/2` for
  `R ≥ 2‖k‖,2‖z‖`), then feeds `improper_integral_eq_sum_yukawa_residues` at `ι = Fin 1`.  `#print axioms`
  = `halfDiskBoundary_eq_sum_of_small_circles` + std-3 (`set_option maxHeartbeats 1200000` for the one
  heavy engine application).  **`k` placed just below the axis (`Im k<0`)** ⇒ no on-contour pole (the
  Plemelj lower boundary value), keeping the engine's open-UHP hypothesis clean.

* **(3a-rest, holomorphy of `[Q̂₀]⁻¹` — the `A(−iy)`-term analytic core) done** —
  `LeanCode/Analysis/MatrixInverseHolomorphic.lean` (NEW, 2026-08-04, namespace `FMSA.MatrixHolo`). The
  remaining eq (20) terms carry `A(−iy) = 2π√(ρρ)W(−iy)/(Δ det(−iy))` = the entries of `[Q̂₀(−y)]⁻¹` (via
  the closed-form inverse), so their `hc`/`hd` need the **UHP holomorphy of the matrix inverse**. Proved
  **entirely generally** (no Baxter structure): if every entry `z ↦ (M z) a b` is `DifferentiableAt w` and
  `det (M w) ≠ 0`, then every inverse entry `z ↦ (M z)⁻¹ i j` is `DifferentiableAt w`. Chain via `inv_def`
  (`A⁻¹ = A.det⁻¹ʳ • A.adjugate`): **`differentiableAt_matrix_det`** (Leibniz `det_apply` — sum over perms
  of entry products, `DifferentiableAt.sum`/`.finsetProd`/`.const_smul`), **`differentiableAt_matrix_adjugate`**
  (`adjugate A i j = det (A.updateRow j (e i))`, a const-row update stays holomorphic), then
  **`differentiableAt_matrix_inv`** (`Ring.inverse (det) = (det)⁻¹` via `Ring.inverse_eq_inv'`, holomorphic
  where `det ≠ 0`, times the adjugate). Corollaries **`differentiableAt_matrix_inv_comp_neg`** (the exact
  `[Q̂₀(−y)]⁻¹` shape, chain rule with `y ↦ −y`) and **`continuousAt_matrix_inv`** (for the engine's `hc`).
  **`#print axioms` = std-3 only** — completely axiom-clean, no contour axiom (pure Mathlib calculus).

  **What still remains to wire this to the physical `Q̂₀`** (concrete-`Q̂₀` assembly): (i) an analytic
  representative of `q0_entry_c` at `s=0` — **DONE**, see next bullet; (ii) matching the **det-orientation**
  of `mixtureDet_pole_free_N` (`det (Q0_mat_c_phys (I·z)) ≠ 0` for `Im z < 0`, i.e. `Re > 0`) to the contour
  variable `−y` in the closed UHP; (iii) the **arc bound** for the `A(−iy)` terms, where the
  additive-diameter cancellation must still beat the `W/det` growth.

* **(3a-rest-i, `s=0` analytic representative) done** — `LeanCode/HSMixture/Q0ComplexRepr.lean` (NEW,
  2026-08-05, namespace `FMSA.Q0Complex`). `q0_entry_c` carries `1/s²`, `1/s³` whose `s=0` singularity is
  *removable* (numerators vanish to matching order) but the literal expression is undefined there — and the
  contour crosses `y = 0`. **`q0_entry_c_repr`** = `Function.update (q0_entry_c ·) 0 (limUnder (𝓝[≠]0) …)`
  (redefine at `0` to the removable limit), with **`q0_entry_c_repr_eq_of_ne`** (agrees with `q0_entry_c`
  for `s≠0`, so all existing `q0_entry_c`/`Q0_mat_c` theorems transfer + the integral is unchanged, `{0}`
  null) and **`differentiable_q0_entry_c_repr`** (entire — `DifferentiableAt` everywhere). Removable point
  by Riemann via **boundedness** (`differentiableOn_update_limUnder_of_bddAbove`, so *no explicit limit
  value needed*): on `‖s‖ < 1/(1+‖σ‖)` (⇒ `‖sσ‖<1`) the two pole pieces are bounded by `‖σ‖²`, `‖σ‖³`
  from the `exp` Taylor remainders **`Complex.norm_exp_sub_one_sub_id_le`** (`‖eᶻ−1−z‖≤‖z‖²`) and
  **`Complex.exp_bound`** (`n=3`, constant `4/18≤1`); off-`0` differentiability by `fun_prop` with
  `s²,s³≠0`; the `s≠0` case of "entire" glued via `Function.update_of_ne` + `congr_of_eventuallyEq`.
  **`#print axioms` = std-3** — fully axiom-clean. Reusable atoms: `normP2_le`, `normP3_le`,
  `differentiableAt_q0_entry_c_of_ne`, `norm_q0_entry_c_le`.

* **(3a-rest-ii, det orientation) done** — `LeanCode/HSMixture/Q0DetContourOrientation.lean` (NEW,
  2026-08-05, namespace `FMSA.MixtureGenN`). Matches the project's two Baxter-det non-vanishing results
  to the contour region (closed UHP). **Convention pinned:** `Q̂₀(k) = Q0_mat_c_phys (I·k)` (kernel
  `e^{−ikσ}=e^{−sσ}`, `s=ik`; cf. `BaxterRenewalDecay`/`Splitting`, `z=ik`), so `[Q̂₀(−y)]⁻¹` has argument
  `Q0_mat_c_phys (I·(−y))` with `Re(I·(−y)) = Im y`. **`det_Q0_contour_ne_zero_of_im_pos`** (open UHP
  `Im y>0` ↦ `Re>0`): `mixtureDet_pole_free_N` at `z=−y` (`Im(−y)=−Im y<0`). **`det_Q0_contour_ne_zero`**
  (closed UHP minus origin, `Im y≥0, y≠0`): open UHP as above + real axis `Im y=0, y≠0` (⇒ `y.re≠0`,
  argument purely imaginary `I·(−y.re)`) via **`pyhs_mixture_no_spinodal`** (the no-spinodal physics
  axiom, `det Q̂₀(I·k)≠0` real `k≠0`). Pole `y=iz` ⇒ argument `z>0` real, det≠0 (real axis) — consistent.
  **`#print axioms` = std-3 + `zeroFree_lowerHalfPlane_of_homotopy` (math) + `pyhs_mixture_no_spinodal`
  (physics)** — exactly the two axioms `mixtureDet_pole_free_N` already uses, **NO new axiom** (even the
  open-UHP lemma inherits the physics axiom, since it is the real-axis boundary datum of the pole-free
  proof). **Origin `y=0`** = the `k=0` compressibility (`det Q̂₀(0)`, removable value in
  `Q0MomentGeOne`/`MixtureDetOrigin`) — the one remaining point, also where `q0_entry_c` is `s=0` junk
  (handled by the `Q0ComplexRepr` representative). For `y≠0` the argument `I·(−y)≠0` ⇒ raw `Q0_mat_c_phys`
  and the entire representative agree, so these det statements transfer to the engine's representative matrix.

* **(3a-rest-iii, `A(−iy)` arc bound — the reusable mechanism) done** —
  `LeanCode/YukawaOZ/YukawaArcBound.lean` (NEW, 2026-08-05, namespace `FMSA.MixtureRDF`).
  **`arc_integral_tendsto_zero`**: for ANY numerator `g` bounded by `M ≥ 0` on the upper arc, the arc
  integral of `g(y)/((y−k)(iy+z))` → 0 (integrand `O(M/R²)`, arc length `πR` ⇒ `O(M/R) → 0`; same
  `‖(iRe^{iθ})•·‖ = R·‖·‖ ≤ 4M/R` squeeze as the leading-term `harc`, now with a variable bounded `g`).
  **Fully axiom-clean (std-3).**  This **generalizes** the leading-term arc bound (`g ≡ K`, constant) to
  any bounded numerator, and reduces the `A(−iy)`-term arc bound to ONE question: is the numerator
  `K·A(−iy)` (resp. `K·A(−iy)·A(−iy)`) bounded on the arc?

  **KEY finding — the numerator bound is NOT entrywise (the remaining concrete work).**  On the arc
  `y = Re^{iθ}` the Baxter argument `s = I·(−y)` has `Re s = R sinθ ≥ 0`, so the diagonal kernels
  `e^{−sσ}` decay — BUT the unlike-pair factor `e^{−λs}` with `λ = (σⱼ−σᵢ)/2 < 0` **grows** like
  `e^{|λ|R sinθ}`.  So `q0_entry_c`, hence `A(−iy) = [Q̂₀(−y)]⁻¹ − I`, is **not** bounded entrywise on the
  arc.  Boundedness holds only for the **full product** `E(−y)[Q̂₀(−y)]⁻¹U₁(y)[Q̂₀ᵀ(−y)]⁻¹E(−y)`, where
  the additive-diameter cancellation `Rᵢⱼ = Rᵢ/2 + Rⱼ/2` kills the growing exponentials (exactly as it
  collapses the leading term to the exponential-free `K/(iy+z)`).  So the concrete-`Q̂₀` step feeding this
  lemma is that **cancellation-tamed numerator bound** — an intricate full-product estimate, not an
  entrywise one; the arc-vanishing *mechanism* is what is proved here.

* **(c, eq (21)/(22) assembly) done** — `LeanCode/HSMixture/MixtureH1Assembly.lean` (NEW, 2026-08-05,
  namespace `FMSA.MatrixQ0`). The algebraic bookkeeping turning `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` (eq 15) into the
  explicit eq (21)/(22) four-term form. **`H1_expand`** (generic): `(1+Aᵀ)·B·(1+A) = B + Aᵀ·B + B·A +
  Aᵀ·B·A` (`noncomm_ring`). **`H1_assembly_phys`**: for the physical Baxter factor, `Ĥ₁ = B₁ + Aᵀ·B₁ +
  B₁·A + Aᵀ·B₁·A` with `A = Amat := U(1−VU)⁻¹V` (the Woodbury off-identity part) — via `H1_eq_phys` +
  `Q0_mat_phys_inv_eq` (`[Q̂₀]⁻¹ = 1+A`) + `[Q̂₀ᵀ]⁻¹ = ([Q̂₀]⁻¹)ᵀ = 1+Aᵀ` (`transpose_nonsing_inv`) +
  `H1_expand`. **`H1_assembly_phys_apply`** (entrywise, = Tang & Lu eq (21) verbatim, verified the index
  structure against the paper): `{H₁}ᵢⱼ = {B₁}ᵢⱼ + ∑ₘ Aₘᵢ{B₁}ₘⱼ + ∑ₙ {B₁}ᵢₙAₙⱼ + ∑ₙ∑ₘ Aₘᵢ{B₁}ₘₙAₙⱼ`
  (single `simp only [add_apply, mul_apply, transpose_apply, sum_mul]`); with `{B₁}ᵢⱼ = bᵢⱼ·e^{−ikRᵢⱼ}`
  carrying the residue `bᵢⱼ` of eq (23), built from the per-pole residue **values**
  (`MixtureYukawaResidue`). **`#print axioms` = std-3** — fully axiom-clean pure matrix algebra.

* **(b, `y=k` ½-Plemelj) done** — `LeanCode/Analysis/SokhotskiPlemeljLower.lean` (NEW, 2026-08-05).
  The on-contour `y=k` real-axis pole. The half-disk axiom needs poles in the *open* UHP; the
  leading-term work placed `k` in the open *lower* half-plane (`Im k<0`), so the physical real-`k` value
  is the **lower** boundary limit `Im k→0⁻`. The project had only the upper axiom
  (`sokhotski_plemelj_upper`, `P.V.+iπ·g(x₀)`); added the two pieces (b) needs, both DERIVED — **no new
  axiom** (only `sokhotski_plemelj_upper` + std-3). **`sokhotski_plemelj_lower`** (`P.V.−iπ·g(x₀)`): by
  **conjugation** — apply the upper axiom to `f := conj∘g`, then conjugate the whole `Tendsto`; `conj`
  commutes with the integral (`integral_conj`), turns the lower kernel `1/(x−x₀+iε)` into the upper
  `1/(x−x₀−iε)`, and flips `+iπ`→`−iπ` (the derivation the axiom docstring flags as intended).
  Plumbing: `Integrable.conj` via `.norm.mono'`+`RCLike.norm_conj`; PV-conj via `←integral_conj`+
  `setIntegral_congr_fun`; `Function.comp` mismatch closed by `Tendsto.congr`. **`sokhotski_plemelj_jump`**:
  `[upper]−[lower] = 2πi·g(x₀)` (the full residue; each side carries the `±iπ` half) — the algebraic
  content of eq (14)'s `½[Q̂₀(−k)]⁻¹U₁(k)[Q̂₀ᵀ(−k)]⁻¹` boundary term (the `½` of that full residue), which
  added to the closed-contour Yukawa residue sum reproduces the eq (14) principal value.

* **(iii-core, cancellation-tamed numerator — the two analytic ingredients) done** —
  `LeanCode/HSMixture/ArcAmplitudeBound.lean` (NEW, 2026-08-05, namespace `FMSA.MixtureRDF`).
  **CORRECTED the (iii) picture**: the eq (20) `A(−iy)` is NOT the raw inverse entry (which carries the
  growing `e^{iyλ}`, `λ<0` unlike pairs) — it is the **amplitude** `2π√(ρρ)W(−iy)/(Δ det(−iy))`, the
  exponential having been removed by the `E(−y)` wrapping. Two ingredients: **(A) the exponent
  cancellation** — each eq (20) term's net `e^{iy·(…)}` exponent `σᵢ/2 + λᵢₘ − Rₘₙ + λⱼₙ + σⱼ/2`
  (`Rₐᵦ=(σₐ+σᵦ)/2`, `λₐᵦ=(σᵦ−σₐ)/2`) **vanishes identically** — `expSum_{diag,left,right,both}_eq_zero`
  (`by ring`, the additive-diameter cancellation, structural key; verified all four index patterns);
  **(B) the far-region `φ` bounds** — `normP2_arc_le` (`‖(1−sσ−e^{−sσ})/s²‖ ≤ 2+‖σ‖`) and `normP3_arc_le`
  (`‖(1−sσ+(sσ)²/2−e^{−sσ})/s³‖ ≤ 2+‖σ‖+‖σ‖²/2`) for `‖s‖≥1`, `Re(sσ)≥0` (the arc: `s=−iy`,
  `Re s=R sinθ≥0` ⇒ `‖e^{−sσ}‖≤1`) — the **far-region duals** of `Q0ComplexRepr.normP2_le`/`normP3_le`
  (which bound the same `φ` near `s=0`); `W`,`det` are built from these same `φ`. Plus the **decay**
  versions `normP2_arc_decay`/`normP3_arc_decay` (`≤C/‖s‖ → 0`, needed for `det→1`). **(C) the assembly
  logic**: `norm_ge_of_norm_sub_one_le` (`‖det−1‖≤d ⇒ ‖det‖≥1−d`, so `det→1 ⇒` bounded below) +
  `amplitude_norm_le` (`‖c·W/(Δ·det)‖ ≤ ‖c‖Wb/(‖Δ‖D)` given `‖W‖≤Wb`, `Δ≠0`, `‖det‖≥D>0`) — turns
  `W`-bounded + `det`-below into the numerator bound `arc_integral_tendsto_zero` consumes. **All
  axiom-clean (std-3).** **Remaining for the FULL A-term arc bound**: supply the concrete `‖W(−iy)‖≤Wb`
  and `‖det(−iy)−1‖≤d` by expanding Tang & Lu's explicit Appendix `W`/`det` — note these explicit
  formulas are **not yet in the project** (whose Baxter machinery is Woodbury-based, `Q0_mat_phys_inv_eq`,
  rather than the `2π√W/det` Appendix form); introducing them is the one remaining piece.

* **(iii-Appendix, explicit `W`/`det` formulas) done** — `LeanCode/HSMixture/AppendixWDet.lean` (NEW,
  2026-08-05, namespace `FMSA.MixtureRDF`). Introduces Tang & Lu p. 95's explicit Appendix formulas (NOT
  previously in the project — its Baxter machinery is Woodbury-based, not the `2π√W/det` form). Defs
  (`s = ik = −iy`): **`phi1`** `=(1−sR−e^{−sR})/s²`, **`phi2`** `=(1−sR+(sR)²/2−e^{−sR})/s³`, **`xiMom`**
  `ξᵢ=∑ₘρₘRₘⁱ`, **`Delta`** `Δ=1−(π/6)ξ₃`, **`Wtl`** (the exact 4-term `Wᵢⱼ(ik)`), **`detTL`** (the exact
  3-term `det(ik)`, the 2×2-reduced Baxter det). Bounds: **`norm_phi1_le`**/**`norm_phi2_le`** (arc decay
  `≤(…)/‖s‖→0`, specialising `normP{2,3}_arc_decay` at `σ=R`, casts via `Complex.mul_re`+`ofReal_re/im`);
  **`norm_weighted_phi1_sum_le`**/**`norm_weighted_phi2_sum_le`** — ANY finite `ρ`-weighted `φ`-sum (the
  shape of every `W`/`det` term) is `≤(∑ₘ‖wₘ‖(…))/‖s‖ → 0` (`norm_sum_le`+`norm_mul`+the φ bound), the
  reusable tool for `‖Wtl‖→0` and `‖detTL−1‖→0`. **All axiom-clean (std-3).**

* **(iii-detbound, the `det → 1` bookkeeping bound) done** — same file, 2026-08-05.
  **`norm_detTL_sub_one_le`**: `‖detTL s ρ R − 1‖ ≤ Cdet/‖s‖` (`Cdet` an explicit constant, for `‖s‖≥1`,
  `0≤Re s`, `∀m 0≤R m`), so `det(−iy) → 1` on the arc (⇒ bounded below by `norm_ge_of_norm_sub_one_le`).
  Reusable bookkeeping lemmas (all axiom-clean std-3): **`norm_sum_le_of_termwise`** (`∀m ‖fm‖≤gm/‖s‖ ⇒
  ‖∑f‖≤(∑g)/‖s‖`), **`norm_phi1_le_const`** (crude `‖φ₁‖≤2+R`), **`norm_const_mul_le`** (pull a constant
  coeff out, `(mul_div_assoc _ _ _).symm` to avoid it hitting the inner `2π/Δ`), **`norm_rhoWeighted_phi{1,2}_sum_le`**
  (single `ρ`-weighted `φ`-sums with per-`m` coeff `κ`, via `sum_congr`-rearrange + the weighted helper),
  **`norm_rhoRho_phi1_phi1_dsum_le`** (the double `φ₁·φ₁` sum, one crude + one decaying `φ₁`). The three
  `detTL` terms map to these; the final glue is `norm_sub_le`×2 + `add_div`×2 + the three term bounds.
  **Pitfalls fixed:** `ρ` implicit not pinned by `hs/hre/hR/κ` ⇒ pass `(ρ := ρ)`; a `-/` inside
  `single-/double-` in a docstring closed the doc comment early.

* **(iii-Wbound, the `‖Wtl‖ ≤ Wb` bookkeeping bound) done** — same file, 2026-08-05.
  **`norm_Wtl_le`**: `‖Wtl s ρ R i j‖ ≤ Wb/‖s‖` (`→ 0`), the exact analogue of the det bound for the
  4-term `Wtl`. New shapes vs det: **`norm_phi{1,2}_mul_le`** (`‖φ_k(R)·c‖ ≤ ‖c‖(…)/‖s‖`, a single `φ`
  times a constant — `Wtl` terms 1, 2) and **`norm_c_phi1_mul_le`** (`‖c₀·φ₁(R₀)·X‖ ≤ ‖c₀‖(2+R₀)B/‖s‖`
  from `‖X‖≤B/‖s‖` — `Wtl` term 3, a `φ₁` *outside* a `φ₁`-sum: crude + decaying); term 4 is a
  `const·φ₂`-sum (`norm_const_mul_le`). Glue: `unfold Wtl` + `simp only [add_div]` + `norm_add_le`×3.
  **All axiom-clean (std-3).** **Pitfall:** the def's `(R i + R j)/2` unfolds/elaborates to
  `R i/2 + R j/2`, and `simp only [Wtl]` normalises the same way — the proof must use that form (and
  `unfold Wtl` rather than a hand-written `hsum`).  **So `‖W‖ ≤ Wb` and `‖det − 1‖ ≤ d` are both in
  place** — feeding `norm_ge_of_norm_sub_one_le` + `amplitude_norm_le` bounds the amplitude `A(−iy)`.

* **(bridge, `N=1` Appendix bridge) done** — `LeanCode/YukawaOZMix/AppendixBridgeN1.lean` (NEW,
  2026-08-05, namespace `FMSA.MixtureRDF`). The final connective piece — Tang & Lu's inverse formula
  `{[Q̂₀]⁻¹}ᵢⱼ = δᵢⱼ + 2π√(ρᵢρⱼ)Wᵢⱼ/(Δ det)·e^{−ikλᵢⱼ}` — proved at **`N=1`** (scalar: `det=q0`, `λ₀₀=0`),
  tying `Wtl`/`detTL` to the project's ACTUAL Baxter entry `q0_entry_c` (with the real PY coefficients).
  **`bridge_N1`**: `q0_entry_c s (σ0) 0 (Q0phys) (Qppphys) (rhoGeoPhys) 1 = 1 − 2π√(ρ₀ρ₀)·Wtl₀₀/vacMix`;
  **`bridge_N1_inv`**: `q0⁻¹ = 1 + 2π√(ρρ)Wtl₀₀/(vacMix·q0)` (the actual bridge form, `det=q0`). **Key
  facts:** `Delta ρ σ = vacMix ρ σ` (both `1−(π/6)∑ρσ³`, `norm_cast`); at `N=1` the two `∑ₘ` `Wtl` terms
  vanish (`(σ₀−σ₀)=0`, `Fin.sum_univ_one`+`sub_self`); the physical PY coefficients are **exactly** Tang
  & Lu's `W` coefficients (`ρ₀Q''phys = 2πρ₀(1+2η)/vac²`, `ρ₀Q'phys = 2πρ₀(σ₀+πξ₂σ₀²/4vac)/vac`). Proof
  = unfold everything + `push_cast` (push `ofReal` inside so `field_simp` sees the `vac⁻¹`) + `field_simp`
  (`s²`,`s³`,`vac`) + `ring` — `√(ρ₀²)` appears identically both sides (as `rho_geo` and `2π√(ρρ)`), so no
  `ρ₀≥0` needed. **`#print axioms` = std-3** — fully axiom-clean.
  **`detTL_eq_q0_N1`** (2026-08-05, denominator side): at `N=1`, `detTL s ρ σ = q0_entry_c … 1` = the
  ACTUAL scalar determinant (`det = the single entry`). So the `N=1` bridge is now closed to the actual
  objects on **both** sides — numerator via `bridge_N1`, denominator via this — giving
  `[Q̂₀]⁻¹ = 1 + 2π√(ρρ)W₀₀/(Δ·detTL)` with `detTL = det Q̂₀`. Proof: same unfold + `push_cast` +
  `field_simp` + `ring`, but now `√(ρ₀²)=ρ₀` is used explicitly (`hsqrt` via `Real.sqrt_mul_self hρ`,
  needs `hρ : 0 ≤ ρ 0`) because `detTL`'s `∑ₘ` `W`-style terms carry a bare `ρ` while `q0_entry_c` carries
  `rhoGeoPhys = √(ρρ)`. **`#print axioms` = std-3.**

* **(origin) `y=0` compressibility point done — axiom-clean, NO physics axiom** —
  `LeanCode/HSMixture/Q0DetContourOrientation.lean` (2026-08-05, build 8735). The last contour point:
  `det_Q0_contour_ne_zero` covers the closed UHP **minus the origin** (`y≠0`, via the two pole-free
  axioms); the origin `y=0` (`s=0`, where the `q0_entry_c` kernel is Lean junk) is closed by the
  **removable value**. **`det_Q0_contour_origin_ne_zero`** (general `N`): if `det Q̂₀(s) → c` as
  `s → 0` (`𝓝[≠] 0`), then `c ≠ 0` — in fact `Re c ≥ 1`, the `k=0` structure factor / isothermal
  compressibility. **Key point: this needs NO physics axiom** — the `≥1` bound is *proved* algebra
  (`Q0_mat_phys_det_ge_one_N` ⇐ `moment_key`), whereas the real-axis `y≠0` needs
  `pyhs_mixture_no_spinodal` (which covers only `k≠0`). So the two together cover the **whole** closed
  UHP: raw value ≠ 0 off the origin, removable value ≠ 0 at it. Supporting: **`Q0_mat_phys_det_ge_one_N`**
  (new in `Q0MomentGeOne.lean`, general-`N` det ≥ 1 — the Woodbury reduction gives the *same* `2×2`
  reduced matrix for every `N`, so `Q0_moment_det_ge_one`'s general-`N` bound lifts; the old `Fin 2`
  `Q0_mat_phys_det_ge_one` now delegates to it) and **`Q0_mat_c_phys_ofReal`** (general-`N` cast
  `Q̂₀(z:ℂ) = (Q0_mat_phys z).map ofReal`, the contour-namespace analogue of `MixtureDetOrigin`'s
  `Fin 2` one). Proof mirrors `detF_Pdens_origin_ne_zero` but on `Q0_mat_c_phys` directly and general
  `N`: `ofReal`-compose the limit onto `𝓝[>] 0`, `ge_of_tendsto` with the `≥1` bound, `Re c ≥ 1 > 0`.
  **坑**: goal orientation is *flipped* vs `MixtureDetOrigin.detF_Pdens_ofReal`, so `RingHom.map_det`
  is used **without** `.symm` (with `.symm` the matrix stays a metavar ⇒ `Fintype ?m` stuck); supply the
  matrix explicitly. `simp` on `det` with `N` a variable gets `Fintype ?m`-stuck ⇒ apply `ge_of_tendsto`
  to the composed `Complex.re ∘ …` and rewrite `Complex.ofReal_re` *inside* `filter_upwards`, not via a
  `funext` det-equation. **`#print axioms` = std-3** for both. **What this closes / does NOT:** it closes
  the *determinant* non-vanishing at the origin (⇒ `[Q̂₀]⁻¹` has no pole at `y=0`, the contour integrand
  is regular there). It does not construct the representative *matrix* inverse at the origin — that would
  reuse `Q0ComplexRepr`'s entry representative entrywise and is only needed if a downstream lemma wants
  the actual `k=0` inverse value rather than pole-absence.

* **(bridge, general `N` — complex rank-2 / Woodbury STRUCTURE done)** —
  `LeanCode/HSMixture/Q0ComplexRankTwo.lean` (NEW, 2026-08-05, namespace `FMSA.ComplexRankTwo`,
  build 8736). The complexification blocker of the general-`N` bridge is **resolved**: the complex-`s`
  analogue of the project's real-`z` Woodbury machinery (`Q0DetRankTwo` + `MixtureQ0Inverse`). Each
  object is the real one with `p1→φ1`, `p2→φ2`, `z→s` (verified: `fFun = (2π/Δ)(σᵢ/2·φ1+φ2)`,
  `gFun = (2π/Δ)((½+πξ₂σᵢ/4Δ)φ1+(πξ₂/2Δ)φ2)`). Ships: **`fFunC`/`gFunC`** (complex Woodbury columns) +
  **`fFunC_gFunC_eq`** (`field_simp; ring` over `ℂ`), **`UmatC`/`VmatC`** + **`UV_apply_C`**
  (√ρ + exp merge via `Real.sqrt_mul`/`Complex.exp_add`), **`Q0_mat_c_phys_eq_one_sub_mul`**
  (`Q̂₀(s) = I−UₒVₒ`, complex rank-2 — closes to `simp only` unfolding `q0_entry_c`),
  **`det_Q0_mat_c_phys_eq_two_by_two`** (`det Q̂₀(s) = det(I−VₒUₒ)`, `Matrix.det_one_sub_mul_comm`), and
  **`Q0_mat_c_phys_inv_closed_form`/`_inv_eq`** (`[Q̂₀(s)]⁻¹ = I + Uₒ(I−VₒUₒ)⁻¹Vₒ`, mirrors
  `Q0_mat_phys_inv_closed_form`'s `expand`+`hVU`+`abel`, with invertibility of the `2×2` now a
  **hypothesis** `IsUnit (det Q̂₀(s))` — the complex `2×2` is singular at HS poles, unlike real `z`
  where `det ≥ 1`; `det_Q0_contour_ne_zero`/`_origin` supply it on the contour region). **All std-3.**
  **This is Tang & Lu's "unique difficulty"** (inverse of an arbitrary `n×n` reduced to a fixed `2×2`)
  for the complex contour argument.

* **(bridge, general `N` — denominator match REDUCED to a scalar sum identity)** —
  `LeanCode/HSMixture/Q0ComplexDetMatch.lean` (NEW, 2026-08-05, `FMSA.ComplexRankTwo`, build 8737).
  Reduces the denominator bridge `detTL = det Q̂₀(s)` (combined with `det_Q0_mat_c_phys_eq_two_by_two`)
  to the `2×2` scalar identity `det(I−VₒUₒ) = detTL`, and supplies the ingredients (all std-3):
  **`p1c_eq_phi1`/`p2c_eq_phi2`** (the `Q0ComplexRankTwo` `p1c`/`p2c` = `AppendixWDet` `phi1`/`phi2`,
  `rfl`), **`p2c_eq_p1c`** (the Tang & Lu simplifying identity **`φ2 = φ1/s + σ²/2s`** — the
  term-shuffle engine; `det(I−VU)` and `detTL` are NOT equal as polynomials in independent `{φ1,φ2}`),
  **`VU_C_apply`** + **`VU00`/`VU01`/`VU10`/`VU11`** (the four reduced entries `(VₒUₒ)_kl = Σρ(1|σ)
  (fFunC|gFunC)`, exp/`√ρ` cancelled), and **`detVU_expand`** = Tang & Lu Appendix **A6**
  (`det(I−VₒUₒ) = (1−Σρ fFunC)(1−Σρσ gFunC) − (Σρ gFunC)(Σρσ fFunC)`). The A6 = A7 (`= detTL`) target
  is **verified numerically** (`9e-16`, random `N=3`, complex `s`), and the tractable closure route is
  documented: the key cancellation `b_q = φ1_q/2 + (πξ₂/2Δ)a_q` ⟹ `fFunC_p gFunC_q − gFunC_p fFunC_q =
  (2π²/Δ²)(a_p φ1_q − a_q φ1_p)` (the `ξ₂` cancels antisymmetrically), then substitute `φ2 = φ1/s +
  σ²/2s`, expand `ξ₃ = Σρσ³`, and match after a `p↔q` reindex.

* **(bridge, general `N` — A6 → A7 closure: math crux done, ingredients verified)** —
  `LeanCode/HSMixture/Q0ComplexDetMatchClose.lean` (NEW, 2026-08-05, `FMSA.ComplexRankTwo`,
  build 8738). The A6 (`detVU_expand`) and A7 (`detTL`) both reduce to a common canonical
  `1 − (2π/Δ)Σρ·GS + (π²/Δ²)Σ∑ρρ·sd`, `GS(m)=σ_mφ1+φ2`, differing only in the double summand
  (`A6sd` vs `detTLsd`). **All mathematically substantive ingredients verified (std-3):**
  **`FG_antisym`** (the `ξ₂`-cancellation `fFunC_p gFunC_q − gFunC_p fFunC_q = (2π²/Δ²)(a_pφ1_q −
  a_qφ1_p)`, pure `ring`), **`detVU_double`** (A6 products → double sum), **`fFunC_eq`/`gFunC_relation`**
  (`fFunC=(2π/Δ)a`, `gFunC=(π/Δ)φ1+(πξ₂/2Δ)fFunC`), **`sum_distrib_prod`/`sum_distrib_prod2`** (pull a
  `Σg` out of a single sum into a double sum), **`aFun`/`A6sd`/`detTLsd`** (canonical summands), and
  **`sdMatch`** — THE crux: `Σ∑ρρ A6sd = Σ∑ρρ detTLsd` via `Finset.sum_comm` symmetrisation (the
  summands are NOT equal pointwise, but `A6sd(m,n)+A6sd(n,m)=detTLsd(m,n)+detTLsd(n,m)` is a `ring`
  identity after `p2c_eq_p1c` `φ2=φ1/s+σ²/2s`, and `ρ_mρ_n` is symmetric). Whole identity **numerically
  confirmed** (A6=A7 to `9e-16`; symmetrised summands agree to `1e-16`, random `N=3/4`, complex `s`).

* **(bridge, general `N` — A6 → A7 DENOMINATOR CLOSURE DONE)** — `Q0ComplexDetMatchClose.lean`
  (2026-08-05, build 8738). **`det_eq_detTL`** (general `N`, complex `s`, axiom-clean std-3):
  `det(I−VₒUₒ) = detTL`. Chain: `detVU_expand` (A6) ▸ **`A6toCanon`** ▸ `sdMatch` ▸ **`detTLtoCanon`**
  (A7). Both A6 and A7 reduce to the canonical `1 − (2π/Δ)Σρ·GS + (π²/Δ²)Σ∑ρρ·sd`, `GS(m)=σ_mφ1+φ2`,
  and `sdMatch` matches the two summands. **`detTLtoCanon`**: bridge phi/Δ/ξ, `sum_distrib_prod`/`_prod2`
  on the `ξ₂`/`ξ₃`-products, combine (`hS` singles, `hDbl` doubles via a `neg_sum2` helper).
  **`A6toCanon`**: `detVU_double`+`FG_antisym` for the product double, `fFunC_eq`/`gFunC_relation` +
  `push_cast [hx2c]` to expose `ξ₂=Σρσ²`, `sum_distrib_prod2` on `SsG`'s product, combine (`hS`/`hDbl`).
  With `det_Q0_mat_c_phys_eq_two_by_two` (`Q0ComplexRankTwo`) this is the general-`N` Appendix
  **denominator** bridge `det Q̂₀(s) = detTL`, closed.

* **(bridge, general `N` — NUMERATOR side, structural reduction done)** — `Q0ComplexDetMatchClose.lean`
  (2026-08-05). The off-identity entry of `[Q̂₀]⁻¹ = I + Uₒ(I−VₒUₒ)⁻¹Vₒ` is
  `√(ρᵢρⱼ)e^{−sλᵢⱼ}·B_ij/detTL`, `B_ij = fFunC_i(1−m₁₁) + gFunC_i·m₁₀ + σⱼ(fFunC_i·m₀₁ + gFunC_i(1−m₀₀))`
  (the `2×2` `adj(I−VₒUₒ)`, `m_kl = (VₒUₒ)_kl`). **`Bsum_combine`** (NEW, std-3): the four `m_kl`-sum
  terms of `B_ij` combine into the single sum `Σ_p ρ_p(σⱼ−σ_p)(fFunC_i gFunC_p − gFunC_i fFunC_p)`,
  whose summand `FG_antisym` reduces to `(2π²/Δ²)(a_i φ1_p − a_p φ1_i)`. The scalar match
  **`B_ij·Δ = 2π·Wtl_ij`** is numerically confirmed (`1e-15`, random `N`, complex `s`) and is
  **single-sum, no symmetrisation** (unlike the det match): after `φ2 = φ1/s + σ²/2s` and `ξ₂`/`ξ₃`
  expansion, the non-sum parts agree at `2π(φ2_i + (σ_i+σ_j)/2·φ1_i)` and the single sums match.
  Verified the reduction chain in scratch through unfold+`p2c_eq_p1c`-subst+ξ-expansion; the final
  scalar single-sum bookkeeping (analogous to `detTLtoCanon`) is the remaining piece.

* **(bridge, general `N` — NUMERATOR scalar match DONE)** — `Q0ComplexDetMatchClose.lean`
  (2026-08-06). **`numMatch`** (general `N`, axiom-clean std-3): `B_ij·Δ = 2π·Wtl_ij`, where
  `B_ij = fFunC_i(1−m₁₁) + gFunC_i·m₁₀ + σⱼ(fFunC_i·m₀₁ + gFunC_i(1−m₀₀))` is the `2×2`
  `adj(I−VₒUₒ)` entry (off-identity of `[Q̂₀]⁻¹ = I + Uₒ(I−VₒUₒ)⁻¹Vₒ` = `√(ρρ)e^{−sλ}·B_ij/detTL`).
  Proved via **`hLHS`/`hRHS`**: both sides → `NS + Σ_p ρ_p·(summand)`, common non-sum
  `NS = 2π(φ2_i + (σᵢ+σⱼ)/2·φ1_i)`, and the summands `L_p`, `R_p` agree pointwise after `φ2 = φ1/s +
  σ²/2s` (`p2c_eq_p1c` + `field_simp; ring`). Single-sum, **no symmetrisation** (the numerator analogue
  of `det_eq_detTL`). Key technique: each side's several `ξ`/`φ`-single-sums are combined into one
  `Σ_p ρ_p·(...)` via a `show`-reshape (`Finset.mul_sum` + `← Finset.sum_add_distrib` + `sum_congr;
  ring`), leaving `NS` to match by `ring`. `Bsum_combine` (the `B` four-`m_kl`-sum → one-sum step) +
  `FG_antisym` feed `hLHS`.

* **(bridge, general `N` — FULL ENTRYWISE BRIDGE DONE)** — `Q0ComplexDetMatchClose.lean` (2026-08-06).
  **`Q0_inv_entry_bridge`** (general `N`, complex `s`, axiom-clean std-3) — the **complete general-`N`
  Tang & Lu Appendix inverse bridge**: `{[Q̂₀(s)]⁻¹}_ij = δ_ij + 2π√(ρᵢρⱼ)·Wtl_ij·e^{−sλᵢⱼ}/(Δ·detTL)`
  (hypothesis `IsUnit (det Q̂₀)`). Assembly: `Q0_mat_c_phys_inv_eq` (Woodbury `[Q̂₀]⁻¹ = I +
  Uₒ(I−VₒUₒ)⁻¹Vₒ`) + `(I−VₒUₒ)⁻¹ = detTL⁻¹•adj` (`Matrix.inv_def` + `det_eq_detTL` +
  `Ring.inverse_eq_inv`) + **`UadjV`** (`Uₒ·adj(I−VₒUₒ)·Vₒ` entrywise = `√(ρᵢρⱼ)e^{−sλ}·B_ij`, via
  `Matrix.mul_apply`+`adjugate_fin_two`+`VU00`..`VU11`+√ρ/exp merge) + **`numMatch`** (`B_ij·Δ = 2π
  Wtl_ij`); the final `eq_div_iff`+`field_simp`+`linear_combination √(ρρ)·numMatch` closes it (the
  `e^{−sλ}` cancels). **Task MML.17 momentum side is now fully closed for general `N`.**

* **(RDF `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` assembly, complex `s` — DONE)** — `Q0ComplexH1Assembly.lean`
  (2026-08-06, `FMSA.ComplexRankTwo`, all std-3). The complex-`s` first-order mixture RDF assembly
  (complex analogue of `MixtureH1Assembly`): **`Q0_mat_c_phys_H1_eq`** (eq 15: from `Q̂₀ᵀ·Ĥ₁·Q̂₀ = B₁`
  and `IsUnit(det)`, `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹`, via generic `H1_eq_of_transformed_c`),
  **`H1_assembly_c`** (eq 21 four-term `Ĥ₁ = B₁ + AmatCᵀB₁ + B₁AmatC + AmatCᵀB₁AmatC`,
  `AmatC = Uₒ(I−VₒUₒ)⁻¹Vₒ` = `[Q̂₀]⁻¹−I`, `noncomm_ring`), **`H1_assembly_c_apply`** (eq 21 entrywise
  `{H₁}ᵢⱼ = {B₁}ᵢⱼ + ∑ₘ Aₘᵢ{B₁}ₘⱼ + ∑ₙ {B₁}ᵢₙAₙⱼ + ∑ₙ∑ₘ Aₘᵢ{B₁}ₘₙAₙⱼ`), and **`AmatC_entry`**
  (the propagator entries resolved to the EXPLICIT amplitudes `Aᵢⱼ = 2π√(ρᵢρⱼ)Wtl_ij e^{−sλᵢⱼ}/(Δ
  detTL)`, via `AmatC = [Q̂₀]⁻¹−I` + `Q0_inv_entry_bridge`). So `Ĥ₁` is fully explicit.

* **(`B₁` eq(23) residue coefficients `bᵢⱼ` — DONE)** — `MixtureYukawaBij.lean` (2026-08-06,
  `FMSA.MixtureRDF`, all std-3).  The residue *mechanism* was already in `MixtureYukawaResidue`
  (`residue_yukawa_pole_general`: `Res_{y=iz}[g(y)/((y−k)(iy+z))] = −g(iz)/(ik+z)`); this file gives
  the assembled coefficient.  **`bij_eq23`** — the general eq (23) form (pair-specific decays `z_{αβ}`,
  four term-types `Kᵢⱼ`, `∑ Kᵢₙ Aⱼₙ(zᵢₙ)`, `∑ Kₘⱼ Aᵢₘ(zₘⱼ)`, `∑ₘₙ Kₘₙ Aᵢₘ(zₘₙ)Aⱼₙ(zₘₙ)`, each over
  its own `s+z_{αβ}`).  **`bij_eqz`** — the equal-decay (single `z`, Tables 1–2) specialization, with
  **`bij_eq23_const`** (`rfl`) identifying it as `bij_eq23` at constant `zmat`/propagator.
  **`bij_eqz_matrix`** — the four equal-`z` sums collapse to `bᵢⱼ(s) = {(I+A)K(I+A)ᵀ}ᵢⱼ/(s+z)` (proof:
  `simp_rw [← Finset.sum_div]` + `← add_div` combine, then matrix decomp `(1+A)K(1+A)ᵀ = K+K Aᵀ+A K+A K Aᵀ`
  via `noncomm_ring`, entries `e1/e2/e3` matched by `mul_comm`/`sum_comm`).  **`bij_eqz_residue`** — the
  **residue value** at the simple pole `s=−z`: `(s+z)·bᵢⱼ(s) = {(I+A)K(I+A)ᵀ}ᵢⱼ`.  **`bij_eq23_contact`**
  / **`bij_eqz_contact`** — Tang & Lu **eq (24) contact value** `lim_{s→∞} s·bᵢⱼ(s) =
  2π√(ρᵢρⱼ)Rᵢⱼ g¹ᵢⱼ(Rᵢⱼ)`: the real Laplace variable `s→∞` sends each `s/(s+z_{αβ})→1` (core
  `tendsto_s_div_s_add` via `(1+z·s⁻¹)⁻¹→1`, `filter_upwards`+`inv₀`), so the limit is the sum of the four
  eq (23) residue amplitudes (equal-`z`: exactly the benchmark `N = (I+A)K(I+A)ᵀ`).  **`g1Contact`** /
  **`g1Contact_eqz`** — the **first-order contact RDF `g¹ᵢⱼ(Rᵢⱼ)`** itself: eq (24) solved through, the
  contact value over `contactPre = 2π√(ρᵢρⱼ)Rᵢⱼ`; **`g1Contact_limit`** / **`g1Contact_eqz_limit`**
  exhibit it as `lim_{s→∞} s·bᵢⱼ(s)/(2π√(ρρ)R)` (one-line `Tendsto.div_const`), and
  **`g1Contact_eqz_spec`** is eq (24) as written `2π√(ρρ)R·g¹ = {(I+A)K(I+A)ᵀ}ᵢⱼ` (prefactor `≠0`,
  `field_simp`).  `g1Contact_eqz` is `z`-independent (`A=A(z)` carries the decay).  `K`/`A` are the data
  inputs (Yukawa residue amplitudes; propagator entries = `AmatC_entry`'s `2π√(ρρ)Wtl/(Δ detTL)`).

* **(numerical alignment of `g1Contact_eqz` — DONE)** — `verify_g1_lean_alignment.py` (repo root,
  2026-08-06).  Recomputes the propagator two disjoint ways at all 24 Table 1–2 state points and pushes
  it through the Lean `g1Contact_eqz` formula.  Results (72 contact values): **(1)** Lean AppendixWDet
  closed form `2π√ρρ·Wtl·e^{−zλ}/(Δ·detTL)` **==** black-box matrix inverse `[Q̂₀(z)]⁻¹−I` to **4.4e-16**
  (numerical witness of `AmatC_entry`/`Q0_inv_entry_bridge` — two completely disjoint machineries);
  **(3)** Lean `g1Contact_eqz` **==** benchmark `g1` to 4.2e-17; **(4)** eq (24) spec `2π√ρρR·g¹ = N` to
  5.6e-17, `Im g¹ = 0` exactly; **(5)** `g0+g1_lean` vs paper column I max 2.2e-4 (OCR residual).  So the
  formalised `g1Contact_eqz` IS the benchmark quantity and reproduces Tang & Lu's published column I.
  A full state-point scan (`scan_g1_deviation.py`) adds: `g¹ ∝ β` exactly (1.1e-16), sign-indefinite per
  pair, small-sphere-dominated under size asymmetry, first order undershoots the full MSA (94 %), and
  `D = g¹/g0` predicts the true error (corr +0.83, worst on `g11` at low `T*`).

**Done (general `N`, complex `s`, axiom-clean):** the ENTIRE Tang & Lu momentum-side first-order RDF
programme — rank-2 + Woodbury inverse (`Q0ComplexRankTwo`), det `2×2` reduction (`Q0ComplexDetMatch`),
denominator `det Q̂₀ = detTL` + numerator `B·Δ = 2π Wtl` + entrywise inverse bridge
`{[Q̂₀]⁻¹}_ij = δ_ij + 2π√(ρρ)Wtl e^{−sλ}/(Δ detTL)` (`Q0ComplexDetMatchClose`), the RDF assembly
`Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` eq(15)/eq(21) with explicit propagator entries (`Q0ComplexH1Assembly`), AND
`B₁`'s eq(23) residue coefficients `bᵢⱼ` (`MixtureYukawaBij`).  `N=1` (both sides) = `AppendixBridgeN1`;
numerical benchmark closed in `benchmark_tanglu_contact.py`.  The momentum-side programme is complete —
every object (`Q̂₀`, `[Q̂₀]⁻¹`, `Ĥ₁`, `B₁`'s `bᵢⱼ`) is formalised in closed form.
The `y=0` compressibility point is now **done** (`det_Q0_contour_origin_ne_zero`, above).

**Numerical benchmark (Tables 1–2) — DONE (2026-08-05).** `benchmark_tanglu_contact.py` (repo root)
reproduces Tang & Lu Tables 1–2 (binary hard-core one-Yukawa, R₂₂/R₁₁ ∈ {1.5, 1.167}, single `z`
with `zR₁₁=1.8`). The first-order contact `g_ij(R_ij) = g⁰_HS + g¹` with `g¹` numerator
`N = (I+A)K(I+A)ᵀ`, `(I+A)_ij = [Q̂₀(z)]⁻¹_ij e^{zλ_ij}` — i.e. driven entirely by the HS Baxter
inverse `[Q̂₀(z)]⁻¹` at the Yukawa decay, the very object this task formalises. **Reproduction of the
paper's own first-order column I is EXACT** (max 2e-4, mean 1e-4 over 72 contact values; residual =
OCR noise). First-order vs full MSA (column II): mean 4.3e-2, max 0.23, **systematic small-sphere
`g11` / low-`T*` breakdown** (same signature as the project's MD (1,1) undershoot). Standalone script
(the `fmsa_ga_matrix_mix` class's LJ/BH/2YK parametrisation does not fit the exact single-`z` model);
Baxter conventions match `_build_Q0_Qpp`/`_build_Qhat`/`_compute_A_prop`. Write-up:
`numerical_notes/results/tanglu_first_order_contact.md`.

**Bookkeeping fix (2026-08-04):** the five newer momentum-side modules — `MixtureQ0Inverse`,
`MixtureRDFEqualDiam`, `MixtureRDFContact`, `MixtureYukawaTransform`, `MixtureYukawaResidue` — were
**never in the root aggregator `LeanCode.lean`** (they had only ever been built individually). Now
registered after `MixtureRDFUniqueness`; full `lake build` green at **8724 jobs**.

**Status.** (1)(2)(4)+eq(15) ✓, (3) per-pole residue **value** ✓, (3) **contour-sum step ✓** (general
engine + Yukawa bridge), (3a) **leading-term hc/hd/harc ✓** (`contourSum_leading_term`, end-to-end),
(3a-rest) **UHP holomorphy of `[Q̂₀]⁻¹` ✓** (`differentiableAt_matrix_inv` + comp-neg/continuousAt), (3a-rest-i)
**`q0_entry_c` s=0 entire representative ✓** (`q0_entry_c_repr`, fully axiom-clean), (3a-rest-ii) **det
orientation ✓** (`det_Q0_contour_ne_zero`, closed UHP minus origin, no new axiom), (3a-rest-iii) **`A(−iy)`
arc-bound mechanism ✓** (`arc_integral_tendsto_zero`, bounded numerator ⇒ arc→0, axiom-clean),
(c) **eq (21)/(22) assembly ✓** (`H1_assembly_phys` + entrywise, axiom-clean), (b) **`y=k` ½-Plemelj ✓**
(`sokhotski_plemelj_lower` + `_jump`, no new axiom), (iii-core) **exponent cancellation + far-region `φ`
bounds/decay + assembly logic ✓** (`expSum_*_eq_zero` + `normP{2,3}_arc_le`/`_decay` +
`amplitude_norm_le` + `norm_ge_of_norm_sub_one_le`), (iii-Appendix) **explicit `W`/`det` formulas +
`φ`-sum bound tools + BOTH `‖det−1‖≤d` and `‖W‖≤Wb` bookkeeping bounds ✓** (`Wtl`/`detTL`/`phi{1,2}` +
`norm_detTL_sub_one_le` + `norm_Wtl_le`), (bridge) **`N=1` Appendix bridge ✓ — both sides**
(`bridge_N1`/`_inv` numerator `q0 = 1−2π√W/Δ`; `detTL_eq_q0_N1` denominator `detTL = det Q̂₀`; axiom-clean),
(origin) **`y=0` compressibility point ✓** (`det_Q0_contour_origin_ne_zero`, general `N`, removable value
`Re c ≥ 1`, **no physics axiom**; closes the whole closed UHP with `det_Q0_contour_ne_zero`),
(benchmark) **numerical Tables 1–2 ✓** (`benchmark_tanglu_contact.py`, first-order column I reproduced
EXACTLY, max 2e-4; write-up `numerical_notes/results/tanglu_first_order_contact.md`),
(bridge-genN-structure) **complex rank-2 + Woodbury inverse ✓** (`Q0ComplexRankTwo.lean`:
`Q̂₀(s)=I−UₒVₒ`, `det=det(I−VₒUₒ)`, `[Q̂₀(s)]⁻¹=I+Uₒ(I−VₒUₒ)⁻¹Vₒ`, all std-3 — the real-`z`→`s`
complexification, Tang & Lu's "unique difficulty"), (bridge-genN-det-reduction) **det match REDUCED
to a scalar sum identity ✓** (`Q0ComplexDetMatch.lean`: `φ2=φ1/s+σ²/2s` identity + `VU` entries +
`detVU_expand`=A6; A6=A7 numerically `9e-16`; std-3), (bridge-genN-A6A7) **A6→A7 DENOMINATOR CLOSURE ✓**
(`Q0ComplexDetMatchClose.lean`: `det_eq_detTL` = `detVU_expand ▸ A6toCanon ▸ sdMatch ▸ detTLtoCanon`,
general `N`, complex `s`, std-3 — `det Q̂₀(s) = detTL` closed),
(bridge-genN-numerator) **NUMERATOR scalar match ✓**
(`numMatch`: `B_ij·Δ = 2π Wtl_ij` via `hLHS`/`hRHS`, general `N`, std-3),
(bridge-genN-ENTRYWISE) **FULL ENTRYWISE INVERSE BRIDGE ✓** (`Q0_inv_entry_bridge`:
`{[Q̂₀]⁻¹}_ij = δ_ij + 2π√(ρρ)Wtl_ij e^{−sλ}/(Δ detTL)`, general `N`, std-3 — via `UadjV` + Woodbury +
`det_eq_detTL` + `numMatch`), (RDF) **`Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` assembly ✓** (`Q0ComplexH1Assembly`:
eq15 `Q0_mat_c_phys_H1_eq`, eq21 `H1_assembly_c`/`_apply`, explicit propagator `AmatC_entry`, std-3),
(`B₁`) **eq(23) residue coefficients `bᵢⱼ` ✓** (`MixtureYukawaBij`: general `bij_eq23`, equal-`z`
`bij_eqz` = `{(I+A)K(I+A)ᵀ}ᵢⱼ/(s+z)` via `bij_eqz_matrix`, residue value `bij_eqz_residue`, std-3);
**MML.17 momentum side FULLY CLOSED for general `N`, complex `s` — every object in closed form**.

---

## Group MIXCHS — moved

*The MIXCHS group (mixture hard-sphere `c_HS` / Baxter–WH ODE) moved to its correct-layer home **`proof_notes_hs_mixture.md` → Group MIXCHS** (2026-08-11): it is HS-mixture-DCF content, not RDF/Mittag-Leffler. The scattered blow-by-blow blocks in the SEED ROUTE section above remain as RDF-seed-route context.*
