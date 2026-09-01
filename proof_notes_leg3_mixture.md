# Mixture leg-3 — roadmap (derive the matrix Blum–Høye root from OZ/Baxter primitives)

**Status: PLANNING (2026‑08‑31).** The scalar (`N=1`) leg-3 is DONE (`proof_notes_leg3_bh_realspace.md`;
`YukawaOZ/{MSABlumHoyeDerivation,MSAGSideOZ,MSAFactorizationFromOZ}.lean`): it derived `h29`/`h33` from
the OZ/Baxter primitives and wired them into `exactMSA_factorization`. This file plans the **mixture
(general `N`, matrix) analog.**

## The situation — mirror image of scalar

On the scalar side the residual gap was the analytic k-space ring `exactMSA_hcore` (still an axiom);
the root conditions `h29`/`h33` were *derived* by leg-3. **On the mixture side it is reversed:**

* the analytic ring **is already discharged** — as the sympy-certified physics axioms
  `matExactMSAEqualDiam_hcore` / `matExactMSAUnequalDiam_hcore` (+ their k-space residuals), the matrix
  analog of `exactMSA_hcore`, `ring`-infeasible by design;
* but the **physical root `MSAMixture.MixBHRoot` / `MixBHRootUneq` is POSITED** (a `Prop` gate consumed
  as `hroot : …`), never derived.

So **mixture leg-3 = replace the posited `MixBHRootUneq` with a theorem** deriving the matrix (29′)/(33′)
from the real-space OZ/Baxter primitives, then feed the existing capstones. It does **not** touch the
`matExact…_hcore` axioms (those are the standing analog of scalar `exactMSA_hcore`).

### The target constraints (matrix h29/h33)

`MSAMixture.MixBHRootUneq` (`MSAMixtureBHRootUneq.lean:98`; equal-σ sibling `MixBHRoot`
`MSAMixtureBHRoot.lean:115`):

* **(29′)** `∀ i j, ∑_l Dt_il·(δ_lj − ρ_l·Q̂_jl(z)) = 2πK_ij/z`  — the c-side, `Q̂ = qhatMixRuneq`.
* **(33′)** `∀ i j, 2π·∑_l Gt_il·(δ_lj − ρ_l·Q̂_lj(z)) = (A_j + z·qp_ij + z²C_ij/2)/z²`  — the g-side.

Every scalar moment identity acquires a `∑_l ρ_l (…)` species contraction and a `Fin N × Fin N` index;
`bhF`/`Dt`/`G` become the matrices `qhatMixRuneq`/`Dt`/`Gt`.

## REUSE — already in the repo (axiom-clean unless noted)

| Scalar leg-3 object | Mixture analog (REUSE) | Location |
|---|---|---|
| `bhBaxterFn`, `bhBaxterFn'` (real-space `Q`,`Q'`) | `baxterQ`, `baxterQ'` (general N, unequal σ) | `MSAMixtureBaxterConv.lean:55,67` |
| the exterior conv `∫ Q(t)(…)` engine | `perL_conv_inner`/`perL_conv_outer` + `integral_canonical`/`integral_tailtail` (the `∑_l ρ_l ∫ Q'_il(t+r)Q_jl(t)` engine) | `MSAMixtureBreakpointConvDirect.lean:697,496,417` |
| `bh_exterior_baxter_relation` (c-side, **exterior**) | — **only the INTERIOR analog exists**: `baxterConvCore_eq_matCoreUneq_proved` (BRK.16, std-3) | `MSAMixtureBreakpointConvDirect.lean:1138` |
| `bhF` / `Q̂(z)` | `qhatMixRuneq` (real-`s`) / `qhatMixCuneq` (complex) | `MSAMixtureBHRootUneq.lean:52,40` |
| `radial_fourier`(core/tail) closed forms | `matCoreUneq`, `matMSACoreCorr`, `matMSAtail` (+ proved `radial_fourier_*`) | `MSAMixtureCoreUneq.lean:195`, `MSAMixtureCore.lean:114,123` |
| `exactMSA_factorization` (wire-in target) | `matMixtureFactorization_of_core` (+ `_of_baxterFourierWH`, HS-side discharged) | `MSAMixtureFactorization.lean:76,93` |
| the HS-side `hHS` | `matSF_of_baxterFourierWH` / `FtHSuneq_mul_transpose` (free algebra) | `MixtureOzStar.lean:112`, `MSAMixtureBHRootUneq.lean:238` |
| root-consuming capstones | `matMSAmixture_unequalDiam_of_hcore` / `_physical`; N=1 `matMSAmixture_fin_one` | `MSAMixtureBHRootUneq.lean:253,296`, `MSAMixtureFinOne.lean:102` |

## BUILD — does NOT exist yet (the actual work)

Phased to mirror scalar leg-3 (`MPhase` = mixture phase):

* **MPhase 1 — matrix Baxter transform + moments.** `∫₀^∞ baxterQ_ij·e^{−sr} dr = qhatMixCuneq … s`
  (matrix analog of `bhBaxter_transform`), its `s=z` value (`… = δ − …` feeding `Q̂` in (29′)/(33′)),
  and the zeroth/first moments (analog of `msaA_eq_baxter_zeroth_moment`,
  `msaQp_sub_msaA_eq_baxter_first_moment`). **Currently only numerically checked** (`msaemix_uneq_symconv.py`,
  ~1e-8). *Smallest, self-contained, unblocks both sides — recommended first step.*
* **MPhase 2 — c-side (29′): matrix `bh_exterior_baxter_relation`.** Compute the **exterior**
  (`r > σ_ij`) convolution `∑_l ρ_l ∫ Q'_il(t+r)Q_jl(t) dt` from `baxterQ`/`baxterQ'`, match to
  `matMSAtail` (`K_ij e^{−z(r−σ_ij)}/r`) ⇒ (29′). Reuses the `perL_conv_*` engine; the INTERIOR analog
  (BRK.16) is the template. Then the coefficient match `→ (29′)` (matrix analog of `h29_of_baxter_exterior`).
* **MPhase 3 — g-side matrix Laplace-convolution stack (the CRUX, largest build).** No mixture analog
  exists (confirmed by grep): need a matrix `rdfLaplaceMoment` (ĝ_ij(s)), a **matrix** convolution
  theorem `∑_l ρ_l ∫(r−t)g_il(|r−t|)Q_jl(t) dt →ᴸ ∑_l ĝ_il(z)·Q̂_jl(z)` (a **matrix product**, species
  sum inside), and the matrix Fubini swap. The scalar `MSAGSideOZ.lean` technique (
  `Integrable.convolution_integrand` + `Measure.prod_restrict` + `integral_integral_swap`) **lifts per
  species `l`**, but the `∑_l ρ_l` contraction must be carried through — it does not lift for free.
* **MPhase 4 — assemble (33′).** Fold MPhase 3's conv result + the g-source moment (matrix analog of
  `bhP_eq_gsource_moment`) ⇒ (33′), matrix analog of `h33_of_gside`.
* **MPhase 5 — wire-in `MixBHRootUneq_of_oz`.** Assemble (29′)+(33′) into `MixBHRootUneq`, feed
  `matMSAmixture_unequalDiam_of_hcore` (and the equal-σ / N=1 capstones). Retires the posited root,
  exactly as `exactMSA_factorization_of_oz` retired `h29`/`h33`. Also prove `hbax`/`hgside`-style
  equivalences (the matrix primitives ⟺ (29′)/(33′)) as on the scalar side.

## Risk / effort

* **MPhase 3 is the crux** — the matrix Laplace convolution with the interior species sum. The scalar
  Fubini discharge is the reusable technique, but the matrix product structure (`∑_l ĝ_il Q̂_jl`) is new.
* **MPhase 2** is medium — the exterior conv reuses the proven `perL_conv_*` engine; mostly transcription.
* **MPhase 1** is small and unblocks everything — **start here.**
* The `matExact…_hcore` physics axioms are **out of scope** (the standing analog of `exactMSA_hcore`);
  mixture leg-3 derives the *root*, not the ring.

## Blueprint

Transcribe scalar `YukawaOZ/{MSABlumHoyeDerivation,MSAGSideOZ,MSAFactorizationFromOZ}.lean` entry-by-entry,
adding `∑_l ρ_l` + `Fin N × Fin N` throughout. New files would live under `YukawaOZMix/` (e.g.
`MixtureBlumHoyeDerivation.lean`, `MixtureGSideOZ.lean`, `MixtureFactorizationFromOZ.lean`), gated in
`ExactMSAProject.lean` alongside the scalar leg-3.
