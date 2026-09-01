# Mixture leg-3 — roadmap (derive the matrix Blum–Høye root from OZ/Baxter primitives)

**Status: MPhase 1–2 DONE + c-side recentering FIX APPLIED to `MixBHRootUneq`, MPhase 3 conv-thm DONE
(2026‑08‑31).** The scalar (`N=1`) leg-3 is DONE
(`proof_notes_leg3_bh_realspace.md`;
`YukawaOZ/{MSABlumHoyeDerivation,MSAGSideOZ,MSAFactorizationFromOZ}.lean`): it derived `h29`/`h33` from
the OZ/Baxter primitives and wired them into `exactMSA_factorization`. This file plans the **mixture
(general `N`, matrix) analog** and logs progress (see **Progress log** at the bottom).

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

* **MPhase 1 — matrix Baxter transform + moments. ✅ DONE (transform), axiom-clean (std-3).**
  `MixtureBlumHoyeDerivation.lean`, namespace `FMSA.ExactMSA.MixLeg3`.
  `baxterQ_transform : ∫_ℝ baxterQ_ij·e^{−sr} dr = ` closed form, and
  `baxterQ_transform_eq_qhatMixRuneq : … = qhatMixRuneq z σ qp Wt Ct A s i j` — the posited real-`s`
  Baxter factor consumed by `MixBHRootUneq` **is** the Laplace transform of the real-space `baxterQ`.
  This is the matrix analog of the scalar `bhBaxter_transform`. **Key structure:** `baxterQ` regroups
  into four support-clean pieces — the dressed poly `qp·(r−λ−σ_i)+(A/2)(r−λ−σ_i)²` (arg `=r−σ_ij`,
  vanishes at `σ_ij`) on `[λ,σ_ij]`; the `Wt`-Yukawa `Wt·e^{−z(r−λ)}` on **all** `[λ,∞)` (spans
  core+tail); the constant `Ct` on `[λ,σ_ij]`; the tail `Ct`-Yukawa on `(σ_ij,∞)`. The `Wt` core-piece
  (`yukawa_shift_interval`) and tail-piece (`yukawa_shift_laplace_Ioi`) share an `e^{−(s+z)σ_ij}`
  term that **cancels algebraically** (no recombination lemma needed); `λ+σ_i=σ_ij` gives
  `e^{−sλ}·e^{−sσ_i}=e^{−sσ_ij}`. Helpers: `baxterQ_poly_moment` (FTC via copied `φ1`/`φ2`
  antiderivatives, general `σ`, no `σ_i≥0` needed), `yukawa_shift_interval`, `expLin_interval`,
  `yukawa_shift_integrableOn_Ioi`. Domain split `ℝ = Iio λ ⊔ Icc λ σ_ij ⊔ Ioi σ_ij` (baxterQ takes
  ONE definite branch per piece — no a.e. arguments). Matches the numeric `msaemix_uneq_symconv.py`
  (~1e-8). **REMAINING (deferred to MPhase 2/4 where consumed):** the `s=z` value
  (`∑_l ρ_l Q̂(z) = δ − …` feeding `Q̂` in (29′)/(33′)) and the zeroth/first `T_n` moments (analogs of
  `msaA_eq_baxter_zeroth_moment`, `msaQp_sub_msaA_eq_baxter_first_moment`). The complex-`s`
  `qhatMixCuneq` analog is a mechanical lift of the same proof if ever needed (real-`s` is what the
  residual gate uses).
* **MPhase 2 — c-side (29′): matrix `bh_exterior_baxter_relation`. ◑ exterior relation DONE
  (axiom-clean), (29′) coefficient-match REMAINING.** The exterior (`r > σ_ij`) convolution
  `∑_l ρ_l ∫ Q'_il(t+r)Q_jl(t) dt` is computed by `baxterQ_exterior_conv` + `mat_exterior_baxter_relation`
  (see Progress log) — it **factors through the MPhase-1 transform `Q̂(z)`** (the `perL_conv_*` engine is
  NOT needed — those are interior sub-regions `r < edgeHi`). REMAINING: match to `matMSAtail`
  (`= K_ij e^{−z(r−σ_ij)}/r`, `MSAMixtureConcrete.lean:77`) ⇒ (29′). The match gives (★):
  `2π K_ij e^{z·σ_ij}/z = S_ij − ∑_l ρ_l S_il Q̂_jl(z)` with `S_ab = Wt_ab e^{z·edgeLo_ab} + Ct_ab e^{z·edgeHi_ab}`.
  Reducing (★) ⇒ (29′) `Dt_ij − ∑_l ρ_l Dt_il Q̂_jl(z) = 2πK_ij/z` is the amplitude algebra:
  unfold `Wt = (2π/z)∑_k ρ_k Gt_ik Dt_kj`, `Ct = ∑_k γ_ik Dt_kj e^{z(σ_k−σ_i)/2}`,
  `γ = δ − 2πρ Gt e^{−zσ}/z` (`MSAMixtureCancellation.lean:74,79,68`) + the per-entry identity
  (`…:89`); this is the matrix analog of scalar `h29_of_baxter_exterior` and is definition-heavy.
* **MPhase 3 — g-side matrix Laplace-convolution stack (the CRUX). ◑ conv theorem DONE (axiom-clean);
  (33′) assembly + edge cross-check REMAINING.** The convolution theorem `mat_laplace_conv`
  `∑_l ρ_l ∫₀^∞ e^{−zr}(∫₀^∞(r−t)g_il(r−t)Q_lj(t)dt)dr = ∑_l ρ_l·ĝ_il(z)·Q̂_lj(z)` **reuses the scalar
  `FMSA.ExactMSA.GSide.laplace_conv_eq_rdf_mul_qhat_of_integrable` per species** (its Fubini swap is
  already discharged, generic in `g`,`Q`) + `Finset.sum_congr` — so the `∑_l ρ_l` contraction the
  roadmap feared is **just linearity**, no new integration-swap work (correcting the earlier "does not
  lift for free"). REMAINING: the concrete mixture g-side OZ Eq (32) (matrix g-source + conv domain, the
  g-side analog of the c-side `hbax`), then assemble (33′) = matrix analog of scalar `h33_of_gside`.
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

## Progress log

### MPhase 1 — the matrix Baxter transform (DONE, axiom-clean std-3)

`LeanCode/YukawaOZMix/MixtureBlumHoyeDerivation.lean` (namespace `FMSA.ExactMSA.MixLeg3`), built green
(8603 jobs), all `[propext, Classical.choice, Quot.sound]`. The Laplace transform of the real-space
Baxter factor `FMSA.ExactMSA.Breakpoint.baxterQ` is the posited closed form:

* **`baxterQ_transform`** `(hs : s≠0) (hsz : 0<s+z) (hσi : 0≤σ_i)` — `∫_ℝ baxterQ_ij·e^{−sr} dr` in
  explicit closed form (`edgeLo`/`edgeHi` form; the integral is over `ℝ` since `baxterQ` vanishes below
  `edgeLo`, so `∫_ℝ = ∫_{support}` = the intended `∫₀^∞` when `edgeLo≥0`).
* **`baxterQ_transform_eq_qhatMixRuneq`** — the same, RHS = `MSAMixture.qhatMixRuneq z σ qp Wt Ct A s i j`.
  So the **posited** real-`s` Baxter factor `qhatMixRuneq` (consumed by the (29′)/(33′) residual gate
  `MixBHRootUneq`) **is** the transform of `baxterQ`. (Cosmetic bridge: unfold `qhatMixRuneq`/`edgeLo`/
  `edgeHi`, normalize `−s·x ↔ −(s·x)`, commute qp/A order.)

**Proof design (reusable for MPhase 2/4):**
* the poly argument `r − edgeLo − σ_i = r − edgeHi` vanishes at the poly/tail junction, so
  `baxterQ_poly_moment` is a `φ1`/`φ2` FTC moment shifted to `[edgeLo,edgeHi]` (antiderivatives copied
  from the `private` ones in `HardSphere/BaxterRealSpace.lean`; holds for **any** `σ_i`, no positivity).
* the `Wt`-Yukawa `Wt·e^{−z(r−edgeLo)}` lives on **all** `[edgeLo,∞)` (core + tail have the SAME form);
  its core interval `yukawa_shift_interval` and tail half-line `yukawa_shift_laplace_Ioi` share an
  `e^{−(s+z)·edgeHi}` term that **cancels by `ring`** — no recombination lemma. `edgeLo+σ_i=edgeHi`
  gives `e^{−s·edgeLo}·e^{−s·σ_i}=e^{−s·edgeHi}` (`hEH`), collapsing the `Ct` core/tail split.
* domain split `ℝ = Iio edgeLo ⊔ Icc edgeLo edgeHi ⊔ Ioi edgeHi` — `baxterQ` takes ONE definite branch
  per piece (branch lemmas `hzero`/`hcore_eq`/`htail_eq`), so **no a.e. arguments**; integrabilities via
  `Continuous.integrableOn_Icc` (core) and `yukawa_shift_integrableOn_Ioi` (tail exp-decay).
* helpers exported for reuse: `yukawa_shift_laplace_Ioi`, `yukawa_shift_interval`, `expLin_interval`,
  `yukawa_shift_integrableOn_Ioi`, `baxterQ_poly_moment`.

**Deferred within MPhase 1** (do when consumed downstream): the `s=z` evaluation
(`∑_l ρ_l·Q̂_jl(z)` feeding `δ − …` in (29′)/(33′)), the `T_n` moments, and the complex-`s`
`qhatMixCuneq` lift (mechanical — real-`s` is what the gate uses).

### MPhase 2 — the matrix exterior Baxter relation (exterior half DONE, axiom-clean std-3)

Same file, built green, all `[propext, Classical.choice, Quot.sound]`, gated in `ExactMSAProject.lean`.

* **`baxterQ_exterior_conv`** `(hz : 0<z) (hσ : ∀k, 0≤σ_k) (hr : edgeHi σ i j < r)` — the per-`l`
  exterior convolution `∫ Q'_il(t+r)·Q_jl(t) dt = −z e^{−zr}·(Wt_il e^{z·edgeLo_il}+Ct_il e^{z·edgeHi_il})·Q̂_jl(z)`.
  **KEY:** on `r > edgeHi_ij`, since `edgeLo_jl + edgeHi_ij = edgeHi_il`, wherever `Q_jl(t)≠0`
  (`t ≥ edgeLo_jl`) the shifted arg `t+r > edgeHi_il`, so `Q'_il(t+r)` is in its TAIL
  `−z(Wt_il e^{−z(·−edgeLo_il)}+Ct_il e^{−z(·−edgeHi_il)})`, which factors `= e^{−zr}·(coeff)·e^{−zt}` —
  pulling `e^{−zr}` out leaves `∫ Q_jl(t)e^{−zt}dt = Q̂_jl(z)` = **the MPhase-1 transform**
  (`baxterQ_transform_eq_qhatMixRuneq` at `s=z`). Proof: `integral_congr_ae` (pointwise, case
  `t<edgeLo_jl` ⇒ `Q_jl=0` kills it) → `integral_const_mul` → MPhase-1 transform. `perL_conv_*` NOT used.
* **`mat_exterior_baxter_relation`** — the assembled Baxter Eq (8):
  `−Q'_ij(r) + ∑_l ρ_l ∫ Q'_il(t+r)Q_jl(t)dt = z e^{−zr}(S_ij − ∑_l ρ_l S_il Q̂_jl(z))`,
  `S_ab = Wt_ab e^{z·edgeLo_ab}+Ct_ab e^{z·edgeHi_ab}`. Matrix analog of scalar `bh_exterior_baxter_relation`.
  `−Q'_ij(r)` tail + per-`l` conv + `Finset.mul_sum` factoring.

**Amplitude algebra (DONE, axiom-clean std-3):**
* **`baxterS_eq_edgeHi_Dt`** — `Wt_il e^{z·edgeLo_il} + Ct_il e^{z·edgeHi_il} = e^{z·edgeHi_il}·Dt_il`,
  via `MSAMixture.cancellation_star` (`Dt − Ct = e^{−zσ}·Wt`); the two `Wt` terms cancel because
  `e^{−zσ_i}·e^{z·edgeHi_il} = e^{z·edgeLo_il}`. Numerically confirmed to `4.4e-16`.
* **`mat_exterior_baxter_relation_Dt`** — the exterior relation with `S` collapsed to `Dt`:
  `−Q'_ij(r) + ∑_l ρ_l ∫ = z e^{−zr}(e^{z·edgeHi_ij}Dt_ij − ∑_l ρ_l e^{z·edgeHi_il}Dt_il Q̂_jl(z))`.

### ⚠ FINDING — the c-side constraint is (♦), not the posited (29′), at unequal σ

Matching `2πr·matMSAtail_ij = 2πK_ij e^{z·σ_ij}e^{−zr}` against `mat_exterior_baxter_relation_Dt`
(cancel `e^{−zr}`, divide `z`, divide the common `e^{z·edgeHi_ij}` off `K` and `Dt_ij`) gives

    (♦)   Dt_ij − ∑_l ρ_l · e^{z·edgeLo_jl} · Dt_il · Q̂_jl(z) = 2π K_ij / z.

The **recentering factor `e^{z·edgeLo_jl}`** is structural: it is `e^{z(edgeHi_il − edgeHi_ij)}` (the
row-`i` tail edge vs the diagonal `K` edge). The posited `MixBHRootUneq` (29′) has the **bare** `Q̂_jl`
(no `e^{z·edgeLo_jl}`). At equal σ, `edgeLo_jl = 0` ⇒ (♦) ≡ (29′); at **unequal** σ they differ.
Since `baxterS_eq_edgeHi_Dt` is proved + numerically confirmed and `mat_exterior_baxter_relation` is
axiom-clean, **(♦) is the rigorously-derived form**, so the posited (29′) appears to need the
recentered transform `e^{z·edgeLo_jl}·qhatMixRuneq_jl` (Baxter `Q̂` centered at the support edge) for the
unequal-σ root — a σ-power factor of exactly the kind `σ=1` masks (cf. `feedback_sigma_one_masks_bugs`).

**(♦) NOW PROVED, axiom-clean std-3 (option B):** `c_side_constraint_of_exterior`
`(hz) (hσ) (hbax : ∀ r > edgeHi, 2πr·matMSAtail_ij = −Q'_ij(r) + ∑_l ρ_l ∫ Q'_il(t+r)Q_jl(t)dt)` derives
exactly (♦). Matrix analog of scalar `h29_of_baxter_exterior` (takes the exterior closure `hbax` as
hypothesis; proof = evaluate at `r = σ_ij+1`, fold by `mat_exterior_baxter_relation_Dt`, cancel `z·e^{−z}`).
This is a Lean-checked fact that the exterior OZ/Baxter closure forces (♦).

**RECENTERING FIX APPLIED, BOTH conjuncts (numerically CONFIRMED).** `MSAMixture.MixBHRootUneq`
(`MSAMixtureBHRootUneq.lean:98`) uses the recentered transform on both conjuncts:
* (29′) `e^{z·edgeLo σ j l}·Q̂_jl` = the OZ-derived (♦) (`mixBHRootUneq_cSide_of_exterior` proves it from
  the exterior closure, axiom-clean).
* (33′) `e^{z·edgeLo σ l j}·Q̂_lj` — **opposite `edgeLo` orientation, transposed `Q̂` index** (Baxter
  Eq (8) `D(I−PQ̂ᵀ)` vs Eq (32) `2πĝ(I−PQ̂)`).

**Numerically confirmed** to machine precision at a physical unequal-σ root against the validated solver
`msa_exact_mix.py` (`_residuals` passes the Tang & Lu gate at `σ₂/σ₁=1.5`): `msaemix_root_recentering_check.py`
gives `(29′) 1.7e-16`, `(33′) 3.6e-15`; the **bare (33′)** (no recentering) misses by `≈5`.  Full library
**build green (8812 jobs)**; the def change is transparent (consumers thread `hroot` to the
`matExactMSAUnequalDiam_hcore` axiom).

⚠ **Course-correction record (kept as a lesson).** A first pass recentered both conjuncts (correct); then
a flawed structural argument — reading the g-side Eq (34) `ĝ_il = Gt_il·e^{−z·edgeHi_il}` as an amplitude
factor that "kills" the `Q̂`-recentering — wrongly **retracted** the (33′) recentering; the solver check
then **refuted the retraction** (bare (33′) residual `≈5`) and restored it.  Lesson: **do not infer the
g-side edge from the c-side by intuition — check against `msa_exact_mix._residuals`.**  The from-first-
principles g-side derivation (via `mat_laplace_conv` + a repo-consistent g-source, matrix analog of the
scalar `bhP`) is still open, but the (33′) *form* is now numerically pinned.

### MPhase 3 — the matrix Laplace-convolution theorem (CRUX engine DONE, axiom-clean std-3)

`mat_laplace_conv` `(hgsupp)(hF1)(hF2)` — `∑_l ρ_l ∫₀^∞ e^{−zr}(∫₀^∞(r−t)g_il(r−t)Q_lj(t)dt)dr
= ∑_l ρ_l·rdfLaplaceMoment(g_il)(z)·(∫₀^∞ e^{−zt}Q_lj(t)dt)`. Proof = `Finset.sum_congr` +
`FMSA.ExactMSA.GSide.laplace_conv_eq_rdf_mul_qhat_of_integrable` per species (the scalar's Fubini swap
is already discharged and generic in `g`,`Q`). **This resolves the roadmap's crux worry**: the `∑_l ρ_l`
species contraction is pure linearity — the scalar g-side machinery reuses wholesale.

### MPhase 3/4 — the g-side fold (DONE, axiom-clean std-3)

`mat_gside_fold` — the mixture analog of the scalar `hoz_of_gside`. Given the g-side OZ equation
Laplace-transformed at `s=z` (`hgside_mix`, the g-side `hbax`), it folds the species-summed
RDF⋆Baxter convolution via `mat_laplace_conv` and produces the g-side constraint
`2π·∑_l ĝ_il(z)·(δ_lj − ρ_l·Q̂_lj(z)) = source`, with `ĝ_il`/`Q̂_lj` supplied by `hgmoment`/`hQtransform`.
**This discharges the convolution-folding crux** (the same crux the c-side had).

**MPhase 4 — the g-source bookkeeping (DONE, axiom-clean std-3):**
* **`gside_33_of_fold`** — recovers the exact (33′) conjunct of `MixBHRootUneq` from the fold output.
  KEY: multiply by `e^{z·edgeHi_ij}` and use `ĝ_il = Gt_il·e^{−z·edgeHi_il}` (the `gam` convention) ⇒
  `ĝ_il·e^{z·edgeHi_ij} = Gt_il·e^{z(edgeHi_ij − edgeHi_il)} = Gt_il·e^{z·edgeLo σ l j}` (edge identity);
  `source = RHS·e^{−z·edgeHi_ij}` cancels. Proof: `keysum` (per-`l` edge identity + `Finset.mul_sum`) +
  `linear_combination R·hc` with `hc : e^{z·edgeHi_ij}·e^{−z·edgeHi_ij}=1`.
* **`gside_33_of_hgside`** — chains `mat_gside_fold` → `gside_33_of_fold`: the **(33′) DERIVED from the
  g-side OZ primitive `hgside_mix`** + the physical identifications (RDF moment `hgmoment`, transform
  `hQtransform`, `ĝ`/`Q̂` conventions `hghat`/`hQhat`).  The full matrix analog of the scalar
  `h33_of_gside`.  Together with the c-side (♦), both root conjuncts stand on recognised OZ/Baxter
  primitives.

**Residual (hypothesis-level, exactly as the scalar):** the `Ioi 0` transform in the fold equals the
full-support `qhatMixRuneq_lj` when `edgeLo_lj ≥ 0`; the general full-support conv domain `[edgeLo,∞)` is
carried as the `hQtransform`/`hQhat` hypothesis (the scalar `h33_of_gside` likewise takes `hQtransform`
as a hypothesis).  The (33′) *form* is numerically pinned to machine precision
(`msaemix_root_recentering_check.py` vs `msa_exact_mix.py`).

### MPhase 5 — the posited root RETIRED (DONE, axiom-clean std-3)

`MixBHRootUneq_of_oz` assembles the derived c-side (29′) (`mixBHRootUneq_cSide_of_exterior`, from the
exterior Baxter closure `hbax`) and the derived g-side (33′) (`gside_33_of_hgside`, from the g-side OZ
primitive `hgside_mix`; bridged by `gside_bracket_sum_eq`, the whole-bracket ↔ `Q̂`-only recentering
identity) into `MSAMixture.MixBHRootUneq`.  So the unequal-σ Blum–Høye root — consumed as a hypothesis by
`matMSAmixture_unequalDiam_of_hcore` and the other capstones — now **stands on the recognised OZ/Baxter
primitives** (exterior DCF closure + g-side OZ + RDF-moment/Baxter-transform identities), the mixture
analog of the scalar `exactMSA_factorization_of_oz`.

**Mixture leg-3 status** (MP1–MP5, axiom-clean throughout): the matrix Baxter transform, the c-side (♦),
the g-side (33′), and the assembly (`MixBHRootUneq_of_oz`) retiring the posited root — mirroring the
scalar leg-3, with the σ-edge recentering (numerically pinned against `msa_exact_mix.py`) as the one
genuinely-new mixture feature.

⚠ **Range of validity (important).** The **c-side (29′) is fully general** (`mat_exterior_baxter_relation`
integrates over the full line). The **g-side (33′) derivation is non-vacuous only for ordered pairs**
`σ_j ≥ σ_l` (`edgeLo_lj ≥ 0`): `gside_33_of_hgside`/`MixBHRootUneq_of_oz` take `hQtransform`
(`∫_{Ioi 0}e^{−zt}Q_lj = qhatMixRuneq_lj`) as a hypothesis, which is **unsatisfiable for `edgeLo_lj < 0`**
(the `Ioi 0` integral misses `[edgeLo_lj,0)` where `baxterQ_lj ≠ 0`). The obstruction is real, not a
transcription detail: the full-support fold `∫_{r>0}e^{−zr}∫_ℝ(r−t)g(r−t)Q(t)dt` does **not** factor as
`ĝ·Q̂` for `t<0` — the per-`t` collapse `e^{−zt}∫_{u>−t}e^{−zu}u g(u)du` is a `t`-dependent *partial*
moment, not `ĝ(z)`. So the general unequal-σ g-side is the **note's unresolved g-source normalization**
(`proof_notes_leg3_bh_gside_eq9.md`), where the `t<0` correction must be absorbed by the g-source. A
future full-support (`Q` on `[edgeLo,∞)`) convolution theorem would discharge `hQtransform` from MPhase 1
unconditionally and close this. (The (33′) *value* is still numerically pinned for all σ vs
`msa_exact_mix.py`; it is the *first-principles Lean derivation* that is ordered-pairs-only.)

**g-side edge structure (numerically pinned):** the g-side carries its OWN `σ`-edge factors, so an
analogous recentering to the c-side (♦) is EXPECTED at unequal σ — two independent signals:
(1) `gam`'s convention `Gt_ij = ĝ_ij(z)·e^{+zσ_ij}` ⇒ `ĝ_il(z) = Gt_il·e^{−zσ_il}` (edge factor
`e^{−zσ_il}` on the transform moment); (2) `∫₀^∞ e^{−zt}Q_lj = qhatMixRuneq_lj` only for
`edgeLo_lj ≥ 0` (the `Ioi 0` transform misses `[edgeLo_lj,0)` when `σ_j < σ_l`). Confirming/pinning the
exact g-side (33′) form needs the concrete mixture g-side OZ Eq (32) (the matrix g-source + conv
domain). So the c-side FINDING is not an isolated slip — the σ-edge care is a **systematic** feature of
the unequal-σ root, strengthening the case that the posited `MixBHRootUneq` needs the recentered
transforms on both (29′) and (33′).
