# Mixture leg-3 — roadmap (derive the matrix Blum–Høye root from OZ/Baxter primitives)

**Status: MPhase 1–5 DONE (posited `MixBHRootUneq` retired on OZ primitives), + MPhase 6 DONE — the
full-support g-side closes the (33′) derivation for ALL unequal σ (the RDF-hard-core overlap is automatic,
`neg_edgeHi_lt_edgeLo`; no size-disparity corner — an earlier `σ_j<σ_i+2σ_l` claim was a flipped-`edgeLo`
artifact), superseding MP5's ordered-pairs-only `Ioi 0` fold (2026‑09‑01).** The scalar
(`N=1`) leg-3 is DONE
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

## MPhase 6 — the full-support convolution: g-side closed for ALL unequal σ (2026‑09‑01)

The g-source normalization is **resolved** — not by absorbing a `t<0` correction into the g-source, but
by recognising that the RDF **hard core** kills the correction outright. Key insight: the RDF
`g_il(u) = 0` for `u < σ_il = edgeHi_il` (particles `i`,`l` can't overlap). Re-run the fold with the inner
`t`-integral over **all of `ℝ`** (so the Baxter transform is the *unconditional* MPhase-1
`∫_ℝ e^{−zt}Q_lj = qhatMixRuneq_lj`, every diameter pair). The naive `t<0` correction
`e^{−zt}∫_{u>−t}e^{−zu}u g(u)du − e^{−zt}ĝ = −e^{−zt}∫_{(0,−t]}e^{−zu}u g(u)du` **vanishes** whenever
`−t < σ_il`, i.e. when `Q`'s support floor satisfies the **overlap `−edgeHi_il < edgeLo_lj`**.

⭐ **The overlap is AUTOMATIC (no size-disparity corner).** With the Lean orientation
`edgeLo σ a b = (σ_b−σ_a)/2`, `edgeHi σ a b = (σ_a+σ_b)/2`:
`edgeLo_lj + edgeHi_il = (σ_j−σ_l)/2 + (σ_i+σ_l)/2 = (σ_i+σ_j)/2 > 0` — **the `σ_l` cancels**, so
`−edgeHi_il < edgeLo_lj` holds for **every** diameter triple (positive diameters). So the fold factors
cleanly for all unequal σ. ⚠ **CORRECTION to the first MP6 write-up:** an earlier claim that this needs
`σ_j < σ_i + 2σ_l` (with a residual "extreme size disparity" corner) came from a **flipped** `edgeLo_lj =
(σ_l−σ_j)/2`; it is **spurious**. Confirmed over **6.5M random triples** (`msaemix_extreme_disparity_check.py`,
diameter ratios to ~1000×): zero violations, margin `= (σ_i+σ_j)/2` exactly. cf [[feedback_sigma_one_masks_bugs]].

Lean (all axiom-clean std-3, `MixtureBlumHoyeDerivation.lean`):
- `rdfLaplaceMoment_shift_hardcore` — the hard-core shift `∫_{Ioi 0}e^{−zr}(r−t)g(r−t) = e^{−zt}ĝ` for
  `t > −σg` (generalises the scalar `rdfLaplaceMoment_shift_from_zero` to `t<0`).
- `laplace_conv_full` / `laplace_conv_full_of_integrable` — the full-support conv thm (inner `t` over `ℝ`,
  hypothesis `-σg < λ`); Fubini via `laplace_conv_full_fubini_swap` (`Ioi 0 ×ˢ ℝ`, `Measure.prod_restrict`
  on the `r` factor only). [The `-σg < λ` hypothesis is generic-math; physically it is always met.]
- `mat_laplace_conv_full` → `mat_gside_fold_full` → `gside_33_of_hgside_full` — the matrix stack; the key
  upgrade is `hQtransform` is now the **full-line** transform, discharged unconditionally by
  `baxterQ_fullline_transform` (`= baxterQ_transform_eq_qhatMixRuneq` at `s=z` mod `mul_comm`).
- `neg_edgeHi_lt_edgeLo` — the overlap `−edgeHi_il < edgeLo_lj` from `0 < σ` (`unfold; linarith`).
- `MixBHRootUneq_of_oz_full` — retires the posited `MixBHRootUneq` on OZ primitives for **ALL** unequal σ;
  the overlap `hcond` is discharged internally from `hσ : 0 < σ` (⇒ **no side condition survives**).
  No `matExactMSAUnequalDiam_hcore`.

**Numerically pinned** (`msaemix_fullsupport_fold_check.py`): the fold `= ĝ·Q̂` to machine precision for
`λ ≥ −σg`, correction genuinely nonzero for `λ < −σg` (rel err `6.1e-2` at `λ=−σg−0.2`, `3.5e-1` at
`λ=−σg−0.6`) — confirming `laplace_conv_full`'s hypothesis is the right one; but for physical diameters
`λ = edgeLo_lj` is **always** `≥ −σg = −edgeHi_il`, so the correction regime is never reached.

**c-side (29′)** is fully general throughout. So both root conjuncts now stand on OZ/Baxter primitives for
**every** unequal-σ combination — the g-side matches the c-side, with no residual.

**Superseded note (pre-MP6, kept for history).** The g-side (33′) derivation was previously non-vacuous
only for ordered pairs `σ_j ≥ σ_l`, because `gside_33_of_hgside`/`MixBHRootUneq_of_oz` took the `Ioi 0`
transform `hQtransform` (`∫_{Ioi 0}e^{−zt}Q_lj = qhatMixRuneq_lj`) as a hypothesis, unsatisfiable for
`edgeLo_lj < 0`. MP6's full-support fold removes that restriction entirely.

**g-side edge structure (numerically pinned):** the g-side carries its OWN `σ`-edge factors, so an
analogous recentering to the c-side (♦) is EXPECTED at unequal σ — two independent signals:
(1) `gam`'s convention `Gt_ij = ĝ_ij(z)·e^{+zσ_ij}` ⇒ `ĝ_il(z) = Gt_il·e^{−zσ_il}` (edge factor
`e^{−zσ_il}` on the transform moment); (2) `∫₀^∞ e^{−zt}Q_lj = qhatMixRuneq_lj` only for
`edgeLo_lj ≥ 0` (the `Ioi 0` transform misses `[edgeLo_lj,0)` when `σ_j < σ_l`). Confirming/pinning the
exact g-side (33′) form needs the concrete mixture g-side OZ Eq (32) (the matrix g-source + conv
domain). So the c-side FINDING is not an isolated slip — the σ-edge care is a **systematic** feature of
the unequal-σ root, strengthening the case that the posited `MixBHRootUneq` needs the recentered
transforms on both (29′) and (33′).

## MPhase 7 — the OZ primitives ARE the root conditions (hbax/hgside_mix discharged, 2026‑09‑01)

`MixBHRootUneq_of_oz_full` consumes `hbax` (exterior Baxter Eq 8 matched to `matMSAtail`) and
`hgside_mix` (g-side OZ Eq 32 Laplace-transformed) as OZ-primitive hypotheses. MP7 shows these are **not
free assumptions**: with the concrete `baxterQ`/`matMSAtail` plugged in they are **equivalent** to the
algebraic root conditions (29′)/(33′) — the matrix analogs of the scalar `hbax_iff_h29` /
`hgside_iff_h33`. All axiom-clean std-3, `MixtureBlumHoyeDerivation.lean`:

- `mat_hbax_of_cside` — reverse `(♦) ⟹ hbax`: fold the Baxter conv by `mat_exterior_baxter_relation_Dt`,
  compute `2πr·matMSAtail = 2πK_ij e^{z·edgeHi_ij} e^{−zr}` (the `r` cancels in `cMSAtail`), match via
  `(♦)` scaled by `z·e^{z·edgeHi_ij}` and the edge identity `edgeHi_ij + edgeLo_jl = edgeHi_il`. Clear the
  `/z` in (♦) first so `linear_combination`'s `ring` needn't cancel `z·z⁻¹`.
- `mat_hbax_iff_cside` — the iff (forward `c_side_constraint_of_exterior`).
- `mat_hgside_of_gside` — reverse `(33′) ⟹ hgside_mix`: fold the conv onto the transforms
  (`mat_laplace_conv_full` + `hgmoment`/`hQtransform`), then run `keysum`/`hexpand` backward, peeling
  `e^{z·edgeHi_ij}` via `E·E⁻¹ = 1`.
- `mat_hgside_iff_gside` — the iff (forward `gside_33_of_hgside_full`).

**Interpretation.** leg-3 now shows `MixBHRootUneq ⟺ (hbax ∧ hgside_mix ∧ RDF-side data)`. The OZ
primitives are exactly the root conditions; their **full unconditional discharge** — proving the concrete
`baxterQ` really solves OZ from first principles — is precisely the ring-infeasible
`matExactMSAUnequalDiam_hcore` content (the analytic k-space ring). So this equivalence is the honest end
of the leg-3 derivation line, mirroring the scalar (whose `hbax`/`hgside` bottomed out at `exactMSA_hcore`).
