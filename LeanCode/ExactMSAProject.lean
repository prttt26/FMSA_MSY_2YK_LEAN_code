import LeanCode.YukawaOZMix.MSAMixtureBreakpointConvDirect
import LeanCode.Closures.FirstOrderEquivalence
import LeanCode.Closures.MSAFamilyConcrete
import LeanCode.YukawaOZMix.MSAMixtureFactorization
import LeanCode.YukawaOZ.MSAClosedForm
import LeanCode.YukawaOZMix.MSAMixturePositivity
import LeanCode.YukawaOZMix.MSAMixtureSelection
import LeanCode.YukawaOZ.MSAFactorizationFromOZ
import LeanCode.YukawaOZMix.MixtureBlumHoyeDerivation
import LeanCode.YukawaOZMix.MSAMixtureBHRootUneqSmooth

/-!
# Exact-MSA track — scope and axiom gate

**What this file is for.** Companion to `FMSAProject.lean`: the same "scope by import + axiom
footprint as a build gate" discipline, for the **exact MSA** track (Waisman / Blum–Høye / Ginoza),
together with everything about the **FMSA ↔ exact-MSA relationship**:

* the exact MSA closed form, single component (`ExactMSA`: the physical root, its uniqueness below
  the coupling threshold, the degree-8 → two-quartics elimination) and mixture (`MSAMixture`: the
  matrix factorization staged on `hcore`, positivity/stability, the Eq.(41) `g_ij=g_ji` selection);
* the **bridge** results: `firstOrder_amplitude_eq_hardSphere_dressed` (MSAEXACT.5 — first-order MSA
  = FMSA-DP HS-dressed amplitudes) and the MSA solution family (`MSASolutionFamily`, MSAFAM — the
  family is `C^∞` at zero coupling, removing Theorem I.1's differentiability hypothesis);
* the exact-MSA **mixture core** proved axiom-free: `baxterConvCore_eq_matCoreUneq_proved` (BRK.16 —
  the real-space Baxter convolution core equals the closed form `matCoreUneq`, std-3, retiring the
  former sympy seam axiom).

Like `FMSAProject.lean`, every `#guard_msgs` block below fails the build if the axiom set of that
declaration changes. All results guarded here are **axiom-clean** (the standard three only).

⚠ **Out of scope by design.** The MSAEXACT.6 / MSAEMIX.1 `hcore` closure-recovery *rings* were
measured `ring`-infeasible; their Fourier layer is discharged from ONE pure-k-space sympy residual
per ring — `exactMSA_kspace_residual` and `matExactMSAEqualDiam_kspace_residual` — carried by the
**out-of-`defaultTargets`** certificate libs `ExactMSACertificate` /
`MatExactMSAEqualDiamCertificate` (`lake build <lib>` on demand).  Those are deliberately **not**
imported or gated here, so the default
build's footprint stays honest — exactly as `FMSAProject.lean` leaves `matOzStar_unique` un-gated.
FOEQ's own gates (the general-order first-order-equivalence theorems the FMSA-DP paper consumes)
live in `FMSAProject.lean`; only the exact-MSA-side bridge result MSAEXACT.5 is gated here.
-/

/-! ## The exact-MSA mixture core (BRK.16) — axiom-free -/

/-- info: 'FMSA.ExactMSA.Breakpoint.baxterConvCore_eq_matCoreUneq_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.Breakpoint.baxterConvCore_eq_matCoreUneq_proved

/-! ## The FMSA ↔ exact-MSA bridge -/

/-- info: 'FMSA.FirstOrderEquivalence.firstOrder_amplitude_eq_hardSphere_dressed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderEquivalence.firstOrder_amplitude_eq_hardSphere_dressed

/-- info: 'FMSA.MSASolutionFamily.exists_contDiffAt_bhRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MSASolutionFamily.exists_contDiffAt_bhRoot

/-- info: 'FMSA.MSASolutionFamily.msaFamily_taylor_eq_hierarchy_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MSASolutionFamily.msaFamily_taylor_eq_hierarchy_concrete

/-! ## The exact MSA closed form — single component and mixture -/

/-- info: 'FMSA.ExactMSA.msaRoot_unique_of_coupling_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.msaRoot_unique_of_coupling_lt

/-- info: 'MSAMixture.matMixtureFactorization_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.matMixtureFactorization_of_core

/-- info: 'MSAMixture.mixStability_eq_det_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.mixStability_eq_det_sq

/-- info: 'MSAMixture.bh41_iff_contact_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.bh41_iff_contact_symm

/-! ## The leg-3 (`N = 1`) Blum–Høye derivation — `h29`/`h33` from the OZ primitives

The scalar Blum–Høye constraints Eq. (29) `Dt·bhF = 2πK/z` and Eq. (33) `2πG·bhF = bhP` are **derived**
(not posited) from the recognised OZ/Baxter primitives: `h29` from Baxter's exterior real-space
relation (Eq. 8) plus the MSA closure, and `h33` from the g-side OZ equation (Eq. 32) Laplace-
transformed at `s = z` — its OZ-convolution term folded by the fully-proved Laplace convolution
theorem `laplace_conv_eq_rdf_mul_qhat_of_integrable` (no Fubini hypothesis; only the physical `L¹`
integrability of the RDF and Baxter moments).  `exactMSA_factorization_of_oz` then feeds the derived
`h29`/`h33` into `exactMSA_factorization`, so the MSA factorization stands on the OZ primitives with
**no new axiom** — its footprint is the standard three plus the single pre-existing physics-computation
axiom `exactMSA_hcore`.  All `#guard_msgs` below fail the build if these footprints change. -/

/-- info: 'FMSA.ExactMSA.h29_of_baxter_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.h29_of_baxter_exterior

/-- info: 'FMSA.ExactMSA.GSide.h33_of_gside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.GSide.h33_of_gside

/--
info: 'FMSA.ExactMSA.GSide.laplace_conv_eq_rdf_mul_qhat_of_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FMSA.ExactMSA.GSide.laplace_conv_eq_rdf_mul_qhat_of_integrable

/-- info: 'FMSA.ExactMSA.GSide.h33_of_gside_baxter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.GSide.h33_of_gside_baxter

/--
info: 'FMSA.ExactMSA.GSide.exactMSA_factorization_of_oz' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 FMSA.ExactMSA.exactMSA_hcore]
-/
#guard_msgs in
#print axioms FMSA.ExactMSA.GSide.exactMSA_factorization_of_oz

/-! **The scalar OZ primitives ARE the root conditions** (`hbax`/`hgside` discharged, both directions).
`hbax_iff_h29` (exterior Baxter Eq 8 `⟺` Eq 29; forward `h29_of_baxter_exterior`, reverse `hbax_of_h29`)
and `hgside_iff_h33` (g-side OZ Eq 32 Laplace `⟺` Eq 33; forward `h33_of_gside_baxter`, reverse
`hgside_of_h33`) — the scalar analogs of the mixture `mat_hbax_iff_cside` / `mat_hgside_iff_gside`, both
complete iffs with the concrete `bhBaxterFn`/`bhBaxterSupp`.  Full unconditional discharge is the
`exactMSA_hcore` ring (as `exactMSA_factorization_of_oz`'s footprint shows). -/

/-- info: 'FMSA.ExactMSA.GSide.hbax_iff_h29' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.GSide.hbax_iff_h29

/-- info: 'FMSA.ExactMSA.GSide.hgside_iff_h33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.GSide.hgside_iff_h33

/-! ## The mixture leg-3 (general `N`, matrix) Blum–Høye derivation — MPhase 1

The mixture analog is the mirror image of the scalar leg-3: the analytic ring is already discharged (as
the `matExactMSA…_hcore` physics axioms), while the physical **root** `MSAMixture.MixBHRootUneq` (the
matrix (29′)/(33′)) is posited.  Mixture leg-3 derives that root from the real-space OZ/Baxter
primitives.  **MPhase 1** proves the matrix Baxter transform: the posited real-`s` Baxter factor
`qhatMixRuneq` **is** the Laplace transform of the real-space Baxter factor `baxterQ`, axiom-clean.
See `proof_notes_leg3_mixture.md`. -/

/-- info: 'FMSA.ExactMSA.MixLeg3.baxterQ_transform_eq_qhatMixRuneq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.baxterQ_transform_eq_qhatMixRuneq

/-! **MPhase 2** — the exterior Baxter relation, matrix analog of the scalar `bh_exterior_baxter_relation`:
on `r > σ_ij` the Baxter convolution `∑_l ρ_l ∫ Q'_il(t+r) Q_jl(t) dt` factors through the MPhase-1
transform `Q̂(z)`, giving `−Q'_ij(r) + ∑_l ρ_l ∫ … = z e^{−zr}(S_ij − ∑_l ρ_l S_il Q̂_jl(z))`.  Matching
`matMSAtail` yields the c-side (29′). -/

/-- info: 'FMSA.ExactMSA.MixLeg3.mat_exterior_baxter_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.mat_exterior_baxter_relation

/-! **MPhase 2 amplitude algebra** — the exterior amplitude bundle collapses to the c-side amplitude
`Dt` via the `e^{zσ}` cancellation `MSAMixture.cancellation_star`, putting the exterior Baxter
convolution in `Dt` form.  ⚠ Matching `matMSAtail` then yields the c-side constraint `(♦)` with a
recentering `e^{z·edgeLo_jl}` on the transform — differing from the posited `MixBHRootUneq` (29′) at
unequal σ (see `proof_notes_leg3_mixture.md`, FINDING). -/

/-- info: 'FMSA.ExactMSA.MixLeg3.baxterS_eq_edgeHi_Dt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.baxterS_eq_edgeHi_Dt

/-- info: 'FMSA.ExactMSA.MixLeg3.mat_exterior_baxter_relation_Dt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.mat_exterior_baxter_relation_Dt

/-! **MPhase 2 c-side constraint (♦), PROVED.**  `c_side_constraint_of_exterior` derives, from the
exterior MSA closure `hbax` (`2πr·c_ij = matMSAtail`-tail = the Baxter convolution RHS on `r > σ_ij`),
the c-side constraint `Dt_ij − ∑_l ρ_l·e^{z·edgeLo_jl}·Dt_il·Q̂_jl(z) = 2πK_ij/z` — the matrix analog of
the scalar `h29_of_baxter_exterior`.  The **recentering `e^{z·edgeLo_jl}`** is the FINDING: it is absent
in the posited `MixBHRootUneq` (29′), which therefore coincides with (♦) only at equal σ.  See
`proof_notes_leg3_mixture.md`. -/

/-- info: 'FMSA.ExactMSA.MixLeg3.c_side_constraint_of_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.c_side_constraint_of_exterior

/-! **The recentering fix, wired to `MixBHRootUneq` (both conjuncts, numerically confirmed).**
`MixBHRootUneq` uses the recentered Baxter transform on **both** conjuncts — (29′) `e^{z·edgeLo σ j l}·Q̂_jl`,
(33′) `e^{z·edgeLo σ l j}·Q̂_lj` — the σ-edge FINDING, confirmed to machine precision at a physical
unequal-σ root against the validated solver `msa_exact_mix.py` (`msaemix_root_recentering_check.py`:
`(29′) 1.7e-16`, `(33′) 3.6e-15`; the bare form misses (33′) by `≈5`).  `mixBHRootUneq_cSide_of_exterior`
additionally proves the (29′) conjunct from the c-side exterior closure (= the OZ-derived (♦)).  The two
conjuncts descend from Baxter's Eq (8)/(32) with opposite `edgeLo` orientation and transposed `Q̂` index. -/

/-- info: 'FMSA.ExactMSA.MixLeg3.mixBHRootUneq_cSide_of_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.mixBHRootUneq_cSide_of_exterior

/-! **MPhase 3 (CRUX) — the matrix Laplace-convolution theorem.**  `mat_laplace_conv` folds the
species-summed RDF⋆Baxter convolution onto `∑_l ρ_l·ĝ_il(z)·Q̂_lj(z)` by reusing the scalar
`FMSA.ExactMSA.GSide.laplace_conv_eq_rdf_mul_qhat_of_integrable` per species (its Fubini swap is already
discharged) — the `∑_l ρ_l` contraction is pure linearity.  The g-side (33′) assembly + its σ-edge
cross-check (which is expected to mirror the c-side (♦) recentering) remain — see
`proof_notes_leg3_mixture.md`. -/

/-- info: 'FMSA.ExactMSA.MixLeg3.mat_laplace_conv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.mat_laplace_conv

/-! **The g-side fold (mixture analog of the scalar `hoz_of_gside`).**  `mat_gside_fold` takes the
mixture g-side OZ equation Laplace-transformed at `s = z` (`hgside_mix`, the g-side analog of the c-side
`hbax`), folds the species-summed RDF⋆Baxter convolution via `mat_laplace_conv`, and yields the g-side
constraint `2π·∑_l ĝ_il(z)·(δ_lj − ρ_l·Q̂_lj(z)) = source` — discharging the convolution-folding crux.
Matching `source`/`ĝ`/`Q̂` to the physical amplitudes recovers the numerically-confirmed (33′). -/

/-- info: 'FMSA.ExactMSA.MixLeg3.mat_gside_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.mat_gside_fold

/-! **The g-side (33′), derived from the g-side OZ primitive.**  `gside_33_of_hgside` chains
`mat_gside_fold` (convolution folding) into `gside_33_of_fold` (g-source bookkeeping): from the mixture
g-side OZ equation Laplace-transformed at `s = z` (`hgside_mix`) + the physical identifications
`ĝ_il = Gt_il·e^{−z·edgeHi_il}`, `Q̂_lj = qhatMixRuneq_lj`, the (33′) conjunct of `MixBHRootUneq` follows —
the full matrix analog of the scalar `h33_of_gside`.  Together with the c-side (♦)
(`mixBHRootUneq_cSide_of_exterior`), both root conjuncts now stand on recognised OZ/Baxter primitives. -/

/-- info: 'FMSA.ExactMSA.MixLeg3.gside_33_of_hgside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.gside_33_of_hgside

/-! ⭐⭐ **MPhase 5 — the posited root retired.**  `MixBHRootUneq_of_oz` assembles the derived c-side (29′)
(`mixBHRootUneq_cSide_of_exterior`, from the exterior Baxter closure) and the derived g-side (33′)
(`gside_33_of_hgside`, from the g-side OZ primitive) into `MSAMixture.MixBHRootUneq`.  So the unequal-σ
Blum–Høye root — consumed as a hypothesis by `matMSAmixture_unequalDiam_of_hcore` etc. — now stands on the
recognised OZ/Baxter primitives, the mixture analog of the scalar `exactMSA_factorization_of_oz`.  ⚠ The
c-side (29′) is fully general; this `Ioi 0`-fold version's g-side (33′) `hQtransform` is satisfiable only
for ordered pairs (`σ_j ≥ σ_l`).  **Superseded by `MixBHRootUneq_of_oz_full`** (MPhase 6), whose
full-support fold closes the g-side for **every** unequal-σ combination. -/

/-- info: 'FMSA.ExactMSA.MixLeg3.MixBHRootUneq_of_oz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.MixBHRootUneq_of_oz

/-! ### MPhase 6 — the full-support convolution: the g-side beyond ordered pairs

The `Ioi 0` fold above needs `∫_{Ioi 0} e^{−zt}Q_lj = qhatMixRuneq_lj`, i.e. `edgeLo_lj ≥ 0` (ordered
pairs `σ_j ≥ σ_l`).  MPhase 6 runs the inner `t`-integral over **all of `ℝ`** — so the Baxter transform
is the *unconditional* MPhase-1 `baxterQ_fullline_transform` (`∫_ℝ e^{−zt}Q_lj = qhatMixRuneq_lj`, every
diameter pair) — and rescues the per-`t` collapse with the **RDF hard core** (`g_il = 0` on `[0,σ_il)`).
The `t<0` partial-moment correction `∫_{(0,−t]}e^{−zu}u g(u)du` vanishes because `−t < σ_il` on `Q`'s
support, i.e. the overlap `-edgeHi_il < edgeLo_lj`, which is **automatic** for positive diameters
(`neg_edgeHi_lt_edgeLo`: the `σ_l` cancels, gap `= (σ_i+σ_j)/2 > 0`) — so the g-side closes for **every**
unequal-σ combination, no ordered-pairs and no size-disparity restriction. -/

/-- info: 'FMSA.ExactMSA.MixLeg3.laplace_conv_full_of_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.laplace_conv_full_of_integrable

/-- info: 'FMSA.ExactMSA.MixLeg3.baxterQ_fullline_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.baxterQ_fullline_transform

/-- info: 'FMSA.ExactMSA.MixLeg3.mat_gside_fold_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.mat_gside_fold_full

/-- info: 'FMSA.ExactMSA.MixLeg3.gside_33_of_hgside_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.gside_33_of_hgside_full

/-! ⭐⭐⭐ **MPhase 6 — the posited root retired for ALL unequal σ.**  `MixBHRootUneq_of_oz_full` is the
full-support upgrade of `MixBHRootUneq_of_oz`: its g-side `hQtransform` is the full-line Baxter transform
(`baxterQ_fullline_transform`, satisfiable for every diameter pair), and the RDF-hard-core overlap it
needs is **automatic** (`neg_edgeHi_lt_edgeLo`, discharged internally from `0 < σ`), so **no side
condition survives** — the whole unequal-σ root stands on OZ/Baxter primitives for **every** diameter
combination, exactly like the c-side.  Axiom-clean; no `matExactMSAUnequalDiam_hcore`. -/

/-- info: 'FMSA.ExactMSA.MixLeg3.MixBHRootUneq_of_oz_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.MixBHRootUneq_of_oz_full

/-! ### MPhase 7 — the OZ primitives ARE the root conditions (`hbax`/`hgside_mix` discharged)

`MixBHRootUneq_of_oz_full` consumes `hbax` (exterior Baxter Eq 8 matched to `matMSAtail`) and `hgside_mix`
(g-side OZ Eq 32 Laplace-transformed) as OZ-primitive hypotheses.  These are not free assumptions: with
the concrete `baxterQ`/`matMSAtail` plugged in they are **equivalent to the algebraic root conditions**
(29′)/(33′) — `mat_hbax_iff_cside` (forward `c_side_constraint_of_exterior` via `mat_exterior_baxter_relation`;
reverse `mat_hbax_of_cside`) and `mat_hgside_iff_gside` (forward `gside_33_of_hgside_full`; reverse
`mat_hgside_of_gside`), the matrix analogs of the scalar `hbax_iff_h29` / `hgside_iff_h33`.  Their full
*unconditional* discharge — that the concrete `baxterQ` really solves OZ — is exactly the ring-infeasible
`matExactMSAUnequalDiam_hcore` content, so this equivalence is the honest end of the leg-3 line. -/

/-- info: 'FMSA.ExactMSA.MixLeg3.mat_hbax_iff_cside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.mat_hbax_iff_cside

/-- info: 'FMSA.ExactMSA.MixLeg3.mat_hgside_iff_gside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.mat_hgside_iff_gside

/-! ### MPhase 8 — the full MSA factorization from the OZ primitives (mixture analog of the scalar
`exactMSA_factorization_of_oz`)

`matMSAmixture_unequalDiam_of_oz` chains `MixBHRootUneq_of_oz_full` (the posited root derived from the OZ
primitives) into the capstone `MSAMixture.matMSAmixture_unequalDiam_of_hcore`, so the full unequal-σ MSA
mixture factorization stands on the OZ primitives (`hbax` + `hgside_mix` + RDF-side data), the HS side by
free `ftilde` algebra.  Its footprint is **std-3 + the single physics axiom `matExactMSAUnequalDiam_hcore`**
— identical in shape to the scalar `exactMSA_factorization_of_oz` (std-3 + `exactMSA_hcore`); the leg-3
derivation adds **no** axiom.  The `_physical` form (radial-Fourier RHS, matching the scalar conclusion
shape) additionally carries `matHSexactUnequalDiam_kspace`, the mixture HS Baxter–Fourier anchor (where the
scalar `radial_fourier(c_HS)` is a proved closed form). -/

/--
info: 'FMSA.ExactMSA.MixLeg3.matMSAmixture_unequalDiam_of_oz' depends on axioms: [propext,
 Classical.choice,
 MSAMixture.matExactMSAUnequalDiam_hcore,
 Quot.sound]
-/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.matMSAmixture_unequalDiam_of_oz

/--
info: 'FMSA.ExactMSA.MixLeg3.matMSAmixture_unequalDiam_physical_of_oz' depends on axioms: [propext,
 Classical.choice,
 MSAMixture.matExactMSAUnequalDiam_hcore,
 MSAMixture.matHSexactUnequalDiam_kspace,
 Quot.sound]
-/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.matMSAmixture_unequalDiam_physical_of_oz

/-! ### MPhase 9 — the equal-diameter root retired via the unequal-diameter leg-3

The equal-σ `MSAMixture.MixBHRoot` (bare `qhatMixR`) was only *posited* — consumed by
`matExactMSAEqualDiam_hcore`, `matMSAmixture_equalDiam`, and the IFT-smoothness analysis, but never
derived.  It is the equal-σ specialization of `MixBHRootUneq` (`edgeLo = 0`, recentering `= 1`,
`qhatMixRuneq = qhatMixR`), so `MixBHRoot_of_oz` retires it onto the SAME OZ/Baxter primitives via
the unequal-σ leg-3 (`MixBHRootUneq_of_oz_full`) + the equal-σ bridge `MixBHRoot_of_MixBHRootUneq`.
Axiom-clean std-3 — no separate equal-diameter derivation, and no physics axiom (the `hcore` enters
only later, at the factorization capstone `matMSAmixture_equalDiam`). -/

/-- info: 'FMSA.ExactMSA.MixLeg3.qhatMixRuneq_eq_qhatMixR_of_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.qhatMixRuneq_eq_qhatMixR_of_equal

/-- info: 'FMSA.ExactMSA.MixLeg3.MixBHRoot_of_MixBHRootUneq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.MixBHRoot_of_MixBHRootUneq

/-- info: 'FMSA.ExactMSA.MixLeg3.MixBHRoot_of_oz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.MixBHRoot_of_oz

/-! ## MSAEMIX.6 — the general-`N` matrix MSA solution family is `C^∞` at `K = 0`, unconditionally

The matrix analogue of the `N = 1` `exists_contDiffAt_bhRoot` (gated above): the mixture MSA
amplitudes `(Dt, Gt)` are a `C^∞` family of the coupling near `K = 0`, seeded from a hard-sphere
Blum–Høye root, at **equal** σ (`exists_contDiffAt_matBhRoot_of_physical`) and at **unequal** σ
(`exists_contDiffAt_matBhRootUneq_of_physical`).  Both are fully unconditional — no
Jacobian/determinant hypothesis — because the IFT's partial-Jacobian invertibility reduces (via the
recentering + a diagonal-conjugation Sylvester argument, `detHuneq_eq_Q0`/`detGuneq_eq_Q0`) to the
**same** physical Baxter matrix `Q0_mat_phys` nonsingular, which M.4
`FMSA.MatrixQ0.Q0_mat_phys_isUnit_det` proves for every physical σ (general, unequal) from the
rank-two Weinstein–Aronszajn positivity `Q0_moment_det_pos`.  Std-3 — the asymmetric row-diameter
block carries **no** physics axiom (in particular no `no_spinodal`); the sole remaining grade is
Blum–Høye transcription faithfulness, exactly as at `N = 1`. -/

/-- info: 'MSAMixture.detHuneq_eq_Q0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.detHuneq_eq_Q0

/-- info: 'MSAMixture.detGuneq_eq_Q0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.detGuneq_eq_Q0

/-- info: 'MSAMixture.exists_contDiffAt_matBhRoot_of_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.exists_contDiffAt_matBhRoot_of_physical

/-- info: 'MSAMixture.exists_contDiffAt_matBhRootUneq_of_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.exists_contDiffAt_matBhRootUneq_of_physical
