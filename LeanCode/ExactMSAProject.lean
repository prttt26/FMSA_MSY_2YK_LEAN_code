import LeanCode.YukawaOZMix.MSAMixtureBreakpointConvDirect
import LeanCode.Closures.FirstOrderEquivalence
import LeanCode.Closures.MSAFamilyConcrete
import LeanCode.YukawaOZMix.MSAMixtureFactorization
import LeanCode.YukawaOZ.MSAClosedForm
import LeanCode.YukawaOZMix.MSAMixturePositivity
import LeanCode.YukawaOZMix.MSAMixtureSelection
import LeanCode.YukawaOZ.MSAFactorizationFromOZ
import LeanCode.YukawaOZMix.MixtureBlumHoyeDerivation

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
axiom each — `exactMSA_kspace_residual` and `matExactMSAEqualDiam_kspace_residual` — carried by the
**out-of-`defaultTargets`** certificate libs `ExactMSA6Certificate` /
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

/-! **The c-side recentering fix, wired to `MixBHRootUneq`.**  `MixBHRootUneq`'s **c-side (29′)** is
corrected to use the recentered Baxter transform `e^{z·edgeLo_jl}·Q̂_jl` (the σ-edge FINDING);
`mixBHRootUneq_cSide_of_exterior` proves that conjunct follows exactly from the c-side exterior closure
via `c_side_constraint_of_exterior` + `∑_l Dt_il·δ_lj = Dt_ij`.  The **g-side (33′) is left with the bare
`Q̂_lj`**: the g-side Eq (34) has a different amplitude structure (`ĝ_il = Gt_il·e^{−z·edgeHi_il}` on the
whole bracket), so it does NOT get a `Q̂`-recentering — the naive Wiener–Hopf-consistency intuition
fails.  The g-side (33′) rigorous form is open (needs the repo-consistent mixture g-source). -/

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
