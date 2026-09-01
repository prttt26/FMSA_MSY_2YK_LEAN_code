import LeanCode.YukawaOZMix.MSAMixtureBreakpointConvDirect
import LeanCode.Closures.FirstOrderEquivalence
import LeanCode.Closures.MSAFamilyConcrete
import LeanCode.YukawaOZMix.MSAMixtureFactorization
import LeanCode.YukawaOZ.MSAClosedForm
import LeanCode.YukawaOZMix.MSAMixturePositivity
import LeanCode.YukawaOZMix.MSAMixtureSelection
import LeanCode.YukawaOZ.MSAFactorizationFromOZ

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
