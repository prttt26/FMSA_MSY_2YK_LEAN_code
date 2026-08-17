import LeanCode.Closures.DPClosureMap
import LeanCode.Closures.FirstOrderEquivalence
import LeanCode.HardSphere.BaxterWienerHopf
import LeanCode.HardSphere.JumpAsymptotic
import LeanCode.HSMixture.MixtureDetGeneralN
import LeanCode.HSMixture.MixtureZerosPhys
import LeanCode.HSMixture.Q0DetRankTwo
import LeanCode.YukawaOZMix.MixtureConvolution
import LeanCode.YukawaOZMix.MixtureDCFSmooth
import LeanCode.YukawaOZMix.MixtureRealSpace
import LeanCode.YukawaOZMix.ReflectedTermSupports
import LeanCode.YukawaOZMix.MixtureRDFStructureFactor
import LeanCode.YukawaOZMix.MixtureYukawaContourTerm

/-!
# FMSA-DP paper — scope and axiom gate

**What this file is for.** The `LeanCode` development covers several tracks:
The paper is `FMSA_dp_output/tex/fmsa_dp_theory.tex`.
This paper contains:
the first-order mixture DCF,
the Mittag-Leffler RDF series and its pole analysis.
These are not claimed:
the matrix OZ★ uniqueness route, the exact-MSA algebra, free energy, cDFT support.


That distinction was drawn by hand once, and a hand-drawn line rots. This file makes it
mechanical, in two ways:

1. **Scope by import.** The imports below are exactly what the paper's chain needs. If a result
   quoted by the paper starts depending on another track, that shows up here as a new import
   rather than being discovered by someone re-auditing the ledger.

2. **The axiom footprint is a build gate, not a claim.** Every `#guard_msgs` block below fails
   the build if the axiom set of that declaration changes. Of the twenty-three results guarded
   here, twenty are axiom-clean and three carry more; the union of what those three reach is
   five non-standard axioms — four mathematical and the one physical. If that stops being true,
   `lake build` says so.

⚠ Adding an import here widens what the paper claims. Do not add one to make a `#guard_msgs`
pass — if a declaration needs a track the paper does not claim, the paper is what should change.

Measured 2026-08-12 against Mathlib `v4.31.0` (rev `fabf563a7c95`).
-/

/-! ## Axiom-clean: the standard three only (twenty results) -/

/-- info: 'FMSA.MRS.star_of_first_order_oz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MRS.star_of_first_order_oz

/-- info: 'FMSA.MRS.star_of_oz1_baxter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MRS.star_of_oz1_baxter

/-- info: 'FMSA.MRS.star_entry_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MRS.star_entry_differentiableAt

/-- info: 'FMSA.MixtureHSPoles.detC_zeros_infinite_phys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MixtureHSPoles.detC_zeros_infinite_phys

/-- info: 'FMSA.MixtureDCFSmooth.pbpConvG_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MixtureDCFSmooth.pbpConvG_eq

/-- info: 'FMSA.MixtureDCFSmooth.dcfOdd_contDiffOn_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MixtureDCFSmooth.dcfOdd_contDiffOn_upper

/-- info: 'FMSA.ReflectedSupports.parity_partners_causal_projection_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ReflectedSupports.parity_partners_causal_projection_zero

/-- info: 'FMSA.MixtureConvolution.pbp_edge_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MixtureConvolution.pbp_edge_eq

/-- info: 'FMSA.MatrixQ0.Q0_mat_phys_isUnit_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MatrixQ0.Q0_mat_phys_isUnit_det

/-- info: 'FMSA.HardSphere.baxter_wiener_hopf_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.HardSphere.baxter_wiener_hopf_factorization

/-- info: 'FMSA.FirstOrderEquivalence.oz_deriv_eq_firstOrderLine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderEquivalence.oz_deriv_eq_firstOrderLine

/-! The paper states its first-order-equivalence theorem at **arbitrary** order, so the
general-order results are gated too, not just the `γ = 1` line above.  The paper text has
already once drifted into claiming that only the product rule was formalized; these three
guards are what make that claim checkable instead of remembered.

`oz_taylor_coeff_eq_cauchy_convolution` is the load-bearing one (general Leibniz on the
constant OZ product), and `cauchy_convolution_middle_empty_iff` is the statement the paper
uses to explain why *first* order, and only first order, is solvable in closed form. -/

/-- info: 'FMSA.FirstOrderEquivalence.oz_taylor_coeff_eq_cauchy_convolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderEquivalence.oz_taylor_coeff_eq_cauchy_convolution

/-- info: 'FMSA.FirstOrderEquivalence.oz_msa_taylor_eq_hierarchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderEquivalence.oz_msa_taylor_eq_hierarchy

/-- info: 'FMSA.FirstOrderEquivalence.cauchy_convolution_middle_empty_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderEquivalence.cauchy_convolution_middle_empty_iff

/-- info: 'FMSA.FirstOrderClosure.dpDCFLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderClosure.dpDCFLinear

/-- info: 'FMSA.FirstOrderClosure.py_first_order_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderClosure.py_first_order_outer

/-- info: 'FMSA.FirstOrderClosure.msa_first_order_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderClosure.msa_first_order_outer

/-! ## The RDF side: structural contrast, all axiom-clean

These back claims the paper's own abstract makes -- that the RDF carries the inverse twice, that
the determinant therefore appears squared, and that the inverse count is what separates a finite
closed form from an infinite Mittag-Leffler series.  They were absent from an earlier version of
this file, which under-scoped the paper.
-/

/-- info: 'FMSA.MixtureRDF.oz1_H1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MixtureRDF.oz1_H1_eq
/-- info: 'FMSA.MixtureRDF.rdf_entry_eq_num_div_det_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MixtureRDF.rdf_entry_eq_num_div_det_sq
/-- info: 'FMSA.MixtureRDF.rdf_sub_dcf_is_dressed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MixtureRDF.rdf_sub_dcf_is_dressed

/-! ## The results that carry axioms

Three of the twenty guarded results reach past the standard three, and between them they reach
five non-standard axioms: `zeroFree_lowerHalfPlane_of_homotopy` and the physical
`pyhs_mixture_no_spinodal` (via `mixtureDet_pole_free_N`), `radialShell_bounded_injective` and
`wiener_causal_resolvent` (via `g0_HS_contact_value`), and
`halfDiskBoundary_eq_sum_of_small_circles` (via the Mittag-Leffler contour term).

Two of the development's seven mathematical axioms stay out of reach:
`circleIntegral_eq_sum_of_small_circles`, which has no consumer outside its own file, and
`sokhotski_plemelj_upper`, which has no consumer anywhere.  The paper quotes the whole ledger
rather than this subset -- overstating an assumption load is the safe direction, and the subset
moves whenever the development grows.

⚠ `matOzStar_unique` (matrix OZ★ uniqueness, the route that discharged the mixture inner-RDF
identification) is deliberately NOT guarded here.  It is a finished result, but the paper states
nothing it corresponds to: the paper's RDF content is the structural contrast -- the inverse
appears twice, hence an infinite Mittag-Leffler series -- not the RDF construction or its
well-posedness.  Guarding it would gate a claim the paper does not make, and would pull
`matRadialShell_bounded_injective` into reach for no stated result.  Add it here only together
with a Part I result that needs it.
-/

/-- info: 'FMSA.MixtureGenN.mixtureDet_pole_free_N' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 FMSA.Analysis.zeroFree_lowerHalfPlane_of_homotopy,
 FMSA.MixtureNoSpinodal.pyhs_mixture_no_spinodal] -/
#guard_msgs in
#print axioms FMSA.MixtureGenN.mixtureDet_pole_free_N

/-- info: 'FMSA.HardSphere.g0_HS_contact_value' depends on axioms: [propext,
 Classical.choice,
 FMSA.radialShell_bounded_injective,
 FMSA.wiener_causal_resolvent,
 Quot.sound,
 FMSA.Analysis.zeroFree_lowerHalfPlane_of_homotopy] -/
#guard_msgs in
#print axioms FMSA.HardSphere.g0_HS_contact_value

/-- info: 'FMSA.MixtureRDF.contourSum_leading_term' depends on axioms: [halfDiskBoundary_eq_sum_of_small_circles,
 propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.MixtureRDF.contourSum_leading_term
