# Convergence subproject: closeout readiness, 2026-11-02

**Status after the merge (2026-11-02).** The convergence library was merged into
`MSA_and_1st_Truncation` 1.0.18: 2639 exact guards, 284 modules. The merge sections below predate it and
are history. Open problems: `../MSA_Convergence/OPEN_PROBLEMS.md`.

This is a preparation record, not a claim that the complete convergence
boundary has been determined. The user asked us to prepare for a
partial or failed outcome and eventual session closure. The research
package remains separate from the frozen foundation until the single
merge-back specified in handoff 036. No TeX file is edited here.

## What can be stated as proved

| Scope | Current evidence | Limit of the claim |
|---|---|---|
| F1–F4 of `FMSA_dp_output/md/FORMALIZATION_TODO.md` | Foundation 1.0.17 Lean declarations and its own formalization ledger; F4 includes a locally proved Pringsheim theorem using only standard axioms | F2/F4 require explicit fold and sign hypotheses; they do not classify every physical mixture state |
| Actual local and canonical branch framework | Research Lean modules from `ActualCanonicalBranch` through `MaximalCanonicalBranch`, `MixtureHSCanonicity` and `MixtureEndpointNoEscape`; latest checker receipt below | Actual local sums and finite selected endpoint limits do not give a general Taylor-radius lower bound |
| One species, one attractive or repulsive tail | `SingleTailCanonicalRadius`, `RepulsiveOneTailBoundary`, `SingleTailFullRealBoundary`, `NonnegativeAbelConverse`; exact real-axis convergence set and endpoint sums | This does not extend to multi-tail or arbitrary multi-species mixtures |
| Multi-tail pure fluid, one coupling ray | `PureFluidFoldTheorem.taylor_radius_is_fold`, commits `0bcd181` and `2e18972`; independently checked below | All positive tail strengths and rates, `0<xi<1`; every `D_t` radius is finite `R`, every `G_t` radius at least `R`, and the endpoint series converge absolutely to an actual root. No interior Jacobian-invertibility or square-root fold claim |
| Pure-fluid mixed tail-strength coefficients | `PureFluidMixedStrict.mixed_coefficients_exact`, commit `ba0c16d`; independently checked below | Exact pattern: `D_t` monomial coefficient vanishes iff it lacks `K_t`, and is strictly positive otherwise; every nonconstant `G_t` monomial coefficient is strictly positive. No mixture statement |
| Conditional mixture endpoint summation | `EventuallySignedEndpointSummation`, with actual MSA root identification at a finite maximal endpoint | Eventual component signs are not established for general PSD mixtures |
| Equal-diameter binary cross-sign class | `EqualDiameterCrossSign` and `EqualDiameterActualStrengthSign`, including the literal `TailMatrix` and `IsRoot` first-equation bridge | Opposite cross signs do not characterize the `R<τ_f` subset |

The complete package check after Claude's exact mixed-sign upgrade is
`PASS: 2625 exact theorem guards, 283 research modules`. The checker
records foundation 1.0.17 unchanged,
standard-three axioms only, exact per-theorem guards, source/import and
artifact hashes. I independently reran it with one Lean process, a
30 GiB monitored cap, and `/tmp/fmsa_lean_single.lock`.

## Refuted claims and evidence level

| Claim or example | Status | Appropriate wording |
|---|---|---|
| Positive real Exact-MSA solution iff Taylor convergence for every state | False as a universal target | The PY-seeded germ, real roots, canonical branch and series radius must be distinguished |
| M3: full canonicity forces convergence on the whole initial interval | Refuted by an external exact/interval certificate with Lean-checked generic implication and actual BH interface | At a certified canonical real point, the original amplitude vector series fails; do not claim every coordinate fails |
| F5 competing-tail real regular branch through `τ=3` but radius at most `2.75` | External interval certificate, not a Lean numerical instance; isolated replay available | It refutes real branch existence implying series convergence |
| PSD tails imply `R=τ_f` or eventual coefficient signs | Refuted by multiprecision and float diagnostics in `claude_two_tail_convergence.md` | External evidence, not a Lean or interval instance |
| F6 second-order supporting coexistence pairs | External interval certificate, not a Lean theorem | Keep its model-formula and scope qualifications |

The broad counterexample is already decisive against the user's former
universal equivalence. Failure to classify every radius does not erase
the proved conditional theorems or the certified counterexamples.

## Questions that remain open

1. For general PSD mixture tails, is the common amplitude radius always
   at least the initial physical canonicity-loss coupling `τ_inst`?
   The targeted binding-pair searches reached only float64 ratios
   `|τ*|/τ₀ > 1`; the last short run reached 1.54004. `τ₀` is a
   sampled zero-frequency proxy, not a certified `τ_inst`.
2. For frustrated one-tail mixtures with at least three species,
   does `R=τ_f` hold? A Lean matrix coefficient counterexample blocks
   a simple Loewner-positivity proof but is not a physical MSA
   counterexample.
3. At equal diameters with binary opposite cross signs, which
   parameters actually have `R<τ_f`? The exact sign class is proved;
   its failure subset is not classified.

Claude integrated the **multi-tail pure-fluid** theorem in handoff 355;
the user's follow-up fixes the merge destination as `MSA_Convergence`
(handoff 356). The local import closure of `PureFluidFoldTheorem` contains
121 research modules, including the ten new fold-family modules, with
no missing local import. Mixed coefficients in separate tail strengths
are now proved with an exact strict sign pattern in
`PureFluidMixedStrict`: the polynomial identity holds for every real
strength vector, not just on a positive ray. The fold theorem does not claim
Jacobian invertibility at every interior point or a nondegenerate
square-root fold; those qualifications must survive in the paper mapping.

## Final verification and merge gate

1. The pure-fluid batch is already integrated and independently
   checked in the research package; do not move it into the frozen
   foundation under the present instruction.
2. Before any later foundation release, run `scripts/check_foundation.py`
   read-only, then the package's
   `check_project.py` under the 30 GiB cap and single-process lock.
   Preserve its `validation.json`, build log, input/artifact hashes,
   exact theorem guards and standard-axiom footprint in the record.
3. Reconcile the chronological TODO and paper correspondence notes so
   an old “open” line is not mistaken for the latest result. Record
   remaining assumptions and external evidence explicitly. The
   paper-writing session, not this session, applies any SI TeX edits.
4. The user has assigned the later **one** deliberate integration into
   `MSA_and_1st_Truncation` to Claude Code (handoff 360), including
   downstream coordination and validation of the new baseline. The
   foundation is still frozen at 1.0.17 now; this session does not
   merge or change it.

The active goal remains incomplete until the correct convergence
boundary is either proved or explicitly delimited as open in the
final deliverables and the authorized integration is finished.
