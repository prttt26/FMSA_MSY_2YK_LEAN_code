# M2 ordinary-kernel regularity certificate

This work targets the numerical-to-actual `EndpointRegular` gap identified in
the earlier external M2 Jacobian audits. All four proof bodies compiled, and
all 22 public axiom reports were actually queried: only propext, Classical.choice
and Quot.sound occur. Their exact guards passed the complete package validation
recorded below. No analytic enclosure or external PASS flag is a premise.

## Statement and scope

The data are exactly one species, sigma=1, eta=1/10, rho=3/(5*pi) and two
rates z=(9/5,12). `M2KernelCertificate.lower` and `upper` give literal rational
bounds for the ORIGINAL ordered amplitudes (Dt1,Dt2,G1,G2). They exactly match the
first four `exact_widened_box_rational` entries of
`results/certificates/codex_m2_jacobian_arb.json`: the frozen root box expanded
by delta=1e-10*max(1,abs(lower),abs(upper)) in each coordinate. Exact source
fractions, rather than rounded displays, define the mathematical domain.

The proved theorem `actual_regular_on_box` states that EVERY amplitude
point in that box has invertible ORIGINAL amplitude partial, for arbitrary
real coupling and arbitrary two-tail strengths. It does not require the
point to be a root, canonical, physically stable or nonnegative componentwise.
The two negative amplitude coordinates are retained. The box is separately
proved nonempty; the result is not made vacuous by inconsistent box premises.

Coupling and strengths occur only as additive amplitude constants in the
first residual. Their disappearance from this derivative is PROVED by the
literal Jacobian identity, rather than assumed as a convention.

## Four parts of the proof

1. `M2JacobianFormula` constructs an equivalence from Fin 4 to the complete
   original amplitude index. The forward/inverse coordinate identities retain
   every original Dt/G entry. Sixteen private exact identities prove all
   candidate symbolic Jacobian entries against `BHPolynomialJacobian.jacobian`
   by expanding the original polynomial dictionaries and kernel algebra.
   `jacobian_formula` and `jacobian_formula_actual` assemble these identities
   for arbitrary original amplitude points, strengths and coupling. SymPy
   supplies ONLY candidate expressions; its differentiation is not trusted.

2. `M2PhysicalBounds` proves twenty-decimal pi bounds and reciprocal bounds
   from mathlib's existing pi theorems and positivity. It proves an explicit
   21-decimal interval for exp(-3/5) from `Real.exp_bound` with 20 finite series
   terms and the full rigorous remainder. The exact exponential multiplication
   identity and monotonicity of nonnegative powers give outward rational
   intervals for multipliers 3,6,20,23,40, covering ALL exponential atoms in
   the sixteen Jacobian formulas. These are real transcendental statements
   checked inside Lean, not rationalized physical constants or Arb premises.

3. `RealIntervalCertificates` proves signed multiplication by bounding all
   four rectangle corners. Addition, negation and absolute-value rules also
   permit explicitly proved outward rounding. The candidate generator rounds
   interval endpoints outward to a grid with denominator 10^24 after each
   arithmetic operation. Every corner/rounding comparison is then proved by
   kernel-checked rational arithmetic. Negative intervals and zero-crossing
   intervals do not require an unproved sign convention.

4. `M2KernelCertificate` proves sixteen entry enclosures and sixteen defect
   bounds as small private lemmas, then assembles the strict uniform row bound

       for every i, sum_j abs((1-C*J(x))_ij) < 1/1000000.

   C is the literal exact rational preconditioner from the previous report.
   `ordered_partial_coordinates` identifies its four-coordinate matrix action
   with the genuine actual partial. The already proved finite maximum-coordinate
   row-defect argument gives injectivity; finite dimensionality supplies a
   continuous linear equivalence in the exact `EndpointRegular` interface.
   No preconditioner inverse or analytic enclosure is supplied as a hypothesis.

The prior external report is used to CHOOSE the rational box and C, not as a
proof that its analytic bounds or PASS flag are valid. All numerical proof
obligations above must be checked independently by the ordinary Lean kernel.

## Reproduction

The existing read-only Python dependency directory supplies SymPy 1.13.2 and
python-flint 0.6.0 (the latter is imported by the old symbolic-model helper;
Arb enclosure results are not premises of the generated Lean proofs).

From the research package root:

```sh
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_jacobian_formula.py > /tmp/M2JacobianFormula.body
python3 scripts/certificates/generate_m2_physical_bounds.py > /tmp/M2PhysicalBounds.body
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_kernel_certificate.py > /tmp/M2KernelCertificate.body
python3 scripts/check_project.py
```

Each `.body` is the exact generated source prefix before the first
`/-- info:` axiom report. Guards are derived only from actual compiler queries,
not guessed by a generator. The generated body comparison is byte-for-byte,
modulo the final newline. Full validation compiles all research modules and
the root against pinned read-only imports and audits the frozen foundation.

## Remaining mathematical obligations

This certificate does not prove that a root lies in the box. The old M2
root-existence, PY-prefix identification, tangency, first-loss, all-real-wave
and complex-domain numerical certificates retain their previously recorded
external status. A regular partial alone is not an all-wave stability test or
a lower bound on the Taylor radius at zero coupling. No universal equivalence
between real-root existence and Taylor convergence follows.

The M1 and M3 analytic interval reports remain external. Generic positive-
density finite-fiber certificates, matrix escape, nonisolated singular endpoint
control and general multitailed Taylor lower bounds remain open. Foundation
1.0.17 and TeX remain untouched; no mathematical axiom is introduced.

## Negative controls

Two ad hoc copies of the first actual generated entry certificate were
compiled separately. Raising the first exponential lower bound by one makes
the proof fail at its real transcendental leaf. Raising the first product
lower bound by one makes the proved-corner arithmetic fail. Both returned
nonzero compiler status with Lean proof diagnostics. No repository proof
source was corrupted. The complete positive certificate compiled successfully.

## Full verification (2026-10-29)

PASS: **1000** exact standard-three-axiom guards, **70** research modules plus
the root, **71** pinned compiler commands. The four new modules add 22 public
theorems; all private arithmetic/formula lemmas are consumed by those guarded
proofs. The complete proof bodies and research root also passed direct pinned
compilation before the full guarded run. Both corrupted actual-certificate
controls were rejected by Lean proof diagnostics. Final generation of all
three source bodies agrees byte-for-byte with the guarded sources before
the compiler-derived axiom-report suffix.

Independent post-run audit checks every input/source/artifact/raw-log hash
and ALL 66 prior module source/artifact/footprint records, unchanged from
the 978-guard baseline. All 530 frozen hashes, nine validated paper imports,
seven prior direct Mathlib imports and two locked raw LeanCode imports are
unchanged. The sole added direct Mathlib import is the already cached
`Mathlib.Analysis.Real.Pi.Bounds`; its artifact is separately anchored before
the run and unchanged afterward, for eight direct Mathlib pins in total. No
shared/Lake build, foundation write, TeX write or merge-back was performed.
The raw compiler log retains style/unused-simp warnings and is preserved
verbatim; all guarded proof checks pass. Existing M1/M2/M3 external rational
checkers still pass their unchanged source/model pins.

Evidence: `results/lean/validation.json`, `results/lean/build.log`.

## Subsequent root-existence extension (2026-10-30)

The earlier root-existence gap is now closed at the exact rational state in
`proof_notes/codex_m2_root_existence.md`: the same box contains exactly one
original signed Dt/G root, and it is actually regular. The box, C and all
proofs in this earlier module remain unchanged. This supplies no exact
joint tangency witness or PY identification; those earlier external/open
qualifications still apply.
