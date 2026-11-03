# Actual M2 joint root germ and a strict-minimum zero-mode contour

All13 new public proof bodies compiled. Their ACTUAL axiom queries contain
exactly propext, Classical.choice and Quot.sound; exact guards are installed.
Full guarded validation AND the independent post-run hash audit PASSED:
1089 exact guards /95 research modules plus root /96 pinned compiler commands.
ALL92 prior sources/artifacts/footprints,530 frozen hashes and all existing
9paper/2raw/9Mathlib import pins are unchanged. No new external import or
shared dependency build. Replay9prefixes/33pins passed before/after checks.

## Constructed result

`M2JointZeroContour.exists_actual_strict_minimum_zero_contour` constructs a
contact y in the existing widened rational box, ONE jointly analytic original
BH root germ P(b,w), and an analytic scalar contour w=psi(b). Its public
`ContourData` predicate records all of the following:

- P(b0,w0)=amplitudes(y), and P gives actual original BH roots throughout a
  parameter neighbourhood, with signed original Dt/G amplitudes retained.
- psi(b0)=w0, psi'(b0)=0, and psi(b)>w0 at every sufficiently near b!=b0.
- On one parameter neighbourhood the TRUE real zero-frequency observable
  f(b,w)=F0(P(b,w)) satisfies f>0 iff w<psi(b), f<0 iff psi(b)<w, and
  f=0 iff w=psi(b). This is the locally unique zero contour ON THIS GERM.
- Along the contour, coupling stays positive and the second tail weight
  stays negative. P(b,psi(b)) is an actual original BH root, its true real
  zero mode and HONEST complex Laplace factor are zero, and its original
  amplitudes fail full canonicity.

No root, inverse, joint germ, contour, derivative, numerical root or external
analytic enclosure is supplied as a premise of the existence theorem.

The physical data remain N=1,sigma=1,eta=1/10,rho=3/(5*pi),rates=(9/5,12),
strengths=(1,w). The b0,w0 are CONSTRUCTED REAL values in the existing widened
rational box near5.6135716462,-4.8287538385, not asserted rational midpoints.
Uniqueness of that boxed contact identifies the point with the earlier
curvature and weight checkpoints. Old narrow witness membership is separate.

This is a local classification of the ZERO-FREQUENCY FACTOR on one jointly
constructed actual root germ. The positive-F0 side is NOT asserted fully
canonical or physically stable. No first contact, HS/PY identification,
all-wave first loss, RDF positivity, global root count or complex Taylor
radius is proved here. At this joint-only checkpoint, contour second
derivatives and local zero-count geometry remained separate. The subsequent
`codex_m2_local_bifurcation.md` now proves the true second-derivative formula,
positive numerical lower bound, actual quadratic lower bound and exact local
zero/one/two-zero picture. The earlier strict minimum and psi'=0 remain valid.
The original initial canonical domain is not enlarged by later islands.

## Actual joint residual and both derivatives on the same germ

`M2JointBranch` proves the exact identity at EVERY parameter/amplitude point

    jointSystem((b,w),x)=F(x)-b*forcing(w)=original coordinate residual,
    F(x)=residualFormula(strength0,0,x),
    forcing(w)=(10*pi/9,pi*w/6,0,0).

Joint analyticity is derived from the actual original BH residual and the
actual continuous amplitude-coordinate equivalence. The amplitude partial
is exactly the OLD four-dimensional Jacobian J(x). Its already proved boxed
row defect discharges injectivity, finite-dimensional surjectivity and hence
analytic-IFT invertibility. The IFT CONSTRUCTS one root germ in BOTH parameters.
The honest real observable is proved analytic for any analytic amplitude germ.

`joint_branch_coupling_geometry` restricts THIS P to (b,w0). Differentiating
its genuine nearby roots gives J*p'=forcing(w0). Old Jacobian injectivity
identifies p' with ALL FOUR certified contact velocities. The existing actual
second-derivative theorem derives the true acceleration equation and genuine
second derivative; its proved error budget gives kappa>4/5. The result records

    f(b0,w0)=0, partial_b f(b0,w0)=0,
    true partial_b partial_b f(b0,w0)=kappa>4/5,
    f(b,w0)>=(b-b0)^2/10 near b0.

`joint_branch_weight_geometry` restricts the SAME P to (b0,w). Differentiating
genuine nearby roots gives J*p'=b0*(0,pi/6,0,0). The previously kernel-proved
weight error budget gives the TRUE partial_w f<-19, with the honest complex
Laplace factor derivative equal to its real embedding. No independent choice
of two unrelated one-dimensional branches is used.

## Scalar analytic IFT, strict minimum and local signs

`ImplicitZeroContour` is a general proved calculus module. A genuine negative
weight derivative discharges the scalar analytic-IFT invertibility condition;
the contour is constructed, with a neighbourhood equivalence f(b,w)=0 iff
w=psi(b). Continuity of the genuine Frechet derivative, obtained from
analyticity, gives one rectangle where every fixed-b weight function is
strictly decreasing. The mean value theorem proves this monotonicity; no
uniform derivative enclosure is assumed.

The actual positive punctured coupling axis f(b,w0)>0 and f(b,psi(b))=0
then force psi(b)>w0 for nearby b!=b0. Fermat's theorem gives its TRUE
first derivative zero. Strict weight monotonicity also gives BOTH strict
sign equivalences and the zero equivalence in one parameter neighbourhood.
No unsupported mixed-Hessian or second implicit-derivative formula is used.

Actual roots along the contour follow by pulling the joint root condition
back along the continuous map b -> (b,psi(b)). Existing exact original factor
identities prove the honest complex factor zero and actual noncanonicity.
The existing `M2ZeroMode.actual_fourier_at_zero` identity also translates
the recorded F0 zero into the genuine physical Fourier factor zero at k=0;
this does not identify it as the FIRST Fourier loss.
Continuity and the already proved parameter signs preserve positive coupling
and negative second weight on this same germ.

## Verification and reproduction

Public declarations: M2JointBranch5, ImplicitZeroContour4,
M2JointZeroContour4. No new external import or transcendental bound is needed.
The existing9 direct Mathlib,9 paper and2 raw LeanCode artifact pins are
retained; the foundation source/config manifest remains frozen.

The standard-library full consumer uses the existing direct pinned compiler:

    python3 scripts/check_project.py

The producer can be replayed in the existing offline dependency environment:

    PYTHONPATH=/tmp/codex_fmsa_arb_deps /opt/anaconda3/bin/python3 scripts/certificates/check_m2_tangency_generation.py

It binds the SAME9 canonical generated prefixes and now33source/input pins,
including all three handwritten joint modules. This is provenance, not a
mathematical premise. The full consumer checks these pins before and after
compilation and invokes no Lake/shared dependency build.

Three actual corrupted copied Lean bodies are rejected: original residual
identity raised by1; generic strict-minimum direction reversed; actual
ContourData strict-minimum direction reversed. Rejection occurs at the
mathematical body, before axiom-message failures. Consumer controls reject
an altered new source hash, an omitted joint-source pin, and a changed ninth
canonical prefix. Producer/full consumer Python-O executions reject without
metadata writes. Source EOF spacing is checked before full input pinning;
raw compiler warnings are preserved.

Completed evidence is in results/lean/validation.json, results/lean/build.log
and the generation replay receipt. ALL prior92 sources, artifacts and axiom
footprints were independently compared after the run and are unchanged.
Foundation1.0.17 and TeX are untouched; research remains active/unmerged.
