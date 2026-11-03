# Actual M2 contour curvature and local zero-mode bifurcation

All10 new public proof bodies compiled and their ACTUAL axiom queries contain
exactly propext, Classical.choice and Quot.sound. Exact guards are installed.
Full guarded validation AND the independent post-run hash audit PASSED:
1099 exact guards /99 research modules plus root /100pinned compiler commands.
ALL95 prior source/artifact/footprint hashes,530 frozen source/config hashes
and all9paper/2raw/9Mathlib pins are unchanged. Same9 generated prefixes now
bind37 source/input pins, checked before and after compilation. No new
external import, transcendental leaf or shared dependency build.

## Constructed conclusion

`M2LocalBifurcation.exists_actual_local_bifurcation` constructs the contact y,
ONE original jointly analytic BH root germ P(b,w), its analytic zero-mode
contour w=psi(b), true derivatives kappa,d and positive neighbourhood radii.
All premises are discharged from the fixed physical data and the existing
widened rational contact box. No root, inverse, germ, contour, Hessian,
acceleration, numerical root count or analytic enclosure is supplied.

The true derivatives on THIS SAME P and contour satisfy

    kappa = partial_b partial_b F0(P)(b0,w0) >4/5,
    -10001 < d = partial_w F0(P)(b0,w0) <-19,
    kappa+d*psi''(b0)=0,
    HasDerivAt (deriv psi) (-kappa/d) b0,
    psi''(b0)=-kappa/d >1/20000.

The true curve, not just a tangent model, has a local lower bound

    psi(b) >= w0+(b-b0)^2/100000.

On a coupling interval and for all sufficiently near weights:

- Below w0: F0(P(b,w))>0 throughout the coupling interval, so no local
  zero-frequency-zero coupling occurs on this germ.
- At w0: the ONLY local zero coupling is b0; all other local couplings
  have strictly positive F0.
- Above w0: there are EXACTLY TWO zero couplings l<b0<r, one on each side,
  with an exhaustive iff for every coupling in the interval. F0 is strictly
  negative between them and strictly positive outside them in the interval.

All these parameters retain positive coupling and negative second weight,
and P gives actual original BH roots throughout the local rectangle.
The existing honest Laplace/physical Fourier identities transfer every
recorded F0 zero to the true factor zero and noncanonicity.

These are zero COUPLINGS of the honest ZERO MODE ON P. Original BH roots
exist throughout this rectangle; this is NOT a zero/one/two count of all
Exact-MSA solutions. The positive-F0 region is not asserted full canonicity
or stability. First contact, HS/PY identification, all-wave first loss,
RDF positivity and complex Taylor radii remain independent.

Data remain N=1,sigma=1,eta=1/10,rho=3/(5*pi),rates=(9/5,12),strengths=(1,w).
The b0,w0 are CONSTRUCTED REAL values in the existing widened rational box
near5.6135716462,-4.8287538385, not asserted rational midpoint values. Old
narrow witness membership remains separate. The positive neighbourhood radii
are existential; no explicit numerical uniform rectangle is certified here.
The contour quadratic bound has its own local neighbourhood, not an asserted
bound over the whole old numerical parameter box. The derivative lower bound
is conservative, not a tight numerical estimate of the contour curvature.

## True second derivative without an assumed Hessian

`ImplicitContourCurvature.contour_acceleration_equation` differentiates the
ACTUAL analytic identity f(t,psi(t))=0 on a genuine neighbourhood. With
Gamma(t)=(t,psi(t)), its true velocity at b0 is (1,0). Let

    A(t)=fderiv Real f (Gamma(t)).

Analyticity gives its true derivative through Gamma. At nearby analytic
points, the chain rule identifies

    deriv(f o Gamma)(t)=A(t)(1,deriv psi(t)).

The actual zero identity makes this function zero near b0. Differentiating
that EVENTUAL identity with `HasDerivAt.clm_apply` retains the derivative of
both the operator and its argument. The first term is the TRUE second
coupling derivative, identified by differentiating the analogous eventual
first-derivative identity on the fixed-weight axis. Linearity identifies the
second term as d*psi''. Derivative uniqueness proves the acceleration equation.
No external Hessian entry or second implicit-chain formula is assumed.
`contour_second_derivative` solves it only after internally verified d!=0.

## Numerical lower bound without new transcendental enclosures

`M2ContourCurvature.weight_slope_abs_lt_of_tangent_equation` uses the OLD
proved q=1e-6 row defect and norm(C*b*f_w)<=1000. The actual tangent equation
and existing linear error theorem give velocity error<.01. Thus the actual
weight velocity norm is<1000.1. The proved L1 gradient budget<=10 gives
|d|<10001, with the correct original Pi-space norm and scalar pairing.

The old actual weight bound d<-19 and true coupling curvature kappa>4/5
then imply -kappa/d>1/20000. Existing second-derivative testing, applied after
subtracting (b-b0)^2/100000, proves the lower bound for the actual contour.
There is no new pi/exp leaf or external interval premise.

`CurvatureData` explicitly records the true real and honest complex weight
derivatives, actual coupling second derivative, true contour acceleration
equation, `HasDerivAt (deriv psi)`, the numerical lower bound and local
quadratic inequality. Its physical existence theorem supplies every premise.

## Exact zero/one/two classification

`LocalMinimumLevels.monotone_sides` uses continuity of the TRUE second
derivative to obtain strict decrease left of the vertex and strict increase
right of it, on arbitrarily small closed intervals. Analyticity supplies
all differentiability and continuity requirements. The intermediate value
theorem constructs the two level intersections, strict monotonicity proves
their uniqueness, and endpoint inequalities place them in the open halves.
The proof gives an exhaustive iff plus both signs between/outside the roots.
No floating enumeration or externally supplied root count is used.

`M2LocalBifurcation` chooses the radius inside the actual joint-root,
physical-parameter-sign and zero-mode-sign neighbourhoods. It translates the
proved level picture of psi to the ORIGINAL observable F0(P(b,w)), using
actual factor identities and the same joint P. `BifurcationData` explicitly
records every coupling, weight, root, zero-count and sign statement.

## Verification and reproduction

New public declarations: ImplicitContourCurvature3, M2ContourCurvature3,
LocalMinimumLevels2, M2LocalBifurcation2. No new external imports or mathematical
axioms. The full consumer is standard-library-only and uses the existing
pinned Lean compiler directly:

    python3 scripts/check_project.py

Expression provenance can be replayed with the existing offline dependencies:

    PYTHONPATH=/tmp/codex_fmsa_arb_deps /opt/anaconda3/bin/python3 scripts/certificates/check_m2_tangency_generation.py

The SAME9 canonical generated prefixes now bind37source/input pins, including
all four handwritten new modules. The receipt is provenance only, never a
mathematical premise; the full consumer audits it before and after compilation.

Actual corrupted copied Lean bodies are rejected: acceleration equation RHS
changed from0 to1; true |d| budget changed from10001 to1; exhaustive two-root
predicate changed to one root. Errors occur in the mathematical bodies before
footprint mismatches. Consumer controls reject a changed final-module hash,
an omitted final-module pin, and a changed ninth prefix. Producer and consumer
reject Python-O without metadata writes. Source whitespace is checked before
pinning; raw compiler warnings are retained.

The post-run independent audit compared ALL95 prior module source,
artifact and footprint hashes, all530 frozen source/config hashes and all
9paper/2raw/9Mathlib import pins; every comparison passed. Completed evidence
is in results/lean/validation.json, results/lean/build.log and the generation receipt.
No foundation/TeX/Claude-owned file is changed; research remains active/unmerged.
