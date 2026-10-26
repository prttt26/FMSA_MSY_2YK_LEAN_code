# Two-tail convergence-set audit and zero-mode stationarity

Codex, 2026-10-26. Base package commit
`41796bb538292db7e97e7787ac811205d3cee586`; mathematical work for future plan
(b). The stable-domain decision is recorded in
`handoff/claude_codex/003_claude_to_codex_stable_domain_decision.md`.
This file is owned by the Codex side of that exchange.

Status: the initial-interval radius criterion is formalized in
`FMSAPaper/StableIntervalRadius.lean` (baseline 1.0.12); the M2 statements below
are paper-level arguments and reproducible exact symbolic identities.
No new assumptions of the existing Lean collection or general tail-domain
certificate are introduced.

## 1. Fixed target and the radius reduction

Fix a packing fraction `0 < eta < eta_max` and a tail shape theta. Write
`t = tau_inst(theta, eta)`, allowing `t = infinity`. The user-selected stable
domain is exactly the initial PY-connected canonical interval `[0,t)`.
Critical states and any later canonical portions are excluded. Multiplication
of a fixed strength vector by positive coupling tau describes the uncapped
temperature range at this density.

Let `p(tau)` be the selected real branch, analytic at the PY seed. Its finite
amplitude vector has Taylor coefficients `a_n` and common radius
`R = min_j R_j`, where `R_j` is the radius of scalar component j. Suppose the
branch is analytic at every point of `[0,t)` and is the continuation of that
seed germ. Then

> Every component Taylor series converges to `p(tau)` at every `0 <= tau < t`
> if and only if `R >= t`.

**Sufficiency.** Every such tau is strictly inside each component's radius.
The sums are analytic there and agree with the branch near zero. Analytic
uniqueness along the real interval identifies them with the branch. The
existing `FMSA.Paper.AnalyticTaylor.eq_jet_sum_on_interval` and
`hasSum_jet_on_interval` supply the scalar Lean interfaces when the analytic
branch and a strict radius inequality have been provided. This argument
does not use coefficient signs or the existence of a real fold.

**Necessity.** If `R < t`, some scalar component has radius R because there
are finitely many components. Choose a real `r` with `R < r < t`; when
`t = infinity`, choose any finite `r > R`. Convergence at r would imply that
component's radius is at least r, a contradiction. This last implication
also holds for conditional convergence: bounded series terms at r force
absolute convergence at every smaller modulus. At r = 0 there is no issue.

Thus equality `R = t` is allowed. No assertion about convergence exactly at
t is used. If `t = infinity`, the requirement is that all component radii
are infinite, namely that the Taylor germ is entire. A claim of failure in
this case additionally needs a finite radius bound for this state.
Algebraicity alone does not exclude an entire polynomial branch.

The analytic regularity/branch matching premises are substantive. An actual
regular BH branch is analytic by `ActualAnalyticBranch`; the assertion that
canonical physical states cannot encounter a singular BH Jacobian is the
paper-level bridge in §8c of `proof_notes_msa_exact.md`, not a completed
Lean bridge. This audit does not replace that missing bridge with an axiom.

The full parameter target is the intersection

`C(eta_max) = intersection_{0 < eta < eta_max} {theta : R(theta,eta) >= t(theta,eta)}`.

Replacing this intersection by the density endpoint requires a monotonicity
theorem and an appropriate one-sided limit. Ordering finitely many sampled
thresholds supplies evidence for such a theorem, not the theorem. Even the
interval form of each fixed-density admissible set must first be established.

## 2. Binding folds and the analytic definition of first loss

For a branch with a finite real fold, the weak ordering

`tau_inst <= tau_fold`

already implies the desired criterion whenever `R = tau_fold`. Strict
ordering is unnecessary. The weak ordering in §8c still carries its physical
and analytic hypotheses: the canonical BH/OZ bridge, sufficient regularity
for the linearised support/Parseval argument, and locally uniform control at
infinity excluding entry of factor zeros from infinity.

The first-loss event is a zero of `det F_tau(i*k)` for some real k, including
k = 0, on the initially canonical branch. A sign change of `det F(0)` or a
change of the rounded finite-grid winding is a crossing detector. It does
not exclude touching zeros or crossings missed between samples. Positive
`I-C(k)` on a continued BH root also does not establish canonicity; §8c
already explains the noncanonical continuation problem.

For a failure certificate it suffices to certify an initial canonical
segment up to some L and a Taylor radius upper bound `R_upper < L`. A tau
strictly between the bound and L is a stable state at which the series
diverges. This is weaker than proving absence of every instability at all
temperatures, and is sufficient for the user's target.

## 3. An exact quadratic zero-mode factor

Use one species, diameter sigma = 1, `rho = 6*eta/pi`, and a finite family of
positive rates `z_i`. The unknown order for two tails is
`u = (D1,D2,G1,G2)`, where D and G are the scaled variables Dt and Gt in
`msa_exact_mix.py` and the F5/F7 residual.

For one tail write `E = exp(-z)` and `c = 12*eta/z`. The actual pieces are

```
W = c*G*D
Ct = (1-c*E*G)*D
M = -rho*(W+(1+z)*Ct)/z
Nc = rho*(W+(1+z+z^2/2)*Ct)/z^2
```

M and Nc add over tails. With `v = 1-eta`, the hard-sphere coefficients are

```
A0  = 2*pi*(1+2*eta)/v^2
B0  = -3*pi*eta/v^2
qp0 = 2*pi*(1+eta/2)/v^2
A   = A0*(1+M)-4*B0*Nc
qp  = qp0*(1+M)+A0*Nc
```

At zero wave number the actual transform gives

`Qhat(0) = -qp/2 + A/6 + sum_i [W_i/z_i + Ct_i*(1+1/z_i)]`.

Substitution proves the off-root identity

`F0(u) := det F(0) = 1-rho*Qhat(0) = A/(2*pi)`.

In particular,

`F0(u) = (1+2*eta)/v^2 + sum_i D_i*(alpha_i+beta_i*G_i)`,

where

```
alpha(z) = rho/(v^2*z^2) * [6*eta+(4*eta-1)*z+(eta-1)*z^2]

beta(z) = 12*eta*rho/(v^2*z^3) *
  [-(1+2*eta)*z*(1-(1+z)*exp(-z))
   +6*eta*(1-(1+z+z^2/2)*exp(-z))]
```

Thus `g := grad F0 = (alpha_i+beta_i*G_i, beta_i*D_i)` in D-then-G order.
The only nonzero Hessian entries are
`H[D_i,G_i] = H[G_i,D_i] = beta_i`. This identity holds for arbitrary real
amplitudes; no BH-root, sign-of-tail, or branch-selection premise is used.

## 4. Stationarity and curvature as polynomial conditions

At fixed eta and rates, write the actual cubic BH residual as

`P(u) = tau*b(w)`, with `b(w) = (2*pi/z1, 2*pi*w/z2, 0, 0)`.

Let `J = DP(u)` and assume `det J != 0`. The forcing b is independent of u
and tau. Differentiation along a real regular branch gives

```
u' = J^{-1}*b
N(u,w) = g(u)*adj(J(u))*b(w)
d/dtau F0(u(tau)) = N/det J
```

The bordered determinant identity is

`det [[J,-b],[g,0]] = N`.

This distinguishes two mechanisms: a BH fold has `det J = 0`, while a
stationary zero-mode factor on a regular BH branch has `N = 0` and
`det J != 0`. They must not be identified.

For the second derivative, put `M = grad_u N * adj(J) * b`. Since N and
det J have no explicit tau dependence, differentiating `N/det J` shows that
at N = 0,

`d^2/dtau^2 F0 = M/(det J)^2`.

Consequently `N = 0`, `M > 0`, and `det J != 0` prove a strict local minimum
of the zero-mode factor on the selected regular branch. A positive value of
F0 there proves a positive **local** minimum, not global absence of a zero.

For two tails P has degree at most 3 in four amplitudes, J degree at most 2,
adj J degree at most 6, and g degree at most 1. Hence N has degree at most 7
and M degree at most 12. These are upper bounds; cancellations can reduce
them. The coefficients depend on eta, rates, pi and exponentials. This is
polynomial algebra in the amplitudes at fixed physical parameters, not a
claim of a polynomial or a decidable sign criterion in the rates themselves.

### A candidate zero-mode boundary system

At fixed eta, z1 and z2, a generic interior disappearance of two zero-mode
zeros can be sought with the six equations in `(u,tau,w)`:

```
P(u)-tau*b(w) = 0       (four equations)
F0(u) = 0
N(u,w) = 0
```

Retain `tau > 0`, `det J != 0`, and `M > 0`, then connect the enclosure to
the PY-seeded branch. An isolated solution on another BH sheet proves
nothing about the physical branch.

There is also an explicit parameter-transversality test. If the minimum is
continued as tau = tau_*(w), its value m(w) satisfies

`m'(w) = tau * g*adj(J)*b_w / det J`,

because the derivative through tau_*(w) vanishes at stationarity. Here
`b_w = (0,2*pi/z2,0,0)`. Nonzero m'(w) and positive M give the usual local
creation/disappearance picture. In the scan coordinate `w = w0*f`, the
derivative is `m_f = w0*m_w`, and w0 is negative.

At the exact boundary m = 0, the zero-mode factor **touches zero**. That
point still counts as a first loss of canonicity, even if the sign and
winding detectors have equal values before and after it. Only a parameter
on the positive-minimum side, with the other routes excluded, can be
classified as having no first loss. The boundary state itself is not an
infinite-tau-inst state merely because it has no transverse crossing.

For an interval implementation, one can avoid explicitly expanding the
degree-seven polynomial N. Introduce four additional unknowns v and solve
the ten low-degree equations in `(u,tau,w,v)`:

```
P(u)-tau*b(w) = 0
J(u)*v-b(w) = 0
F0(u) = 0
g(u)*v = 0
```

With `det J != 0`, these are equivalent to the six-equation system. Each
equation has total degree at most three in these unknowns at fixed eta and
rates. An additional linear solve
`J*a = -D^2 P[u][v,v]` gives curvature as
`v^T*H_F0*v + g*a`. This offers an alternative to forming a large adjugate;
invertibility and branch linkage must still be certified.

### What a global certificate would additionally need

On a compact regular branch segment `[0,L]`, positivity of F0 at both ends
and at **every** interior stationary point implies positivity throughout:
otherwise the minimum on the compact interval would be a nonpositive
stationary value. A cover must include degenerate stationary points, not
just candidates satisfying M > 0.

For all tau >= 0, add a justified control of the unbounded end and of any
branch endpoints/escape. In either case, F0 positivity excludes only k = 0.
Finite-k zeros and the high-frequency tail still need independent control
before claiming canonicity. These are remaining obligations, not supplied
by the polynomial stationarity system.

## 5. Reproduction and scope of the evidence

Run from the package root:

```
python3 scripts/coupling_singularities/codex_zero_mode_stationarity.py --model-crosscheck
```

The output is
`results/coupling_singularities/codex_zero_mode_stationarity.json`. The
script verifies the scalar zero-mode formula, its gradient/Hessian, the
generic 4D bordered determinant, Jacobi's determinant derivative and the
adjugate directional-derivative identity. They are checked by exact SymPy
rational/polynomial simplification; `E = exp(-z)` is treated as an independent
symbol, so no numerical approximation of the exponential enters those checks.

The optional model comparison evaluates the independently derived expression
against the actual `_pieces`/`qhat` functions in `msa_exact_mix.py` at 27
off-root amplitude configurations. Its floating-point agreement checks
transcription, not an interval theorem. The result records the script and
actual-model source hashes and labels the scopes separately.

The direction/curvature statements above also have elementary paper proofs;
their use still requires an actual regular branch. No Lean baseline files,
Claude-owned scans/results, or TeX are changed by these computations.

## 6. Next mathematical obligations

1. The Lean radius/initial-interval equivalence, including extended endpoints
   and the actual-MSA Taylor-sum interface, is proved in
   `StableIntervalRadius.actual_regular_branch_converges_before_iff`. The
   physical canonicity-to-Jacobian-regularity bridge remains open.
2. A selected-sheet, nondegenerate zero-mode tangency certificate is now
   established at eta=0.1, z=(1.8,12), using the ten-equation system (§7).
   Its global firstness and its role in the convergence boundary remain open.
3. Global control and finite-k exclusion sufficient to upgrade a zero-mode
   result to a statement about the user's initial canonical interval.
4. A sufficient tail condition or a certified all-density parameter region;
   the algebraic identities here do not yet establish one.

## 7. Certified local zero-mode tangency on the PY-seeded real branch

The independent Arb certificate is
`scripts/coupling_singularities/codex_m2_tangency.py`, with result and run log
under the same basename in `results/coupling_singularities/`. It reuses only
the generic polynomial residual and automatic-differentiation arithmetic
from `formalization/certificates/f5_competing_tails.py`; all physical constants
are constructed directly with Arb decimal, exponential and pi operations.
It does not use that older certificate's assumed high-precision error bound.

At sigma=1, eta=0.1, z=(1.8,12), K=(1,w), the ten-equation system has a
unique root in the reported ten-dimensional box. Outward-rounded bounds are

```
f = w/w0 in [0.5044323145431001, 0.5044323267212183]
tau      in [5.613571580093759, 5.613571712365194]
F0''     in [0.9908615927082075, 0.9908856055251728]
m_f      in [202.33284987011206, 202.33606759542454]
```

Here w0=-(1/z1+1/z1^2)/(1/z2+1/z2^2), as in the scans. The BH Jacobian is
certified nonsingular over the entire amplitude root box. Positive curvature
and positive parameter derivative imply a nondegenerate local minimum with
value crossing zero as f increases: locally two nearby zero-mode zeros for
smaller f, a double contact at the certified parameter, and no nearby zero
for larger f. This is a local statement about F0; the full canonical factor
and finite-k modes have not been checked.

### Existence, uniqueness and branch selection

For a box X centered at y and an exactly represented floating preconditioner
C, the code encloses

`K = y-C*F(y) + (I-C*J(X))*(X-y)`.

It checks strict containment K inside X and a weighted infinity-norm bound
strictly below one for I-C*J(X). Thus the associated fixed-point map is a
contraction into X for every enclosed parameter value, giving existence,
uniqueness and nonsingularity. The ten-equation root check has contraction
bound less than 3.541e-6. Floating Newton steps only choose centers and C;
all proof inequalities use Arb enclosures at 192-bit precision.

The branch link uses 382 parameter slabs from tau=0 through
5.613637848081656, uniformly over the certified w box. Each slab has a unique
BH root and nonsingular Jacobian; the largest contraction bound is below
0.893. At tau=0, D=0 and
`G_i=(A0+z_i*qp0)/(2*pi*z_i^2*F_HS(z_i))` solve the residual by direct
substitution: the first two equations have a factor D_i, and the last two
reduce to `2*pi*G_i*F_HS(z_i)=A0/z_i^2+qp0/z_i`. The certificate verifies
F_HS(z_i)>0 and encloses this seed in the first slab.

Fresh certified endpoint boxes lie inside both adjacent slabs, so uniqueness
glues the roots to a continuous PY-seeded branch. The entire tangency tau
box and amplitude box lie in the final slab, identifying the augmented root
with that branch. The JSON records every slab and endpoint box. The branch
is mathematically selected by this chain; a floating continuation match is
not used as the branch-selection proof.

The implementation preserves the common tau factor when enclosing
`C*(P(y)-tau*b(w))`, evaluating it as `C*P(y)-tau*(C*b(w))`.
Evaluating each residual interval before preconditioning loses cancellation
and can create a false step-size barrier even on this regular branch.
Fresh endpoint boxes also avoid accumulated interval wrapping. These are
algebraic enclosure improvements; strict inclusion and contraction checks
remain mandatory on every accepted slab.

### Reproduction and limits

With numpy 1.26.4 and python-flint 0.6.0 available, run

```
python3 scripts/coupling_singularities/codex_m2_tangency.py
```

For an isolated installation, use `python3 -m pip install --no-deps --target
/tmp/codex_fmsa_arb_deps python-flint==0.6.0`, then prefix the command with
`PYTHONPATH=/tmp/codex_fmsa_arb_deps`. The output records both source hashes
and dependency versions. A displaced constraint F0+0.001 fails the same
Krawczyk test, providing a negative control. Successful output is labelled
`PASS_LOCAL_ZERO_MODE_TANGENCY` only after the root, geometry, negative
control and complete branch link have all passed.

This certificate proves a local zero-mode touching event, not that it is the
first loss on the initial canonical interval. It does not exclude earlier
zero-mode or finite-k loss, certify a Taylor radius, or determine an
all-density parameter boundary. It adds no Lean theorem or axiom and does
not change the foundation 1.0.12 baseline.
