# Actual M2 fixed-coupling weight transversality

The three new module bodies have compiled. All11 public axiom footprints
were ACTUALLY queried and contain exactly propext, Classical.choice and
Quot.sound. Their exact message guards are installed. Full guarded validation
and the independent post-run hash audit PASSED:1076 exact guards /92 research
modules plus root /93 pinned compiler commands. ALL89 prior module sources,
compiled artifacts and footprints,530 frozen hashes and all9paper/2raw/
9Mathlib import pins are unchanged. No new external import or shared build.

## Constructed conclusion and scope

`M2WeightTransversality.exists_actual_negative_weight_branch` constructs a
ten-dimensional contact y in the existing widened rational box, together
with an analytic original BH root germ p in the SECOND tail weight, at the
FIXED coupling b=y4. With w=y5 and the honest real zero-frequency observable,

    p(w)=amplitudes(y),  F0(p(w))=0,
    d/ds F0(p(s)) at s=w = slope < -19.

The genuine complex Laplace factor has derivative Complex.ofReal(slope).
There is no supplied root, inverse, tangent, branch, numerical root or
external analytic enclosure in this existence theorem.

Data remain one species, sigma=1, eta=1/10, rho=3/(5*pi), rates (9/5,12),
strengths (1,s). The constructed b,w are REAL values in the existing exact
rational joint box, near5.6135716462,-4.8287538385; they are not asserted to
equal the numerical rational midpoints. Old narrow-box membership is separate.

Together with the earlier actual positive coupling curvature, this closes
the weight-transversality obligation at this SAME unique boxed contact.
At this weight-only checkpoint, joint root-germ/contour geometry remained
separate. The subsequent result in `codex_m2_joint_zero_contour.md` constructs
one joint germ and its strict-minimum local zero contour with both signs.
First contact, HS/PY membership, all-wave canonicity/first loss and complex
Taylor radii remain independent. No RDF positivity or universal root/Taylor
convergence equivalence follows. Foundation1.0.17 is frozen and no TeX is written.

## Actual analytic germ and true tangent equation

`M2WeightBranch` proves exact independence of the residual at coupling0 from
weight. Combined with the already proved exact affine coupling dependence,

    R_b(s,x) = F(x)-b*forcing(s),
    F(x)=residualFormula(strength0,0,x),
    forcing(s)=(10*pi/9,pi*s/6,0,0).

F is genuinely analytic by composing the original analytic BH residual with
the actual continuous amplitude-coordinate equivalence and fixed coupling0.
The forcing is affine and analytic, so R_b is jointly analytic in (s,x).
Derivative uniqueness identifies its amplitude partial with the actual old
four-dimensional Jacobian, at EVERY amplitude point. The already proved row
defect gives injectivity, finite-dimensional surjectivity and a continuous
linear equivalence. This DISCHARGES the invertibility condition of the
analytic implicit-function theorem; invertibility is never assumed.

`root_in_box_constructs_weight_branch` constructs an actual analytic local
weight branch through ANY original boxed root at arbitrary b,w. Its root
condition is stated for the ORIGINAL signed Dt/G amplitudes and strengths.
Differentiating genuine nearby roots gives

    J(p(w))*p'(w)=b*(0,pi/6,0,0).

This is `root_curve_weight_velocity`; it uses exact residual identities and
derivative uniqueness, not a postulated tangent equation or finite difference.

## Rigorous sign bound for the actual observable

`curvature_gradient_eq` proves at EVERY ten-variable point that the full
system's last-row velocity block is exactly the original zero-mode gradient.
Four literal scalar polynomial identities avoid unfolding an entire large
matrix. There is no root-only differentiation or unrelated surrogate Hessian.

`M2WeightCertificate` uses the same exact rational four-dimensional C as the
old boxed Jacobian certificate. It defines v0=C*(b*(0,pi/6,0,0)). Already
proved full-Jacobian entry intervals, the existing pi enclosure and the
literal b interval give

    ||v0|| <=1000,
    gradient(F0)*v0 < -20.

Every emitted interval operation and exact expression identity is proved in
Lean. Python chooses arithmetic candidates only. No new transcendental
bounds, numerical inverse or external PASS is a proof premise.

The old Jacobian row defect q=1e-6 and `solution_error_bound` give

    ||p'(w)-v0|| <= q*1000/(1-q) < 1/100.

The already proved L1 gradient budget<=10 bounds the true observable error
by<1/10. The final safe bound is slope<-19. `hasDerivAt_along` identifies
this with the genuine derivative of F0; `honest_factor_hasDerivAt` proves
its honest complex Laplace-factor counterpart.

## Reproduction and rejection controls

The pinned Lean compiler is invoked directly through `scripts/check_project.py`;
no Lake/shared dependency build is invoked. The new modules add no external
imports. The existing9 direct Mathlib artifact pins remain unchanged.

Expression replay uses the existing offline dependencies, for example:

    PYTHONPATH=/tmp/codex_fmsa_arb_deps /opt/anaconda3/bin/python3 scripts/certificates/check_m2_tangency_generation.py

The producer binds9 exact generated source prefixes and30 source/input
fingerprints. The full consumer is standard-library-only and checks these
before and after compilation. Provenance is never a mathematical premise.

Actual copied Lean proof controls are rejected at the mathematical body:
adding another weight forcing to the true tangent equation, and replacing
the approximate slope target<-20 by<-30. Separate consumer controls reject
an altered new-module input hash and altered ninth canonical prefix. Both
producer and full checker reject Python -O before starting their work.
Raw style warnings are retained in the validation log.

Public declarations: M2WeightBranch5, M2WeightCertificate2,
M2WeightTransversality4. Validation evidence is in
`results/lean/validation.json`, `results/lean/build.log` and
`results/certificates/codex_m2_tangency_generation.json`.
