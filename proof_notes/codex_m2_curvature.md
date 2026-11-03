# Actual M2 second derivatives and a strict zero-mode minimum

All four new module bodies have compiled. All15 public axiom reports were
ACTUALLY queried and contain exactly propext, Classical.choice and Quot.sound.
Complete guarded validation passed1065 exact guards across89 research modules
plus root (90 pinned compiler commands). The independent post-run hash audit
also passed. Eight generated prefixes and26 input fingerprints passed replay
and were checked before and after compilation.

## Constructed mathematical conclusion

`M2Curvature.exists_actual_positive_curvature_branch` constructs an actual
two-sided analytic original BH root curve through the previously constructed
ten-dimensional M2 contact. Its honest real zero-frequency observable f has

    f(b)=0, f'(b)=0, f''(b)=kappa > 4/5.

The HONEST complex Laplace factor has the same genuine second derivative,
equal to the real embedding of kappa. This is a derivative of the actual
factor function, not a finite-difference or a standalone Hessian expression.

`exists_actual_strict_zero_mode_minimum` additionally constructs a neighbourhood
on which

    f(t) >= (t-b)^2/10.

Thus f(t)>0 at every sufficiently near t!=b. The contact is a nondegenerate
strict local minimum WITH RESPECT TO COUPLING. A weight-transversality or
two-parameter nondegeneracy assertion is not included.

The fixed data remain N=1,sigma=1,eta=1/10,rho=3/(5*pi),z=(9/5,12),strengths
(1,w). The b,w in the existing widened rational box are CONSTRUCTED REAL
values, near5.6135716462 and-4.8287538385, not claimed to be exact rational
midpoints. The old narrow serialized witness box is still not certified.
The curve is constructed through the actual joint zero; it is not supplied
as a premise and is not identified with the HS/PY germ at coupling0.

## Actual acceleration and second derivative

`M2BranchSecondDerivative` works directly with the ALREADY proved true
ten-variable Jacobian J of the full original contact system. With amplitudes
x, certified velocity v and a true analytic root curve p, define

    Gamma(t) = (p(t),t,w,deriv p(t)).

Matching the base point and true velocity proves Gamma(b)=y. Analyticity gives
the TRUE acceleration a=deriv(deriv p)(b), and componentwise differentiation
proves Gamma'(b)=(v,1,0,a), retaining every coordinate.

Near b, all four velocity equations of the full system vanish. This follows
by differentiating actual root germs at every nearby analytic point, using
the existing `root_curve_velocity` and the neighbourhood root condition.
The full-system derivative therefore proves

    A_acc*a = b_acc,
    (A_acc)_ij = J_(4+i,6+j),
    (b_acc)_i = -sum_j J_(4+i,j)*v_j - J_(4+i,4).

The full system's last component on Gamma(t) is genuinely f'(t), by the
existing along-curve derivative theorem. Differentiating that eventual
identity gives the TRUE f''(b):

    kappa = c + sum_j g_j*a_j,
    c = sum_j J_(9,j)*v_j + J_(9,4),  g_j = J_(9,6+j).

The direct coupling columns are retained until proved bounded, even where
their exact interval is [0,0]. No unproved Hessian block identity, inverse,
acceleration equation or differentiation of a root-only implication is used.
`root_curve_second_derivative` contains the actual acceleration equation and
HasDerivAt for the genuine first derivative function.

## Kernel-checked numerical error estimate

`M2CurvatureCertificate` reuses the already proved full-Jacobian entry
intervals as its leaves. It needs NO new pi/exp enclosures. Its rational C
is the earlier four-dimensional preconditioner, only an untrusted candidate
choice. Every emitted interval operation and expression identity is proved.
All16 defect bounds and every complete row sum give

    sum_j abs((I-C*A_acc)_ij) < 10^-6.

It also proves, in the actual finite Pi-space norm,

    a0=C*b_acc,  ||a0||<=1000,  sum_j abs(g_j)<=10,
    c+sum_j g_j*(a0)_j > 9/10.

`PreconditionedLinearError.solution_error_bound` is a generic proved theorem:
from J*a=b and row defect q<1, ||Cb||<=M implies

    ||a-Cb|| <= q*M/(1-q).

It derives a-Cb=(I-CJ)*a and closes the norm estimate algebraically; an
inverse is not assumed. Its separate `pairing_norm_le` proves the correct
scalar pairing bound in that same Pi-space norm.

With q=10^-6,M=1000 the acceleration error is <1/100. The true curvature
therefore differs from the proved approximate curvature by <1/10. Hence
the true second derivative is >4/5. The numerical probe near0.9908736 was
only used to select these generous rational targets; it is never a premise.

## Strictness and the honest complex factor

The real observable is analytic by its exact quadratic amplitude formula and
the actual analytic root curve. Subtract (t-b)^2/10 and apply the existing
Mathlib second-derivative test: the new function has first derivative0 and
second derivative kappa-1/5>0. Its local minimum gives the explicit quadratic
lower bound, which implies punctured strict positivity.

The genuine honest-factor first derivative holds at every nearby analytic
point. Consequently its derivative function eventually equals
Complex.ofReal of the REAL observable derivative. Differentiating this
eventual identity with the real continuous linear embedding gives the true
complex second derivative. The real derivative is explicitly typed before
embedding, avoiding an inference of a complex-valued derivative instead.
All-amplitude honest-moment identities justify this route; no whole-integral
second-derivative interchange is assumed.

The only new direct Mathlib import is the ALREADY cached read-only
`Analysis.Calculus.DerivativeTest`. No dependency build is required.

## Reproduction and validation status

From this research package root, regenerate the receipt ONLY BEFORE starting
full validation. The receipt and all its inputs remain locked until it ends:

```sh
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_curvature_certificate.py > /tmp/M2CurvatureCertificate.body
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/check_m2_tangency_generation.py
python3 scripts/check_project.py
```

The new numeric body extends the existing provenance mechanism to8 generated
canonical prefixes and26 source/input fingerprints. The full checker uses
only Python standard library to check that receipt before and after Lean.
The receipt is provenance, not a mathematical premise. Full guarded validation and the independent post-run audit passed. Evidence:
`results/lean/validation.json` and its unedited raw `results/lean/build.log`.
Every input, source, artifact and raw-log hash was verified. ALL85 earlier
module sources, compiled artifacts and axiom footprints are unchanged, as are
all530 frozen source/configuration hashes, nine paper imports, two raw LeanCode
pins and all eight OLD direct Mathlib pins. The ninth direct Mathlib pin is
the previously cached read-only DerivativeTest artifact; no shared dependency
build occurred. Compiler style/deprecation warnings remain in the raw log.
New curvature-source-hash and eighth-generated-prefix corruptions are rejected
by the receipt consumer, and Python -O is rejected before metadata writes.
The checker imports no SymPy/Flint; the explicit producer supplies provenance
only, never a mathematical premise.

The actual direction-action identity raised by1 was rejected by Lean with
the expected false equality. A separate control raising the actual approximate-curvature target from9/10
to2 also exited1 with the expected false inequality. Both are actual copied
proof fragments. No original proof or certificate was corrupted.

## Scope and proposed paper correspondence

Cite `exists_actual_positive_curvature_branch` for the constructed true
second derivative and kappa>4/5, and `exists_actual_strict_zero_mode_minimum`
for the strict coupling minimum and explicit local quadratic lower bound.
The original zero-frequency observable equals actual A/(2*pi), the honest
renewal determinant and the physical Fourier factor by `M2ZeroMode`.

These are LOCAL statements at the constructed joint contact. Weight
transversality, first contact, HS/PY membership, all-wave canonicity/first
loss, narrow-box membership and complex/Taylor radii remain independent.
No RDF positivity or universal real-root/Taylor equivalence follows.
Generic matrix escape, nonisolated endpoint limits, positive-density fiber
certificates and multitailed complex Taylor lower bounds remain open.
Foundation1.0.17 and its cache remain read-only. TeX is untouched; no new
mathematical axiom or merge-back. Research remains active.

Subsequent weight work: the separate modules documented in
`codex_m2_weight_transversality.md` construct a fixed-coupling weight germ and
prove its true negative zero-mode derivative at the same boxed contact.
That result is independent of the coupling-curvature theorem above and
retains the firstness/PY/all-wave/radius limitations.
