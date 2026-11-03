# Isolated singular endpoints and exact actual BH fiber certificates

2026-10-28 local. Three modules, 53 new theorems. All compiled; every ACTUAL
axiom report was queried before exact guards and contains exactly propext,
Classical.choice and Quot.sound. Full-package validation and independent hash
auditing have PASSED. Foundation 1.0.17 remains frozen. No
TeX, shared dependency build, numerical file or Claude-owned note is modified.

## What is proved, and what is not discharged

An isolated ACTUAL endpoint root, even singular, forces the entire finite left
limit from one approaching cluster. No Jacobian inverse, full limit, endpoint
value, global bound or canonicity of the old path is assumed. For a canonical
prefix it suffices to isolate the root among actual endpoint roots IN CANONICAL
CLOSURE. This extends regular-cluster limit control to isolated singular roots.

The literal actual BH polynomial system and an exact elimination-certificate
verification pipeline are proved. Supplied identities with nonzero univariate
coordinate eliminants imply a finite relevant fiber and hence the full singular
endpoint limit. For active scalar tails at nonzero coupling, rate-factor
saturation nonvanishing is discharged INTERNALLY from the first BH equation.

No generic certificate instance has been constructed here. No theorem asserts
that every actual BH endpoint fiber is finite or isolated. The remaining work
includes exact certificate construction or another proof for nonisolated relevant
fibers. A square polynomial system, a degree count or finitely many floating
solutions is not substituted for such a proof. The research goal stays open.

## IsolatedEndpointLimits: 19 theorems

Let p be continuous on [0,b), b>0, in a finite-dimensional real amplitude space,
and let t_n<b approach b with p(t_n)->a. If p does not tend to a, metric
nonconvergence gives frequent exits from an epsilon-ball around a. For EVERY
0<r<epsilon and EVERY c<b, the continuous distance function on a connected
left-tail interval has a point t>c with dist(p(t),a)=r: it takes a value below r
along the approaching sequence and one at least epsilon at an exit point.

Choose one crossing after b-1/(n+1). Its times tend to b. Its amplitude values
lie on the SAME compact sphere of radius r, so a subsequence tends to d with
dist(d,a)=r. No global bound on p is used. These are the actual proofs in
`cluster_and_exits_give_crossings`, `spherical_crossings_have_cluster` and
`nonlimit_has_spherical_clusters`.

For a continuous residual R, root continuity makes d a root at coupling b.
Thus isolation of a in the endpoint fiber contradicts nonconvergence. This is
`isolated_fiber_cluster_has_limit`. `finite_set_isolated` and
`finite_fiber_cluster_has_limit` discharge isolation if a finite fiber has
already been certified. No square-free, rank or ordinary-fold assumption.

The ACTUAL specialization uses the existing BH residual and `IsRoot` interface:

- `actual_nonlimit_has_spherical_roots` produces actual endpoint roots at every
  sufficiently small radius, with their own genuine approaching sequences.
- `actual_nonlimit_forces_nonisolated_roots` rules out isolation, not merely
  Jacobian invertibility, if the full limit fails.
- `actual_isolated_cluster_has_limit` and
  `actual_finite_fiber_cluster_has_limit` give the full actual left limit.
- `bounded_actual_prefix_finite_fiber_limit` obtains a cluster internally from
  the original-norm prefix bound and produces the actual limiting root.
- `actual_isolated_cluster_bounds_prefix` derives an honest bound on the ENTIRE
  original prefix from ONE isolated finite cluster, even a singular one.

If p is canonical before b, each new crossing cluster d lies in canonical
closure. `canonical_nonlimit_has_spherical_roots` retains that extra information;
`canonical_isolated_cluster_has_limit` needs isolation only among actual roots
in that closure. `canonical_finite_fiber_cluster_has_limit` needs finiteness
only of the relevant intersection, allowing unrelated noncanonical algebraic
components. `scalar_maximal_limit_of_finite_canonical_fiber` combines it with
the already proved scalar no-escape/physical-cluster theorem. The result is an
actual root in canonical closure, noncanonical with a true physical Fourier
zero, and the WHOLE finite left limit. No endpoint value or bound is supplied.

`actual_regular_root_isolated` uses the TRUE analytic IFT at the actual regular
root. Combining this with the topological argument gives
`actual_regular_cluster_has_limit` for ANY continuous actual root prefix, with
no canonicity or physical sign hypotheses along that prefix. This strengthens
the earlier canonical-prefix regular-cluster limit theorem.

Isolation supplies a continuous finite limit only. A singular root can have a
nonanalytic one-sided branch; analytic continuation through it is NOT inferred.
Conversely a nonisolated fiber does not prove that a particular branch lacks a
limit. Failure of a full limit implies nonisolation, not an equivalence.

## BHResidualPolynomials: 20 theorems

Use independent coordinates Bool × T × Fin N × Fin N for all Dt/G entries,
and Option of that type for coupling (None). No original amplitude direction
is quotiented or renormed; `amplitude_values_injective` checks that encoding.
Fixed rates/densities/diameters, pi, exponentials and fixed-data inverses are
REAL coefficients. No amplitude variable is put in a denominator.

The module constructs literal MvPolynomials for gamma, W, C, M, N, A, Qp,
dressedQhat at fixed real frequency, and both actual residual families.
`eval_*` proves each evaluation identity off root, for ALL actual amplitudes
and coupling values. Row/column indices, finite sums and unequal-diameter
edge constants remain those of the original frozen definitions. Repeated and
empty finite index families are retained; no physical sign hypothesis is needed
for these algebraic identities. The frozen total real-division semantics are
preserved even outside the physical parameter domain, not replaced by clearing
an amplitude denominator or rationalizing physical constants.

`actual_root_iff_polynomial_zeros` is an IFF for the ORIGINAL full BH root.
`specializeTime` is a genuine ring homomorphism substituting the endpoint b
for coupling. `eval_specializeTime` proves its compatibility with full point
evaluation. The specialized `endpointPoly` has proved actual residual coordinate
values and `actual_endpoint_root_iff_polynomial_zeros`. Finiteness is NOT a
consequence of this representation alone. No formal Bezout degree/cardinality
bound is asserted by this module.

## BHFiniteFiberCertificates: 14 theorems

A `CoordinateFiberCertificate` contains explicit proof data:

    nonzero P_i in R[X] for EVERY original amplitude coordinate i,
    a saturation polynomial D,
    multiplier polynomials H_ij,
    identities D * P_i(X_i) = sum_j H_ij * endpointPoly_j.

These are literal equalities of exact REAL-coefficient MvPolynomials. A future
symbolic computation can supply multipliers and eliminants; their identities
must be proved in Lean, for example by normalization. Floating/rationalized
physical data do not establish these identities for the actual parameters.

`certificate_coordinate_zero` evaluates them at an ACTUAL BH root. If D is
nonzero there, every coordinate is a root of its nonzero univariate P_i.
`finite_set_of_coordinate_annihilators` takes the finite real root sets, forms
their finite product, and uses the injective ORIGINAL amplitude encoding.
Hence `actual_fiber_finite_of_certificate` proves finiteness with D=1, while
`canonical_fiber_finite_of_certificate` needs nonvanishing only on actual roots
in canonical closure. These theorems do not assume the desired finiteness.

`actual_cluster_limit_of_certificate`, `canonical_cluster_limit_of_certificate`
and `scalar_maximal_limit_of_certificate` connect those literal identities to
the actual full singular-cluster limit and physical scalar endpoint conclusions.
The certificate identities, eliminant nonzero proofs and saturation nonvanishing
remain explicit mathematical proof DATA, not newly declared axioms.

### Active scalar tails discharge saturation nonvanishing

For N=1, define the polynomial F_u to be the literal first BH factor evaluated
at rate z_u, after coupling specialization. The actual first equation gives

    Dt_u * F_u = 2*pi*b*K_u/z_u.

If b, z_u and K_u are nonzero, its right side is nonzero, so F_u is nonzero at
EVERY actual root, even outside canonical closure. These are
`scalar_first_factor_equation` and `scalar_first_factor_ne_zero_of_active`.
Thus `scalarRateSaturation = product_u F_u` is nonzero. ANY natural power of
it can be used as D, with nonvanishing internally discharged.

`scalar_fiber_finite_of_rate_saturated_certificate` now needs only the EXACT
certificate and the concrete saturation-power identity, plus nonzero coupling,
rates and active strengths. No finiteness, canonicity or Jacobian premise.
`scalar_maximal_limit_of_rate_saturated_certificate` combines it with the
constructed physical scalar maximal branch and prior no-escape proof, yielding
its whole actual physical Fourier-zero limiting root, including singular roots.
Coupling positivity, physical rates and all needed bounds/cluster data are
internally discharged by the existing maximal-branch interface.

Crucial remaining obligation: construct the actual eliminants/multipliers and
prove their identities for a specified family/point. This batch constructs
NO generic instance of CoordinateFiberCertificate. Inactive zero strengths
need a different saturation argument or a proved reduction; they are not silently
included in the active-tail corollary. Repeated/empty finite tails remain allowed.
For general N an entrywise-active K does not prove matrix factor invertibility;
the scalar nonzero-factor proof is not transferred to matrices.

## Numerical collaboration and limits of scope

Claude independently reviewed the isolation argument (133). The targeted
M1/M2/M3 diagnostics in 134 are requested as FLOAT evidence only, with unresolved
homotopy paths/component detection and endpoint definitions reported explicitly.
Rank deficiency occurs at isolated multiple roots too. Neither a rank diagnosis
nor finite numerical root enumeration certifies finiteness, nonisolation or
multiplicity. Those results cannot instantiate the certificate proof fields.
Handoff 136 reports all three traced roots numerically regular, but unresolved
large-modulus homotopy paths remain. M1 has a nearby real partner and a very
small singular-value ratio; exact regularity/separation still needs a certificate.

General nonisolated relevant fibers, actual generic elimination-certificate
construction, finite MATRIX escape, generic multitailed complex Taylor-radius
LOWER bounds and tail/all-density classification remain open. The prior
positive-density single-attractive-tail beta<R=fold/full endpoint theorem remains
unchanged. No universal real-root/Taylor iff, first-wave-number claim, RDF
positivity, analytic extension through arbitrary singular roots, or enlargement
of the user-chosen INITIAL canonical domain is inferred.

## Verification and proposed SI correspondence

PASS: 919 exact standard-three guards /63 research modules plus root /
64 direct pinned compiler commands. All 53 new actual reports were queried
before strict guards. Independent post-run audit checks EVERY input/source/
artifact/raw-log hash. ALL 60 prior source/artifact/footprint records remain
unchanged; all 530 frozen source/config hashes and nine validated-paper /
seven Mathlib / two separately locked LeanCode source-cache pins remain
unchanged. No new direct dependency import, shared/Lake build or merge-back.
Evidence: `results/lean/validation.json`, `results/lean/build.log`; reproducible
checker: `python3 scripts/check_project.py`.

The main Markdown TODO records exact theorem names/assumptions and proposed SI
citations after PASS. Cite isolation/full-limit theorems with their explicit
isolation or certificate conditions; do not change a generic singular-limit
claim to unconditional on the strength of this certificate INTERFACE. No
paper/TeX build is run.
