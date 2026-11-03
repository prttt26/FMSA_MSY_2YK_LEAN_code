# Exact scalar quadratic reduction and constructed vacuum fiber certificates

Date: 2026-10-28. Research package only; frozen foundation 1.0.17 and TeX
are unchanged. New modules: `ScalarQuadraticBH` (39 public theorems) and
`VacuumFiberCertificate` (8 public theorems). All 47 actual compiler axiom
queries report exactly propext, Classical.choice and Quot.sound. Both modules
with their exact guards and the package root passed direct pinned compilation.
Full-project verification and the independent post-run hash audit have passed.

## Actual finite-tail scalar reduction

The original amplitudes are `(Dt_u,G_u)` with one species and any finite tail
index type T. Set `X_u=Dt_u*G_u`. The new polynomial ring is
`MvPolynomial (Bool x T) Real`, with separate Dt and X variables. All rates,
density, diameter, pi and physical exponentials remain EXACT real coefficients.
Coupling b is fixed when discussing an endpoint fiber.

The reduced dictionary is literal:

    W_u = (2*pi*rho/z_u)*X_u,
    C_u = Dt_u-exp(-z_u*sigma)*W_u,
    M_u = -(rho/z_u)*(W_u+(1+z_u*sigma)*C_u),
    N_u = (rho/z_u^2)*(W_u+(1+z_u*sigma+(z_u*sigma)^2/2)*C_u).

The true physical A and Qp are their original finite moment sums. The true
fixed-frequency Qhat is affine in A,Qp,W,C. Hence the exact rate factor and
second source are affine polynomials:

    F_u = 1-rho*Qhat(z_u),
    S_u = (A+z_u*Qp+sum_v z_u^2*z_v/(z_u+z_v)*C_v)/z_u^2.

Every dictionary evaluation is PROVED equal to its original actual BH value
at `encode(Dt,G)=(Dt,Dt*G)`: `eval_wPoly`, `eval_cPoly`, `eval_mPoly`,
`eval_nPoly`, `eval_aPoly`, `eval_qpPoly`, `eval_qhatPoly`,
`eval_factorPoly`, `eval_sourcePoly`. Scalar support edges are simplified
exactly; no transform approximation or closure assumption is made.

The reduced equations are

    P_u = Dt_u*F_u-2*pi*b*K_u/z_u = 0,
    Q_u = 2*pi*X_u*F_u-Dt_u*S_u = 0.

`eval_firstPoly` identifies P with the ORIGINAL first residual.
`eval_secondPoly` identifies Q with Dt TIMES the ORIGINAL second residual.
This multiplier is retained throughout the proof.

The eleven `degree_*` theorems prove all dictionary polynomials have total
degree at most one and both residual families have total degree at most two.
They use the actual MvPolynomial degree algebra, not a CAS degree report.
The degree bounds hold without nonzero/sign/physical hypotheses; Lean's
fixed-data coefficients use totalized division even at degenerate data.

## Exact inverse and root-set correspondence

`decode(Dt,X)=(Dt,X/Dt)` is an inverse when every Dt_u is nonzero, proved in
`decode_encode` and `encode_decode`. The actual-root IFF reduced-root theorem
`actual_root_iff_reduced_of_nonzero` retains that chart condition explicitly.
The forward map `actual_root_gives_reduced` holds at ALL original roots,
including zero coupling and inactive tails.

For b!=0, z_u!=0 and K_u!=0, the first ACTUAL equation gives

    Dt_u*F_u = 2*pi*b*K_u/z_u != 0.

Thus `actual_dt_ne_zero_of_active` discharges the original chart condition.
The reduced first equation independently discharges it at every reduced root
in `reduced_dt_ne_zero_of_active`. Consequently `reduced_root_decodes_actual`,
`active_fiber_eq_decode_image` and `reduced_fiber_eq_encode_image` prove a
true two-sided root correspondence for ANY finite active scalar tail family
at nonzero coupling/rates. No sign, density, diameter, vacancy, canonicity,
Jacobian or distinct-rate premise is needed for this algebraic statement.
Repeated and empty finite tail families are included.

`active_fiber_finite_iff_reduced` proves finiteness equivalent for these two
fibers. `actual_cluster_limit_of_reduced_finite_fiber` supplies the whole left
limit at an approaching continuous actual root cluster, including singular
roots, AFTER reduced-fiber finiteness has been proved. Only the endpoint needs
nonzero coupling; the old prefix still starts at zero coupling. No amplitude
bound or canonical old-prefix premise is supplied.

This is not an assertion that a square quadratic system has finite fibers.
Positive-density elimination identities remain to be constructed and checked.
The reduced degree and variable count make that task smaller; neither a
Bezout slogan nor floating root enumeration discharges it.

## Verified failure of unconditional reverse substitution

`reduced_zero_at_zero_coupling` proves Dt=X=0 solves the multiplied equations
at b=0 for ANY data. At physical vacuum, sigma=z=1, the original exact BH
system instead requires G_u=2. `decoded_zero_not_actual_at_vacuum` and
`zero_coupling_reduction_has_spurious_root` prove that decoding the reduced
zero by totalized division gives G=0 and fails the ORIGINAL root equations.
This remains a counterexample with active strengths, by taking every K_u=1.
A chosen tail u supplies the required nonempty family.

Precise scope: the reduced zero is ALSO the encoding of the genuine vacuum
root Dt=0,G=2. The failure is loss of the G coordinate and failure of the
proposed inverse X/Dt at Dt=0. It is not a proof of an unmatched reduced root
under the forward image, or a counterexample to existence of original roots.
The exact theorem statements record failure of decoding. This correction
explains why the active/nonzero chart conditions cannot simply be discarded;
it does not assert they are necessary for every individual state.

## First constructed exact original-fiber certificate family

`VacuumFiberCertificate` supplies a real instance of
`BHFiniteFiberCertificates.CoordinateFiberCertificate`, for ANY finite
species and tail sets, unequal diameters, positive rates, arbitrary fixed
coupling and arbitrary strengths, including signed and inactive tails.
Density is identically zero. This is an exact original Dt/G certificate;
it does not use the scalar X/Dt chart or assume activity/nonzero coupling.

The constructed root point is

    D0_uij = 2*pi*b*K_uij/z_u,
    G0_uij = (1+z_u*edgeHi_ij)/z_u^2 + sum_v b*K_vij/(z_u+z_v).

`rootPoint_is_actual` proves it is a genuine original root. For every amplitude
coordinate i, the univariate eliminant is `X-C(rootPoint_i)`;
`eliminant_ne_zero` proves each nonzero. Saturation is exactly ONE.
The triangular multiplier matrix is explicit. In residual notation,

    Dt_uij-D0_uij = R1_uij,
    G_uij-G0_uij = (R2_uij + sum_v [z_v/(z_u+z_v)]*R1_vij)/(2*pi).

`first_residual`, `source_affine` and `second_resolver` prove these actual
identities at arbitrary amplitudes, before any root equation is imposed.
`multiplier_sum` checks the finite polynomial combination, preserving every
species coordinate and tail index. `certificate_identity` uses the already
proved actual residual evaluation and infinite-domain polynomial extensionality
to prove the exact MvPolynomial ideal identity. It does not infer polynomial
identities from numerical sample evaluations or root-only identities.

The definition `certificate` fills ALL certificate fields with proved data.
`actual_vacuum_fiber_finite` really invokes the existing exact fiber checker
on that constructed certificate. Existence of this certificate is not an
extra hypothesis. This completes the first concrete certificate family;
it does not replace the still-open POSITIVE-density construction obligation.

## Separate external M1/M3 exact-witness audit

Claude's 140 export rounded endpoints with nstr, losing nonzero widths.
Our 141 audit identified this and missing common-parameter witness data;
142 / commit 926f29f corrects both in a NEW result
`results/two_tail/two_tail_endpoint_interval_exact.json`, preserving 140.
All authoritative interval endpoints are now exact dyadic rational strings.

The new independent standard-library checker
`scripts/certificates/check_endpoint_witness_rational.py` recomputes interval
I-CJ from the saved C,J, checks the saved error matrix covers that exact
product, recomputes the Krawczyk image from center,C,f(center),E,X and checks
that the saved K covers it. It verifies strict K inclusion, norm upper
bounds, positive widths, stored A signs, all source/diag hashes, the exact
physical parameters and both endpoint roots' inclusion in M3's SAME common
parameter box. It ignores PASS flags and rounded displays as evidence.

All ten point witnesses and the M3 common parameter witness pass. Upward-rounded
maximal point norm bounds are 0.503039715228 (M1) and 0.354549856640 (M3);
the M3 common parameter bound is 0.354549856640. Corrupted error matrices,
K images on the boundary, norm reports, A signs and omitted source pins are
rejected. Reproduce with
`python3 scripts/certificates/check_endpoint_witness_rational.py`.

This checks the RATIONAL PART of the EXTERNAL witness. Analytic J/f/A
enclosures and root preservation through the unrecorded shrink iterations
remain dependent on Claude's mpmath AD calculation/source. It is not an Arb
replay of M1/M3 or a Lean proof. M1 still lacks a same-branch certificate;
this is not a proof that no connecting branch exists. M3's local common
segment is separate from PY-seed matching, all-wave first loss and Taylor
radii. Classifier comparisons remain FLOAT evidence at these two controls.

The M2 upstream JSON metadata also changed during this work. A fresh independent
Arb calculation reproduced EXACTLY the same C and all numerical bounds; commit
c447b67 updates only that report's upstream source hash. Its standard-library
checker passes again. The mathematical certificate was unchanged.

## Verification and manuscript correspondence

PASS: 966 exact standard-three guards /65 research modules plus root /
66 direct pinned compiler commands. All 47 new actual axiom reports were
queried before generating strict guards. Independent post-run audit verifies
EVERY input/source/artifact/raw-log hash; ALL 63 prior module source, artifact
and footprint records unchanged; all 530 frozen source/config hashes and nine
validated-paper/seven Mathlib/two separately locked raw LeanCode pins unchanged.
No new external direct dependency import or shared/Lake build. Evidence:
`results/lean/validation.json`, `results/lean/build.log`. Reproduce with
`python3 scripts/check_project.py`; it writes only research outputs and audits
the frozen dependency read-only before and after compilation.

Suggested SI citations, not applied to TeX:

- Cite `actual_root_iff_reduced_of_nonzero`, `reduced_root_decodes_actual` and
  the image identities with their precise chart/activity conditions.
- Cite `degree_firstPoly` and `degree_secondPoly` for the quadratic degree
  bounds. Do not turn them into a finiteness or universal bound on root counts.
- Cite `actual_cluster_limit_of_reduced_finite_fiber` with its explicit
  reduced-finiteness hypothesis, retaining that proof obligation.
- Cite `VacuumFiberCertificate.certificate_identity` and
  `actual_vacuum_fiber_finite` as the CONSTRUCTED vacuum certificate example.
  Retain zero density and positive rates; arbitrary finite mixtures are covered.
- Keep zero-coupling reverse substitution and physical pi/exp coefficients
  exact. The external M2 interval evidence is a separate item and has not been
  turned into an actual EndpointRegular proof by these algebraic results.

General nonisolated relevant endpoint fibers, positive-density generic exact
certificate construction, finite matrix escape, generic multitailed complex
Taylor-radius LOWER bounds and tail/all-density classification remain open.
A full continuous singular endpoint limit is not automatic analyticity there.
The initial canonical domain and the positive-density single-attractive-tail
beta<R=fold/full-endpoint theorem remain unchanged. No universal real-root /
Taylor-convergence equivalence, RDF positivity, first-instability wave-number
claim, new mathematical axiom, foundation change, merge-back or TeX write.
