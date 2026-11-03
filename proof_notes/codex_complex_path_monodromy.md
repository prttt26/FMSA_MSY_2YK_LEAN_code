# Generic complex-path monodromy and the genuine vector Taylor radius

Five actual Lean bodies and their exact compiler guards passed standalone
validation. Their actual axiom footprints are exactly
`{propext, Classical.choice, Quot.sound}`. Three mathematical corruptions fail
inside proof bodies, before the footprint guards. Full checker20313 actually
exited0:1141 guards /105 research modules plus root /106 commands. Independent
post-run audit verified all127 inputs, source/artifact/root/rawlog hashes,
ALL104 prior module fingerprints and every frozen/import/replay hash. Both
published external receipts and all their input pins remain unchanged.
No new external Lean import or shared dependency build.

## What is proved

`MSAConvergence/ComplexPathMonodromy.lean` works for any complex Banach amplitude
space E, a connected parameter space S, a continuous coupling path gamma and
a continuous lift p through residual roots R(gamma(t),p(t))=0.

1. `regular_lifts_eq`: a second continuous root lift matching p at any one
   seed equals it everywhere. Along p, the original residual is smooth and
   its true amplitude partial is invertible. The analytic IFT supplies LOCAL
   uniqueness; an open/closed argument on S propagates equality. Global root
   uniqueness, an inverse and uniqueness of other algebraic sheets are not
   assumed. The coupling path need not be differentiable at polygon corners.
2. `changed_lift_excludes_continuous_root`: if two path times have the same
   coupling but different lifted values, there is no single-valued continuous
   root over the whole path matching the seed. The seed is a THIRD independent
   time and can precede the closed subpath; this accommodates the HS-to-loop
   prefix in the actual M3 witnesses.
3. `changed_lift_excludes_analytic_germ`: an analytic candidate that solves R
   only NEAR the seed is also excluded. The analytic identity principle
   proves its residual vanishes throughout the connected complex domain;
   then the proved regular-lift uniqueness yields the contradiction.
4. `radius_le_of_changed_lift`: for a GENUINE Banach-valued power-series germ
   g at zero, locally solving R and matching the seed, the actual formal-series
   radius is at most any positive r whose disc contains the entire path.
   The series sum is analytic in its convergence disc, equals g near zero,
   and hence cannot be single-valued around the changed lift. No coefficient
   signs, nearest-singularity fit or assumed global root identity is used.
5. `not_summable_of_radius_lt_norm`: outside that radius, the ordinary vector
   coefficient series does not converge. Convergence would make its terms
   tend to zero, so their norms give radius at least |z|. Thus conditional
   as well as absolute convergence is excluded. This last theorem needs no
   completeness hypothesis.

The separate M3 endpoint replayer correction is committed as97aa792 and its
fresh512-bit audit passed all8420 checks and10 controls. The exact conclusion
R<=84<337/4<rigorous tau_lo remains EXTERNAL until its actual numerical objects
instantiate these generic Lean interfaces.

## Validation and explicit limits

Standalone command:

```sh
python3 /tmp/compile_msa_research.py MSAConvergence/ComplexPathMonodromy.lean --output
```

The helper selects the pinned Lean4.31.0 directly, forwards
`relaxedAutoImplicit=false` and `maxSynthPendingDepth=3`, and uses only existing
read-only dependency artifacts. It writes only the research package's own
artifact. The standalone log `/tmp/msa_complex_path_guarded.log` is empty and
the actual compiler process9487 exited0. Raw five-footprint prototype process
28324 exited0; after removing its unused completeness parameter, all five
exact guards passed without warnings.

Three separate controls replace a real loop by a tautological equality,
strengthen r to r/2, or reverse the radius/norm comparison. All actual compiler
processes53289/58349/42045 exited1 with their FIRST errors in the mathematical
proof bodies, before the footprint assertions.

The five-body1141 checkpoint closes the GENERIC analytic implication.
The later completed1268/114 checkpoint now connects it to the literal
original finite-mixture complex BH residual, true real/complex Jacobians,
constructed HS germs and equal original real/complex intrinsic radii. See
`ActualComplexBH` and `proof_notes/codex_actual_complex_bh.md`. Physical HS
data discharge germ, seed canonicity and inverse premises internally.
Numerical path/root-box/determinant/link/gluing/changed-endpoint instances
remain open; no external receipt is promoted to a Lean numerical theorem.
The selected nonisolated finite-cluster limit gap was closed under1178,
and compressed H2 under1220. General mixture norm escape exclusion and
multitail Taylor-radius LOWER classification remain open. No all-component
or boundary divergence, exact/nearest radius, first-loss frequency or RDF
positivity is asserted.
No new axiom, TeX/foundation write, shared build, merge or push.
