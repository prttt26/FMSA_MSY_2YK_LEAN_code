# Actual RDF amplitude derivatives

This work addresses the differentiability gap left by `JacobianExterior` and
`RadialVariationL2`. It does not identify the actual h tangent with an L2
Fourier solution, and it does not establish canonical factor uniqueness.

For a fixed compact interval [0,R], let X = C([0,R], E), where E is a complete
real normed algebra. Let T(q)u(r) = integral_0^r q(r-t)u(t) dt. The existing
unconditional Volterra existence and uniqueness theorem gives bijectivity
of A(q) = I - T(q), for every continuous q. The Banach inverse theorem then
gives a bounded inverse. This is unrelated to any sufficient global weighted
kernel norm bound below one: no such bound is needed on a compact interval.

The bilinear estimate ||T(q)u|| <= R ||q|| ||u|| makes q -> T(q) a bounded
linear map. Smooth inversion on the open set of invertible bounded operators
proves joint C-infinity dependence of Y(q,g) = A(q)^(-1)g. Differentiating
A(q)Y(q,g) = g gives the actual Frechet derivative equation

    A(q) dY[dq,dg] = dg + T(dq)Y(q,g).

The actual MSA recentered Q and G source are finite sums of fixed continuous
functions with coefficients `bhCoefficient`, already proved C-infinity in
the original amplitude-space norm. A separate `BaxterMatrix` type confines
the matrix operator norm to the Volterra codomain and does not replace the
norm used for these actual amplitude derivatives.

The existing `nonlinearCausalG_renewal` and compact Volterra uniqueness identify
the newly bundled compact solution with the existing constructed
`nonlinearCausalG`. Subtracting the fixed affine background gives the actual
`nonlinearRDFExcess`. The fixed causal shifts and hard-core indicator then
give parameter C-infinity of `nonlinearRDFMoment`, `nonlinearH` and
`nonlinearG` at every fixed real r. Rates, densities and diameters are fixed;
no root, sign, free-volume or kernel-smallness premise is needed for this
pointwise parameter statement.

Scope still open: uniform global decay or L2 control of the actual h tangent
on a canonical state; transcription of the actual linearized OZ equation
into the spectral matrix identity; recovery of amplitudes from a vanishing
DCF tangent; canonical continuation and its endpoint. Pointwise C-infinity,
even at every r, must not be described as differentiability in a global L2
space. No universal real-root/Taylor-convergence equivalence follows.

Baseline 1.0.17: 20 Volterra and 24 actual RDF theorems, all exact std3
guards; 68 paper modules and 529 guards overall. The default foundation
build passed 9080 jobs and workspace plus three compatibility targets passed
9236 jobs. The paper checker passed with 530 frozen source/config hashes.
The 1.0.16 manifest is archived byte-for-byte. New manifest SHA256:
`09ade0691482098319e832c6c721b77ef70d99bb76cec5bc84b498357dd9219c`.
Evidence: `formalization/results/baseline_1_0_17/`. Independent downstream
proof builds are NOT_RERUN; active-import impact checks are separate.
No TeX was written.
