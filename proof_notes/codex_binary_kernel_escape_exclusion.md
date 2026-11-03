# Finite amplitude escape: an actual binary mixture class

2026-11-01. Research package only. Foundation 1.0.17 and TeX are untouched.
The four new modules contain 33 public theorems, all with exact queried axiom
footprints: propext, Classical.choice and Quot.sound. No new axiom is added.

## Exact physical conclusion

`BinaryExchangeSymmetry.exists_hs_maximal_branch_with_finite_axis_cluster`
constructs the actual maximal initial canonical branch from the following data:

- two species with the same fixed positive number density r and diameter a;
- any finite positive tail rates, including repeated rates and an empty tail set;
- each tail strength matrix invariant under simultaneous species exchange,
  equivalently K_00 = K_11 and K_01 = K_10;
- positive physical vacancy, equivalently eta < 1.

Tail strengths can have either sign; no positivity or positive semidefiniteness
of K is required. No eta <= 0.8 restriction is used. The amplitude norm is the
ORIGINAL product of the entrywise Pi norms; no norm is changed.

If the constructed maximal initial branch ends at a finite coupling beta, it
has a genuine approaching sequence of actual roots whose amplitudes converge
to an actual endpoint root in canonical closure, with a physical Baxter
Fourier-factor determinant zero at some real frequency, possibly zero.
Finite amplitude escape is excluded. No root curve, inverse, amplitude bound,
endpoint value, kernel symmetry along the branch, or endpoint regularity is
supplied to this theorem.

The intermediate `hs_prefix_no_finite_escape` applies to any continuous actual
canonical prefix through the honest HS seed. It excludes exactly

    for every B and c < beta, some t in [0,beta) with c < t has norm(p(t)) > B.

The stronger intermediate `BinaryCanonicalProperness.canonical_roots_uniformly_bounded`
bounds ALL actual canonical binary roots over each bounded strength set,
provided their actual coefficient kernels have exchange symmetry. This latter
kernel symmetry is an explicit structural premise for the off-branch result;
it is derived internally for the physical HS-seeded branch above.

## Reusable scalar resolvent estimate

`ScalarKernelResolventBounds` has 13 theorems. For arbitrary finite coefficient
data c, put F_c(s) = 1 - laplace(c)(s). If F_c has no zero in the OPEN right
half-plane, then at each fixed positive real s there are constants C0 > 0 and
C1 >= 0, independent of c, such that

    norm(F_c(s)^(-1)) <= C0,
    norm(sourceMap_s(c) / F_c(s)) <= C1.

These estimates do not assume scalar physical amplitudes. Normalize the frame
(1, compactKernel(c)) in R times the finite actual-kernel image. Its norm-one,
zero-free closure is compact. Laplace injectivity excludes an identically zero
limit scalar symbol; the proved scalar Hurwitz closure theorem then excludes
zeros at each interior frequency. A positive common minimum modulus follows.
The source descends to the same compact-kernel image and is a bounded linear
functional there. Thus its quotient is bounded even when raw coefficients grow.
Repeated rates and redundant coefficient directions cause no extra assumption.

## Actual mixture channels and source orientation

`BinaryCanonicalChannels` has eight theorems. For an actual exchange-symmetric
kernel with equal r and a, the ORIGINAL factor is diagonal in the fixed plus
and minus species modes. Its determinant is exactly F_plus * F_minus. Actual
matrix canonicity therefore implies zero-freeness of both scalar factors.

The first BH equation originally contains the TRANSPOSED transform; the second
contains the UNTRANSPOSED transform. The proved exchange identities handle this
orientation before adding or subtracting the two original column equations.
For each row i and tail u they give

    (D_i0 +/- D_i1) * F_+/-(z_u) = (2*pi/z_u) * (K_i0 +/- K_i1),
    (2*pi*r) * (G_i0 +/- G_i1) * F_+/-(z_u) = sourceMap(row kernel mode).

The row kernel mode is the same scalar mode coefficient up to a unit sign.
In particular the second identity retains its density factor r. Applying the
uniform inverse and source estimates bounds both amplitude row modes. Their
sum and difference recover both original entries. Finite summation yields the
original product/Pi norm bound, including the empty-tail case.
`BinaryCanonicalProperness` formalizes this argument in three theorems.

## Kernel symmetry is derived on the physical branch

`BinaryExchangeSymmetry` has nine theorems. It proves exact species-swap
covariance of the nonlinear W, C, M, N, A, Qp, dressed Qhat, source, both BH
equations and the finite coefficient vector. Physical strength exchange also
implies reciprocity for two species.

The HS seed's invariance is proved from its ACTUAL zero-D second equation and
the existing physical HS matrix inverse. It is not an extra seed assumption.
Swapping a root yields another root at the same coupling. The swapped path is
continuous and agrees with the original at the seed. Actual connected
canonical-root uniqueness makes the two paths agree on the whole prefix.
Thus exchange symmetry of every actual kernel is a conclusion of physical
data and canonical continuation. The existing general maximal-branch and
boundary-alternative theorems then give the stated endpoint cluster result.

## Remaining general-mixture obstruction

This does NOT exclude escape for unequal diameters, unequal compositions,
non-exchange-symmetric binary strengths, or general higher-component mixtures.
The general mixed-amplitude escape alternative remains open. The earlier 480
random numerical states are external evidence, not a replacement for a proof.

The scalar compactness argument does not automatically transfer to matrices:
a nonzero normalized matrix symbol can be identically singular. For example,
the generic rational factors I - t/(s+1) E_01 have determinant one throughout
the right half-plane and tend to I at positive infinite frequency, yet their
inverses grow with t at a fixed interior frequency. This is an obstruction to
a proposed general analytic inference, NOT a counterexample of actual MSA
roots. Actual root equations or an additional derived matrix structure must
exclude such degeneracy. No physical no-escape axiom is introduced.

The endpoint assertion is a CLUSTER assertion. It does not prove a unique full
limit at a singular endpoint, automatic equality of the complex Taylor radius
with the real stable endpoint, or the originally proposed real-root/Taylor iff.

## Validation

PASS at 2026-11-01T19:37:42.730381+00:00: 1508 exact axiom-footprint guards,
136 research modules plus the root, 137 recorded compiler commands. The prior
132 module artifacts were reused; only the four new modules and root were
compiled. The single prescribed incrementally reused package check exited 0.
Evidence is in `results/lean/validation.json` and `results/lean/build.log`.
The 530 frozen source/config hashes and direct import pins (10 validated paper,
two raw LeanCode and 57 cached Mathlib artifacts) were preserved. The prescribed checker
uses exact source/command/artifact and dependency reuse, without rebuilding
frozen imports. All 33 raw proof bodies were compiled before generating their
exact guards.

A deliberate mathematical negative control removes only the factor r from
the second original row-channel claim. Both channel proof bodies then fail
with `ring failed, ring expressions not equal` at their `linear_combination`
steps. This is a proof-body failure, not a guard-message mismatch or timeout.
The actual density factor is retained in the committed theorem.
