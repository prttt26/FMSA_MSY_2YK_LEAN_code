# Eventual-sign endpoint summation for the actual mixture branch

## Mathematical statement and Lean interface

For a finite mixture, let `M` be the constructed maximal canonical
HS-seeded Exact MSA branch, and suppose its endpoint `b` is finite.
Assume that for every entry of each original BH amplitude `Dt` and
`G`, there is a nonzero real multiplier `s` and an index `m` such that
`s c_n ≥ 0` for every Taylor coefficient `n ≥ m`. The multiplier and
cutoff may depend on the entry.

`EventuallySignedEndpointSummation.maximal_mixture_endpoint_sum_of_eventual_component_signs`
proves that the full finite-dimensional amplitude series converges at
`b`, and its sum is `PhysicalEndpointLimit` for the actual path. In
particular the sum satisfies `MultiTailMixture.IsRoot`, belongs to
the closure of canonical amplitudes, is itself noncanonical, is the
path's unique selected left limit, and has a real Fourier zero. This
does not claim uniqueness of all possible roots at `b`.

## Proof structure

The scalar lemma
`summable_endpoint_of_eventually_nonnegative_coefficients` bounds
every tail partial sum at `b` by the finite interior left limit after
removing the finite polynomial head. Multiplying coefficients by `s`
gives `summable_endpoint_of_eventually_signed_coefficients`.

For the actual mixture, `EventuallySignedTaylor` and the maximal
branch analyticity establish `b ≤ amplitudeRadius`. The existing
maximal-branch criterion identifies every interior Taylor sum with
the physical path. The mixture noescape theorem supplies the unique
finite left limit. Applying the scalar lemma to every original
amplitude entry gives full vector summability; the existing endpoint
identification theorem identifies its sum with the physical limit.

The eventual-sign assumption is substantive. Binary attractive
mixtures already have components with both signs at low orders, and
eventual one-sign behavior is not established generally. The theorem
provides a sufficient endpoint criterion, not an unconditional
mixture convergence boundary.

Validation: full project checker PASS, 2405 exact theorem guards / 265
research modules, standard `propext`, `Classical.choice`, `Quot.sound`
only; one Lean compiler capped at 30 GiB RSS. Frozen foundation
1.0.17 and TeX unchanged.
