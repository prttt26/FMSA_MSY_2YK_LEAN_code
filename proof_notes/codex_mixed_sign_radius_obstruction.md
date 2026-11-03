# Coefficient oscillation when a canonical mixture outlives its Taylor radius

`MixedSignRadiusObstruction.lean` proves a necessary feature of a genuine
Taylor-radius shortfall. Define `Oscillates a` to mean that for every order
cutoff `m`, some `n ≥ m` has `a n > 0` and some (possibly different) `n ≥ m`
has `a n < 0`. This is stronger than merely observing a finite sign change.

The elementary `eventually_signed_or_oscillates` shows that any real sequence
either has one weak sign from some order onward or satisfies `Oscillates`.
The package's already proved `EventuallySignedTaylor` Pringsheim theorem
then gives `oscillating_original_component_of_radius_lt_interval`: if an
original amplitude path is real analytic on `[0,b)` and its common Taylor
radius is strictly less than `b`, one original `D` or `G` coordinate
oscillates in this unbounded-order sense.

`canonical_state_beyond_radius_has_oscillating_component` applies the result
to the ACTUAL `MaximalBranch` root and original Blum–Høye coefficients at
any canonical state `b` strictly beyond the common radius, whether the
maximal interval is finite or infinite. The branch supplies its own
analyticity from the exact MSA/canonicity interface. A second theorem,
`maximal_branch_oscillating_original_component`, uses a finite maximal
endpoint when the radius is smaller than that endpoint.
`exists_hs_branch_with_radius_shortfall_obstruction` constructs the
HS-seeded branch from finite physical mixture data (`vacMix > 0`, symmetric
tail strengths) and includes the conditional conclusion at every real
canonical state on that constructed branch.

This theorem requires a strict radius shortfall as a premise. It does not
establish one for a specific numerical mixture, nor does it give the radius
for PSD tails. M3's external monodromy/canonicity certificates are separate
evidence for a canonical-state shortfall; a kernel instance would require
their numerical checks in Lean. It also does not say that every coordinate
oscillates, or that coefficients alternate at consecutive orders.

Full research-package validation after this addition: 1724 exact theorem
guards across 184 modules, all five new proofs with only `propext`,
`Classical.choice` and `Quot.sound`; foundation 1.0.17 unchanged. No TeX or
foundation write.
