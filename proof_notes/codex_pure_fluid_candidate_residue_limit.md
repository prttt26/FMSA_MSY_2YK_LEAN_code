# Pure-fluid candidate and actual BH pole limits

`PureFluidCandidateResidueLimit.lean` proves real-axis punctured-neighborhood
limits at each negative tail rate. The generic `simple_pole_tendsto` and
`finite_simple_pole_tendsto` lemmas show that a regular head plus a finite
sum of simple rational poles has the expected scaled limit when the target
rate is distinct from the other rates and all numerators are continuous.

For positive pairwise distinct rates, the candidate dressing satisfies

    lim_(s → -z_t, s ≠ -z_t) (s+z_t) P_cand(s) = formalPoleP_t,
    lim_(s → -z_t, s ≠ -z_t) (s+z_t) Shat_cand(s) = formalPoleS_t.

Under the paper's `r` node system and `U(z_t)≠0`, these become

    -(w_t/U(z_t)) Shat_cand(z_t),
    -(w_t/U(z_t)) P_cand(z_t).

The same generic lemma applies to the ACTUAL Blum–Høye root identities
from `PureFluidExactResidueForm`. For an actual `MultiTail.IsRoot`, positive
pairwise distinct rates, and nonzero `F(z_u)` at every positive node,
the genuine `rationalPart` and `exponentialPart` have respective limits

    -Lambda_t Shat(z_t),
    -Lambda_t P(z_t),

where `Lambda_t = dressedStrength_t = rho D_t/F(z_t)`. These are limits
along the punctured real axis; no complex-meromorphic residue theorem is
claimed. At repeated rates, individual terms sharing one pole must be
summed before taking its scaled limit. The later
`PureFluidCoincidentPoleLimits` module proves that combined limit;
see `codex_pure_fluid_coincident_pole_limits.md`.

This closes the earlier gap between formal pole coefficients and analytic
real-axis pole limits. It does not identify candidate and actual functions:
that also requires matching the origin coefficients and proving the
candidate dressing belongs to the actual HS-seeded solution branch.
Existence of the node-system solution, all-order coefficient signs, and
`R=tau_f` remain open.

Full research validation: PASS, 1800 exact standard-three theorem guards /
195 modules. The new module has ten guarded theorems and uses only
`propext`, `Classical.choice`, and `Quot.sound`. Frozen foundation 1.0.17
unchanged; no TeX write or new axiom.
