# Pure-fluid pole limits with coincident tail rates

`PureFluidCoincidentPoleLimits.lean` removes the injective-rate condition
from the real-axis pole-limit comparison. The generic theorem partitions a
finite tail family into rates equal to `z_t` and rates different from it.
The latter terms are continuous at `s=-z_t`; the former combine into one
simple pole. Consequently its scaled punctured limit is the sum of all
same-rate numerator values.

For the candidate finite-sum dressing, Lean obtains

    lim_(s → -z_t, s ≠ -z_t) (s+z_t) P_cand(s)
      = sum_(u: z_u=z_t) formalPoleP_u,
    lim_(s → -z_t, s ≠ -z_t) (s+z_t) Shat_cand(s)
      = sum_(u: z_u=z_t) formalPoleS_u.

When the `r` node system holds and `U(z_u)≠0` for all indices at the
same rate, each summand equals its candidate cross-node coefficient.

For an ACTUAL `MultiTail.IsRoot`, positive rates and nonzero actual
node factors, the companion limits are

    -sum_(u: z_u=z_t) Lambda_u Shat(z_u),
    -sum_(u: z_u=z_t) Lambda_u P(z_u),

with `Lambda_u=dressedStrength_u=rho D_u/F(z_u)`. This is exactly the
combined pole coefficient required when rates repeat. It is a limit
along the punctured real axis; no complex-meromorphic residue theorem
is asserted. Cancellation among same-rate contributions is allowed.

These seven theorems close the repeated-rate residue bookkeeping gap.
They do not prove that candidate and actual functions coincide globally:
origin/moment matching, candidate node-system solvability and actual
HS-branch identification remain open, as do all-order positivity and
`R=tau_f`.

Full project validation: PASS, 1807 exact standard-three theorem guards /
196 research modules. Frozen foundation 1.0.17 unchanged. No TeX write
or new axiom.
