# Pure-fluid PY node positivity from the actual frozen formulas

`PureFluidHardSphereNodePositivity.lean` formalizes the Step 4 inequalities
needed by the proposed all-order pure-fluid positivity proof. Its inputs
are exactly the foundation definitions `ExactMSA.F0`, `rhoOf`, `bA0`,
`qp0`, `phi1`, and `phi2`; no alternate hard-sphere factor is assumed.

For `z>0`, the elementary gap

    z(1+exp(-z)) - 2(1-exp(-z))

is strictly positive. Lean proves this by differentiating
`z-2+(z+2)exp(-z)` and using `Real.add_one_lt_exp z` to show its
derivative is positive on `(0,∞)`.

For `0<xi<1`, Lean proves the exact identity

    F0(xi,z) - exp(-z) F0(xi,-z)
      = (1-exp(-z)) + [6xi/(1-xi)]
        [z(1+exp(-z))-2(1-exp(-z))]/z²,

then its strict positivity. The identity itself only requires `xi≠1`
and `z≠0`. Separately, the frozen transforms satisfy `phi1(z)<0` and
`phi1(z)+2phi2(z)<0`. Together with the exact PY relation
`qp0(xi)-bA0(xi)/2 = π/(1-xi)`, these show `F0(xi,z)>1` at every
positive node. Thus the actual node ratio
`omega=exp(-z)F0(xi,-z)/F0(xi,z)` is below one and
`kappa=(1-omega)/z` is strictly positive.

The proof is pointwise for positive tail rates, exactly what the node
formulas need. It does not yet prove `F0(xi,x)>1` for negative `x`.
Moreover, `actual_F0_at_zero` proves `F0(xi,0)=1` for the FROZEN
totalized rational definition: the paper's phrase “for every real x”
cannot be used literally with that definition at zero. A separate
removable-singularity extension would be needed for that wording.
The module does not yet connect the proposed dressing to every actual BH root. The latter,
all-order coefficient positivity, and radius equality remain open.

Full research validation: PASS, 1765 exact standard-three theorem guards /
190 modules. This module adds eleven guarded theorems. Frozen foundation
1.0.17 unchanged; no TeX write or new axiom.
