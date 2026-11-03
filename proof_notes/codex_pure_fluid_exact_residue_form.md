# Actual pure-fluid BH factor: full finite-pole formulas

`PureFluidExactResidueForm.lean` turns the earlier node identities into
the full rational/exponential formulas of Step 1 in the paper proof.
For an ACTUAL `MultiTail.IsRoot`, positive finite rates and nonzero
factor at each positive rate, define

    Lambda_t = rho D_t / F(z_t),
    c = sum_t Lambda_t P(z_t),
    a = rho amplitudeA,  q = rho amplitudeQp.

Then Lean proves, as identities of the existing real rational
expressions for every real `s`, including Lean's totalized values at
denominator zeros,

    P(s) = 1-a/s³+(a-q)/s²+(q-a/2-c)/s
           -sum_t Lambda_t Shat(z_t)/(s+z_t),
    Shat(s) = a/s³+q/s²+c/s
              -sum_t Lambda_t P(z_t)/(s+z_t).

The proof substitutes the already proved actual-root relations
`rho W_t=Lambda_t Shat(z_t)` and
`rho C_t=Lambda_t P(z_t)` into the ORIGINAL finite BH factor split.
No candidate `U,g` dressing or residue theorem is assumed. Repeated
rates are allowed for the algebraic identities; analytic residues at
coincident poles would combine their terms.

This is the exact comparison target for the proposed dressing. Still
open are the construction/identification of that dressing from the
actual BH system, its original moment relations, coefficient positivity
and radius equality. The theorem is an identity of the genuine factor
pieces, not a proof that the candidate representation holds.

Full research validation: PASS, 1776 exact standard-three guards /
192 modules. Both new theorem footprints contain only `propext`,
`Classical.choice`, and `Quot.sound`. Foundation 1.0.17 unchanged;
no TeX write or new axiom.
