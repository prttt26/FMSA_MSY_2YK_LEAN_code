# Single attractive tail: a zero-mode root strictly before the fold

The Lean module `FMSAPaper/SingleTailSpinodal.lean` proves this for one
hard-sphere species and one attractive Yukawa tail, at every positive rate,
density and diameter with positive free volume. It uses the existing actual
Blum–Høye parametrization and physical branch, not a supplied fold or sign
assumption. Every one of its 14 theorems has an exact standard-three-axiom
guard. No new axiom or TeX write is involved.

## Exact statements and scope

- `AS_fold_neg`: the actual scalar coefficient A is strictly negative at
  the endpoint of the quartic physical branch.
- `exists_zero_before_fold`: there is a parameter u strictly between the
  PY seed parameter and the fold parameter, with A=0 and strictly positive
  coupling below the fold.
- `actual_single_tail_zero_before_fold`: the same witness lies on the
  existing `SingleTailRadius.physBranch`, is an actual `IsRoot` of the BH
  system, and is strictly before `foldCoupling`.
- `actual_single_tail_zero_lt_radius`: for every continuous PY-seeded actual
  root germ, that witness's coupling is strictly below its actual common
  Mathlib `amplitudeRadius (branchCoefficients p)`.

The A=0 condition is the scalar zero-mode condition in the existing Baxter
normalization. The Lean capstones explicitly state the actual coefficient
A, actual BH root and actual Taylor radius. They do not assert that this
witness is the first mode to vanish, or that the RDF is nonnegative.
If a finite-k zero occurs earlier, the first real-k loss is earlier still.
With the usual definition of the initial canonical endpoint as the first
real-k zero, its endpoint is no later than the A=0 witness and therefore
strictly below the fold/radius. This last statement uses that physical
endpoint definition; the new module does not introduce an axiom defining
or computing a general mixture canonical endpoint.

## Parametrization and normalization

Write x=z*sigma>0, eta=pi*rho*sigma^3/6, v=1-eta>0, E=exp(-x). Use the
existing quantities from `SingleTailParametrization`:

```
J = E*(x+2)+x-2,
H = E*(2*x+2)+x^2-2,
Ht = 2-2*x+E*(x^2-2),
a = -(18*eta^2*J+6*eta*v*H+x^3*v^2),
b = -18*eta^2*J+6*eta*v*Ht-E*x^3*v^2,
d = v*x^2*(1-E)+6*eta*J,
m = (1+2*eta)*d.
```

Existing Lean results give J>0, d>0 and a<b<0. The coupling is
`q(u)=-Lambda*u^2*(u-a)*(u-b)`, with Lambda>0. Its smaller critical point
c1 lies in (a,b), and q is strictly increasing from the seed a to c1.

`AS_param` substitutes the existing `DtS` and `GS` directly into the
existing actual `AS` definition and proves, for nonzero physical denominators
and u!=0,

```
A(u)/(2*pi) = N(u)/(x*v^3*d^2),
N(u)=2*u^2-2*(a+b+m)*u+2*a*b+m*(a+b).
```

The d in the denominator is exactly the d used in m. The Lean identity is
proved for arbitrary positive physical diameter, not only sigma=1. An
independent SymPy scalar transcription at sigma=1 verifies the same identity
directly from gamma,C,W,M,Nc and A, rather than assuming the zero-mode
quadratic formula. Its exact algebra is reproduced by

```
python3 scripts/coupling_singularities/codex_single_tail_spinodal.py
```

The result is `results/coupling_singularities/codex_single_tail_spinodal.json`.

## Sign at the critical point

Let S=a+b and Q(u)=4*u^2-3*S*u+2*a*b. Its two roots are c1<c2. Exact ring
identities give

```
N(u) = (u+m)*(S-2*u)+Q(u),
Q(S/2)=-(a-b)^2/2<0.
```

Thus c1<S/2<c2, so S-2*c1>0. For the other factor, direct homogeneous
expansion gives

```
Q(-m) = -36*eta^2*v^2*x^2*J^2
        +3*eta*v^3*x^2*J*R1 + v^4*x^4*R0,
R1 = -2*J-3*x^2*(1-E),
R0 = -3*(1-E)*J-2*((1-E)^2-E*x^2).
```

All three terms are strictly negative. Indeed E<1 and J>0 imply R1<0.
Mathlib's `Real.self_lt_sinh_iff` gives sinh(x/2)>x/2. Multiplying by
2*exp(-x/2)>0 yields `1-E>x*exp(-x/2)>0`, hence
`(1-E)^2>E*x^2` and R0<0. These inequalities are proved in
`exp_square_gap`, `expRemainder_neg` and `critical_neg_spinScale`.
Therefore Q(-m)<0, which implies c1<-m<c2. Consequently

`N(c1)=(c1+m)*(S-2*c1)<0`.

The denominator x*v^3*d^2 is positive, so A(c1)<0.

## Intermediate value and actual branch/radius

At the seed u=a, DtS=0 and A=QppS>0. N is a globally continuous polynomial.
The intermediate value theorem therefore gives a<u_s<c1 with N(u_s)=0;
u_s<0 ensures the actual parametrization denominators are nonzero, and
`AS_param` gives A(u_s)=0. Strict monotonicity of the already proved quartic
branch yields `0<tau_s=q(u_s)<q(c1)=tau_fold`.

`branch_q` identifies the inverse quartic value at tau_s with u_s. Thus the
witness is on the existing actual `physBranch`, and `physBranch_isRoot`
discharges the actual BH root identity. Finally the existing unconditional
`SingleTailRadius.single_tail_radius_eq_fold` identifies every continuous
PY-seeded actual root germ's common radius with tau_fold. This proves the
strict inequality tau_s<R for its actual Taylor coefficients, without a
supplied sign, analyticity, fold or convergence premise.

## Manuscript handoff and limits

The former single-tail statement "A=0 before the fold is numerical only"
can be replaced by a citation to
`FMSA.Paper.SingleTailSpinodal.actual_single_tail_zero_before_fold` and
`actual_single_tail_zero_lt_radius`, with positive rate/density/diameter,
positive free volume and attractive strength. The strict inequality is
about an A=0 witness on the actual PY branch; do not label the witness as
the first mode without a first-mode argument. Finite-k firstness, RDF
positivity, a general mixture canonical-to-Jacobian bridge, and mixed-sign
multitail conditions are not proved by this module.

Claude's independent review in messages 018 and its attachments checks the
definition-free sign steps and supports the conclusion on 42 float states.
Those samples are not proof premises. The Lean proof checks the two
definition-dependent identities exactly and covers every state in the
stated physical domain.
