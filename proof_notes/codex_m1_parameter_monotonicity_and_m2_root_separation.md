# M1 parameter monotonicity and M2 local root separation (2026-10-28)

These are EXTERNAL numerical certificates and independent exact-rational
checks, not Lean proofs. No Lean source, compiler artifact, foundation file
or TeX file is changed. The existing 966-guard Lean evidence remains intact.

## 144: same M1 branch, with all bridge witnesses independently checked

Claude's `two_tail_m1_fold_branch.json` parametrizes the four-equation actual
scalar BH root locus by p=Dt1. The unknowns are y=(Dt2,G1,G2,tau). Four closed
p slabs cover the hull of the two endpoint root boxes from the exact 142
certificate; three point witnesses identify the curves at the internal breaks.

The independent standard-library checker
`scripts/certificates/check_m1_fold_witness_rational.py` recomputes EVERY slab's
I-CJ, C*R_p and full mean-value Krawczyk expression, checks strict inclusion
and the norm, and also checks all THREE INITIAL point Krawczyk witnesses at
the breaks. Geometric inclusion of a final bridge box alone would not suffice.
It checks there are exactly three bridges, no gaps in the exact p cover,
matching break values, shrunk/initial/adjacent-box containments, endpoint-root
inclusions, both exact A signs, the wide tau hull and all source hashes.

All four slab and three point witnesses pass. The largest original slab norm
is at most 0.663623849666 (rounded UP). Analytic f/J/R_p/A enclosures and root
preservation through the unrecorded shrinking iterations remain external
mpmath-AD evidence. The old exact endpoint certificates are also checked.

This proves, externally with those analytic inputs, that the endpoints belong
to one continuous real root curve. Without tau monotonicity, opposite A signs
only locate a zero somewhere along that curve and in its WIDE tau hull. They
do not alone put its coupling between the endpoint couplings. A continuous
curve can leave that coupling interval and return.

## New independent Arb monotonicity certificate

The NEW script
`scripts/certificates/codex_m1_parameter_monotonicity_arb.py` computes no new
roots, centers or parameter slabs. It reuses the exact four existing boxes
and their exact rational preconditioners C. It independently constructs the
literal original residual R in (Dt1,Dt2,G1,G2,tau), with exact eta=49/100,
sigma=1, z=(3/5,21/25) and the exact w from 144. Physical pi and exponentials
remain exact symbolic coefficients before Arb evaluation.

SymPy differentiates R with respect to y and p. It forms

    E = I-C*R_y,
    v = -C*R_p

symbolically BEFORE interval evaluation. Both are independent of tau and
polynomial of amplitude degree at most two. Each expression is shifted about
the saved exact center and collected into monomials in the four deviations.
Arb at 256 bits evaluates constant coefficients first, retaining cancellations,
then multiplies by the small deviation balls. There are no finite differences,
float physical constants, or interval wrappers around a float Jacobian.
Integer monomial powers use repeated interval multiplication, which also
works for deviation balls crossing zero without invoking a logarithm branch.

The original raw-AD E norm was about 0.664. The new centered symbolic enclosures
have infinity norm LESS THAN 0.001736 on each SAME entire slab box. However a
single infinity-norm bound for all derivative coordinates is still too coarse
to certify the much smaller tau derivative. The following exact component
calculation resolves this, without an extra root search or smaller slabs.

Let d=-R_y^(-1)*R_p at any point of a box. Since ||E||_infinity<=q<1,
R_y and C are invertible, and

    d = v+E*d.

From the saved interval endpoints define M_ij=max(abs(E_ij)),
V_i=max(abs(v_i)), q=max_i sum_j M_ij, and

    D0 = max_i V_i/(1-q),
    B0_i = D0,
    B1 = V+M*B0,
    B2 = V+M*B1.

The norm bound gives |d_i|<=B0_i. Substituting into d=v+E*d proves successively
|d_i|<=B1_i and |d_i|<=B2_i. A final signed interval gives

    v_i.lower-sum_j M_ij*B2_j <= d_i
                              <= v_i.upper+sum_j M_ij*B2_j.

All these operations, including the strict positive lower bound, are computed
with exact Fractions from the outward dyadic Arb endpoints. The independent
standard-library checker
`scripts/certificates/check_m1_parameter_monotonicity_rational.py` recomputes
these bounds and matches every source box, center and C against 144.

On ALL FOUR slabs it proves externally

    137/1000000 < d(tau)/d(p) < 176/1000000.

The tighter individual tau-derivative enclosures are approximately

| slab | lower | upper |
|---|---:|---:|
| 0 | 0.0001378896 | 0.0001751793 |
| 1 | 0.0001378010 | 0.0001750906 |
| 2 | 0.0001377123 | 0.0001750019 |
| 3 | 0.0001376236 | 0.0001749133 |

Those table decimals are orientation only. The exact fractions in
`results/certificates/codex_m1_parameter_monotonicity_arb.json` and the simple
strict rational bounds above are authoritative.

## Consequence: M1 zero in the narrow coupling bracket

The implicit root curves have d(tau)/d(p)>0 in every slab. They agree at all
three breaks, hence tau is strictly increasing along the assembled curve.
The EXACT endpoint roots lie on that curve, with opposite exact A signs.
On the subarc joining those two roots, continuity therefore gives A=0 at
some point with

    tau_lo < tau_zero < tau_hi.

This is the exact narrow coupling bracket from 142, now on ONE branch. Its
rational endpoints are recorded in the new report. The WHOLE p-cover extends
very slightly past the unknown exact endpoint p values, so this statement is
about the connecting subarc; it does not replace the wide Y-box tau hull for
the entire certified cover.

The new script also independently verifies the honest zero-frequency moment
identity for sigma=1. SymPy proves the removable Laplace block limits -1/2,
1/6 and 1, then exactly simplifies

    Qhat_zero = -Qp/2+A/6+sum_u [(W_u+C_u)/z_u+C_u],
    1-rho*Qhat_zero = A/(2*pi).

This uses the honest limiting moments, not substitution of zero into a
rational formula with removable denominators. Hence the physical det F(0)
has the same sign-change bracket. Neither PY-seed matching for this M1 curve, first loss,
all-wave behaviour, a fold location, RDF positivity nor a Taylor radius is
supplied. This remains an external result, not an instantiated Lean theorem.

## 145: what M2 second-root separation does and does not say

The independent standard-library checker
`scripts/certificates/check_m2_second_root_witness_rational.py` rechecks all
three saved Krawczyk tests: the second-root box X2 and the two window boxes
Y1,Y2. It recomputes the exact matrix products and coupling mean-value terms,
strict K inclusions, norm bounds, parameter coverage, source/diag hashes,
old frozen root-box hash and old PY cover-file hash. All pass:

| box | upward-rounded norm bound |
|---|---:|
| X2 | 0.339299407974 |
| Y1 | 0.310039905181 |
| Y2 | 0.339299407974 |

It verifies X2 is disjoint from the old amplitude box, Y1 contains that old
box, Y2 contains X2, and Y1/Y2 are disjoint. For EACH FIXED w in W, these
are two disjoint local root graphs over the reported tau window. Varying w
is a family of such graphs, not one fixed physical model's curve.

The distinction from the selected PY root at the contact parameters uses
old 009/011: their linked actual root graph reaches r1. At the SAME parameters,
r2 is distinct from that selected graph's root. This is not a proof that the
two roots belong to different global connected components of the algebraic
root locus, or that continuation outside the window can never join them.
At an excluded canonical endpoint, the meaningful comparison is with the
selected limiting root, rather than membership of an endpoint omitted from
the open initial domain. No canonicity verdict about r2 itself is inferred.

The old 7357-slab PY chain was not rerun here; its pinned compressed cover
hash was checked. Its analytic bounds and the new mpmath-AD bounds remain
inherited external evidence. The older 013 all-wave certificate is also a
separate historical result, not a new assertion of this second-root checker.
Float exploration up to tau about 17 or backward toward a fold is not used.

## Reproduction, negative controls and unchanged Lean baseline

```sh
python3 scripts/certificates/check_m1_fold_witness_rational.py
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/codex_m1_parameter_monotonicity_arb.py
python3 scripts/certificates/check_m1_parameter_monotonicity_rational.py
python3 scripts/certificates/check_m2_second_root_witness_rational.py
```

The analytic calculation needs python-flint and SymPy; validated versions are
0.6.0 and 1.13.2. With those installed normally the PYTHONPATH prefix is
unnecessary. The current session's pinned packages already live at that path.
The 256-bit replay is byte-identical; a 384-bit independent recomputation
also proves the same strict derivative bounds. All reports pin their actual
inputs and sources; no stored PASS flag is accepted as mathematical evidence.

Rejected negative controls: a missing bridge, a corrupt point-bridge norm,
a wrong C*R_p product, a parameter-cover gap, changed C, changed component
bound, changed tau derivative, omitted source pins, wrong M2 norm/product,
and an incorrectly narrowed M2 window. No scan or root-tracing rerun.

The 966 exact standard-three guards /65 Lean modules plus root /66 compiler
commands were NOT rerun because no Lean input changed. Their entire existing
input/source/artifact/raw-log hash audit passes, including all 530 frozen
hashes and nine paper/seven Mathlib/two raw LeanCode pins. All old M2 and M1/M3
rational checkers pass too. No new mathematical axiom or numerical premise
was inserted into Lean. General exact positive-density fiber certificates,
matrix escape and generic multitailed complex Taylor LOWER bounds remain open.
