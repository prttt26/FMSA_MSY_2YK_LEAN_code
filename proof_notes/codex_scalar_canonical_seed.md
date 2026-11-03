# Scalar HS canonicity at every physical density, without the homotopy axiom

Date: 2026-10-28. Research package over frozen foundation 1.0.17 / 06e3268.
New modules: `HolomorphicHomotopy.lean` (1 theorem) and
`ScalarCanonicalSeed.lean` (9 theorems). No foundation/TeX/numerical edits,
new mathematical axioms or merge-back.

## What is proved

For ONE species, positive diameter, nonnegative density with eta<1 and any
finite positive tail rates, the ACTUAL initial HS density-weighted causal
kernel has an invertible renewal factor at EVERY complex frequency Re(s)>=0.
Frequency zero and vacuum are included, using honest integrals. The conclusion
is independent of the unused G amplitudes and does not require the dilute L1
budget. Repeated rates and empty finite tails are allowed.

This covers the one-species eta=0.47..0.49 states motivating Claude 104.
It does not prove full initial canonicity of arbitrary unequal-diameter
mixtures at high density, global existence of an MSA branch, or a Taylor
radius reaching the whole real stable interval.

## The exact pure-analysis axiom statement is now a theorem

The frozen `FMSA.Analysis.zeroFree_lowerHalfPlane_of_homotopy` is an AXIOM:
for an entire family H_t jointly continuous on [a,b] x C, a uniform radius
bounding all closed-lower-half-plane zeros, no real-axis zeros at any t,
and no open-lower-half-plane zeros at a imply the same zero-freeness at b.
`HolomorphicHomotopy.zeroFree_lowerHalfPlane_of_homotopy` proves EXACTLY that
statement, with no extra hypothesis and without consuming the old axiom.

Work in the relative parameter space P=[a,b], which is preconnected. Let G
be the set of parameters with no strict-lower-half-plane zero.

- G is open: at a parameter in G the function is nonzero on the entire
  compact closed lower half-disc of the uniform escape radius (the real
  boundary is handled by the supplied real-axis premise). Joint continuity
  and the compact-tube lemma give a parameter neighbourhood nonzero on this
  whole compact set. The escape bound excludes every remaining zero.
- G is closed: at any closure parameter the limiting entire function is
  nontrivial (evaluate at -i(R+1), beyond the escape radius). Our previously
  PROVED `HolomorphicZeroPersistence.zero_free_at_closure` applies to the
  connected open lower half-plane. Its proof uses isolated zeros and the
  reciprocal maximum-modulus principle, not a Hurwitz/Rouche axiom.
- The supplied base point lies in G. The nonempty clopen set G is therefore
  all of the connected interval, including the endpoint b.

No zero-count integral, winding-number implementation, argument-principle
axiom, positivity of a real part or additional physics assumption is needed.
The frozen source and axiom declaration remain unchanged; this is a separate
research theorem to use at integration time.

## Actual scalar half-plane result

The frozen `BaxterLowerHalfPlane.lean` already proves all required scalar
homotopy INPUTS. `scalar_baxterH_no_lower_zero` reassembles them with the new
PROVED homotopy theorem. It NEVER calls the frozen final half-plane theorem.
Its physical family is the same actual definition

    rhoPhys(sigma,eta)=6 eta/(pi sigma^3),
    baxterH(sigma,eta,k)=1-Qhat_complex(eta,sigma,rhoPhys(sigma,eta),k).

The inputs are the dilute seed, joint continuity, entire Qhat, uniform
escape radius, the nonzero-real-frequency k^6 norm dominance identity, and
the actual polynomial-integral origin formula. Each input was individually
queried from the installed pinned Lean and has only the standard three axioms.
The two N=1 physical coefficient identities have the same footprint.

`scalar_baxter_symbol_nonzero` converts back to any physically coupled
(eta,sigma,rho), rho>=0 and eta<1. Strict lower frequencies use the new
homotopy theorem; the real boundary uses the proved k^6 result away from
zero and `one_sub_Qhat_complex_zero_ne_zero` at the TRUE integral origin.
At rho=0 the integral kernel is zero identically, so vacuum is handled
without division by density. Thus the honest scalar Baxter factor is nonzero
on the ENTIRE closed lower half-plane, including k=0.

The deliberate footprint comparison is:

    frozen FMSA.HardSphere.Qhat_complex_ne_one_of_im_neg:
      standard three + FMSA.Analysis.zeroFree_lowerHalfPlane_of_homotopy;
    new FMSA.Convergence.ScalarCanonicalSeed.scalar_baxterH_no_lower_zero
      and scalar_baxter_symbol_nonzero: standard three ONLY.

The old theorem keyword never served as evidence of an axiom-free proof.
The mixture physics axiom is likewise not consumed.

## Genuine actual-kernel identification

At N=1, `actual_scalar_hs_kernel_eq_poly` proves equality in REAL SPACE:

    nonlinearCausalKernel(z,rho,sigma,0,G)(r,0,0)
      = q0_poly(etaMix(rho,sigma),sigma_0,rho_0,r).

It uses the proved N=1 physical Qp/A coefficient identities and the actual
zero-Dt W/C cancellation. No transform, formal pole value, nearby root or
root-only identity is substituted for this real-space equality.

`actual_scalar_hs_laplace_eq` proves the genuine causal integral equals
`Qhat_complex(...,-I*s)`. The kernel is actually integrable, its tail beyond
sigma vanishes and interval/causal integrals are identified before changing
frequency variables. This includes s=0. Since Im(-I*s)=-Re(s), the new scalar
factor nonzero theorem applies on Re(s)>=0. The one-species determinant is
its actual (0,0) entry, so `actual_scalar_hs_canonical` proves FULL actual
initial canonicity at every physical eta<1, with no smallness condition.

## Actual branches and correct Taylor interpretation

`exists_scalar_analytic_canonical_hs_seed` reuses the already-proved physical
analytic HS seed, then combines the new all-density initial canonicity with
proved genuine canonical openness. It CONSTRUCTS an analytic root germ
through (0,baseSeed), with positive common amplitude radius, nearby actual
roots and full nearby canonicity, for arbitrary finite K. No canonical seed,
Jacobian inverse, branch curve, K sign or K-symmetry premise is supplied.

`exists_scalar_convergent_canonical_hs_interval` constructs a common b>0
such that for every real abs(t)<b the branch is analytic, an actual MSA root,
fully canonical, and ALL amplitude Taylor series sum TO those roots. This is
a local interval, not a lower bound reaching the full stability endpoint.

`exists_scalar_series_extension_of_physical_axis_units` applies to a branch
given only on the initial nonnegative interval. Its seed VALUE p(0)=(0,baseSeed)
is supplied, but initial full canonicity is discharged internally at every
physical density eta<1. One-species K symmetry is automatic. Continuous branch,
actual roots and units of the physical Fourier factor at EVERY real wave
number throughout the interval remain explicit. It constructs the genuine
analytic extension e, agreeing with ORIGINAL p throughout the interval, and
proves the exact correct criterion

    AmplitudeHasSumTo e p bound <-> bound<=amplitudeRadius(branchCoefficients e).

It does not infer that radius inequality from real-axis canonicity or replace
the all-wave-number premise by a finite sample. No arbitrary negative-time
values of p are differentiated. There is no universal real-root/Taylor iff.

## Read-only import provenance and reproducibility

Existing nine validated FMSAPaper import pins and all six prior direct Mathlib
pins are retained. One cached Mathlib `Analysis.Complex.Convex` import supplies
the lower-half-plane connectedness. Two additional direct LeanCode imports
supply the scalar inputs: `HardSphere.BaxterLowerHalfPlane` and
`HSMixture.MixtureNoSpinodalN1`. Their exact released source hashes and
PRE-EXISTING cached artifact hashes are independently locked in
`cached-foundation-imports.json`, checked before/after and recorded separately
from the nine paper-validation-covered imports. They are never rebuilt by
research validation. These imports may expose old axiom declarations; every
new actual footprint checks that none is consumed by the proofs.

Run `python3 scripts/check_project.py` from the research package. Required
coverage: 680 exact standard-three theorem guards, 45 research modules + root,
46 direct pinned compiler commands; all 530 frozen source/configuration hashes;
all previous nine FMSAPaper / six Mathlib pins plus the Convex pin and both
separately locked direct LeanCode sources/artifacts. EVERY research input,
source, artifact and raw-log hash is audited. No Lake/shared build is invoked.


Full validation and independent audit: PASS. There are 680 exact standard-three
research guards across 45 modules plus root / 46 pinned compiler commands.
EVERY input/source/artifact/raw-log hash matches. All 43 previous research
module sources, artifacts and footprints are unchanged. All 530 frozen
source/configuration hashes, all nine paper-validation-covered pins and all
six previous Mathlib pins are unchanged; the new Convex pin and both separately
locked direct LeanCode source/cache pairs match their pre-use hashes. The new
lock is itself a hashed validation input. Results are in
`results/lean/validation.json` and `results/lean/build.log`.

## Remaining obligations

Arbitrary unequal-diameter mixture initial canonicity beyond the proved
low-density neighbourhood; global PY-connected branch existence/continuation
without finite amplitude escape; endpoint existence/control; all-wave-number
parameter certificates; complex Taylor-radius lower bounds and tail/all-density
classification. No strict fold inequality, RDF positivity, unexamined observable
series or amplitude-family global-L2 differentiability is inferred.
