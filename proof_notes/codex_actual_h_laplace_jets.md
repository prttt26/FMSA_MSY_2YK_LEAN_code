# Actual h radial-moment Laplace jets and resolvent transfer

Research file: `MSAConvergence/ActualHLaplaceJets.lean` (11 theorems), over
immutable foundation 1.0.17. The alias `hMomentLaplace` is exactly the
positive-axis Laplace integral of r times the existing `nonlinearH`; it does
not introduce a surrogate h. This research remains outside the SI.

## The actual fixed-contact identity

Let R_ij=`edgeHi sigma i j`, Y=`nonlinearCausalG`, q=`nonlinearCausalKernel`
including row density, and F=`nonlinearGSource`. Amplitudes p=(Dt,G) vary
while rates, densities and diameters remain fixed. With R_ij>0,
`weighted_h_positive_shift` proves at every r>0, including r=R_ij,

    r*h_p,ij(r) = -r + causalShift(Y_p,ij,R_ij)(r).

In the hard core the actual h is -1 and the causal shift is zero. Outside
and at contact, the existing actual moment equals the shifted RDF excess;
Y=excess+r+R restores exactly the background above. The proof uses the
actual constructors, not a hypothesized root curve or a supplied OZ identity.

`weighted_hVariation_positive_shift` proves the genuine existing
`JacobianExterior.hVariation` satisfies

    r*delta h_p,v,ij(r) = causalShift(delta Y_p,v,ij,R_ij)(r).

The contact does not move with the amplitude parameter. Its indicator is
retained explicitly, so no derivative of a moving contact or endpoint atom
is silently omitted.

## Actual integrability before splitting the transform

`causalShift_laplace_integrable` proves that a genuinely integrable damped
causal field remains absolutely integrable after any fixed real shift, on
the full real line. It extends the weighted field by the Ici(0) indicator,
uses the zero-measure endpoint equivalence with Ioi(0), translates the
integrable function and retains the exact complex exponential prefactor.
No continuity or integrability of the undamped field is presumed.

`hMomentLaplace_of_causal_integrable` proves both actual integrability and

    Hmoment_p,ij(s) = -1/s^2 + exp(-s*R_ij)*Laplace(Y_p,ij)(s),

when Re(s)>0 and the actual Y integral is integrable. The affine background
and shifted-Y integrals are separately justified before splitting their sum.
The core term is -1/s^2, with no R-dependent factor; contact dependence is
entirely in the shift. `hVariation_laplace_shift` similarly proves actual
integrability and the scalar shift formula for r*delta h whenever the actual
causal tangent integral exists.

## Genuine whole-family amplitude differentiation

`actual_hMoment_local_laplace` uses the parameter-neighbourhood-uniform Y
bound from `ActualLaplaceJets`. In a common far right half-plane it supplies
actual Hmoment integrability and the off-root affine-core formula throughout
a neighbourhood of p, for every species pair.

`actual_hMoment_laplace_jets` combines this neighbourhood identity with the
proved whole-Y-family amplitude smoothness and integral derivative. It gives
one cutoff depending on p, not on direction v, such that for every s beyond
it and every pair:

- the actual base Hmoment integral is absolutely integrable;
- the whole actual Hmoment family is C-infinity in the real amplitudes at p;
- every genuine r*delta h has an absolutely integrable Laplace integral;
- that integral equals the genuine whole-family amplitude Frechet derivative;
- the derivative is exp(-s*R_ij) times the genuine Y-transform derivative.

The -1/s^2 background has zero amplitude derivative because s and contact
are fixed. No differentiation of an identity valid only at BH roots is used.

## The additive phase is explicit

The frozen foundation defines R_ij=(sigma_i+sigma_j)/2 and

    D(s) = rdfPhase(sigma,s) = diag(exp(-s*sigma_i/2)).

`additive_contact_phase_sandwich` explicitly invokes the existing proved
`rdfPhase_contact_product`. For any complex matrix X,

    [exp(-s*R_ij)*X_ij]_ij = D(s)*X*D(s).

This step is an additive-contact theorem. For a general non-additive contact
matrix, only the scalar shift expression is justified; no D*X*D factorization
is asserted. This addresses Claude audit 057 directly. The causal Y shift is
proved from its actual pair contact and does not acquire Baxter Q's different
lower-edge shift by assumption.

`actual_hVariation_laplace_phase` then gives the true integrated h tangent
matrix as D(s)*D_p Laplace(Y)(s)[v]*D(s), at a common far-right cutoff for all v.
The two matrix factors stay in their proved order.

## Eliminate the unknown G transform

Let T(s)=I-Laplace(q)(s). The actual local off-root renewal and its genuine
parameter derivative, with T a proved unit under computed strong damping,
give

    Laplace(Y) = Laplace(F)*T inverse,
    Laplace(delta Y) =
      (Laplace(delta F) + Laplace(F)*T inverse*Laplace(delta q))*T inverse.

`actual_hVariation_laplace_resolvent` proves the resulting actual h formula:

    Laplace(r*delta h) = D(s)*
      ((Laplace(delta F)+Laplace(F)*T inverse*Laplace(delta q))*T inverse)*D(s).

All right-side source/kernel families and their true variations have the
proved finite dictionaries and exact existing J/L interfaces from
`ActualLaplaceJets`. Thus the unknown actual G transform is eliminated.
The theorem retains each noncommutative product order. Source normalization
remains the existing 1/(2*pi); it is not absorbed or dropped in this transfer.

## Assumptions and limits

Actual capstones require finite species/tails, positive rates and positive
diameters. Repeated rates, signed/zero densities and arbitrary amplitudes are
allowed. No BH root, residual-kernel direction, nonzero-free-volume,
canonical-state, root-curve, physical small-kernel-budget or Wiener inverse
axiom is assumed. The generic shift lemmas have their own exact integrability
premises, discharged internally at the actual capstones.

All h-transform results are in a constructed sufficiently far right
half-plane. They are first amplitude derivatives, not all-order coupling
Fourier interchange. They do not supply Fourier-boundary integrability,
global actual h-tangent L2, full tangent OZ, canonical factor/amplitude
recovery, general no-fold or a tail-shape/Taylor convergence classification.
In particular, the affine causal G itself is not asserted integrable on the
Fourier axis; the damped decomposition must not be evaluated there by using
an undefined integral's default value. No universal real-root/Taylor
convergence equivalence is asserted.

## Reproduction

Use `python3 scripts/check_project.py`. Exact guards come from the actual
compiler reports; source/artifact/command/log hashes are in `results/lean/`.
The direct pinned compiler reads prevalidated imports and audits all 530
frozen source/configuration hashes and six direct FMSAPaper artifact pins
before/after. No shared dependency build, foundation/TeX/numerical write or
merge-back is performed.

## Remaining analytic route to investigate (not proved)

The main gap is now actual canonical decay, rather than further derivative
notation. A possible route avoiding a general Wiener inversion axiom is:

1. Use the actual finite J/L/phase formulas to prove uniform strip estimates
   qhat(s)=q(0)/s+O(1/s^2) at large |s|. The rate tails allow a narrow negative
   real-part strip; explicit finite formulas also retain the finite spatial
   derivative jumps at contacts.
2. From a genuinely canonical, closed-right-half-plane zero-free renewal
   factor and these uniform high-frequency estimates, prove a slightly wider
   zero-free strip. Do not replace canonicity by pointwise real-k stability.
3. For the actual Volterra resolvent, subtract q(0)/(s+b) to obtain an
   integrable O(1/s^2) vertical-line remainder. Prove its contour shift from a
   known far-right inverse Laplace representation to a negative vertical
   line. This should yield actual exponential resolvent decay without using
   the frozen Wiener axiom.
4. Apply that actual resolvent to the existing exponentially decaying excess
   source and its genuine tangent source. The affine G background must be
   cancelled using the actual mass/contact normalizations before deriving
   global actual h-tangent L1/L2 and Fourier-boundary tangent OZ.

Each item is still a proof obligation, as are maintenance of initial
canonicity, canonical factor/amplitude recovery and the general convergence
classification. This route is a plan, not extra mathematical hypotheses
silently appended to a completed no-fold theorem.

Verified isolated checkpoint (2026-10-28): PASS, 223 exact standard-three-axiom
guards across fourteen research modules plus root, including 11 new guards
here. Every source/artifact/log hash matches; all 530 frozen source/configuration
hashes and six direct validated import artifact pins remain unchanged before/after.
No shared dependency build. Foundation manifest SHA:
`09ade0691482098319e832c6c721b77ef70d99bb76cec5bc84b498357dd9219c`.
