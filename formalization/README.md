# FMSA paper formalization

Integrated proofs for `FMSA_dp_output/md/FORMALIZATION_TODO.md`, under
`MSA_and_1st_Truncation/FMSAPaper/`. The default package entry imports
`FMSAPaper.lean`, which imports every paper module. This is part of the
published foundation package and its normal Lake environment.
The pre-integration 1.0.3 manifest and validation evidence are archived.

Run from `Lean_code/MSA_and_1st_Truncation/`:

```sh
lake build
python3 formalization/check.py
```

The checker uses the default Lake build for sixty paper modules and all
413 theorem footprints through `#guard_msgs`, audits the versioned foundation,
checks that the default entry imports the complete collection, and saves source
and compiled-artifact hashes and build logs in
`formalization/results/validation.json`. Allowed axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

## Proved scope

| Item | Principal declaration | Scope |
|---|---|---|
| F1 homogeneous polynomial | `FMSA.Paper.ActualStrengthJets.actual_jets_homogeneous_polynomial` | One finite monomial coefficient table for every strength vector and any continuous actual PY-seeded root. Each order-n monomial has exactly n strength factors; the seed is included. |
| F1 actual factor dictionary | `FMSA.Paper.ActualBaxterJets.factor_jet_basis`, `factorPrime_jet_basis` | Every coupling jet of the actual finite-tail factor and ordinary spatial derivative retains the same fixed basis. |
| F1 actual full-line convolution | `FMSA.Paper.ActualBaxterJets.convolution_jet_cauchy` | All-order Cauchy rule for the actual factor integral, with mixed-rate basis-product integrability discharged internally. Infinite tails and repeated rates are included. |
| F1 actual boundary correction | `FMSA.Paper.ActualBaxterBoundaryJets.convolution_with_lowerJump_jet` | The actual lowerValue atom is retained in the corrected convolution. `ordered_lowerJump_jet_zero` proves its vanishing in the ordered positive-radius convention by support geometry. |
| F1 Baxter normalization and assembly | `FMSA.Paper.BaxterNormalization.primitive_hasDerivAt`, `primitive_shell_window`, `normalized_correlation_jet_cauchy` | The full primitive divided by 2*pi has derivative -r*c on the ordered positive axis off contact; its shell identity also crosses contact. The actual DCF Cauchy sum uses the paper convention q = Q/(2*pi), with no infinite-series convergence premise. |
| F1 whole-line boundary integration by parts | `FMSA.Paper.BaxterIntegrationByParts.product_integration_by_parts_with_lower_edges`, `product_integration_by_parts_ae` | Both actual lower-edge atoms are retained, for arbitrary amplitudes and either edge order. The pointwise theorem excludes the coincident-edge displacement; the a.e. version holds on the full real line. |
| F1 reflected primitive derivative | `FMSA.Paper.BaxterSecondDerivative.fullPrimitive_second_hasDerivAt`, `realPrimitive_eq_re` | Full existing Baxter primitive, all species orders, derivative on the second convolution factor with its lower-edge contribution, away from lower/reflected-contact edges. The full weak version is supplied below. |
| F1 second-factor Cauchy sum | `FMSA.Paper.ActualBaxterSecondJets.normalized_correlation_second_jet_cauchy` | All orders of the actual ordered positive-axis DCF in q = Q/(2*pi), with negative convolution sign and explicit lower-edge product at each coefficient partition. No convergence hypothesis. |
| F1 weak derivative of the factor | `FMSA.Paper.BaxterWeakDerivative.q_weak_derivative` | Against every compactly supported C1 test function, the actual factor's weak derivative equals qPrime plus lowerValue times the lower-edge Dirac mass, with no upper-contact atom. |
| F1 full reflected weak formula | `FMSA.Paper.BaxterWeakPrimitive.fullPrimitive_weak_derivative` | Full real line, arbitrary amplitudes and all species orders, compact C1 tests. Both linear lower-edge atoms and the second-factor convolution atom are retained. Positive rates and nonnegative diameters suffice. |
| F1 actual radial weak identification | `FMSA.Paper.ActualRadialWeak.root_primitive_weak`, `root_second_weak` | Every species pair at an actual symmetric-strength root with nonzero free volume. Tests are compactly supported in the positive radial axis; the full reflected weak formula represents 2*pi times the test integral of r*c. No extra reciprocity, small-kernel or coupling-convergence premise. |
| F1 test/jet interchange | `FMSA.Paper.BaxterWeakJetBasis.primitive_test_jet_integral`, `BaxterSecondIntegralJets.second_test_jet_integral`, `RadialIntegralJets.ordered_test_jet_integral` | Coupling jets commute with integration against compactly supported continuous tests, for the full reflected primitive, the second-factor numerator and r times the ordered radial DCF. Each integrand is a fixed finite integrable dictionary with smooth amplitude coefficients (`FiniteIntegralJets.jet_integral_linear`); no derivative-under-integral or domination premise is assumed. |
| F1 weak identity at every coupling order | `FMSA.Paper.BaxterWeakCauchy.fullPrimitive_weak_cauchy`, `ActualRadialWeakJets.local_root_second_weak_cauchy`, `normalized_local_root_weak_cauchy` | Every coefficient of the full reflected weak identity, for any smooth amplitude curve on the whole real line; for an actual local symmetric-strength root branch with nonzero free volume, every coefficient of r times the ordered radial DCF of every species pair, in q = Q/(2*pi). The convolution term is an explicit Cauchy sum over order partitions, including its lower-edge product; both linear Dirac coefficients are retained. Tests are C1, compactly supported in the positive radial axis. No series-convergence premise. |
| F1 actual radial Fourier identification | `FMSA.Paper.ActualRadialIdentification.root_radial_fourier`, `local_root_radial_fourier` | At every nonzero real wave number, the spectral Baxter coefficient equals the Fourier transform of the ordered radial DCF. Symmetric-strength actual BH roots, positive rates/diameters and nonzero free volume suffice. Core reciprocity follows from the automatic finite Wronskian certificate; no separate reciprocity or small-kernel-budget assumption remains. |
| F1 mixed-rate spatial blocks | `FMSA.Paper.MixedRateSpatialMembership.actual_cross_inner_hasForm`, `actual_cross_outer_hasForm` | Actual exponential Baxter cross blocks belong to the fixed polynomial/exponential space on both ordered positive core intervals. Mixed-rate integration uses z+w, so coincident positive rates are included. |
| F1 full multirate assembly | `FMSA.Paper.MultirateSpatialMembership.numerator_inner_hasForm`, `numerator_outer_hasForm` | The complete convolution numerator belongs to the fixed space on both ordered core pieces, for arbitrary amplitudes. Single-tail polynomial blocks and actual mixed-rate integrals are combined by an exactly proved finite superposition identity. |
| F1 actual DCF jets | `FMSA.Paper.ActualSpatialJets.core_jet_inner_hasForm`, `core_jet_outer_hasForm` | Every order of r times the actual DCF belongs to that space. Only local finite-order amplitude smoothness is needed; no series convergence or smooth choice of spatial coordinates is assumed. |
| F1 all species and knots | `FMSA.Paper.OrderedSpatialJets.ordered_core_jet_hasForm`, `ordered_exterior_jet_hasForm`, `ordered_jet_contDiffAt_off_knots` | For the existing ordered radial definition, all species pairs and all three positive-radius pieces are covered. Every coefficient is smooth away from the contact and absolute diameter-difference edge. Requires positive diameters and a nonempty finite tail family; repeated positive rates are allowed. This does not prove Fourier reciprocity. |
| F1 strict truncations | `FMSA.Paper.SpatialJets.weighted_truncation_hasForm` | Finite strict truncations preserve the space for r times the DCF, not generally for the unweighted DCF. |
| F1 spatial dimension | `FMSA.Paper.SpatialDictionary.space_finrank_le`, `jet_hasForm_of_representation` | A finite-dimensional space of dimension at most 5+2M, closed under coupling jets of fixed coefficient representations. Membership also implies spatial smoothness on the specified set. |
| F1 exterior | `FMSA.Paper.PhysicalExteriorJets.exterior_jet` | Any actual local root has an exterior DCF linear in coupling. All Taylor orders except one vanish beyond contact, with no series-convergence assumption. |
| F1 scaling | `FMSA.Paper.StrengthScaling.exists_actual_roots_with_scaled_jets` | Compatible actual physical BH roots for every scalar strength rescaling, with D and G coefficients scaling by a^n. Includes zero/negative a, repeated rates, unequal diameters and zero-density species under the existing seed assumptions. |
| F1 Cauchy sum | `FMSA.Paper.FiniteBasis.jet_of_local_baxter_identity` | A local linear-plus-bilinear Baxter identity in a fixed finite dictionary gives the full normalized Cauchy sum at every order. |
| F1 tails/jumps | `FMSA.Paper.FiniteBasis.jet_integral_add_jump` | Whole-line integrals plus jump evaluations yield the Cauchy sum. Basis-product integrability is explicit; compact support and distinct rates are not required. |
| F2 obstruction | `FMSA.Paper.Fold.not_analytic_root` | A coupling derivative outside the amplitude Jacobian's image precludes differentiable, hence analytic, root continuation through the point. |
| F2 radius/divergence | `FMSA.Paper.FoldRadius.actual_radius_le_fold`, `actual_nonconvergence_beyond_fold` | For the actual BH residual, a continuous finite branch regular before a positive transverse fold has common Taylor radius at most the fold and no componentwise sum at any larger real coupling. |
| F3 convergence | `FMSA.Paper.TaylorRoot.exists_physical_taylor_convergence_theorem` | Constructs the actual smooth physical PY-seeded BH branch. Componentwise Taylor convergence at one implies local equality with that branch, roots on (-1,1), the Abel limit, and an endpoint real root. Conditional endpoint convergence is included. |
| F3 contrapositive | `FMSA.Paper.TaylorRoot.actual_nonconvergence_of_no_real_root` | For the actual smooth root branch, absence of any real root at one rules out a finite endpoint sum for all components. |
| F4 nonnegative regrouping | `FMSA.Paper.NonnegativeRecenter.summable_of_recenter_summable` | Convergence of the recentered series at a nonnegative displacement forces convergence of the original series at the resulting point, without assuming that point lies inside the original disk. The center is strictly inside the original radius. |
| F4 scalar Pringsheim | `FMSA.Paper.Pringsheim.not_analyticAt_endpoint` | A nonnegative real scalar series with finite positive radius has no real analytic continuation across its positive endpoint agreeing with the interior sum. Endpoint divergence is not asserted. |
| F4 positive-order signs | `FMSA.Paper.SignedPringsheim.not_analyticAt_endpoint`, `le_radius_of_analytic_continuation` | The constant coefficient is unrestricted; multiplying all positive-order coefficients by one fixed nonzero scalar must make them nonnegative. A positive initial radius and consistent analytic continuation on (0,b) imply radius at least b. The actual-MSA connections are discharged by `ActualAnalyticBranch` and `ActualAnalyticTaylor`. |
| F3/F4 actual seed analyticity | `FMSA.Paper.ActualAnalyticTaylor.exists_analytic_seed_positive_radius` | Positive rates/diameters, nonnegative species densities and positive free volume yield a physical PY-seeded local analytic root and strictly positive common Taylor radius. No sign or convergence hypothesis. |
| F4 actual fold equality | `FMSA.Paper.ActualAnalyticTaylor.actual_radius_eq_fold` | Continuous finite branch, two-sided local root germ at zero, regularity before a positive transverse fold, and all positive-order coefficients of each component having one sign imply common radius equal to the fold. Different components may have different signs. |
| F4 actual Taylor sums | `FMSA.Paper.ActualAnalyticTaylor.actual_hasSum_before_endpoint` | Under regular-branch and all-order sign hypotheses, every component Taylor series converges to the actual branch value at every coupling in [0,b). The endpoint need not be a fold; convergence exactly at b is not asserted. |
| Initial-interval radius criterion | `FMSA.Paper.StableIntervalRadius.analytic_branch_converges_before_iff`, `actual_regular_branch_converges_before_iff` | Every amplitude component sums to the selected branch at every 0 <= tau < b iff b <= the common Mathlib radius. Extended endpoints include infinity; equality is admissible. The actual BH interface states continuity, root and invertible-Jacobian premises explicitly, without sign or fold premises. Identifying b with physical canonicity loss and discharging regularity from canonicity remain separate. |
| Finite-interval failure witness | `FMSA.Paper.StableIntervalRadius.nonconvergence_witness_before` | If a certified radius upper bound lies strictly below a certified initial stable interval length, some coupling inside that interval is outside the common radius and at least one amplitude series is not summable. No claim of stability from finite-grid crossing detection. |
| F4 single tail, unconditional | `FMSA.Paper.SingleTailRadius.single_tail_radius_eq_fold`, `single_tail_coefficients_nonneg`, `single_tail_branch_exists` | One hard-sphere species, one attractive Yukawa tail, any `z, ρ, σ > 0` with positive free volume: for every continuous PY-seeded root germ, all positive-order Taylor coefficients of both amplitude components are nonnegative and the common Taylor radius equals the explicit fold coupling `q(c₁)`. No sign, fold or convergence hypothesis. The BH system is reduced exactly to `τ = -Λ u²(u-a)(u-b)` with `a = -P < b < 0` (`SingleTailParametrization`); `1/q'` is absolutely monotone below the fold (`QuarticBranch`, `AbsolutelyMonotone`, Faà di Bruno); the upper bound uses non-continuation through the fold, not a Jacobian computation. |
| F4 single-tail zero mode before the fold | `FMSA.Paper.SingleTailSpinodal.AS_fold_neg`, `actual_single_tail_zero_before_fold`, `actual_single_tail_zero_lt_radius` | For the same all-state physical domain, actual A is negative at the fold, and the actual PY branch has an A=0 root at a strictly positive coupling strictly below the fold and the common Taylor radius of every continuous seed root germ. The exact parametrization and IVT discharge the witness; it is not asserted to be the first mode. |
| Actual zero-frequency integral | `FMSA.Paper.BaxterZeroMode.fourierQ_zero`, `scalar_fourierFactor_zero`, `scalar_spectral_den_zero` | All finite mixtures: the actual integral has its explicit moment value at zero. One species with finite tails: F(0)=A/(2*pi), and the spectral denominator is its square, with no root premise. |
| Actual radial zero mode | `FMSA.Paper.RadialZeroMode.root_radial_symbol`, `root_zero_moment`, `root_factor_gram_radial`, `actual_single_tail_zero_moment_before_radius` | Actual symmetric-strength BH roots: r^2*c is L1 and the continuous sinc Fourier symbol equals the actual spectral coefficient for every real k, including zero. One attractive tail has an actual 4*pi*rho*integral r^2*c=1 witness at positive coupling strictly inside the common Taylor radius. Firstness and general canonical-to-Jacobian regularity remain separate. |

The F3 proof transports all normalized jets through the actual polynomial BH
residual. Convergence makes the Taylor sum analytic; its residual has zero jets
and hence vanishes locally. Implicit-function uniqueness identifies it with the
original smooth branch. The analytic identity theorem extends the root identity,
and Abel and continuity give the endpoint. No analyticity of the original smooth
branch or root-series identity is assumed. SI theorem `si-thm:radiusreal` and
correspondence table `si-tab:si-corr4` cite the declarations; `make check` passed.

## Remaining obligations and corrections

- **F1: Lean proof complete (SI citation pending).** Multivariate polynomiality, arbitrary continuous
  seed-branch identification, the actual factor dictionary, full-line Cauchy
  convolution and the actual lower-edge correction are now proved. The full
  reflected, distributional Cauchy identity in the SI convention is proved
  as described at the end of this item. The complete multirate
  numerator, its normalization to r times the DCF, all coupling orders,
  all positive-radius pieces and the exchanged-row definition are now proved.
  The Fourier identification is now connected to actual symmetric-strength
  roots with nonzero free volume via the automatic Wronskian certificate.
  It follows from that certificate, not from choosing the larger-diameter row.
  Both first-factor and second-factor ordered Cauchy sums are now proved in
  paper normalization. The second-factor sum retains its lower-edge product;
  the earlier corrected-convolution coefficient theorem is now supplemented
  by actual integration by parts and the factor's weak-derivative identity.
  The second-factor ordered Cauchy formula, full primitive ordinary derivative,
  two-sided boundary integration by parts and factor weak derivative are now
  proved. The full real-line weak identity now retains both linear Dirac terms,
  and it is identified with the actual radial DCF for every species pair at a
  symmetric-strength root, using tests supported in the positive radial axis.
  Transport of that complete weak identity through all coupling jets is now
  proved (`ActualRadialWeakJets.normalized_local_root_weak_cauchy`), including
  the integral/jet interchange and the explicit Cauchy expansion of the
  convolution boundary term. With this, the Lean side of F1 is complete; the
  SI citation is pending in the paper-writing session.
  New citations are recorded in the Markdown backlog; this session does not edit the SI.
- With coincident rates, `5 + 2M` is an upper bound on span dimension, not always
  its dimension: duplicate exponentials are dependent. The SI now includes
  this qualification.
- The seed-Jacobian recursion is a positive-order statement. Order zero needs
  its separate seed equation; the generic truncation-through-n-1 argument does
  not justify the displayed recursion at n=0. The SI now separates n=0.
- **F2 is done under explicit fold assumptions.** The finite continuous branch,
  pre-fold Jacobian invertibility and endpoint range transversality are premises.
  Connectedness and local implicit uniqueness identify any analytic candidate
  with the branch up to the endpoint. No square-root normal form is needed.
  The common radius is the infimum of Mathlib's scalar component radii.
  Existence or numerical location of a fold at a particular state is not proved.
  SI theorem `si-thm:radiusfold` and table `si-tab:si-corr4` cite the result.
- **F3 is done.** The local series-root premise is now discharged using the
  actual smooth branch and convergence, and the SI cites the result. The result
  gives real solutions and a real endpoint root, not positivity or uniqueness
  among all real roots.
- **F4 is proved under the stated sign and fold hypotheses; for one species and one
  attractive tail it is proved unconditionally (1.0.11, `SingleTailRadius`), which covers HSY.**
  `ActualAnalyticBranch` derives analyticity from the actual polynomial residual,
  continuity, local root identity and invertible amplitude Jacobian, using the
  real implicit-function theorem at order omega. `AnalyticTaylor` identifies the
  canonical Taylor sum on its interval of convergence and supplies the signed
  radius lower bound. `ActualAnalyticTaylor.actual_radius_eq_fold` combines this
  with the proved fold upper bound. Its hypotheses do not assume analyticity,
  positive radius or series/branch identification. `actual_hasSum_before_endpoint`
  gives actual branch values as the sums before the endpoint. The physical PY
  seed has positive common radius without any sign hypothesis. No actual-model
  all-order sign theorem for general multitails or convergence-at-the-fold
  claim is supplied. `SingleTailSpinodal` additionally proves an actual A=0
  witness strictly before the single-tail fold/radius, for all positive
  rate/density/diameter states with positive free volume, without assuming
  first-mode canonicity or a fold sign. `BaxterZeroMode` and `RadialZeroMode`
  identify it with the actual factor determinant zero and the physical DCF
  zero-moment denominator, proving the required moment integrability and
  continuity at zero rather than using the raw quotient convention.
- **F5/F6: certified by interval arithmetic (2026-10-22), not in Lean.** See
  `certificates/README.md`. F5: for z = (1.8, 12), weights (1, -6) and
  eta = 0.2, 0.3, 0.4, a validated Krawczyk chain shows the PY-seeded branch is
  real and regular on [0, 3], and a validated monodromy loop on |tau| = 2.75
  returns to a disjoint enclosure, so R_c <= 2.75 and the series diverges at
  tau = 3. F6: for z = 5, T* = 0.02, two distinct equal-p/equal-mu pairs, each
  with a common tangent below beta f/V on all of 0 < rho* < 6/pi. These are
  computer-assisted proofs about the stated finite models (the BH residual of
  `msa_series_radius.py`, the closed second-order jet of
  `finite_order_two_tangents.py`). Finite-order sign measurements still do not
  verify the all-order sign hypothesis of F4.
- The proposed universal biconditional between positive real solution existence
  and Taylor convergence is not asserted. A real root or regular real branch
  does not control nearer complex singularities. The proved contrapositive
  concerns absence of **any real root** for the actual smooth root branch.

Integration was requested on 2026-10-22. The foundation is versioned as 1.0.14;
1.0.3 through 1.0.13 are preserved in their versioned release manifests.
The old workspace `Lean_code/formalization` compatibility symlink was removed;
use this package's `formalization/` directory.
Historical independent-check results are in `results/pre_integration_1_0_3/`;
current checks use only the package's normal Lake environment.

## Session ownership

The user instructed this Lean session not to write to `FMSA_dp_output/tex/`
(2026-10-22). Record proposed manuscript changes in
`FMSA_dp_output/md/FORMALIZATION_TODO.md` for the paper-writing session.
Do not run paper builds that generate files in `tex/`.
