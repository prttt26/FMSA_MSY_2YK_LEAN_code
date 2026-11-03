# Two-tail convergence numerics (Claude)

Float64 numerics for the convergence set of one component with a mixed-sign two-Yukawa tail,
`K = (1, w)` at rates `z = (z1, z2)`, `z2 > z1`. The amplitude is `f = w/w0`, with
`w0 = −(1/z1 + 1/z1²)/(1/z2 + 1/z2²)`. A state passes when `R_c ≥ τ_inst`. This is evidence,
not proof. The write-up is `proof_notes/claude_two_tail_convergence.md`.

## Provenance

These scripts were developed and run in the foundation tree
(`../MSA_and_1st_Truncation/scripts/coupling_singularities/`) on 2026-10-23–26. They were moved
here unchanged when the foundation was frozen at 1.0.17, and the foundation copies were reverted
to 06e3268. Only the `sys.path` setup and the default output directory (`results/two_tail/`)
differ.

The result headers record the command as it was run, so the earlier ones carry foundation-tree
paths. After the move, the Codex control point (handoff 011) and the LJ cell
`η = 0.49, f = 0.1953125` reproduced digit for digit from this directory.

Foundation modules (`msa_coupling_series_sign_probe`, `family_crossing`,
`msa_instability_before_fold_check`, and through them `msa_exact_mix`) are imported read-only.
`nearest.py` here **shadows** the foundation's `nearest.py`, because it is first on `sys.path`.
It is a superset: the new keywords `res_rel='hadamard'` and `sheet_retry` default to the old
behaviour.

## Files

| script | output in `results/two_tail/` | what |
|---|---|---|
| `nearest.py` | — | nearest physical-sheet singularity. Adds a Hadamard-relative fold residual and the sheet-test retry for near-real complex folds (handoff 015) |
| `two_tail_margin.py` | — | one state: `R_c` first, then trace to `min(lam_max, 1.02 R_c)`. Status is `crossing_bracket` / `no_crossing_up_to_cap` / `trace_stalled` / `R_unresolved`. Since 2026-10-27, when a real fold binds with margin in `[0, 1e-3)`, `R_c` is the smallest `|τ*|` over 8 Padé scales (`n_scales` in the result); the scan JSONs predate this |
| `two_tail_scan.py` | `two_tail_scan_free_z1.*`, `two_tail_scan_z1_1.8.*`, `two_tail_scan_z1_2.9637.*` | evaluates a 14-point `f` grid per `(z1, z2, η)` cell, counts sign changes, then bisects to `Δf < 2e-3` |
| `two_tail_m2_locate.py` | `two_tail_m2_locate.jsonl` | 10-equation Newton solve for the zero-mode touch `(f_M2, τ_touch)`. `--control` reproduces handoff 011 |
| `two_tail_m2_batch.py` | `m2_free_z1_eta0.49.*` | the locator seeded at each cell's outer bracket point |
| `two_tail_m2_fine.py` | `two_tail_m2_fine*.log` | fine `f` resolution inside a bracket: margin, `τ_f`, `min det F(0)` along the branch |
| `two_tail_classify.py` | `two_tail_classify_free_z1.*`, `two_tail_classify_below_eta0.4{7,9}.*` | per cell, 9 points across the scan bracket, typed `R` / `C+` / `F1` / `Fc` / `Finf` / `U`; the (last pass, first fail) pair gives M1 / M2 / M3, refined up to 3 levels; M2 vs M3 by the touch locator. `--below D` searches `[lo − D, lo]`. The 76-cell run predates the multi-scale `margin` |
| `two_tail_recheck_real.py` | `two_tail_recheck_real_free_z1.log`, `two_tail_recheck_complex_free_z1.*` | redoes every pass of a classify JSON at 8 Padé scales and flags those with a singularity inside `τ_inst`. The `R` run's JSON write failed (numpy bool, since fixed); its log has every row and is the record |
| `two_tail_classify_correct.py` | `two_tail_classify_corrected_free_z1.*` | applies the recheck flags to the classify JSON, recomputes brackets and verdicts, and substitutes the `--below` runs (read-only on its inputs) |
| `two_tail_recheck_lo.py` | `two_tail_recheck_lo_slices.*` | redoes the pass end `lo` of every scan bracket at 8 Padé scales; a bracket stands iff `lo` is not flagged (the defect only creates false passes). 2026-10-28: 0 of 79 slice cells flagged |
| `two_tail_fiber_diag.py`, `two_tail_fiber_m1_endgame.py` | `two_tail_fiber_diag.{json,log}`, `two_tail_fiber_m1_endgame.log` | FLOAT diagnostics of the endpoint fiber {BH roots at τ = β} for three controls (handoff 134/136): the literal Lean N = 1 two-tail residual (4 cubics, checked against `msa_exact_mix._residuals`), a total-degree homotopy (81 paths), Jacobian singular values, and a 40-digit endgame for the M1 control. Not a finiteness/isolation certificate |
| `two_tail_m2_jacobian_interval.py` | `two_tail_m2_jacobian_interval{,_widened}.{json,log}` | EXTERNAL interval certificate (mpmath iv, 192 bits; handoff 137/138): uniform invertibility of the BH amplitude Jacobian over the amplitude part of Codex's certified M2 root box (read-only, sha256 recorded); AD of the literal Lean residual in interval arithmetic, exact dyadic C, `‖I − C J(box)‖∞ ≤ 3.5e-8`. Not a Lean proof |
| `two_tail_endpoint_interval.py` | `two_tail_endpoint_interval_exact.{json,log}` (authoritative: every endpoint an exact rational, full parametric witness, exact inclusion checks; handoff 142); `two_tail_endpoint_interval.{json,log}` (handoff 140, decimal-rounded serialization, superseded) | EXTERNAL interval certificates at the M1 / M3 controls (handoff 140): Krawczyk root boxes with uniform Jacobian invertibility at exact couplings, rigorous `det F(0)` signs (the float bisection brackets were wrong at both), rigorous sign-change brackets, and for M3 one parametric box over the whole bracket. M1's single-branch claim is not certified (near-fold sensitivity) |
| `two_tail_m1_fold_branch.py`, `check_m1_fold_branch_rational.py` | `two_tail_m1_fold_branch.{json,log}`, `check_m1_fold_branch_rational.log` | EXTERNAL interval certificate (handoff 144): the two M1 endpoint roots lie on one continuous real BH branch, parametrised by `Dt_1` with `τ` an unknown (4 chained mean-value Krawczyk slabs); `det F(0)` changes sign along it. The stdlib checker recomputes the rational part |
| `two_tail_m2_second_root.py`, `check_m2_second_root_rational.py`, `two_tail_m2_branch_explore.py` | `two_tail_m2_second_root.{json,log}`, `check_m2_second_root_rational.log`, `two_tail_m2_branch_explore.log` | EXTERNAL interval certificate (handoff 145): M2's second real root is a separate regular root, disjoint from Codex's box; the local branches through the two roots are disjoint over a τ window (τ in mean-value form); with Codex 009/011 it is not on the PY-seeded branch. Stdlib rational re-check. The arclength continuation is FLOAT evidence for where that branch goes |
| `two_tail_m3_arb_recheck.py`, `check_m3_arb_recheck_rational.py` | `two_tail_m3_arb_recheck.{json,log}`, `check_m3_arb_recheck_rational.log` | EXTERNAL Arb re-check (handoff 147) of the M3 certificate's analytic part. It uses a SymPy transcription of the Lean residual polynomials, exact derivatives and centered Taylor forms in python-flint (run with `PYTHONPATH=/tmp/codex_fmsa_arb_deps`), and imports no other two_tail script. All six stored M3 Krawczyk witnesses hold. Tiny endpoint boxes sit inside the parametric box with A signs + / −. Stdlib rational re-check included |
| `two_tail_py_chain.py`, `check_py_chain_rational.py` | `two_tail_py_chain_{M1,M3}.{json.gz,log}`, `check_py_chain_rational_{M1,M3}.log` | EXTERNAL Arb certificate (handoff 157). Starting from the exact HS seed at τ = 0, chained parametrised Krawczyk slabs (τ as parameter; for M1, Dt1 as parameter after τ = 9.5, with dτ/dp > 0) carry one regular root curve to τ_hi. A > 0 holds up to τ_lo and A < 0 at τ_hi, so the first det F(0) zero on the PY-seeded branch lies in the rigorous bracket. Stdlib rational re-check included |
| `two_tail_first_loss.py`, `check_first_loss_rational.py` | `two_tail_first_loss_{M1,M3}.{json.gz,log}`, `check_first_loss_rational_{M1,M3}.log` | EXTERNAL Arb certificate (handoff 167). On every chain slab box covering [0, τ_lo] and for every real k, the scalar physical Fourier factor F(u, k) = 1 − ρ∫q e^{−ikr} is nonzero. Finite k uses a second-order march; large k uses an analytic tail bound; k = 0 uses F = A/2π. With the Lean `canonical_path_of_physical_factor_units` and `actual_scalar_hs_canonical`, the PY-seeded branch is fully canonical on [0, τ_lo], so the first loss lies in (τ_lo, τ_hi). Stdlib rational re-check included |
| `two_tail_tables.py` | — | prints the proof note's tables: free `z1` from the corrected classify JSON (with mechanism and pattern checks), slices from the scan JSONs (read-only) |
| `single_tail_sweep.py` | `single_tail_sweep.log` | 42 single-tail states: `det F(0)` changes sign strictly before the fold (numeric check of 1.0.13) |


### Coefficient signs (2026-10-31; proof note section *Coefficient signs: final status*)

| Script | Output | What it does |
|---|---|---|
| `mixture_sign_flip_mp.py` | `mixture_sign_flip_mp.log` | EXTERNAL mp: binary residual port; order 1 and 2 coefficients of opposite sign |
| `attractive_pair_series_mp.py` | `attractive_pair_series_mp_{1,2,3}.log` | EXTERNAL mp: exact Cauchy recursion for the cubic residual, no root tracking; sign changes, radius from the coefficients, partial sums |
| `indefinite_binary_check.py` | `indefinite_binary_check.log` | entrywise-positive indefinite binaries: `τ_f`, `τ_inst`, `τ_neg`, coefficient radius |
| `indefinite_binary_mp.py` | `indefinite_binary_mp.log` | EXTERNAL mp: divergence at canonical states for `K = [[1/20,1],[1,1/20]]` |
| `indefinite_mode_check.py` | `indefinite_mode_check.log` | which channel carries each fold of the symmetric state |
| `attractive_high_order_survey.py` | `attractive_high_order_survey_seed1.log`, `attractive_high_order_survey_ternary_seed1.log` (`--ternary`), `attractive_high_order_survey_quaternary_seed1.log` (`--quaternary`) | order 150 against the arclength fold: pure, PSD and indefinite binaries; PSD with N = 3, 4 |
| `psd_late_flip_mp.py` | `psd_late_flip_mp.log` | EXTERNAL mp: the late sign change of a PSD binary is real |
| `attractive_real_branch.py` | `attractive_real_branch.log` | pseudo-arclength real branch; use `first_fold` rather than the end of `trace_coupling_mix`, which can jump a fold |
| `attractive_branch_points.py` | `attractive_branch_points.log` | augmented Newton for complex branch points |
| `attractive_pair_ratio.py` | `attractive_pair_ratio.log` | minimises `|τ*|/τ_f` by warm-started tracking; superseded: its one-radius sheet test let in the ratios below 1 in the log |
| `attractive_pair_fast.py` | `attractive_pair_fast.log`, `attractive_pair_fast_retest.log`; `attractive_pair_fast_two_radii.log` is from its first, two-radius test, whose hits are false | global search on the explicit cubic: first fold, turning-point count, branch points from nothing, four-radius square-root sheet test |
| `attractive_sign_margin.py`, `attractive_margin_mp.py` | `attractive_sign_margin.log`, `attractive_margin_mp_{1,2}.log` | search on the dip depth of the coefficients; EXTERNAL mp decider, which shows the negative values at rates near 0.05 are float artifacts |
| `normal_form_sign.py`, `attractive_normal_form_check.py` | `normal_form_sign.log`, `attractive_normal_form_check.log` | near-tie form `y² + a y + β/y`: `Lam` against `a`, sign of the scaling function, comparison with coefficients; measured `Lam`, amplitudes, phases |
| `attractive_lam_bound.py` | `attractive_lam_bound.log` | direct search for `ln ρ/θ < √3` |
| `attractive_tie_limit.py` | `attractive_tie_limit_{control,control3,search,strong2,strong3,strong2_random,signs}.log` | closed-form first correction to `√3` as the weak tail vanishes; controls against exact branch points; sign of `a` with one to three strong tails |
| `multivariate_sign_test.py`, `multivariate_sign_mp.py` | `multivariate_sign_test_{T2_o12,T2_o24,T3_o12}.log`, `multivariate_sign_mp_T2.log` | sign of every mixed Taylor coefficient in `(τ₁, …, τ_T)`: float cubic recursion; EXTERNAL mp Picard recursion, no cut |
| `shifted_affine_signs.py`, `shifted_affine_closed_form.py` | `shifted_affine_signs.log`, `shifted_affine_closed_form.log` | blocks of the affine system in `(D, D(G − G₀))`: `FD, FP ≤ 0`, `SD` in closed form, `SP < 0`; EXTERNAL 60-digit check |
| `invariant_cone.py` | `invariant_cone_T2.log` | smallest cone invariant under the Taylor recursion; escapes the orthant |
| `h_function_algebra.py` | `h_function_algebra.log` | exact computer algebra for the steps of the pure-fluid positivity proof, valid for every T |
| `h_function_representation.py` | `h_function_representation.log` | EXTERNAL 60 digits: the H-function form against the BH factors, T = 1…5, the two integrals, signs in `θ`, `κ > 0` |
| `h_positivity_algebraic.py` | `h_positivity_algebraic.log` | EXTERNAL 50 digits: coefficients of `H` and `r` in `θ` against the Picard form and the squared-norm Cauchy form |
| `lambda_parametrization.py` | `lambda_parametrization_check.log`, `lambda_parametrization_signs_T2.log` | explicit rational parametrization of the branch in `Λ`; coefficients in `Λ` alternate |
| `d_variable_signs.py` | `d_variable_signs_T{1,2,3}.log` | `F0 − F` and `G − G0` as series in `D` alone: the first is nonnegative in the samples, the second is not |
| `symmetric_binary_theorem_check.py` | `symmetric_binary_theorem_check.log` | mode formulas of exchange-symmetric binaries against the mixture solver; closed-form folds of the indefinite example |
| `covariance_route_check.py` | `covariance_route_check.log` | Codex's covariance route (handoff 200) on actual roots, with canonicity loss as the control |
| `matrix_h_function_check.py` | `matrix_h_function_check.log` | the matrix H-function form against actual mixture roots, N = 2–4, T = 1–3 |
| `mixture_loewner_test.py` | `mixture_loewner_test.log` | Loewner order of the coefficient matrices of `G_t` (false), and the sign of the excess-energy series |
| `mixture_energy_attack.py`, `mixture_energy_search.py`, `mixture_energy_fast.py`, `mixture_energy_mp.py`, `energy_negative_state.py` | `mixture_energy_{attack,search,fast,mp}.log`, `energy_negative_state.log` | positivity of the excess-energy coefficients: constructed attack, slow and tensor searches, EXTERNAL mp decider (negative coefficients are real), the negative window at high order |
| `mixture_pair_search.py` | `mixture_pair_search.log` (weak: few pairs), `mixture_pair_search_seeded.log` (`--seeded`) | principal-sheet branch points of mixtures on the tensor recursion, objective smallest `ln ρ/θ`; finds pairs inside the fold |
| `mixture_below_one_check.py`, `psd_counterexample_float.py`, `psd_counterexample_mp.py` | `mixture_below_one_check.log`, `psd_counterexample_float.log`, `psd_counterexample_mp.log` | the binary with `K_t` PSD and `R < τ_f`: coefficients and fine trace; rounding, `τ_inst`; EXTERNAL mp with exact rational input |
| `matrix_h_function_algebra.py` | `matrix_h_function_algebra.log` | EXTERNAL exact rationals, N ≤ 4: constraints of the matrix form, symplectic hard-sphere matrix |
| `t1_rank_one_check.py` | `t1_rank_one_check.log` | `κ̃ ⪰ 0`, the inner function `Ξ`, the scalar closure for T = 1, rank one |
| `mixture_special_search.py` | `mixture_special_search.log` | one direction with T ≥ 2, and T = 1 with rank 2: pairs and `ln ρ/θ` |
| `canonical_disk_test.py`, `mixture_disk_search.py` | `canonical_disk_test.log`, `mixture_disk_search.log` | canonicity on `|τ| < τ_inst` and at branch points; wider sample **INVALID at complex tau: windings went through the float64 `_pieces`; see `disk_winding_redo.log`.** |
| `mixture_inst_search.py`, `mixture_inst_descent.py` | `mixture_inst_search.log`, `mixture_inst_descent.log` | search for `R < τ_inst` with `K_t` PSD: none found |
| `stieltjes_logconvex_test.py` | `stieltjes_logconvex_test.log` | log-convexity and Hankel tests of the Stieltjes picture |
| `uhp_monodromy_test.py`, `uhp_monodromy_survey.py` | `uhp_monodromy_test.log`, `uhp_monodromy_survey_{loose,strict}.log` | closed-loop monodromy, with M3 as a control |
| `herglotz_test.py`, `herglotz_identity.py`, `herglotz_gram_check.py` | `herglotz_identity.log`, `herglotz_gram_check.log` | Herglotz identity, Gram matrix, closed form at τ = 0; the ray test `herglotz_test.py` has no discrimination |
| `sign_cone_test.py`, `sign_cone_search.py` | `sign_cone_test.log`, `sign_cone_search.log` | orthant cone and linear positive forms |
| `affine_factor_signs.py` | `affine_factor_signs.log` | coefficient signs in the affine variables (D, P) |
| `symmetric_binary_mode_signs.py` | `symmetric_binary_mode_signs.log` | mode series of symmetric binaries |
| `pure_sign_adversarial.py` | `pure_sign_adversarial.log` | adversarial search on the smallest coefficient margin |
| `matrix_r_positivity.py` | `matrix_r_positivity.log` | matrix H and r: no negative entry on entrywise nonnegative PSD theta |
| `matrix_r_integral.py` | `matrix_r_integral.log` | matrix r~ as an integral of powers of theta(k) |
| `frustration_criterion_test.py` | `frustration_criterion_test.log` | sign-frustration criterion against logged Lam < sqrt 3 states, random states, one direction |
| `frustration_base_rate.py` | `frustration_base_rate.log` | base rate of that criterion on the seeded distribution |
| `equal_diameter_cross_sign.py` | `equal_diameter_check.log`, `equal_diameter_cross_sign.log` | equal diameters: same vs opposite sign of the density-concentration coupling; the first search of this script ran the opposite class for no state, fixed before this log |
| `equal_diameter_descent.py` | `equal_diameter_descent.log`, `equal_diameter_descent2.log` | descent on the ratio, opposite class; stops at 0.99989, unresolved |
| `equal_diameter_fold_recheck.py` | `equal_diameter_fold_recheck.log` | coefficient radius behind the opposite-class Lam readings |
| `counterexample_to_equal_diameter.py` | `counterexample_to_equal_diameter.log` | the certified counterexample followed in sigma_2 toward equal diameters |
| `equal_diameter_counterexample.py`, `equal_diameter_counterexample_mp.py`, `equal_diameter_control.py` | `equal_diameter_counterexample.log`, `equal_diameter_counterexample_rounded3.log`, `equal_diameter_counterexample_mp.log`, `equal_diameter_control.log` | R < tau_f at equal diameters: float to order 3000, EXTERNAL mp at exact rational input, and the control flipping one b_s |
| `t1_abstract_scan.py` | `t1_abstract_control.log`, `t1_abstract_scan.log` | T = 1 abstract equation, N = 2 |
| `t1_frustrated_scan.py` | `t1_frustrated_scan.log` | T = 1, N = 3, 4, frustrated and unfrustrated K0 |
| `t1_near_tie_scan.py` | `t1_near_tie_scan.log`, `t1_near_tie_scan_fixed.log` | T = 1 near ties by coefficient ratio; overstated by narrow turns, see the note's warning |
| `t1_branch_points.py` | `t1_branch_points.log`, `t1_branch_points_fixed.log`, `t1_branch_points_physical.log` | T = 1 direct branch points with ray test; first log used the older fold |
| `t1_branch_points_recheck.py`, `t1_hits_recheck.py`, `t1_candidate_check.py`, `t1_inside_recheck.py` | `t1_branch_points_recheck.log`, `t1_hits_recheck.log`, `t1_candidate_check.log`, `t1_candidate_check2.log`, `t1_inside_recheck.log`, `t1_gated_recheck.log` | coefficient and direct-solve checks of the hits; narrow real turns |
| `pitchfork_abstract.py`, `pitchfork_physical.py` | `pitchfork_abstract.log`, `pitchfork_physical.log` | pitchfork before the fold at zero coupling, and R discontinuous there; by the independent referee, kept as run |
| `r_weight_structure.py`, `r_weight_divided_difference.py` | `r_weight_structure.log`, `r_weight_divided_difference.log` | the multilinear weight of r as a divided difference of the square root, a real integral, and a Schur ratio; exact |
| `r_euler_identity.py` | `r_euler_identity.log` | r in terms of H alone, r(x) = E m0 - x E ln H(x); exact |
| `t1_cancellation_symbolic.py` | `t1_cancellation_symbolic.log` | exact expansion of the T = 1, N = 3 polynomial system near a pitchfork |
| `t1_cancellation_scan.py` | `t1_cancellation_scan.log` | scan of b_12; no pairs even in its control, so uninformative |
| `t1_inverse_design.py` | `t1_inverse_design.log`, `t1_inverse_design_seeded.log`, `t1_inverse_design_seeded2.log`, `t1_inverse_design_strict.log`, `t1_inverse_design_pitchfork.log` | K0 from a chosen p; only the pitchfork log is seeded correctly with the strict sheet test |
| `t1_descend_ratio.py`, `t1_descend_recheck.py`, `t1_hit_coefficients.py`, `t1_strict_sheet.py`, `t1_strict_recheck_lam.py` | `t1_descend_ratio.log`, `t1_descend_recheck.log`, `t1_hit_coefficients.log`, `t1_strict_sheet.log`, `t1_strict_recheck_lam.log` | following the shallow hit, which leaves the sheet; the strict sheet test and its recheck of older readings |
| `t1_tiny_pair.py` | `t1_tiny_pair.log` | pairs at the closed-form scale; design points not checked to be on the branch, so unresolved |
| `t1_b12_coefficient_scan.py` | `t1_b12_coefficient_scan.log` | scan of b_12 by coefficients only; no oscillation, no jump |
| `t1_descend_strict.py`, `t1_gradient_lam.py`, `normal_form_sheet.py` | `t1_descend_strict.log`, `t1_descend_strict_lam.log`, `t1_gradient_lam.log`, `t1_gradient_lam2.log`, `normal_form_sheet.log` | descent on the ratio and on Lam under the strict sheet test; the normal form keeps its pair on the sheet at all B |
| `complex_path_check.py`, `complex_pieces.py`, `disk_recheck.py`, `disk_winding_redo.py`, `disk_hit_check.py` | `complex_path_check.log`, `disk_recheck.log`, `disk_winding_redo.log`, `disk_hit_check.log` | `_pieces` drops imaginary parts, so windings at complex tau were invalid; redone, and canonicity on the disk is false at one rank-one state |
| `disk_sector_measure.py` | `disk_sector_measure.log` | INVALID, kept as a record: float64 path and wrong M_1 normalisation; use `disk_recheck.log` |
| `inst_search_deep.py` | `inst_search_deep.log` | search for R below tau_inst where the disk is deeply non-canonical; none found |
| `fictitious_tail_pole.py` | `fictitious_tail_pole.log` | pure fluid with a passive tail: the simple pole of G_1 before the fold, against closed form |
| `referee_checks/r1.py`, `r3.py`, `r4.py`, `r5.py`, `r6.py`, `r7.py` (`r2_run.py` helper) | `referee_r1.log`, `referee_r3.log`, `referee_r4.log`, `referee_r5.log`, `referee_r6.log`, `referee_r7.log` | the independent referee's checks of the T >= 2 turn, kept as run: exponent 1/3, bounds on r~ and H, tensor leakage, zero diagonal of K^, the pole against the fold in p |
| `t1_scurve_search.py` | `t1_scurve_search.log` | T = 1, N = 3, physical Xi, with S-curves as the target; stayed on a plateau, so uninformative |
| `t1_descent.py` | `t1_descent.log`, `t1_descent_gated.log`, `t1_descent_physical.log` | T = 1 descent on Lam, xi in [0, 1] vs [-1, 1], and at xi of actual hard-sphere states; only the gated and physical logs count resolved pairs only |

Set `OMP_NUM_THREADS=1` (and the OpenBLAS/MKL equivalents) in the launching shell.
