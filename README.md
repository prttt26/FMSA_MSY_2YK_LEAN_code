# MSA_and_1st_Truncation

Stable Lean 4 foundation for Exact MSA and its first coupling truncation
(FMSA), including shared hard-sphere, OZ, Baxter, transform and approximation
infrastructure. The original `LeanCode.*` module names and `FMSA.*` declaration
names are retained.

```bash
lake build
```

The default entry `MSA_and_1st_Truncation.lean` imports `LeanCode.lean` and
the paper theorem collection `FMSAPaper.lean`. It does not import any downstream
project. The package
requires only the pinned Mathlib dependency; the Lean toolchain is v4.31.0.
`release-manifest.json` records the validated source/configuration baseline.
Downstream projects lock its version and manifest digest. A foundation
change requires a deliberate new baseline and downstream revalidation.

## Standalone checkout

This directory is the published repository root. `lakefile.toml` sets
`packagesDir = "../.lake/packages"` so that sibling projects in the authors'
workspace share one Mathlib checkout; in a fresh clone, Lake therefore places
the dependencies in a `.lake/` directory next to the clone. Clone into an
otherwise empty parent directory, then run

```bash
lake exe cache get
lake build
python3 formalization/check.py
```

Memory: `LeanCode/YukawaOZ/ExactMSASparseDt2.lean` peaks at about 21 GB RSS and
`LeanCode/HSMixture/MixtureChordFamily.lean` at about 8 GB (measured 2026-10-22), so a
full build needs roughly 24 GB of RAM plus swap, or building that module on its own
first (`lake build LeanCode.YukawaOZ.ExactMSASparseDt2`). The CI workflow adds swap
for this reason.

`formalization/audit_foundation.py` checks the source/configuration hashes
against `release-manifest.json` without any other repository.

## Numerical scripts and evidence

`scripts/` holds the numerical and SymPy checks behind the foundation's theorems
(exact MSA, multitail, finite-order thresholds), and `results/` holds their recorded
outputs and build/axiom-audit logs (moved from the authors' workspace on 2026-10-22).
They are evidence, not proof premises. Some scripts import Python modules from the
authors' parent research repository (via `parents[3]` on `sys.path`), so they run only
in that workspace. Lean audit inputs inside `results/` are stored as `*.lean.txt` so
that they are not part of the hashed source set; copy one to a `.lean` file to run it
with `lake env lean`.

## Proof notes

`proof_notes/` holds the per-group proof records for the foundation (hard
spheres, OZ/Baxter/pole/OZFIX, contact value, Yukawa DCF and Wiener-Hopf,
mixture DCF/RDF, breakpoints, exact MSA and its Blum-Hoye derivation, free
energy, documented failures), and `proof_notes/MATH_AXIOMS.md`, the registry of
general-purpose mathematical axioms and their retirement history (its live-axiom
inventory is dated; the current per-theorem footprints are the `#guard_msgs`
gates). The closure notes (PYE/HNCB/FOEQ/MSAFAM) live in
the separate `Other_Closures` project. Task status for every group, the
re-derived axiom ledger and the open items are in `TODO.md` (it replaces the
`todo_lean.md` and per-track task files that the notes still mention by name).

## 1.0.13: single-tail zero mode strictly before the fold

The paper collection has 58 modules and 385 exact standard-axiom guards.
`SingleTailSpinodal.AS_fold_neg` proves that the actual scalar A is negative
at the quartic fold for every positive rate, density and diameter with
positive free volume. `actual_single_tail_zero_before_fold` constructs an
actual PY-branch BH root with A=0 at a strictly positive coupling below the
fold. `actual_single_tail_zero_lt_radius` places that witness strictly inside
the common Taylor radius of every continuous PY-seeded actual root germ.
This completes the all-state single attractive-tail zero-before-fold result;
it does not identify the first mode or prove RDF positivity.

The separate two-tail control now has certified local contact, zero-mode
firstness, all real-wave-number exclusion and an analytic disk of radius
5.614 extending beyond its first instability. These are interval and paper
complex-analysis certificates, not Lean theorems. See the two Codex notes
under `proof_notes/` for exact scopes and reproduction commands.

## 1.0.12: convergence on the initial stable interval

The paper collection reached 57 modules and 371 exact standard-axiom guards.
`StableIntervalRadius.analytic_branch_converges_before_iff` proves that all
amplitude-component Taylor series sum to an analytic selected branch at every
nonnegative coupling below an extended endpoint b exactly when b does not
exceed the common radius. Equality is allowed; b may be infinite.
`actual_regular_branch_converges_before_iff` supplies the actual BH interface
from continuity, roots and invertible amplitude Jacobians, with no coefficient
sign or fold hypothesis. `nonconvergence_witness_before` gives a divergent
coupling inside any interval extending past the common radius.

The physical identification b = tau_inst and the implication from canonical
physical states to BH Jacobian regularity remain separate mathematical
obligations. This does not certify a tail-parameter region. The independent
M2 zero-mode algebra is recorded in `proof_notes/codex_two_tail_reduction_audit.md`
and the reproducible symbolic script `scripts/coupling_singularities/codex_zero_mode_stationarity.py`.

## 1.0.11: the single-tail fold binds, unconditionally

The paper collection reached 56 modules and 361 exact standard-axiom guards.
`SingleTailRadius.single_tail_radius_eq_fold`: for one hard-sphere species and
one attractive Yukawa tail (any rate, diameter and density with positive free
volume), every continuous PY-seeded exact-MSA root germ has common Taylor radius
equal to the explicit fold coupling, and `single_tail_coefficients_nonneg` shows
all positive-order coefficients of both amplitude components are nonnegative.
This discharges, for one tail, the all-order sign hypothesis that F4 assumes.
Proof route:

- `SingleTailParametrization` reduces the actual BH system exactly to
  `τ = -Λ u² (u - a)(u - b)`, with `a = -P < b < 0` and `P` the first-order denominator.
- `QuarticBranch` builds the inverse branch and proves that it cannot be continued
  analytically through the fold.
- `AbsolutelyMonotone` uses Faà di Bruno to show that all derivatives of the branch
  are nonnegative.
- `SingleTailExpBounds` proves the exponential inequalities behind `a < b < 0`.

Several tails are not covered; competing tails can bind at complex branch points
(F5).

## 1.0.10: the weak identity at every coupling order (F1 complete in Lean)

The paper collection now has 51 modules and 258 exact standard-axiom guards.
`FiniteIntegralJets`, `BaxterWeakJetBasis`, `BaxterSecondIntegralJets` and
`RadialIntegralJets` prove that coupling jets commute with integration against
compactly supported tests, for the full reflected primitive, the second-factor
numerator and r times the ordered radial DCF: each integrand is a fixed finite
integrable dictionary with smooth amplitude coefficients, so no
derivative-under-integral premise is used. `BaxterWeakCauchy.fullPrimitive_weak_cauchy`
gives every coefficient of the full reflected weak identity for any smooth
amplitude curve, with the convolution term as an explicit Cauchy sum including
its lower-edge product and both linear Dirac coefficients retained.
`ActualRadialWeakJets.normalized_local_root_weak_cauchy` specializes this to an
actual local symmetric-strength MSA root branch with nonzero free volume, every
species pair, tests compactly supported in the positive radial axis, in the
paper normalization q = Q/(2*pi). This closes the last Lean obligation of F1;
F5/F6 numerical certificates remain open. Downstream builds were not re-run for
this baseline: the change is confined to leaf `FMSAPaper` modules that no
downstream project imports.

## 1.0.9: full reflected weak identity and actual radial identification

The paper collection now has 44 modules and 221 exact standard-axiom guards.
`BaxterWeakPrimitive.fullPrimitive_weak_derivative` proves the full-line
reflected identity for arbitrary amplitudes and compact C1 tests, retaining
both linear lower-edge Dirac contributions and the second-factor convolution
atom. `ActualRadialWeak.root_second_weak` identifies it with the actual radial
DCF for every species pair at a symmetric-strength MSA root, for tests compactly
supported in the positive radial axis. Positive rates, nonnegative diameters
and nonzero free volume are explicit. The assembly of this complete weak
identity through coupling jets, including integral/jet interchange, remains
open, as do the F5/F6 numerical certificates.

## 1.0.8: second-factor Cauchy formula and actual lower-edge atoms

The paper collection reached 41 modules and 210 exact standard-axiom guards.
`BaxterIntegrationByParts` proves whole-line integration by parts with both
lower-edge atoms. `BaxterSecondDerivative` differentiates the full reflected
primitive through the second factor away from the edges and identifies it with
the existing Baxter primitive. `ActualBaxterSecondJets` proves the normalized
ordered DCF Cauchy formula at every coupling order, including the explicit
lower-edge product. `BaxterWeakDerivative` proves the actual factor's weak
derivative and its Dirac coefficient against compact C1 test functions.
The full reflected weak identity and all-species positive-radial identification
were completed in 1.0.9; coupling-jet assembly and F5/F6 remain open.

## 1.0.7: actual analytic branches and conditional fold equality

The paper collection reached 37 modules and 192 exact standard-axiom guards.
`ActualAnalyticBranch` uses the real analytic implicit-function theorem to
prove regular actual MSA branches analytic. `AnalyticTaylor` identifies the
canonical Taylor sums and their positive radii. `ActualAnalyticTaylor` proves
a positive common radius for the physical PY seed, convergence to the actual
branch before a regular endpoint under all-order component signs, and equality
of that radius with a transverse fold under the explicit fold hypotheses.
No extra analyticity, radius or Pringsheim premise remains. The model-specific
all-order sign hypothesis and convergence exactly at the fold remain separate.

## 1.0.6: scalar Pringsheim without additional axioms

The paper collection reached 34 modules and 173 exact standard-axiom guards.
`NonnegativeRecenter` supplies the positive-series regrouping argument;
`Pringsheim` proves the finite-positive-radius endpoint obstruction;
`SignedPringsheim` removes the constant term, permits either coefficient sign,
and proves a radius lower bound from consistent positive-axis analytic
continuation. The actual-MSA analytic interfaces were completed in 1.0.7;
the model's all-order sign condition remains an explicit hypothesis.

## 1.0.5: actual DCF normalization and Fourier identification

The paper collection reached 31 modules and 162 exact standard-axiom guards.
`BaxterNormalization` assembles the actual DCF Cauchy sum in the paper's
q = Q/(2*pi) convention and proves normalized primitive derivatives and shell
identities. `ActualRadialIdentification` connects the ordered radial DCF to the
actual spectral Baxter coefficient, deriving core reciprocity from an actual
symmetric-strength root with nonzero free volume. No additional small-kernel
budget is required for this Fourier identity. The full reflected distributional
Cauchy formula remains open; manuscript changes are handed off through Markdown.

## 1.0.4: integrated FMSA paper proofs

At the user's request on 2026-10-22, the 29 paper modules and their 151 exact
standard-axiom gates were moved into `FMSAPaper/` and included in the default
build. The public module and theorem names are preserved. The former independent
validation records and the 1.0.3 release manifest are archived; no separate Git
repository or additional Lake package was created for these proofs.

Run `python3 formalization/check.py` for the default-build and footprint audit.
See [the paper scope ledger](formalization/README.md) for proved statements and
remaining obligations. In particular, F2 retains explicit fold hypotheses, F3
does not prove the converse, and F1's full distributional correspondence and
F5/F6 numerical certificates remain open. F4 is proved under explicit fold and
all-order sign hypotheses; manuscript citation is handed off in the Markdown backlog. Integration
does not turn those remaining obligations into proved claims.

## Completed scope and assumptions

The arbitrary finite-mixture/tail automatic Wronskian construction and
actual structural closure on the explicit analytic budget domain are
proved. Repeated positive rates, unequal diameters and zero-density species
are included where stated. The four former single-tail matrix closure/HS
Fourier axioms are proved theorems with the original formulas, at supplied
roots on their explicit physical domain. See the retained records in
`../proof_notes_msa_exact.md` and `../results/multitail_extension/`.

“Completed” refers to this recorded scope. It does not establish global
root existence, all-state decay, g>=0, thermodynamic route consistency,
physical Maxwell/binodal accuracy or SCOZA.

`LeanCode/FMSAProject.lean` retains the historical FMSA paper gate, including
three results with five extra assumptions across their dependency union.
Those conditional contour/contact/no-spinodal results are preserved and
remain explicitly labelled; retiring the four matrix axioms does not
retire unrelated assumptions. Exact MSA and new multitail results retain
their existing standard-axiom gates.

## Shared first-order interface

`LeanCode/Closures/ClosureExpansions.lean` provides shared coupling calculus,
MSA first order and the minimal PY first-order comparison cited by FMSA.
`LeanCode/Closures/DPClosureMap.lean` supplies the generic DP linear map,
error estimates, radial injectivity, Yukawa approximation and conditional
WH continuity. Existing finite-order jet algebra and formula-specific
anomaly certificates are retained as auxiliary comparison tools; they do
not establish a universal anomaly threshold. Its PY application and HNCB pull-back results now live in
Other_Closures. FirstOrderEquivalence, MSASolutionFamily and MSAFamilyConcrete
stay here because they connect Exact MSA to its first truncation.

## 1.0.1：高阶 B 层级与有限阶空间表示

2026-10-12 按用户授权补入
[`MSABHierarchy.lean`](LeanCode/YukawaOZMix/MSABHierarchy.lean)，默认 Exact-MSA
入口导入该模块。新增 11 条定理均有标准公理足迹门控，既有物理定义、
证明和旧门控未改动。原 `1.0.0` 清单归档为 `release-manifest-1.0.0.json`；
当前补丁版本经过基础、两个下游及工作区重建后重新封存。

使用归一化 Taylor 系数（导数除以阶乘），设

```text
T0=I-C0, S0=I+H0, T0*S0=I,
R_n = sum_(j=1..n-1) H_j C_(n-j),
H_n T0 = S0 C_n + R_n,
T0=Q_plus Q_minus^T, T0^T=T0.
```

原始 `B_n=Q_plus^T H_n Q_plus` 给出

```text
C_n = Q_minus B_n Q_minus^T - T0 R_n.
```

定义修正层级
`B_eff_n=Q_plus^T (H_n-R_n S0) Q_plus`，则每阶恢复
`C_n=Q_minus B_eff_n Q_minus^T`。一阶 `R_1=0`，二阶
`R_2=H_1 C_1`。新定理保留混合物矩阵乘法的顺序。
这里的 B 是与 Fourier OZ 系数一致的矩阵层级；不能直接把它与尚未
识别的单边 Laplace WH 分子混用。

B 形式本身不证明有限空间闭式：原始 B 和低阶 H 的硬球谱分母需要在
完整 DCF 中处理。另一条定理链直接沿用既有固定空间基底导数等式：
若某个固定几何分片上的实际 DCF 已表示为
`c(K,r)=sum_l a_l(K) phi_l(r)`，且系数具有所需有限阶光滑性，则

```text
c_n(r) = sum_l [a_l^(n)(K0)/n!] phi_l(r),
c_<=L(tau,r) = sum_l phi_l(r) sum_(n=0..L) [a_l^(n)(K0)/n!] tau^n.
```

因此每阶与严格有限阶截断保留同一有限空间表示，不要求无限耦合级数
收敛。闭式基底、真实物理系数的识别以及系数递推的正则性仍由其对应
物理定理提供。新模块没有自动构造任意阶修正 B 的 WH 投影，也没有
把“写成有限空间基底”提升为“所有物理参数下都有正则系数”或统一精度保证。

## Finite-order source hierarchy (foundation 1.0.3)

`LeanCode/MSABSourceProject.lean` guards 82 new standard-axiom theorems.
The actual scalar single-tail corrected one-sided source is a single Yukawa
term at every finite order. The actual finite-tail mixture excess-renewal
source has an evaluated, order-independent piecewise polynomial/Yukawa
dictionary for unequal additive diameters and repeated positive rates.
Actual BH-root coefficients are constructed by the two physical HS seed
block solves at every order, including zero-density species.

Fourier-OZ B is a different object: a reflected HS zero with nonzero DCF
obstructs its membership in the prescribed finite Yukawa source class.
The actual RDF reconstruction retains the HS propagator and lower-order
terms. Automatic actual-root admissibility discharges the algebraic radial
OZ certificates on the established analytic-budget domain; this does not
prove global decay, physical phase accuracy or g>=0.
See `../results/msa_b_hierarchy_physical/validation.json` and the paper
handoff in `../../FMSA_dp_output/md/lean_b_hierarchy_proof_handoff.md`.
