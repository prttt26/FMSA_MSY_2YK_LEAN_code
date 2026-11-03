# Actual H-function node identification on an HS root germ

`PureFluidActualNodeGerm.lean` implements the local route suggested by
Claude's handoff 253. For fixed positive finite tail rates, the
explicit `actualWeight` is continuous in the original BH amplitudes.
The previously proved global partial fractions then make
`U_actual(z_t)` continuous in those amplitudes. At zero first
amplitudes, `actualU=1` for every second-amplitude seed value.
Consequently every continuous path through that HS seed has
`U_actual(z_t)≠0` for **all** tail nodes on one neighbourhood of zero
coupling. Finite tail indices let Lean choose a common neighbourhood.

For physical `0<xi<1`, the original BH factor at each node is also
continuous in the original amplitudes and equals the hard-sphere
`F0(xi,z_t)>1` at zero first amplitudes. Thus its positive-node values
are simultaneously nonzero on another common neighbourhood.

The main theorem,
`actual_candidate_identification_eventually_on_seed_root_germ`,
combines these two eventually nonzero facts with the actual-root node
weight identification from commit `4811dbd`. Given a **continuous
two-sided root germ** of the original pure-fluid `MultiTail.IsRoot`
through the zero-tail seed, with positive rates that may coincide, Lean proves
that sufficiently near zero the actual weights and actual node ratios
solve the paper's finite `r` system. The actual factor then equals the
candidate finite H-function dressing at every real frequency away
from zero and the finite negative tail poles.

The same module now constructs the smooth pure-fluid root germ from
physical `0<xi<1` data by reusing the frozen
`MultiTail.exists_contDiffAt_root` theorem. The companion
`PureFluidActualAnalyticGerm` module proves that this root germ is
analytic at zero, so the local candidate identification is data-level.
The removal of rate injectivity uses the later
`PureFluidActualPerTailWeights` identities.
Local nonvanishing still does not imply global
nonvanishing on an arbitrary canonical branch. The local theorem does
not establish formal-series coefficient positivity or radius equality.

All seven declarations have exact standard-three axiom guards. Complete
validation: `PYTHONDONTWRITEBYTECODE=1 python3 scripts/check_project.py -j 4`.
The frozen foundation remains version 1.0.17; its direct import is
source/artifact pinned in `cached-foundation-imports.json`. No TeX was edited.
