# Analytic original pure-fluid MSA root germ and local H dressing

`PureFluidActualAnalyticGerm.lean` proves the **original** finite-tail
pure-fluid Blum–Høye residual `MultiTail.residual` is real analytic in
coupling and all original amplitudes. The rational tail denominators
are fixed by the positive rates; the proof expands the genuine `W,C,M,N`
and factor definitions and uses analytic operations on finite sums.

The frozen `MultiTail.exists_contDiffAt_root` theorem already constructs
a smooth two-sided root germ through the hard-sphere state for every
`0<xi<1`, every finite family of positive rates, and every real signed
coupling direction. The research module checks that its residual
vanishes on a neighbourhood and that its amplitude Jacobian at the
seed is the frozen invertible triangular map. The existing analytic
implicit-function theorem then upgrades this **same root germ** to
`AnalyticAt ℝ p 0`. No independent or merely formal branch is used.

Combining that analytic germ with `PureFluidActualNodeGerm` yields a
data-level existence theorem for finite positive rates, including
coincident ones: near zero
coupling the actual node weights and node ratios satisfy the paper's
finite `r` linear system, and the **original** BH factor equals the
finite H-function candidate dressing for every real frequency away
from zero and the finite negative tail poles. The node `U` and factor
nonvanishing hypotheses are proved locally rather than supplied.

This is an analytic **germ** statement. It does not prove the H-function
weights positive, formal-series coefficient signs, global continuation,
or a Taylor-radius equality. The later
`PureFluidActualPerTailWeights` module supplies the individual
coincident-rate identities used by the strengthened data-level theorem.

Three declarations have exact standard-three axiom guards. Full
validation: `PYTHONDONTWRITEBYTECODE=1 python3 scripts/check_project.py -j 4`
passed with 1908 guards/207 research modules, foundation 1.0.17
unchanged. The newly used frozen `LeanCode.YukawaOZ.MSAMultiTailFamily`
source and pre-existing compiled artifact are individually SHA-256
pinned in `cached-foundation-imports.json`. No TeX was edited.
