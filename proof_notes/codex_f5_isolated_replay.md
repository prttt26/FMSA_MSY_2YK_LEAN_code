# F5 isolated replay: real regular MSA branch with a smaller Taylor radius

The frozen foundation's `formalization/certificates/f5_competing_tails.py` is
an **external interval certificate**, not a Lean instance. This research
package owns `scripts/certificates/replay_f5_isolated.py`, which SHA-pins the
frozen script, copies it to a temporary directory, executes it there and
preserves the raw JSON result and log under `results/certificates/`. The
foundation is read only throughout. The default command runs the eta=0.2
positive state and the eta=0.1 negative control:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 scripts/certificates/replay_f5_isolated.py
```

Use `--full` for all three positive states eta=0.2, 0.3 and 0.4 plus the
same negative control. A previously isolated run can be checked with
`--existing-run DIR`, where DIR has a byte-for-byte copy of the frozen
script, `run.log` and `results/f5_competing_tails.json`.

The quick positive state has one hard-sphere species at eta=0.2, diameter
one, rates z=(1.8,12), signed tail strengths (1,-6), and coupling tau in
[0,3]. The original F5 script obtains 168 linked real Krawczyk pieces,
with worst contraction 0.8657801767055928, and 7330 pieces on the complex
loop of radius 2.75, with worst contraction 0.9999090946047939. Its
start/end loop enclosures are disjoint. The wrapper independently recomputes
that box separation from the serialized rectangles and checks the exact
input, strict contraction values, branch and monodromy flags, source SHA,
and negative control. On the current machine, the entire eta=0.2 result and
negative control matched the frozen JSON field by field, excluding elapsed
time. The receipt records hashes for the raw result and log.

The certified conclusion is a PY-seeded **real regular root branch** on
[0,3] while monodromy bounds its Taylor radius by 2.75, so its coupling
series diverges at 3. It refutes universal *real-root existence implies
Taylor convergence*. The amplitude components in this signed-tail example
are not all positive, and the certificate does not assert full physical
canonicity on [0,3]. The stronger canonical-state counterexample M3 is
tracked separately. Replaying the same interval implementation checks
reproducibility; it does not turn the external arithmetic or the Python–MSA
residual transcription into a Lean theorem.

## Residual provenance and remaining formal interface

The Python `Model.residual` is a source-level transcription of the pure-fluid
finite-tail Blum–Høye equations. The frozen Lean definition
`FMSA.ExactMSA.MultiTail.IsRoot` in
`LeanCode/YukawaOZ/MSAMultiTailSystem.lean` uses the same unit-diameter
unknowns `(Dt_t,G_t)` and the equations `Dt_t·factor(z_t)=2πK_t/z_t` and
`2πG_t·factor(z_t)=secondRHS(z_t)`. In the Python source, `gam`, `M`, `N`,
`A`, `qp`, `Qh`, `F` and `src` correspond respectively to Lean's `gam`,
`momentM`, `momentN`, `amplitudeA`, `amplitudeQp`, `Qhat`, `factor` and
`secondRHS`. The Python coefficient arrays `xA`, `xB` group the `W` and `C`
terms of Lean's `Qhat`; `sD` groups the finite-tail term of `secondRHS`.
This is a read-only source audit of the formula, **not** a kernel proof that
executes the Python certificate inside Lean. The frozen foundation has
numerical point checks of this transcription; a fully formal F5 instance
would need an exact serialized interval certificate plus a Lean checker for
those interval operations and the script-to-Lean dictionary.
