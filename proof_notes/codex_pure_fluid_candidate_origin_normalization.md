# Candidate pure-fluid dressing: origin cancellation and infinity normalization

`PureFluidCandidateOriginConstraint.lean` closes two analytic interfaces
in the paper's Step 2 construction. For arbitrary real `U,g` and every
nonzero real frequency `s`, Lean proves the exact identity

    2 P_cand(s) + (2 − 2s + s²) Shat_cand(s)
      = (q0 + 2) U + (a0/2 − q0 − 2 + s) g,

where `a0=hardA(xi)` and `q0=hardQ(xi)`. This evaluates the earlier
polynomial polar identity directly on the actual frozen PY rational
basis. It needs no polynomial or analytic assumption on `U,g`, because
it is pointwise algebra at `s≠0`.

For the concrete finite-sum candidate `U(s),g(s)`, nonzero tail rates
make both functions continuous at `s=0`. Therefore the left side has
the punctured real-axis limit

    (q0 + 2) U(0) + (a0/2 − q0 − 2) g(0).

The module also proves `U(s)→1`, `g(s)→0`, the actual hard-sphere
basis limits, and finally `P_cand(s)→1`, `Shat_cand(s)→0` as
`s→+∞`. These infinity results do not require positive rates;
finiteness suffices. The origin result assumes each rate is nonzero.

The identity shows cancellation of the polar part in one specified
linear combination. It does not yet extract the individual Laurent
coefficients of `P_cand,Shat_cand`, identify them with the actual BH
moment definitions, prove candidate/actual global equality, or establish
all-order positivity and `R=tau_f`.

Full project validation: PASS, 1817 exact standard-three theorem guards /
197 research modules. Frozen foundation 1.0.17 unchanged. No TeX write
or new axiom.
