# Candidate dressing finite-pole decomposition and coefficient matching

`PureFluidCandidatePoleCoefficients.lean` expands the concrete
finite-sum `U,g` from `PureFluidDressingCandidates` inside the proposed
hard-sphere rational/exponential dressing. Lean proves exact identities

    P_cand(s) = P0(s) + sum_t N^P_t(s)/(s+z_t),
    Shat_cand(s) = Shat0(s) + sum_t N^S_t(s)/(s+z_t),

with explicit `poleNumeratorP/S` functions. These are identities of
Lean's totalized real rational expressions at every real `s`; no
distinctness, root, or convergence premise enters.

For `z_t≠0`, substituting `s=-z_t` in each one-pole numerator gives the
defined `formalPoleP/S`. If the paper's `r` linear system holds and
`U(z_t)≠0`, Lean then proves

    formalPoleP_t = -(w_t/U_t) Shat_cand(z_t),
    formalPoleS_t = -(w_t/U_t) P_cand(z_t).

Thus the candidate's individual pole numerators have exactly the
cross-node coefficients of the ACTUAL BH formulas in
`PureFluidExactResidueForm`, under `Lambda_t=w_t/U_t`.

The word “formal” is deliberate. The module has not proved a punctured
neighborhood limit of `(s+z_t)P_cand(s)` or of the exponential piece.
That limit needs positive, pairwise distinct rates (or combined-pole
bookkeeping), and continuity of the regular terms at `-z_t`.
The later `PureFluidCandidateResidueLimit` module proves these limits
under positive pairwise distinct rates; see
`codex_pure_fluid_candidate_residue_limit.md`.
Matching the full origin/moment coefficients and identifying the
candidate with an actual HS-seeded branch also remain open.

Full package validation: PASS, 1790 exact standard-three theorem guards /
194 modules; eight guarded theorems in this module. Frozen foundation
1.0.17 unchanged; no TeX write or extra axiom.
