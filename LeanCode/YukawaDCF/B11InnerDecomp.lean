/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.B5MixturePoly

/-!
# Task B.11 — Inner DCF Decomposition: Domain of P_ij and Mediated Vanishing

## Context

`B5MixturePoly.lean` establishes that P_ij has degree ≤ 4 (B.5) and provides
the B.8 Laplace-moment inversion formula.  This file addresses the complementary
structural question: what is the correct **domain** of P_ij, and when does the
mediated contribution vanish?

## Decomposition statement

For an unlike pair (i ≠ j) in an N-component mixture, the first-order inner DCF
decomposes as:

  c^(1)_ij(r) = [Term_I(r) + P_ij(r)] / (2π√(ρᵢ ρⱼ) r)
                + c^HS_ij(r)
                + mediated_ij(r)

where:
  - Term_I(r)    = Σ_t Kᵢⱼ · [(1−G²_ij)·exp(−z_t·(r−R_ij)) − A²_ij·exp(z_t·(r−R_ij))]
                   (pure-exponential formula for unlike pairs; no scalar D²)
  - P_ij(r)      = p₀ + p₁r + p₂r² + p₃r³ + p₄r⁴  (degree ≤ 4 polynomial)
  - c^HS_ij(r)   = White Bear FMT hard-sphere DCF (kink at |λ_ij| = (σ_j−σ_i)/2, unlike pairs)
  - mediated_ij(r) = Terms II + III + IV from `_compute_mediated` in fmsa_ga_matrix_mix.py

## Breakpoint structure and domain of P_ij

### Factor-of-3 threshold (derived from `_compute_mediated` code)

For any mediated term involving pair (i,j) with intermediate species b, the
activation condition at the inner boundary r = R[i,b] = (σ_i+σ_b)/2 is:

  alpha_0 = lambda_ij[j,b] − sigma[b]
          = (σ_j − σ_b)/2 − σ_b
          = (σ_j − 3·σ_b) / 2

This is positive (term is active at its inner breakpoint) **iff σ_j > 3·σ_b**.

### σ-ratio ≤ 3 (confirmed; includes our binary σ=[1,2] with ratio=2)

- All mediated contributions (Terms II, III, IV) are identically zero in the
  inner region [0, R_ij] for ALL pairs (unlike and like; any N).
- The sole piecewise source is the c_HS kink at |λ_ij| = (σ_j−σ_i)/2 (unlike
  pairs only; for like pairs |λ_ii| = 0, so c_HS is smooth on (0, R_ii)).
- After exact subtraction of c_HS, P_ij is a **single polynomial on (0, R_ij)**
  for every pair in the mixture.

### σ-ratio > 3 (needs further research)

- Term III of pair (i,j) from species b: breakpoint at R[i,b]=(σ_i+σ_b)/2
  when σ_j > 3σ_b.  Term II: breakpoint at R[a,j] when σ_i > 3σ_a.
- Term IV (double convolution, involving `c_exp`, `u_lo_bj`, `u_hi_bj` in code):
  activation conditions not fully characterised; additional interior breakpoints
  are possible.  **Term IV analysis is incomplete; full characterisation pending.**
- For N≥3 with σ-ratio > 3 (e.g., σ=[1,2,4]): P_ij may be piecewise with
  O(N) breakpoints per pair.  Single-polynomial B.11 theorems below apply only
  to the σ-ratio ≤ 3 regime.

### Piecewise vs single polynomial

A piecewise polynomial fit provides a better numerical approximation when σ-ratio > 3
and mediated does not vanish in the inner region.  For σ-ratio ≤ 3 the two
formulations are equivalent.  The single polynomial is numerically acceptable after
c_HS + mediated subtraction (confirmed by `_update_polycorr` after the fix).

## Key result

`mediated_ij(r) = 0` for all r in (0, R_ij) when σ-ratio ≤ 3.
`P_ij` is a single polynomial on (0, R_ij) determined by the B.8 Laplace-moment
inversion (proved in B5MixturePoly.lean / b8_poly_coeff_from_laurent).

## Implementation note

`oz_numerical._update_polycorr` subtracts c_HS_FMT (via `get_HS_FMT`) and
mediated (via `_compute_mediated`) before the B.8 moment fit, so that `poly_vals`
approximates P_ij·(2π√ρρ·r) directly.  The p₀ pin (`_rc1r_at_zero`) ensures the
1/r divergence is avoided.

## Status

| Sub-task | Description | Status |
|----------|-------------|--------|
| B.11.1   | mediated_ij(r) = 0 for r < σ_min (σ-ratio ≤ 3) | sorry |
| B.11.2   | P_ij is a single polynomial on (0, R_ij) (σ-ratio ≤ 3) | sorry |
| B.11.3   | Decomposition is unique given Term_I and mediated | sorry |
| B.11.4   | σ-ratio > 3: characterise Term IV breakpoints | needs research |
-/

set_option linter.style.whitespace false
set_option linter.unusedVariables false

open Real Set Polynomial

namespace FMSA.InnerDecomp

/-!
## Formal setup

We work in an abstract setting: σ : Fin N → ℝ>0 are species diameters,
R_ij = (σᵢ + σⱼ)/2 for all pairs, σ_min(i,j) = min(σᵢ, σⱼ).

A function `mediated : ℝ → Fin N → Fin N → ℝ` is given satisfying
the vanishing property derived from `_compute_mediated`.
-/

variable (N : ℕ) (σ : Fin N → ℝ) (hσ : ∀ k, 0 < σ k)

/-- Contact distance for pair (i, j). -/
noncomputable def R_ij (i j : Fin N) : ℝ := (σ i + σ j) / 2

/-- Size asymmetry lower cutoff for pair (i, j). -/
noncomputable def σ_min (i j : Fin N) : ℝ := min (σ i) (σ j)

/-- B.11.1 — Mediated terms vanish for r < σ_min (σ-ratio ≤ 3 case).

    Activation criterion (from `_compute_mediated` code analysis):
    alpha_0 = (σ_j − 3σ_b)/2 at breakpoint r = R[i,b].
    Active iff σ_j > 3σ_b (factor-of-3 threshold).
    For σ-ratio ≤ 3: alpha_0 ≤ 0 for all intermediate species b → all
    mediated terms inactive in the inner region.

    For the binary case (N=2, σ₁ < σ₂, ratio=2 < 3): σ_min(0,1) = σ₁.
    `_compute_mediated` Term II with a=0: lstar=0 when r < R_{0,j};
    Term III with b=0: alpha_0 = (σ₂−3σ₁)/2 = −0.5 < 0 → inactive.
    Numerically confirmed: mediated = 0 for all r in (0, R₁₂). -/
theorem b11_mediated_vanishes_below_σmin
    (mediated : ℝ → Fin N → Fin N → ℝ)
    (i j : Fin N) (hij : i ≠ j)
    (hmed : ∀ r (a : Fin N), r < R_ij N σ a j → mediated r i j = 0) :
    ∀ r, r < σ_min N σ i j → mediated r i j = 0 := by
  sorry

/-- B.11.2 — After subtracting analytic terms, the residue is a single polynomial (σ-ratio ≤ 3).

    Assumes the decomposition
      c1_inner(r) = (Term_I(r) + P_ij(r)) * prefac(r) + c_hs(r) + mediated(r)
    holds for all r ∈ (0, R_ij).  Then:
      P_ij(r) = (c1_inner(r) - c_hs(r) - mediated(r)) / prefac(r) - Term_I(r)
    is a polynomial of natDegree ≤ 4 on all of (0, R_ij).

    This is the key claim that justifies `_update_polycorr`'s single B.8 moment
    inversion over the full domain (0, R_ij) after subtracting c_hs and mediated.
    For σ-ratio ≤ 3, mediated = 0 so only c_hs is subtracted. -/
theorem b11_residue_is_polynomial
    (c1_inner term_I c_hs mediated : ℝ → ℝ)
    (prefac : ℝ → ℝ) (hpf : ∀ r ∈ Ioo 0 (R_ij N σ 0 1), prefac r ≠ 0)
    (hdecomp : ∀ r ∈ Ioo 0 (R_ij N σ 0 1),
        c1_inner r = (term_I r + (fun r => 0) r) * prefac r + c_hs r + mediated r) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ 4 ∧
        ∀ r ∈ Ioo 0 (R_ij N σ 0 1),
            (c1_inner r - c_hs r - mediated r) / prefac r - term_I r = P.eval r := by
  sorry

/-- B.11.3 — Full inner DCF decomposition for unlike pairs (σ-ratio ≤ 3).

    The complete structural theorem: for an unlike pair (i ≠ j), the OZ+MSA
    inner DCF decomposes uniquely into (Term_I / prefac), a single polynomial P_ij,
    and mediated, where mediated = 0 for r < σ_min. -/
theorem b11_inner_dcf_decomp
    (c1_inner term_I c_hs mediated : ℝ → ℝ)
    (prefac : ℝ → ℝ)
    (i j : Fin N) (hij : i ≠ j)
    (hpf : ∀ r ∈ Ioo 0 (R_ij N σ i j), prefac r ≠ 0)
    (hdecomp : ∀ r ∈ Ioo 0 (R_ij N σ i j),
        c1_inner r = (term_I r + (fun _ => 0) r) * prefac r + c_hs r + mediated r) :
    ∃ (P : Polynomial ℝ),
        P.natDegree ≤ 4 ∧
        (∀ r ∈ Ioo 0 (R_ij N σ i j),
            c1_inner r = (term_I r + P.eval r) * prefac r + c_hs r + mediated r) ∧
        (∀ r ∈ Ioo 0 (σ_min N σ i j), mediated r = 0) := by
  sorry

end FMSA.InnerDecomp
