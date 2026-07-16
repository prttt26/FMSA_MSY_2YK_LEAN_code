/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterPoles
import LeanCode.HardSphere.RadialFourierCHSComplex
import LeanCode.Analysis.ResidueAtSimplePole

/-!
# Task POLE.4 — residue formula + `h_explicit` (in progress)

## Status

**B.1 — residue-at-a-simple-pole fact: DONE**, now in its own stable file
`ResidueAtSimplePole.lean` (extracted 2026-07-15 so that other work streams, e.g. the mixture groups (MML/MZERO), can
depend on the small, generic lemma without rebuilding alongside this file's much larger and
actively-changing Group OZFIX content).

**What's left for the rest of `POLE.4` (not attempted this pass, honestly larger than the
original scope suggested):**

1. **Assembling the actual physical residue formula needs a new complex-valued `Ĉ`.** The
   target residue is of `f(k) = k·Ĉ(k)·e^{ikr}/[(1-ρQ̂(k))(1-ρQ̂(-k))]` at each pole `k_n` of
   `1-ρQ̂(k)` (from `POLE.3`). `Ĉ(k) := radial_fourier (c_HS eta sigma) k` is currently only
   defined for **real** `k` (`RadialFourierCHS.lean`, Task OZ.8) — extending it to complex `k`
   in closed form, entire, is its own `POLE.1`-style undertaking (a new closed-form/entireness
   pair), not yet started. Without it, the residue formula can't even be *stated* precisely.
2. Given (1), derive `Res_n = N_res(k_n)/D_res'(k_n)` via `residue_of_simple_pole`, with
   `D_res(k) := 1-ρQ̂(k) = G_baxter(k)/(-ik)³` (`k≠0`) and `N_res(k) := k·Ĉ_complex(k)·e^{ikr}/
   (1-ρQ̂(-k))` — mechanical once (1) exists, using `baxter_cube_mul_F_eq_G` and
   `G_baxter`'s already-proven entireness/derivative structure.
3. **B.2 — mirror pole family.** `POLE.3`'s `Qhat_complex_zeros_infinite` only gives the
   upper-half-plane, positive-real-part family; the sine-transform inversion (closing the
   contour upward) also needs the mirrored family (negative real part, same positive imaginary
   part). Check the symmetry claim (`G_baxter`'s zero set closed under `k ↦ -k̄`-type reflection)
   numerically first, then either re-derive `POLE.3`'s argument for the mirror family or find
   a direct symmetry argument from `Npoly`/`Dpoly`'s coefficient structure.
4. **B.3 — `h_explicit` definition + convergence.** Define `h_explicit(r) := (1/2πr)·Re[Σ_n
   Res_n·e^{ik_n r}]` for `r>σ`; prove convergence via the pole-growth law (`Re(k_n)` spacing
   `=2π/σ` exact, `Im(k_n)~2ln(Re(k_n))`) combined with the residue-magnitude asymptotic this
   file's formula would give, matching the previously-validated `n^{1-2r}` numerical decay law —
   needs re-deriving that exponent symbolically from the now-exact residue formula, not just
   citing the earlier numerical fit.

None of 1–4 is expected to be *harder in kind* than what `POLE.1`–`11` already did (closed-form
complex extensions, `HasDerivAt`+FTC estimates, `Summable`/`tsum` convergence via comparison
tests) — but each is a genuine, multi-lemma undertaking in its own right, not a quick follow-on.
-/

open Filter Topology intervalIntegral

namespace FMSA.HardSphere

/-! ### Residue formula assembly

Rewrites the residue target `k·Ĉ(k)·e^{ikr}/[(1-ρQ̂(k))(1-ρQ̂(-k))]` purely in terms of
`G_baxter` via `baxter_cube_mul_F_eq_G` (`(-ik)³(1-ρQ̂(k))=G_baxter(k)`, valid `k≠0`):
`(-ik)³(ik)³ = k⁶` (direct algebra), so
`k·Ĉ(k)·e^{ikr}/[(1-ρQ̂(k))(1-ρQ̂(-k))] = k⁷·Ĉ(k)·e^{ikr}/[G_baxter(k)·G_baxter(-k)]`
— then `residue_of_simple_pole` applies directly with `D:=G_baxter`, `N(k):=k⁷Ĉ(k)e^{ikr}/
G_baxter(-k)`. -/

/-- The residue-computation target. -/
noncomputable def Hhat_residue_integrand (eta sigma rho r : ℝ) (k : ℂ) : ℂ :=
  k ^ 7 * Chat_complex eta sigma k * Complex.exp (Complex.I * k * r) /
    (G_baxter eta sigma rho k * G_baxter eta sigma rho (-k))

/-- **Residue at a pole `k_n` of `1-ρQ̂`**, via `residue_of_simple_pole`. Two explicit
non-degeneracy hypotheses (standard genericity, not yet established from first principles):
`G_baxter`'s zero at `k_n` is *simple* (`hGderiv_ne`), and `-k_n` is not itself a zero
(`hGneg_ne` — expected, since `POLE.3`'s poles are upper-half-plane and its construction
never produces lower-half-plane zeros, but not yet proved as a general fact; see `B.2`). -/
theorem Hhat_residue_at_pole (eta sigma rho r : ℝ) (hsigma : 0 < sigma) {k_n : ℂ}
    (hkn_ne : k_n ≠ 0) (hzero : G_baxter eta sigma rho k_n = 0)
    (hGderiv_ne : G_baxter_deriv eta sigma rho k_n ≠ 0)
    (hGneg_ne : G_baxter eta sigma rho (-k_n) ≠ 0) :
    Tendsto (fun k => (k - k_n) * (Hhat_residue_integrand eta sigma rho r k)) (𝓝[≠] k_n)
      (𝓝 (k_n ^ 7 * Chat_complex eta sigma k_n * Complex.exp (Complex.I * k_n * r) /
        (G_baxter eta sigma rho (-k_n) * G_baxter_deriv eta sigma rho k_n))) := by
  set N : ℂ → ℂ := fun k => k ^ 7 * Chat_complex eta sigma k * Complex.exp (Complex.I * k * r) /
    G_baxter eta sigma rho (-k) with hNdef
  set D : ℂ → ℂ := G_baxter eta sigma rho with hDdef
  have hNcont : ContinuousAt N k_n := by
    have hCcont : ContinuousAt (Chat_complex eta sigma) k_n :=
      (Chat_complex_differentiableAt eta sigma hsigma hkn_ne).continuousAt
    have hGnegcont : ContinuousAt (fun k => G_baxter eta sigma rho (-k)) k_n :=
      ((G_baxter_entire eta sigma rho).continuous.continuousAt (x := -k_n)).comp
        (continuous_neg.continuousAt)
    have hexpcont : ContinuousAt (fun k : ℂ => Complex.exp (Complex.I * k * r)) k_n :=
      (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_id).mul continuous_const)).continuousAt
    have hnum : ContinuousAt (fun k : ℂ => k ^ 7 * Chat_complex eta sigma k *
        Complex.exp (Complex.I * k * r)) k_n :=
      ((continuousAt_id.pow 7).mul hCcont).mul hexpcont
    exact hnum.div hGnegcont hGneg_ne
  have hD : HasDerivAt D (G_baxter_deriv eta sigma rho k_n) k_n :=
    G_baxter_hasDerivAt eta sigma rho k_n
  have hres := residue_of_simple_pole N D (G_baxter_deriv eta sigma rho k_n) k_n hD hzero
    hGderiv_ne hNcont
  have heq : ∀ k : ℂ,
      (k - k_n) * (N k / D k) = (k - k_n) * (Hhat_residue_integrand eta sigma rho r k) := by
    intro k
    rw [hNdef, hDdef]
    unfold Hhat_residue_integrand
    rw [div_div, mul_comm (G_baxter eta sigma rho (-k))]
  have hN_eq : N k_n = k_n ^ 7 * Chat_complex eta sigma k_n * Complex.exp (Complex.I * k_n * r) /
      G_baxter eta sigma rho (-k_n) := rfl
  rw [hN_eq, hDdef, div_div] at hres
  exact hres.congr' (Filter.Eventually.of_forall heq)

/-! ### `h_explicit` — the residue series (Task `POLE.4`, Phase B.3)

`h_explicit(r) := (1/2πr)·Re[Σ_n (Res_n + Res_n^mirror)]`, summing `Hhat_residue_at_pole`'s
residue value at each pole `k_n` (drawn from an abstract pole family `kfam : ℕ → ℂ` — e.g.
`POLE.3`'s witness function, not yet exposed as a standalone name; `h_explicit` is stated
generically over any `kfam` so it doesn't need that refactor to typecheck) together with its
mirror `-conj(k_n)` (`B.2`'s `G_baxter_conj`/`G_baxter_zero_mirror` — the conjugate-symmetric
partner needed for the sine-transform inversion contour to close over the *whole* pole set, not
just the upper-right family `POLE.3` constructs).

**Convergence** needs a magnitude bound on each paired term. The exact closed-form residue
formula (`Chat_complex`+`G_baxter`+`G_baxter_deriv`, all proved unconditionally this project) was
checked numerically (scratch, not committed) at **three different `σ`** (`σ=1,2,0.5`, `η=0.3`,
Newton-refined pole locations up to `n=320`): `|Res_n(r)|` decays *exactly* like `n^{1-2r/σ}`
(log-log slopes match `1-2r/σ` to 3 decimal places at every tested `σ`, e.g. `σ=2,r=3⇒slope≈
-2.000`, `σ=0.5,r=1⇒slope≈-3.00`). **Correction (this pass): an earlier check only tested `σ=1`**,
where `1-2r/σ` and `1-2r` coincide — the `σ`-dependence was masked; re-testing at `σ≠1` confirmed
the general exponent is `1-2r/σ`, not the `σ`-independent `1-2r` first assumed. The heuristic
derivation: at a pole `k_n`, `G_baxter(k_n)=0` forces `|e^{-ik_nσ}|=‖Npoly(k_n)‖/‖Dpoly(k_n)‖=
Θ(n²)`, i.e. `Im(k_n)=Θ((2/σ)\ln n)` — a **consequence** of the pole equation, not an independent
asymptotic input; propagating this through `Chat_complex(k_n)=Θ(1)`, `G_baxter(±k_n)=
G_baxter_deriv(k_n)=Θ(n³)`, `k_n^7=Θ(n^7)` gives `|residue\_term(k_n)|=Θ(n)·|e^{ik_nr}|=Θ(n)·
e^{-r\cdot Im(k_n)}=Θ(n^{1-2r/σ})`. `h_explicit_summable` below takes this decay law as an
explicit hypothesis (mirroring `POLE.3`'s `hstep` pattern and `Hhat_residue_at_pole`'s two
non-degeneracy hypotheses) — a fully rigorous (inequality-level, not just `Θ`-heuristic) symbolic
derivation is a further undertaking, not attempted this pass. Absolute summability needs
`p := 1-2r/σ < -1 ⟺ r > σ` (`Real.summable_nat_rpow`) — exactly the physically-relevant exterior
domain, with **no gap** left open (unlike the earlier, incorrect `r>1` threshold this replaces). -/

/-- The residue-formula value at a single pole `k_n`, matching `Hhat_residue_at_pole`'s limit. -/
noncomputable def residue_term (eta sigma rho r : ℝ) (k_n : ℂ) : ℂ :=
  k_n ^ 7 * Chat_complex eta sigma k_n * Complex.exp (Complex.I * k_n * r) /
    (G_baxter eta sigma rho (-k_n) * G_baxter_deriv eta sigma rho k_n)

set_option maxHeartbeats 4000000 in
-- Large combined magnitude-bound assembly (many `set`-introduced local defs accumulate a big
-- elaboration context); every individual step is simple, but the proof as a whole needs the
-- extra budget.
/-- **`residue_term` magnitude bound** (Task `POLE.5`, A.4): at a zero `k` of `G_baxter` with
`Im(k)≥0` and `‖k‖` past an explicit threshold, `‖residue_term(k)‖ ≤ C·‖k‖^{1-2r/σ}` — the
rigorous (not just numerically-checked) version of the `n^{1-2r/σ}` decay law, assembled from
`abs_exp_ikr_upper_of_zero` (numerator exponential decay), `Chat_complex_norm_bound` +
`exists_D_for_exp_neg_bound` (numerator `Chat_complex` factor, `Θ(1)` via cancellation against
the `1/‖k‖²` in `Chat_complex_norm_bound`), and `G_baxter_neg_lower_bound` +
`G_baxter_deriv_lower_bound_of_zero` (denominator, `Θ(‖k‖⁶)`). `C`/the threshold are left
existential (not simplified to a closed form) — genuine but not claimed optimal. **Holds for any
`r>0`, not just `r>σ`** (Task `OZFIX.4`, the `σ`-boundary case): the underlying magnitude bound
(`abs_exp_ikr_upper_of_zero`) only ever needs `0<r`; the stronger `σ<r` some callers supply is for
their own downstream *summability* threshold, not for this pointwise bound. This matters for
`h_explicit`'s antiderivative series (`Hterm`), whose *own* decay is one power of `‖k‖` better
than `h_explicit_term`'s, making it summable already at `r=σ` — needed to evaluate
`oz_linear_op`'s inner integral at its lower endpoint `max(r-t,σ)`, which can equal `σ` exactly. -/
theorem residue_term_norm_bound {eta sigma rho r : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (hr : 0 < r) :
    ∃ C M : ℝ, 0 < C ∧ 1 ≤ M ∧ ∀ {k : ℂ}, G_baxter eta sigma rho k = 0 → 0 ≤ k.im → M ≤ ‖k‖ →
      ‖residue_term eta sigma rho r k‖ ≤ C * ‖k‖ ^ (1 - 2 * r / sigma) := by
  obtain ⟨M0, hM0pos, hM0N, hM0T⟩ := exists_hkN_hkT_threshold eta sigma rho hsigma
  obtain ⟨D, hDpos, hD⟩ := exists_D_for_exp_neg_bound heta0 heta1 hsigma hrho
  have hmupos := baxterMu_pos heta0 heta1 hsigma hrho
  have hnupos := baxterNu_pos heta0 heta1 hrho
  set mu : ℝ := rho * q_prime_py eta sigma with hmudef
  set nu : ℝ := rho * q_doubleprime_py eta with hnudef
  set K1 : ℝ := |py_a0 eta| * (sigma + 1) + |py_a1 eta / sigma| * (sigma ^ 2 + 2 * sigma + 2) +
    |py_a3 eta / sigma ^ 3| * (sigma ^ 4 + 4 * sigma ^ 3 + 12 * sigma ^ 2 + 24 * sigma + 24)
    with hK1def
  set K2 : ℝ := |py_a0 eta| + |py_a1 eta / sigma| * 2 + |py_a3 eta / sigma ^ 3| * 24 with hK2def
  have hK1nn : 0 ≤ K1 := by rw [hK1def]; positivity
  have hK2nn : 0 ≤ K2 := by rw [hK2def]; positivity
  set CCbound : ℝ := 2 * Real.pi * K1 + 2 * Real.pi * K1 * D + 4 * Real.pi * K2 with hCCdef
  have hCCpos : 0 ≤ CCbound := by rw [hCCdef]; positivity
  set M : ℝ := max (max M0 1) (max (2 * nu / mu) (max (4 / sigma) (4 * (mu + nu + 1))))
    with hMdef
  refine ⟨(32 * (CCbound + 1) / sigma) * (4 * mu) ^ (r / sigma), M, by positivity, ?_, ?_⟩
  · calc (1:ℝ) ≤ max M0 1 := le_max_right _ _
      _ ≤ M := le_max_left _ _
  · intro k hzero hkim hkM
    have hk1 : 1 ≤ ‖k‖ := by
      calc (1:ℝ) ≤ max M0 1 := le_max_right _ _
        _ ≤ M := le_max_left _ _
        _ ≤ ‖k‖ := hkM
    have hk0 : 0 < ‖k‖ := lt_of_lt_of_le one_pos hk1
    have hkN : M0 ≤ ‖k‖ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hkM)
    have hkD : 2 * nu / mu ≤ ‖k‖ := by
      have : 2 * nu / mu ≤ M :=
        le_trans (le_max_left _ _) (le_max_right (max M0 1) _)
      linarith [this, hkM]
    have hkS : 4 / sigma ≤ ‖k‖ := by
      have : 4 / sigma ≤ M :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right (max M0 1) _))
      linarith [this, hkM]
    have hkT4 : 4 * (mu + nu + 1) ≤ ‖k‖ := by
      have : 4 * (mu + nu + 1) ≤ M :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right (max M0 1) _))
      linarith [this, hkM]
    have hkNfull := hM0N k hkN
    have hkTfull := hM0T k hkN
    -- Denominator bounds
    have hGderiv := G_baxter_deriv_lower_bound_of_zero heta0 heta1 hsigma hrho hzero hk1 hkNfull
      hkD hkS hkTfull
    have hGneg := G_baxter_neg_lower_bound heta0 heta1 hsigma hrho hkim hk1 hkNfull
    have hGneg4 : ‖k‖ ^ 3 / 4 ≤ ‖G_baxter eta sigma rho (-k)‖ := by
      have hmuquarter : mu ≤ ‖k‖ / 4 := by linarith [hkT4, hnupos]
      have hnuquarter : nu ≤ ‖k‖ / 4 := by linarith [hkT4, hmupos]
      have hmuk : mu * ‖k‖ ≤ ‖k‖ ^ 2 / 4 := by nlinarith [hmuquarter, hk0]
      have hnuk : nu ≤ ‖k‖ ^ 2 / 4 := by nlinarith [hnuquarter, hk1]
      have hsum : mu * ‖k‖ + nu ≤ ‖k‖ ^ 2 / 2 := by linarith [hmuk, hnuk]
      have hksq : ‖k‖ ^ 2 / 2 ≤ ‖k‖ ^ 3 / 4 := by nlinarith [hkT4, hmupos, hnupos, hk0]
      have hmuxnu : mu * ‖k‖ + nu ≤ ‖k‖ ^ 3 / 4 := by linarith [hsum, hksq]
      linarith [hGneg, hmuxnu]
    -- Numerator bounds
    have hExpNegBound : ‖Complex.exp (-Complex.I * k * sigma)‖ ≤ D * ‖k‖ ^ 2 := hD hzero hk1 hkD
    have hEnn : 0 ≤ D * ‖k‖ ^ 2 := by positivity
    have hChatBound := Chat_complex_norm_bound eta sigma hsigma
      (by intro hk0'; rw [hk0'] at hk0; simp at hk0) hk1 hkim hExpNegBound hEnn
    have hChatBoundC : ‖Chat_complex eta sigma k‖ ≤ CCbound := by
      rw [hCCdef]
      have hstep1 : 2 * Real.pi * K1 * (1 + D * ‖k‖ ^ 2) / ‖k‖ ^ 2 + 4 * Real.pi * K2 / ‖k‖ =
          2 * Real.pi * K1 / ‖k‖ ^ 2 + 2 * Real.pi * K1 * D + 4 * Real.pi * K2 / ‖k‖ := by
        rw [show 2 * Real.pi * K1 * (1 + D * ‖k‖ ^ 2) =
          2 * Real.pi * K1 + 2 * Real.pi * K1 * D * ‖k‖ ^ 2 by ring]
        rw [add_div, mul_div_assoc]
        congr 2
        field_simp
      rw [hstep1] at hChatBound
      have hksq1 : (1:ℝ) ≤ ‖k‖ ^ 2 := by nlinarith [hk1]
      have hpiK1nn : 0 ≤ 2 * Real.pi * K1 := by positivity
      have hpiK2nn : 0 ≤ 4 * Real.pi * K2 := by positivity
      have hinv2 : 2 * Real.pi * K1 / ‖k‖ ^ 2 ≤ 2 * Real.pi * K1 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hksq1, hpiK1nn]
      have hinv1 : 4 * Real.pi * K2 / ‖k‖ ≤ 4 * Real.pi * K2 := by
        rw [div_le_iff₀ hk0]
        nlinarith [hk1, hpiK2nn]
      linarith [hChatBound, hinv1, hinv2]
    have hExpR := abs_exp_ikr_upper_of_zero heta0 heta1 hsigma hrho (by linarith : (0:ℝ) < r)
      hzero hk1 hkNfull hkD
    -- Assemble
    unfold residue_term
    rw [norm_div, norm_mul, norm_mul, norm_pow]
    rw [norm_mul]
    have hDenomPos : 0 < ‖G_baxter eta sigma rho (-k)‖ * ‖G_baxter_deriv eta sigma rho k‖ := by
      have h1 : 0 < ‖G_baxter eta sigma rho (-k)‖ := by nlinarith [hGneg4, hk1]
      have h2 : 0 < ‖G_baxter_deriv eta sigma rho k‖ := by
        have hk3pos : 0 < ‖k‖ ^ 3 := by positivity
        nlinarith [hGderiv, hsigma, hk3pos]
      positivity
    rw [div_le_iff₀ hDenomPos]
    have hDenomLower : sigma * ‖k‖ ^ 6 / 32 ≤
        ‖G_baxter eta sigma rho (-k)‖ * ‖G_baxter_deriv eta sigma rho k‖ := by
      have h1 : 0 ≤ ‖k‖ ^ 3 / 4 := by positivity
      have h2 : 0 ≤ sigma * ‖k‖ ^ 3 / 8 := by positivity
      calc sigma * ‖k‖ ^ 6 / 32 = (‖k‖ ^ 3 / 4) * (sigma * ‖k‖ ^ 3 / 8) := by ring
        _ ≤ ‖G_baxter eta sigma rho (-k)‖ * ‖G_baxter_deriv eta sigma rho k‖ :=
            mul_le_mul hGneg4 hGderiv h2 (by linarith [hGneg4, h1])
    have hRpowEq : (‖k‖ ^ 2 / (4 * mu)) ^ (-r / sigma) =
        (4 * mu) ^ (r / sigma) * ‖k‖ ^ (-(2 * r) / sigma) := by
      rw [show (-r / sigma : ℝ) = -(r / sigma) by ring]
      rw [Real.rpow_neg (by positivity)]
      rw [Real.div_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_two ‖k‖, ← Real.rpow_mul hk0.le]
      rw [show (2:ℝ) * (r / sigma) = 2 * r / sigma by ring]
      rw [inv_div]
      rw [show (4 * mu) ^ (r / sigma) / ‖k‖ ^ (2 * r / sigma) =
        (4 * mu) ^ (r / sigma) * (‖k‖ ^ (2 * r / sigma))⁻¹ by ring]
      rw [← Real.rpow_neg hk0.le]
      congr 2
      ring
    rw [hRpowEq] at hExpR
    have hKpowEq : ‖k‖ * ‖k‖ ^ (-(2 * r) / sigma) = ‖k‖ ^ (1 - 2 * r / sigma) := by
      nth_rewrite 1 [show ‖k‖ = ‖k‖ ^ (1:ℝ) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hk0]
      congr 1
      ring
    have hfinal : ‖k‖ ^ 7 * ‖Chat_complex eta sigma k‖ *
        ‖Complex.exp (Complex.I * k * r)‖ ≤
        ‖k‖ ^ 7 * CCbound * ((4 * mu) ^ (r / sigma) * ‖k‖ ^ (-(2 * r) / sigma)) := by
      have hk7nn : (0:ℝ) ≤ ‖k‖ ^ 7 := by positivity
      have hstep1 : ‖k‖ ^ 7 * ‖Chat_complex eta sigma k‖ ≤ ‖k‖ ^ 7 * CCbound :=
        mul_le_mul_of_nonneg_left hChatBoundC hk7nn
      have hstep2 : ‖k‖ ^ 7 * ‖Chat_complex eta sigma k‖ *
          ‖Complex.exp (Complex.I * k * r)‖ ≤ ‖k‖ ^ 7 * CCbound *
          ((4 * mu) ^ (r / sigma) * ‖k‖ ^ (-(2 * r) / sigma)) := by
        apply mul_le_mul hstep1 hExpR (norm_nonneg _)
        positivity
      exact hstep2
    have hpow76 : ‖k‖ ^ 7 * ‖k‖ ^ (-(2 * r) / sigma) = ‖k‖ ^ (7 - 2 * r / sigma) := by
      nth_rewrite 1 [← Real.rpow_natCast ‖k‖ 7]
      rw [← Real.rpow_add hk0]
      norm_num
      congr 1
      ring
    have hpow16 : ‖k‖ ^ (1 - 2 * r / sigma) * ‖k‖ ^ 6 = ‖k‖ ^ (7 - 2 * r / sigma) := by
      nth_rewrite 1 [← Real.rpow_natCast ‖k‖ 6]
      rw [← Real.rpow_add hk0]
      norm_num
      congr 1
      ring
    have hCCle : CCbound ≤ CCbound + 1 := by linarith
    have hstep3 : CCbound * (4 * mu) ^ (r / sigma) * ‖k‖ ^ (7 - 2 * r / sigma) ≤
        (CCbound + 1) * (4 * mu) ^ (r / sigma) * ‖k‖ ^ (7 - 2 * r / sigma) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCCle (by positivity))
      positivity
    calc ‖k‖ ^ 7 * ‖Chat_complex eta sigma k‖ * ‖Complex.exp (Complex.I * k * r)‖
        ≤ ‖k‖ ^ 7 * CCbound * ((4 * mu) ^ (r / sigma) * ‖k‖ ^ (-(2 * r) / sigma)) := hfinal
      _ = CCbound * (4 * mu) ^ (r / sigma) * ‖k‖ ^ (7 - 2 * r / sigma) := by
          rw [← hpow76]; ring
      _ ≤ (CCbound + 1) * (4 * mu) ^ (r / sigma) * ‖k‖ ^ (7 - 2 * r / sigma) := hstep3
      _ = ((32 * (CCbound + 1) / sigma) * (4 * mu) ^ (r / sigma) * ‖k‖ ^ (1 - 2 * r / sigma)) *
          (sigma * ‖k‖ ^ 6 / 32) := by
          rw [← hpow16]
          field_simp
      _ ≤ ((32 * (CCbound + 1) / sigma) * (4 * mu) ^ (r / sigma) * ‖k‖ ^ (1 - 2 * r / sigma)) *
          (‖G_baxter eta sigma rho (-k)‖ * ‖G_baxter_deriv eta sigma rho k‖) := by
          apply mul_le_mul_of_nonneg_left hDenomLower
          positivity

/-- Paired residue term at `kfam n`, combined with its mirror `-conj(kfam n)` (`B.2`). -/
noncomputable def h_explicit_term (eta sigma rho r : ℝ) (kfam : ℕ → ℂ) (n : ℕ) : ℂ :=
  residue_term eta sigma rho r (kfam n) +
    residue_term eta sigma rho r (-(starRingEnd ℂ) (kfam n))

/-- **`h_explicit_term` magnitude bound** (Task `POLE.5`, A.4): at a zero `k` of `G_baxter`
with `Im(k)≥0` and `‖k‖` past an explicit threshold, `‖h_explicit_term(k)‖ ≤ 2C·‖k‖^{1-2r/σ}` —
`residue_term_norm_bound` applied to both `k` and its mirror `-conj(k)` (`G_baxter_zero_mirror`
for the zero condition; `‖-conj(k)‖=‖k‖` and `(-conj(k)).im=k.im` so the mirror needs no new
threshold). -/
theorem h_explicit_term_norm_bound {eta sigma rho r : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (hr : sigma < r) :
    ∃ C M : ℝ, 0 < C ∧ 1 ≤ M ∧ ∀ {k : ℂ}, G_baxter eta sigma rho k = 0 → 0 ≤ k.im → M ≤ ‖k‖ →
      ‖residue_term eta sigma rho r k + residue_term eta sigma rho r (-(starRingEnd ℂ) k)‖ ≤
        2 * C * ‖k‖ ^ (1 - 2 * r / sigma) := by
  obtain ⟨C, M, hCpos, hM1, hbound⟩ := residue_term_norm_bound heta0 heta1 hsigma hrho
    (hsigma.trans hr)
  refine ⟨C, M, hCpos, hM1, ?_⟩
  intro k hzero hkim hkM
  have hnormeq : ‖-(starRingEnd ℂ) k‖ = ‖k‖ := by
    rw [norm_neg, RCLike.norm_conj]
  have himeq : (-(starRingEnd ℂ) k).im = k.im := by
    simp [Complex.conj_im]
  have hzeroMirror : G_baxter eta sigma rho (-(starRingEnd ℂ) k) = 0 := G_baxter_zero_mirror hzero
  have hkimMirror : 0 ≤ (-(starRingEnd ℂ) k).im := by rw [himeq]; exact hkim
  have hkMMirror : M ≤ ‖(-(starRingEnd ℂ) k)‖ := by rw [hnormeq]; exact hkM
  have h1 := hbound hzero hkim hkM
  have h2 := hbound hzeroMirror hkimMirror hkMMirror
  rw [hnormeq] at h2
  calc ‖residue_term eta sigma rho r k + residue_term eta sigma rho r (-(starRingEnd ℂ) k)‖
      ≤ ‖residue_term eta sigma rho r k‖ +
        ‖residue_term eta sigma rho r (-(starRingEnd ℂ) k)‖ := norm_add_le _ _
    _ ≤ C * ‖k‖ ^ (1 - 2 * r / sigma) + C * ‖k‖ ^ (1 - 2 * r / sigma) := by linarith [h1, h2]
    _ = 2 * C * ‖k‖ ^ (1 - 2 * r / sigma) := by ring

/-- **`h_explicit`**: the residue-series candidate for `oz_h eta sigma rho` outside the core
(`r > σ`), built from an abstract pole family `kfam`. -/
noncomputable def h_explicit (eta sigma rho r : ℝ) (kfam : ℕ → ℂ) : ℝ :=
  (1 / (2 * Real.pi * r)) * (∑' n : ℕ, h_explicit_term eta sigma rho r kfam n).re

/-- **`h_explicit`'s series is (absolutely) summable**, conditional on the numerically-confirmed
`n^{1-2r/σ}` magnitude decay of each paired residue term, for `r > σ` — exactly the physical
exterior domain. -/
theorem h_explicit_summable {eta sigma rho r : ℝ} (hsigma : 0 < sigma) (hr : sigma < r)
    {kfam : ℕ → ℂ} {C : ℝ}
    (hbound : ∀ n : ℕ,
      ‖h_explicit_term eta sigma rho r kfam n‖ ≤ C * ((n : ℝ) + 1) ^ (1 - 2 * r / sigma)) :
    Summable (h_explicit_term eta sigma rho r kfam) := by
  have hp : (1 - 2 * r / sigma : ℝ) < -1 := by
    have h2 : 1 < r / sigma := (lt_div_iff₀ hsigma).mpr (by linarith)
    have h3 : 2 * r / sigma = 2 * (r / sigma) := by ring
    linarith [h2, h3]
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (1 - 2 * r / sigma)) := Real.summable_nat_rpow.mpr hp
  have h1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 - 2 * r / sigma)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (1 - 2 * r / sigma)) 1).mpr h0
  have hg : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (1 - 2 * r / sigma)) := by
    convert h1 using 2 with n
    push_cast
    ring
  exact Summable.of_norm_bounded (hg.mul_left C) hbound

/-- **`h_explicit_summable`, concrete instantiation** (Task `POLE.5`, A.5): given a pole
family `kfam` that is a zero set of `G_baxter` with `Im≥0` and `‖kfam n‖` growing at least
linearly (`c·n+d ≤ ‖kfam n‖`, matching `G_baxter_pole_family_exists`'s `hgmem`+`hk1re` data —
`c := 2π/σ`, `d` from the disk-membership offset), `h_explicit_term` is genuinely `Summable`.
Uses `residue_term_norm_bound`'s `Θ(‖k‖^{1-2r/σ})` bound (rigorous, `POLE.5`'s main result)
composed with the negative-exponent `rpow` antitone step (`Real.rpow_le_rpow_iff_of_neg`, same
technique as `abs_exp_ikr_upper_of_zero`) to convert to an `n`-indexed bound, then
`Summable.of_norm_bounded_eventually` (only finitely many small `n` need excluding, where the
linear lower bound might fall short of `residue_term_norm_bound`'s threshold `M`). -/
theorem h_explicit_summable_of_pole_family {eta sigma rho r : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) (hr : sigma < r) {kfam : ℕ → ℂ}
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖) :
    Summable (h_explicit_term eta sigma rho r kfam) := by
  obtain ⟨C, M, hCpos, hM1, hbound⟩ := h_explicit_term_norm_bound heta0 heta1 hsigma hrho hr
  have hp : (1 - 2 * r / sigma : ℝ) < -1 := by
    have h2 : 1 < r / sigma := (lt_div_iff₀ hsigma).mpr (by linarith)
    have h3 : 2 * r / sigma = 2 * (r / sigma) := by ring
    linarith [h2, h3]
  have hp0 : (1 - 2 * r / sigma : ℝ) < 0 := by linarith
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (1 - 2 * r / sigma)) := Real.summable_nat_rpow.mpr hp
  have h1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 - 2 * r / sigma)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (1 - 2 * r / sigma)) 1).mpr h0
  have hg0 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (1 - 2 * r / sigma)) := by
    convert h1 using 2 with n
    push_cast
    ring
  set g : ℕ → ℝ := fun n => 2 * C * (min c d) ^ (1 - 2 * r / sigma) * ((n : ℝ) + 1) ^
    (1 - 2 * r / sigma) with hgdef
  have hg : Summable g := by
    rw [hgdef]
    have := hg0.mul_left (2 * C * (min c d) ^ (1 - 2 * r / sigma))
    simpa [mul_assoc] using this
  apply Summable.of_norm_bounded_eventually hg
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M ≤ c * (N : ℝ) + d := by
    obtain ⟨N, hN⟩ := exists_nat_ge ((M - d) / c)
    refine ⟨N, ?_⟩
    rw [div_le_iff₀ hc] at hN
    linarith [hN]
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (Set.finite_Iio N)
  intro n hn
  simp only [Set.mem_setOf_eq, not_le] at hn
  by_contra hcontra
  simp only [Set.mem_Iio, not_lt] at hcontra
  have hNn : M ≤ c * (n : ℝ) + d := by
    have : c * (N : ℝ) ≤ c * (n : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      exact_mod_cast hcontra
    linarith [hN, this]
  have hMk : M ≤ ‖kfam n‖ := le_trans hNn (hkfam_re n)
  have hb := hbound (hkfam_zero n) (hkfam_im n) hMk
  have hLpos : 0 < c * (n : ℝ) + d := by
    have : (0:ℝ) ≤ c * (n:ℝ) := by positivity
    linarith [hM1, hNn]
  have hkpos : 0 < ‖kfam n‖ := lt_of_lt_of_le hLpos (hkfam_re n)
  have hnp1pos : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hmono : ‖kfam n‖ ^ (1 - 2 * r / sigma) ≤ (c * (n:ℝ) + d) ^ (1 - 2 * r / sigma) :=
    (Real.rpow_le_rpow_iff_of_neg hkpos hLpos hp0).mpr (hkfam_re n)
  have hminpos : 0 < min c d := lt_min hc hd
  have hcdge : (min c d) * ((n:ℝ) + 1) ≤ c * (n:ℝ) + d := by
    rcases le_or_gt c d with hle | hle
    · rw [min_eq_left hle]; nlinarith [Nat.cast_nonneg n (α := ℝ)]
    · rw [min_eq_right hle.le]; nlinarith [Nat.cast_nonneg n (α := ℝ), hle]
  have hmono2 : (c * (n:ℝ) + d) ^ (1 - 2 * r / sigma) ≤
      ((min c d) * ((n:ℝ) + 1)) ^ (1 - 2 * r / sigma) :=
    (Real.rpow_le_rpow_iff_of_neg hLpos (by positivity) hp0).mpr hcdge
  have hmono3 : ((min c d) * ((n:ℝ) + 1)) ^ (1 - 2 * r / sigma) =
      (min c d) ^ (1 - 2 * r / sigma) * ((n:ℝ) + 1) ^ (1 - 2 * r / sigma) :=
    Real.mul_rpow hminpos.le hnp1pos.le
  have : ‖h_explicit_term eta sigma rho r kfam n‖ ≤
      2 * C * (min c d) ^ (1 - 2 * r / sigma) * ((n:ℝ) + 1) ^ (1 - 2 * r / sigma) := by
    have hchain : ‖kfam n‖ ^ (1 - 2 * r / sigma) ≤
        (min c d) ^ (1 - 2 * r / sigma) * ((n:ℝ) + 1) ^ (1 - 2 * r / sigma) := by
      calc ‖kfam n‖ ^ (1 - 2 * r / sigma) ≤ (c * (n:ℝ) + d) ^ (1 - 2 * r / sigma) := hmono
        _ ≤ ((min c d) * ((n:ℝ) + 1)) ^ (1 - 2 * r / sigma) := hmono2
        _ = (min c d) ^ (1 - 2 * r / sigma) * ((n:ℝ) + 1) ^ (1 - 2 * r / sigma) := hmono3
    calc ‖h_explicit_term eta sigma rho r kfam n‖ ≤ 2 * C * ‖kfam n‖ ^ (1 - 2 * r / sigma) := hb
      _ ≤ 2 * C * ((min c d) ^ (1 - 2 * r / sigma) * ((n:ℝ) + 1) ^ (1 - 2 * r / sigma)) :=
          mul_le_mul_of_nonneg_left hchain (by positivity)
      _ = 2 * C * (min c d) ^ (1 - 2 * r / sigma) * ((n:ℝ) + 1) ^ (1 - 2 * r / sigma) := by ring
  linarith [this, hn]

/-! ### Task `OZFIX.1` — single-exponential inner moment integral

`oz_linear_op`'s inner integral is `∫ s, s·h(s)`, but for `h := h_explicit`, `s·h_explicit(s) =
s·(1/(2πs))·Re[∑' n, h_explicit_term(n)(s)] = (1/(2π))·Re[∑' n, h_explicit_term(n)(s)]` — the `s`
cancels against `h_explicit`'s own `1/(2πs)` prefactor. Since `h_explicit_term(n)(s) = A(k_n)·
exp(I·k_n·s) + A(-conj k_n)·exp(-I·conj(k_n)·s)` with `A(k) := k^7·Chat_complex(k)/(G_baxter(-k)·
G_baxter_deriv(k))` **independent of `s`** (all of `residue_term`'s `s`-dependence is the single
factor `exp(I·k_n·s)`), the needed inner integral is the **zeroth** exponential moment `∫
exp(iks)`, not the first moment `∫ s·exp(iks)` originally anticipated — genuinely simpler, and
(unlike `OZExteriorBridge.lean`'s `inner_integral_bridge`) needs **no case split** on `r-t ≷ σ` at
this step: the closed form below is valid on any `[lo,hi]` including `[max(r-t,σ), r+t]` directly.
A case split only re-enters later (`B.5`), when matching `max(r-t,σ)` against `oz_forcing`'s own
`if r < σ+t` structure. -/

/-- **Zeroth-moment closed form** (`OZFIX.1`, B.2): mirrors `zeta0_formula`'s `HasDerivAt`+FTC
technique (`BaxterZeros.lean`) but for a general interval `[lo,hi]` (not the fixed `[0,σ]`) and
the `+I` sign convention matching `residue_term`'s `exp(I·k_n·r)` (not `zeta0_formula`'s `-I`). -/
theorem moment0_formula {k : ℂ} (hk : k ≠ 0) (lo hi : ℝ) :
    ∫ s in lo..hi, Complex.exp (Complex.I * k * s) =
      Complex.exp (Complex.I * k * hi) / (Complex.I * k) -
        Complex.exp (Complex.I * k * lo) / (Complex.I * k) := by
  have hc : (Complex.I * k) ≠ 0 := by simp [Complex.I_ne_zero, hk]
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => Complex.exp (Complex.I * k * s) / (Complex.I * k))
      (Complex.exp (Complex.I * k * s)) s := by
    intro s
    have h1 : HasDerivAt (fun z : ℂ => Complex.I * k * z) (Complex.I * k) (s:ℂ) := by
      have h2 : HasDerivAt (fun z : ℂ => z) (1:ℂ) (s:ℂ) := hasDerivAt_id (s:ℂ)
      simpa using h2.const_mul (Complex.I * k)
    have h4 := (h1.cexp).comp_ofReal
    have h5 := h4.div_const (Complex.I * k)
    refine h5.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun s => Complex.exp (Complex.I * k * s))
      MeasureTheory.volume lo hi := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  rw [integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hint]

/-! ### Task `OZFIX.3` — `h_explicit_term`'s antiderivative

Rather than interchanging the sum and the `s`-integral directly (the originally-planned route via
`MeasureTheory.hasSum_integral_of_dominated_convergence`), the more efficient route is to get
`h_explicit`'s own derivative as a termwise sum first (Mathlib's
`hasDerivAt_tsum_of_isPreconnected`, a Weierstrass-M-test-style differentiation-under-the-sum
theorem), then apply this project's
usual `HasDerivAt`+FTC pattern (`integral_eq_sub_of_hasDerivAt`) once, to the whole series at
once. This lemma is the per-term building block that theorem needs: `residue_term(·)(k)/(I·k)` is
an antiderivative of `residue_term(·)(k)` (dividing by `I·k` exactly cancels the `I·k` picked up
by differentiating `exp(I·k·r)`, mirroring `moment0_formula`'s internal antiderivative fact). -/
theorem residue_term_hasDerivAt {eta sigma rho : ℝ} {k : ℂ} (hk : k ≠ 0) (r : ℝ) :
    HasDerivAt (fun r : ℝ => residue_term eta sigma rho r k / (Complex.I * k))
      (residue_term eta sigma rho r k) r := by
  unfold residue_term
  set A : ℂ := k ^ 7 * Chat_complex eta sigma k /
    (G_baxter eta sigma rho (-k) * G_baxter_deriv eta sigma rho k) with hAdef
  have h1 : HasDerivAt (fun r : ℝ => Complex.exp (Complex.I * k * r) / (Complex.I * k))
      (Complex.exp (Complex.I * k * r)) r := by
    have hh1 : HasDerivAt (fun z : ℂ => Complex.I * k * z) (Complex.I * k) (r:ℂ) := by
      have hh2 : HasDerivAt (fun z : ℂ => z) (1:ℂ) (r:ℂ) := hasDerivAt_id (r:ℂ)
      simpa using hh2.const_mul (Complex.I * k)
    have hh4 := (hh1.cexp).comp_ofReal
    have hh5 := hh4.div_const (Complex.I * k)
    refine hh5.congr_deriv ?_
    field_simp
  have h2 := h1.const_mul A
  have h3 := h2.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem Filter.univ_mem (fun x _ => by
      change k ^ 7 * Chat_complex eta sigma k * Complex.exp (Complex.I * k * x) /
          (G_baxter eta sigma rho (-k) * G_baxter_deriv eta sigma rho k) / (Complex.I * k) =
        A * (Complex.exp (Complex.I * k * (x:ℂ)) / (Complex.I * k))
      rw [hAdef]; ring))
  refine h3.congr_deriv ?_
  rw [hAdef]; ring

/-- **`h_explicit_term`'s antiderivative** (`OZFIX.3`): the pole+mirror pairing of
`residue_term_hasDerivAt`, giving an explicit antiderivative of `h_explicit_term` — the per-term
piece `hasDerivAt_tsum_of_isPreconnected` needs to differentiate `h_explicit` termwise. -/
theorem h_explicit_term_hasDerivAt {eta sigma rho : ℝ} {k : ℂ} (hk : k ≠ 0) (r : ℝ) :
    HasDerivAt (fun r : ℝ => residue_term eta sigma rho r k / (Complex.I * k) +
        residue_term eta sigma rho r (-(starRingEnd ℂ) k) / (Complex.I * (-(starRingEnd ℂ) k)))
      (residue_term eta sigma rho r k + residue_term eta sigma rho r (-(starRingEnd ℂ) k)) r := by
  have hk' : -(starRingEnd ℂ) k ≠ 0 := by
    simpa using hk
  exact (residue_term_hasDerivAt hk r).add (residue_term_hasDerivAt hk' r)

/-- **`residue_term`'s magnitude is non-increasing in `r`** for `Im(k)≥0` (`OZFIX.3`
prerequisite): `‖exp(ikr)‖=exp(-r·Im(k))` decreases as `r` increases, so the value at any base
point `r1` dominates for all `r≥r1` — the uniform (`r`-independent) bound
`hasDerivAt_tsum_of_isPreconnected` needs on an interval `[r1,∞)`. -/
theorem residue_term_norm_le_of_le {eta sigma rho : ℝ} {k : ℂ} (hkim : 0 ≤ k.im)
    {r1 r : ℝ} (hr1r : r1 ≤ r) :
    ‖residue_term eta sigma rho r k‖ ≤ ‖residue_term eta sigma rho r1 k‖ := by
  unfold residue_term
  have hnum : ‖k ^ 7 * Chat_complex eta sigma k * Complex.exp (Complex.I * k * (r:ℂ))‖ ≤
      ‖k ^ 7 * Chat_complex eta sigma k * Complex.exp (Complex.I * k * (r1:ℂ))‖ := by
    conv_lhs => rw [norm_mul, Complex.norm_exp]
    conv_rhs => rw [norm_mul, Complex.norm_exp]
    have hre1 : (Complex.I * k * (r:ℂ)).re = -k.im * r := by
      simp [Complex.mul_re, Complex.mul_im]
    have hre2 : (Complex.I * k * (r1:ℂ)).re = -k.im * r1 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre1, hre2]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (by nlinarith [hkim, hr1r])
  rw [norm_div, norm_div]
  gcongr

/-- **`h_explicit_term`'s magnitude bound, uniform over `[r1,∞)`** (`OZFIX.3`
prerequisite for `hasDerivAt_tsum_of_isPreconnected`): extends `h_explicit_term_norm_bound`
(only stated at a single `r`) to hold for *every* `y≥r1`, using the same bound value (evaluated
at `r1`) throughout — via `residue_term_norm_le_of_le`'s monotonicity plus the triangle
inequality. This is the `y`-independent (only `n`-dependent) summable bound
`hasDerivAt_tsum_of_isPreconnected` needs on the open interval `Set.Ioi r1`. -/
theorem h_explicit_term_norm_bound_uniform {eta sigma rho r1 : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) (hr1 : sigma < r1) :
    ∃ C M : ℝ, 0 < C ∧ 1 ≤ M ∧ ∀ {k : ℂ}, G_baxter eta sigma rho k = 0 → 0 ≤ k.im → M ≤ ‖k‖ →
      ∀ {y : ℝ}, r1 ≤ y →
        ‖residue_term eta sigma rho y k + residue_term eta sigma rho y (-(starRingEnd ℂ) k)‖ ≤
          2 * C * ‖k‖ ^ (1 - 2 * r1 / sigma) := by
  obtain ⟨C, M, hCpos, hM1, hbound⟩ := residue_term_norm_bound heta0 heta1 hsigma hrho
    (hsigma.trans hr1)
  refine ⟨C, M, hCpos, hM1, ?_⟩
  intro k hzero hkim hkM y hr1y
  have hnormeq : ‖-(starRingEnd ℂ) k‖ = ‖k‖ := by rw [norm_neg, RCLike.norm_conj]
  have himeq : (-(starRingEnd ℂ) k).im = k.im := by simp [Complex.conj_im]
  have hzeroMirror : G_baxter eta sigma rho (-(starRingEnd ℂ) k) = 0 := G_baxter_zero_mirror hzero
  have hkimMirror : 0 ≤ (-(starRingEnd ℂ) k).im := by rw [himeq]; exact hkim
  have hkMMirror : M ≤ ‖(-(starRingEnd ℂ) k)‖ := by rw [hnormeq]; exact hkM
  have h1 := hbound hzero hkim hkM
  have h2 := hbound hzeroMirror hkimMirror hkMMirror
  rw [hnormeq] at h2
  have hmono1 : ‖residue_term eta sigma rho y k‖ ≤ ‖residue_term eta sigma rho r1 k‖ :=
    residue_term_norm_le_of_le hkim hr1y
  have hmono2 : ‖residue_term eta sigma rho y (-(starRingEnd ℂ) k)‖ ≤
      ‖residue_term eta sigma rho r1 (-(starRingEnd ℂ) k)‖ :=
    residue_term_norm_le_of_le hkimMirror hr1y
  calc ‖residue_term eta sigma rho y k + residue_term eta sigma rho y (-(starRingEnd ℂ) k)‖
      ≤ ‖residue_term eta sigma rho y k‖ +
        ‖residue_term eta sigma rho y (-(starRingEnd ℂ) k)‖ := norm_add_le _ _
    _ ≤ ‖residue_term eta sigma rho r1 k‖ + ‖residue_term eta sigma rho r1 (-(starRingEnd ℂ) k)‖ :=
        add_le_add hmono1 hmono2
    _ ≤ C * ‖k‖ ^ (1 - 2 * r1 / sigma) + C * ‖k‖ ^ (1 - 2 * r1 / sigma) := by linarith [h1, h2]
    _ = 2 * C * ‖k‖ ^ (1 - 2 * r1 / sigma) := by ring

/-- **`h_explicit_term`'s antiderivative series** (`OZFIX.3`): the pole+mirror
antiderivative from `h_explicit_term_hasDerivAt`, packaged as a function of `(n, r)` so it can be
summed over `n`. -/
noncomputable def Hterm (eta sigma rho : ℝ) (kfam : ℕ → ℂ) (n : ℕ) (r : ℝ) : ℂ :=
  residue_term eta sigma rho r (kfam n) / (Complex.I * kfam n) +
    residue_term eta sigma rho r (-(starRingEnd ℂ) (kfam n)) /
      (Complex.I * (-(starRingEnd ℂ) (kfam n)))

set_option maxHeartbeats 4000000 in
-- Large combined summability assembly (many `set`-introduced local defs accumulate a big
-- elaboration context, mirroring `residue_term_norm_bound`'s own need for extra budget); every
-- individual step is simple, but the proof as a whole is long.
/-- **`residue_term` pole+mirror pair, uniformly summable in `n` for every `y≥r0`** (`OZFIX.3`
prerequisite for `hasDerivAt_tsum_of_isPreconnected`, which needs the bound for
*every* `n` — not just cofinitely many, unlike `h_explicit_summable_of_pole_family`'s
`Summable.of_norm_bounded_eventually`-based proof). Deliberately bounds the **sum of the two
individual norms** (not `‖h_explicit_term‖`, the norm of their sum): `Hterm`'s two summands have
different denominators (`I·k_n` vs. `I·(-conj k_n)`), so `h_explicit_series_hasDerivAt`'s
antiderivative-summability step needs each piece controlled separately; a bound on
`‖h_explicit_term‖` alone would be too weak (triangle inequality only goes one way). The weaker
`‖h_explicit_term(y)‖ ≤ u n` bound follows trivially at any call site via `norm_add_le`. Built
from `residue_term_norm_bound` at `r0` plus `residue_term_norm_le_of_le`'s monotonicity (extending
validity to every `y≥r0`), with an explicit finite correction on `n<N` via
`summable_of_ne_finset_zero` covering the `n` too small for the asymptotic rate to kick in. -/
theorem h_explicit_term_uniform_summable_bound_of_pole_family {eta sigma rho r0 : ℝ}
    (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) (hr0 : sigma < r0)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n : ℕ, ∀ {y : ℝ}, r0 ≤ y →
        ‖residue_term eta sigma rho y (kfam n)‖ +
          ‖residue_term eta sigma rho y (-(starRingEnd ℂ) (kfam n))‖ ≤ u n := by
  obtain ⟨C, M, hCpos, hM1, hbound⟩ := residue_term_norm_bound heta0 heta1 hsigma hrho
    (hsigma.trans hr0)
  have hp : (1 - 2 * r0 / sigma : ℝ) < -1 := by
    have h2 : 1 < r0 / sigma := (lt_div_iff₀ hsigma).mpr (by linarith)
    have h3 : 2 * r0 / sigma = 2 * (r0 / sigma) := by ring
    linarith [h2, h3]
  have hp0 : (1 - 2 * r0 / sigma : ℝ) < 0 := by linarith
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (1 - 2 * r0 / sigma)) := Real.summable_nat_rpow.mpr hp
  have h1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 - 2 * r0 / sigma)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (1 - 2 * r0 / sigma)) 1).mpr h0
  have hg0' : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (1 - 2 * r0 / sigma)) := by
    convert h1 using 2 with n
    push_cast
    ring
  set g : ℕ → ℝ := fun n => 2 * C * (min c d) ^ (1 - 2 * r0 / sigma) * ((n : ℝ) + 1) ^
    (1 - 2 * r0 / sigma) with hgdef
  have hg : Summable g := by
    rw [hgdef]
    have := hg0'.mul_left (2 * C * (min c d) ^ (1 - 2 * r0 / sigma))
    simpa [mul_assoc] using this
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M ≤ c * (N : ℝ) + d := by
    obtain ⟨N, hN⟩ := exists_nat_ge ((M - d) / c)
    refine ⟨N, ?_⟩
    rw [div_le_iff₀ hc] at hN
    linarith [hN]
  have hgN : ∀ n : ℕ, N ≤ n →
      ‖residue_term eta sigma rho r0 (kfam n)‖ +
        ‖residue_term eta sigma rho r0 (-(starRingEnd ℂ) (kfam n))‖ ≤ g n := by
    intro n hn
    have hNn : M ≤ c * (n : ℝ) + d := by
      have hcn : c * (N : ℝ) ≤ c * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        exact_mod_cast hn
      linarith [hN, hcn]
    have hMk : M ≤ ‖kfam n‖ := le_trans hNn (hkfam_re n)
    have hnormeq : ‖-(starRingEnd ℂ) (kfam n)‖ = ‖kfam n‖ := by rw [norm_neg, RCLike.norm_conj]
    have himeq : (-(starRingEnd ℂ) (kfam n)).im = (kfam n).im := by
      simp only [Complex.neg_im, Complex.conj_im, neg_neg]
    have hzeroMirror : G_baxter eta sigma rho (-(starRingEnd ℂ) (kfam n)) = 0 :=
      G_baxter_zero_mirror (hkfam_zero n)
    have hkimMirror : 0 ≤ (-(starRingEnd ℂ) (kfam n)).im := by rw [himeq]; exact hkfam_im n
    have hkMMirror : M ≤ ‖(-(starRingEnd ℂ) (kfam n))‖ := by rw [hnormeq]; exact hMk
    have hb1 := hbound (hkfam_zero n) (hkfam_im n) hMk
    have hb2 := hbound hzeroMirror hkimMirror hkMMirror
    rw [hnormeq] at hb2
    have hLpos : 0 < c * (n : ℝ) + d := by
      have hcnn : (0:ℝ) ≤ c * (n:ℝ) := by positivity
      linarith [hM1, hNn]
    have hkpos : 0 < ‖kfam n‖ := lt_of_lt_of_le hLpos (hkfam_re n)
    have hnp1pos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have hmono : ‖kfam n‖ ^ (1 - 2 * r0 / sigma) ≤ (c * (n:ℝ) + d) ^ (1 - 2 * r0 / sigma) :=
      (Real.rpow_le_rpow_iff_of_neg hkpos hLpos hp0).mpr (hkfam_re n)
    have hminpos : 0 < min c d := lt_min hc hd
    have hcdge : (min c d) * ((n:ℝ) + 1) ≤ c * (n:ℝ) + d := by
      rcases le_or_gt c d with hle | hle
      · rw [min_eq_left hle]; nlinarith [Nat.cast_nonneg n (α := ℝ)]
      · rw [min_eq_right hle.le]; nlinarith [Nat.cast_nonneg n (α := ℝ), hle]
    have hmono2 : (c * (n:ℝ) + d) ^ (1 - 2 * r0 / sigma) ≤
        ((min c d) * ((n:ℝ) + 1)) ^ (1 - 2 * r0 / sigma) :=
      (Real.rpow_le_rpow_iff_of_neg hLpos (by positivity) hp0).mpr hcdge
    have hmono3 : ((min c d) * ((n:ℝ) + 1)) ^ (1 - 2 * r0 / sigma) =
        (min c d) ^ (1 - 2 * r0 / sigma) * ((n:ℝ) + 1) ^ (1 - 2 * r0 / sigma) :=
      Real.mul_rpow hminpos.le hnp1pos.le
    have hchain : ‖kfam n‖ ^ (1 - 2 * r0 / sigma) ≤
        (min c d) ^ (1 - 2 * r0 / sigma) * ((n:ℝ) + 1) ^ (1 - 2 * r0 / sigma) := by
      calc ‖kfam n‖ ^ (1 - 2 * r0 / sigma) ≤ (c * (n:ℝ) + d) ^ (1 - 2 * r0 / sigma) := hmono
        _ ≤ ((min c d) * ((n:ℝ) + 1)) ^ (1 - 2 * r0 / sigma) := hmono2
        _ = (min c d) ^ (1 - 2 * r0 / sigma) * ((n:ℝ) + 1) ^ (1 - 2 * r0 / sigma) := hmono3
    calc ‖residue_term eta sigma rho r0 (kfam n)‖ +
        ‖residue_term eta sigma rho r0 (-(starRingEnd ℂ) (kfam n))‖ ≤
        C * ‖kfam n‖ ^ (1 - 2 * r0 / sigma) + C * ‖kfam n‖ ^ (1 - 2 * r0 / sigma) := by
          linarith [hb1, hb2]
      _ = 2 * C * ‖kfam n‖ ^ (1 - 2 * r0 / sigma) := by ring
      _ ≤ 2 * C * ((min c d) ^ (1 - 2 * r0 / sigma) * ((n:ℝ) + 1) ^ (1 - 2 * r0 / sigma)) :=
          mul_le_mul_of_nonneg_left hchain (by positivity)
      _ = g n := by rw [hgdef]; ring
  set u : ℕ → ℝ := fun n => g n +
    (if n ∈ Finset.range N then
      ‖residue_term eta sigma rho r0 (kfam n)‖ +
        ‖residue_term eta sigma rho r0 (-(starRingEnd ℂ) (kfam n))‖
      else 0) with hudef
  have hufin : Summable (fun n : ℕ => (if n ∈ Finset.range N then
      ‖residue_term eta sigma rho r0 (kfam n)‖ +
        ‖residue_term eta sigma rho r0 (-(starRingEnd ℂ) (kfam n))‖ else 0)) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro b hb
    simp [hb]
  have hu : Summable u := hg.add hufin
  refine ⟨u, hu, fun n y hy => ?_⟩
  have hkim' : 0 ≤ (-(starRingEnd ℂ) (kfam n)).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hkfam_im n
  have hstep : ‖residue_term eta sigma rho y (kfam n)‖ +
      ‖residue_term eta sigma rho y (-(starRingEnd ℂ) (kfam n))‖ ≤
      ‖residue_term eta sigma rho r0 (kfam n)‖ +
        ‖residue_term eta sigma rho r0 (-(starRingEnd ℂ) (kfam n))‖ :=
    add_le_add (residue_term_norm_le_of_le (hkfam_im n) hy)
      (residue_term_norm_le_of_le hkim' hy)
  rcases lt_or_ge n N with hn | hn
  · have hun : u n = g n + (‖residue_term eta sigma rho r0 (kfam n)‖ +
        ‖residue_term eta sigma rho r0 (-(starRingEnd ℂ) (kfam n))‖) := by
      change g n + (if n ∈ Finset.range N then _ else 0) = _
      simp [Finset.mem_range.mpr hn]
    have hg_nonneg : 0 ≤ g n := by rw [hgdef]; positivity
    rw [hun]; linarith [hstep, hg_nonneg]
  · have hgb := hgN n hn
    have hun : g n ≤ u n := by
      change g n ≤ g n + (if n ∈ Finset.range N then _ else 0)
      have hthis : (if n ∈ Finset.range N then
          ‖residue_term eta sigma rho r0 (kfam n)‖ +
            ‖residue_term eta sigma rho r0 (-(starRingEnd ℂ) (kfam n))‖ else (0:ℝ)) = 0 := by
        simp [Finset.mem_range, not_lt.mpr hn]
      linarith [hthis]
    linarith [hgb, hun]

set_option maxHeartbeats 4000000 in
-- Large combined assembly (many local defs, mirroring the previous theorem's need); every
-- individual step is simple, but the proof as a whole is long.
/-- **`h_explicit`'s own derivative, as a termwise sum** (`OZFIX.3` payoff): for a
concrete pole family (`G_baxter`-zeros, `Im≥0`, linear `‖kfam n‖` growth), `∑' n, Hterm(n)(z)` is
differentiable at any `r` past a threshold `r0>σ`, with derivative `∑' n, h_explicit_term(n)(r)`
— exactly `2πr·h_explicit(r)`'s own (complex, pre-`Re`) numerator. Proved via Mathlib's
`hasDerivAt_tsum_of_isPreconnected` (a Weierstrass-M-test differentiation-under-the-sum theorem)
on `t := Set.Ioi r0`, **not** a raw sum/integral interchange: the uniform bound is
`h_explicit_term_uniform_summable_bound_of_pole_family`; the antiderivative series' convergence at
the base point `r` (which must lie in the *open* set `t`, hence strictly `>r0`) reuses the same
bound, via one more application of `residue_term_norm_le_of_le`'s monotonicity bringing the bound
at `r` down to the bound at `r0`. -/
theorem h_explicit_series_hasDerivAt {eta sigma rho r0 r : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) (hr0 : sigma < r0) (hr0r : r0 < r)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    (hkfam_ne : ∀ n, kfam n ≠ 0) :
    HasDerivAt (fun z => ∑' n, Hterm eta sigma rho kfam n z)
      (∑' n, h_explicit_term eta sigma rho r kfam n) r := by
  obtain ⟨u, hu, hub⟩ := h_explicit_term_uniform_summable_bound_of_pole_family heta0 heta1 hsigma
    hrho hr0 hc hd hkfam_zero hkfam_im hkfam_re
  have hu_nonneg : ∀ n, 0 ≤ u n := fun n =>
    le_trans (by positivity) (hub n le_rfl)
  have hv_le : ∀ n : ℕ, u n / (c * (n:ℝ) + d) ≤ u n / d := by
    intro n
    have hden1 : d ≤ c * (n:ℝ) + d := by nlinarith [hc, Nat.cast_nonneg n (α := ℝ)]
    exact div_le_div_of_nonneg_left (hu_nonneg n) hd hden1
  have hv_summable : Summable (fun n : ℕ => u n / (c * (n:ℝ) + d)) := by
    apply Summable.of_nonneg_of_le
      (fun n => div_nonneg (hu_nonneg n) (by nlinarith [hc, hd, Nat.cast_nonneg n (α := ℝ)]))
      hv_le
    simpa using hu.div_const d
  have hH0 : Summable (fun n => Hterm eta sigma rho kfam n r) := by
    apply Summable.of_norm_bounded hv_summable
    intro n
    unfold Hterm
    have hkim' : 0 ≤ (-(starRingEnd ℂ) (kfam n)).im := by
      simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hkfam_im n
    have hnormeq : ‖-(starRingEnd ℂ) (kfam n)‖ = ‖kfam n‖ := by rw [norm_neg, RCLike.norm_conj]
    calc ‖residue_term eta sigma rho r (kfam n) / (Complex.I * kfam n) +
        residue_term eta sigma rho r (-(starRingEnd ℂ) (kfam n)) /
          (Complex.I * (-(starRingEnd ℂ) (kfam n)))‖
        ≤ ‖residue_term eta sigma rho r (kfam n) / (Complex.I * kfam n)‖ +
          ‖residue_term eta sigma rho r (-(starRingEnd ℂ) (kfam n)) /
            (Complex.I * (-(starRingEnd ℂ) (kfam n)))‖ := norm_add_le _ _
      _ = ‖residue_term eta sigma rho r (kfam n)‖ / ‖kfam n‖ +
          ‖residue_term eta sigma rho r (-(starRingEnd ℂ) (kfam n))‖ / ‖kfam n‖ := by
          rw [norm_div, norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul, hnormeq]
      _ ≤ ‖residue_term eta sigma rho r0 (kfam n)‖ / ‖kfam n‖ +
          ‖residue_term eta sigma rho r0 (-(starRingEnd ℂ) (kfam n))‖ / ‖kfam n‖ := by
          have hkpos : 0 < ‖kfam n‖ := lt_of_lt_of_le
            (by nlinarith [hc, hd, Nat.cast_nonneg n (α := ℝ)]) (hkfam_re n)
          gcongr
          · exact residue_term_norm_le_of_le (hkfam_im n) hr0r.le
          · exact residue_term_norm_le_of_le hkim' hr0r.le
      _ = (‖residue_term eta sigma rho r0 (kfam n)‖ +
          ‖residue_term eta sigma rho r0 (-(starRingEnd ℂ) (kfam n))‖) / ‖kfam n‖ := by ring
      _ ≤ (‖residue_term eta sigma rho r0 (kfam n)‖ +
          ‖residue_term eta sigma rho r0 (-(starRingEnd ℂ) (kfam n))‖) / (c * (n:ℝ) + d) := by
          apply div_le_div_of_nonneg_left _ (by nlinarith [hc, hd, Nat.cast_nonneg n (α := ℝ)])
            (hkfam_re n)
          positivity
      _ ≤ u n / (c * (n:ℝ) + d) := by
          apply div_le_div_of_nonneg_right (hub n le_rfl)
          nlinarith [hc, hd, Nat.cast_nonneg n (α := ℝ)]
  have hderiv : ∀ n (y : ℝ), y ∈ Set.Ioi r0 →
      HasDerivAt (Hterm eta sigma rho kfam n) (h_explicit_term eta sigma rho y kfam n) y := by
    intro n y _
    exact h_explicit_term_hasDerivAt (hkfam_ne n) y
  have hbnd : ∀ n (y : ℝ), y ∈ Set.Ioi r0 → ‖h_explicit_term eta sigma rho y kfam n‖ ≤ u n := by
    intro n y hy
    unfold h_explicit_term
    exact (norm_add_le _ _).trans (hub n (le_of_lt hy))
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hderiv hbnd
    (Set.mem_Ioi.mpr hr0r) hH0 (Set.mem_Ioi.mpr hr0r)

/-- **`oz_linear_op`'s inner integral in closed form** (`OZFIX.3` payoff, FTC form):
the closed-form antiderivative of `∑'n, h_explicit_term(n)(s)`, via `h_explicit_series_hasDerivAt`
+ this project's usual `HasDerivAt`+FTC pattern (`integral_eq_sub_of_hasDerivAt`). Continuity of
the integrand (needed for `IntervalIntegrable`) is a Weierstrass-M-test consequence
(`continuousOn_tsum`) of the same uniform bound. -/
theorem h_explicit_series_integral {eta sigma rho r0 : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) (hr0 : sigma < r0)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    (hkfam_ne : ∀ n, kfam n ≠ 0)
    {lo hi : ℝ} (hlo : r0 < lo) (hloi : lo ≤ hi) :
    ∫ s in lo..hi, (∑' n, h_explicit_term eta sigma rho s kfam n) =
      (∑' n, Hterm eta sigma rho kfam n hi) - (∑' n, Hterm eta sigma rho kfam n lo) := by
  obtain ⟨u, hu, hub⟩ := h_explicit_term_uniform_summable_bound_of_pole_family heta0 heta1
    hsigma hrho hr0 hc hd hkfam_zero hkfam_im hkfam_re
  have hcont_term : ∀ n : ℕ, Continuous (fun s : ℝ => h_explicit_term eta sigma rho s kfam n) := by
    intro n
    unfold h_explicit_term residue_term
    fun_prop
  have hcontOn : ContinuousOn (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n)
      (Set.Ici r0) :=
    continuousOn_tsum (fun n => (hcont_term n).continuousOn) hu (fun n y hy => by
      unfold h_explicit_term
      exact (norm_add_le _ _).trans (hub n hy))
  have hderiv : ∀ s ∈ Set.uIcc lo hi,
      HasDerivAt (fun z => ∑' n, Hterm eta sigma rho kfam n z)
        (∑' n, h_explicit_term eta sigma rho s kfam n) s := by
    intro s hs
    rw [Set.uIcc_of_le hloi] at hs
    have hr0s : r0 < s := lt_of_lt_of_le hlo hs.1
    exact h_explicit_series_hasDerivAt heta0 heta1 hsigma hrho hr0 hr0s hc hd hkfam_zero hkfam_im
      hkfam_re hkfam_ne
  have hint : IntervalIntegrable (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n)
      MeasureTheory.volume lo hi := by
    apply ContinuousOn.intervalIntegrable
    apply hcontOn.mono
    rw [Set.uIcc_of_le hloi]
    intro x hx
    exact le_trans hlo.le hx.1
  exact integral_eq_sub_of_hasDerivAt hderiv hint

/-! ### Task `OZFIX.4` — `Hterm`'s summability extends down to `r=σ`

`oz_linear_op`'s inner integral has lower endpoint `max(r-t,σ)`, which can equal `σ` exactly (when
`r≤σ+t`) — but `h_explicit`'s own series is only known summable for `r>σ` strictly (matching the
PY hard-sphere contact discontinuity). The fix: `residue_term_norm_bound` turned out to need only
`0<r`, not `σ<r` (an unused hypothesis, `1.3` discovery) — so `Hterm`'s *own* series (one power of
`‖k‖` better than `h_explicit_term`'s, from the extra `1/(I·k_n)` factor) is summable already at
`r=σ` (effective exponent `-2`, comfortably `<-1`), even though `h_explicit_term`'s own series
(exponent `-1` at `r=σ`) is not. This lets `oz_linear_op`'s inner integral be evaluated via a
*one-sided* FTC (`integral_eq_sub_of_hasDerivAt_of_le`: continuous on the closed interval,
differentiable only on the open interior) instead of the two-sided `h_explicit_series_integral`
used elsewhere. -/

/-- **`Hterm`'s magnitude, uniformly summable in `n`, for every `y≥σ`** (`OZFIX.4`): the
uniform bound `continuousOn_tsum` needs on `Set.Icc σ hi` (any `hi`), and in particular the base
case a one-sided FTC needs at `oz_linear_op`'s inner integral's lower endpoint `σ`. -/
theorem Hterm_uniform_summable_bound_of_pole_family {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n : ℕ, ∀ {y : ℝ}, sigma ≤ y → ‖Hterm eta sigma rho kfam n y‖ ≤ u n := by
  obtain ⟨C, M, hCpos, hM1, hbound⟩ := residue_term_norm_bound heta0 heta1 hsigma hrho hsigma
  have hexp1 : (1:ℝ) - 2 * sigma / sigma = -1 := by field_simp; norm_num
  rw [hexp1] at hbound
  set p : ℝ := -2 with hpdef
  have hp0 : p < 0 := by rw [hpdef]; norm_num
  have hp1 : p < -1 := by rw [hpdef]; norm_num
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ p) := Real.summable_nat_rpow.mpr hp1
  have h1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ p) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ p) 1).mpr h0
  have hg0' : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
    convert h1 using 2 with n
    push_cast
    ring
  set g : ℕ → ℝ := fun n => 2 * C * (min c d) ^ p * ((n : ℝ) + 1) ^ p with hgdef
  have hg : Summable g := by
    rw [hgdef]
    have := hg0'.mul_left (2 * C * (min c d) ^ p)
    simpa [mul_assoc] using this
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M ≤ c * (N : ℝ) + d := by
    obtain ⟨N, hN⟩ := exists_nat_ge ((M - d) / c)
    refine ⟨N, ?_⟩
    rw [div_le_iff₀ hc] at hN
    linarith [hN]
  -- Central quantity: the sum of the two `residue_term` norms *at σ*, divided by `‖kfam n‖`.
  -- `‖Hterm(n)(y)‖` (any `y≥σ`) is bounded by this (triangle inequality + monotonicity down to
  -- `σ`); `corrOverK` itself is bounded by `g n` (the same `residue_term_norm_bound`-based decay
  -- rate as before, now with an extra `1/‖k‖` from the division baked into `p`).
  set corrOverK : ℕ → ℝ := fun n => (‖residue_term eta sigma rho sigma (kfam n)‖ +
    ‖residue_term eta sigma rho sigma (-(starRingEnd ℂ) (kfam n))‖) / ‖kfam n‖ with hcorrdef
  have hgN : ∀ n : ℕ, N ≤ n → corrOverK n ≤ g n := by
    intro n hn
    have hNn : M ≤ c * (n : ℝ) + d := by
      have hcn : c * (N : ℝ) ≤ c * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        exact_mod_cast hn
      linarith [hN, hcn]
    have hMk : M ≤ ‖kfam n‖ := le_trans hNn (hkfam_re n)
    have hnormeq : ‖-(starRingEnd ℂ) (kfam n)‖ = ‖kfam n‖ := by rw [norm_neg, RCLike.norm_conj]
    have himeq : (-(starRingEnd ℂ) (kfam n)).im = (kfam n).im := by
      simp only [Complex.neg_im, Complex.conj_im, neg_neg]
    have hzeroMirror : G_baxter eta sigma rho (-(starRingEnd ℂ) (kfam n)) = 0 :=
      G_baxter_zero_mirror (hkfam_zero n)
    have hkimMirror : 0 ≤ (-(starRingEnd ℂ) (kfam n)).im := by rw [himeq]; exact hkfam_im n
    have hkMMirror : M ≤ ‖(-(starRingEnd ℂ) (kfam n))‖ := by rw [hnormeq]; exact hMk
    have hb1 := hbound (hkfam_zero n) (hkfam_im n) hMk
    have hb2 := hbound hzeroMirror hkimMirror hkMMirror
    rw [hnormeq] at hb2
    have hLpos : 0 < c * (n : ℝ) + d := by
      have hcnn : (0:ℝ) ≤ c * (n:ℝ) := by positivity
      linarith [hM1, hNn]
    have hkpos : 0 < ‖kfam n‖ := lt_of_lt_of_le hLpos (hkfam_re n)
    have hnp1pos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have hinv1 : ‖kfam n‖ ^ (-1:ℝ) / ‖kfam n‖ = ‖kfam n‖ ^ p := by
      rw [hpdef, div_eq_mul_inv, ← Real.rpow_neg_one ‖kfam n‖, ← Real.rpow_add hkpos]
      norm_num
    have hcorr_le : corrOverK n ≤ 2 * C * ‖kfam n‖ ^ p := by
      rw [hcorrdef]
      calc (‖residue_term eta sigma rho sigma (kfam n)‖ +
          ‖residue_term eta sigma rho sigma (-(starRingEnd ℂ) (kfam n))‖) / ‖kfam n‖
          ≤ (C * ‖kfam n‖ ^ (-1:ℝ) + C * ‖kfam n‖ ^ (-1:ℝ)) / ‖kfam n‖ := by
            apply div_le_div_of_nonneg_right _ hkpos.le
            linarith [hb1, hb2]
        _ = 2 * C * (‖kfam n‖ ^ (-1:ℝ) / ‖kfam n‖) := by ring
        _ = 2 * C * ‖kfam n‖ ^ p := by rw [hinv1]
    have hmono : ‖kfam n‖ ^ p ≤ (c * (n:ℝ) + d) ^ p :=
      (Real.rpow_le_rpow_iff_of_neg hkpos hLpos hp0).mpr (hkfam_re n)
    have hminpos : 0 < min c d := lt_min hc hd
    have hcdge : (min c d) * ((n:ℝ) + 1) ≤ c * (n:ℝ) + d := by
      rcases le_or_gt c d with hle | hle
      · rw [min_eq_left hle]; nlinarith [Nat.cast_nonneg n (α := ℝ)]
      · rw [min_eq_right hle.le]; nlinarith [Nat.cast_nonneg n (α := ℝ), hle]
    have hmono2 : (c * (n:ℝ) + d) ^ p ≤ ((min c d) * ((n:ℝ) + 1)) ^ p :=
      (Real.rpow_le_rpow_iff_of_neg hLpos (by positivity) hp0).mpr hcdge
    have hmono3 : ((min c d) * ((n:ℝ) + 1)) ^ p = (min c d) ^ p * ((n:ℝ) + 1) ^ p :=
      Real.mul_rpow hminpos.le hnp1pos.le
    have hchain : ‖kfam n‖ ^ p ≤ (min c d) ^ p * ((n:ℝ) + 1) ^ p := by
      calc ‖kfam n‖ ^ p ≤ (c * (n:ℝ) + d) ^ p := hmono
        _ ≤ ((min c d) * ((n:ℝ) + 1)) ^ p := hmono2
        _ = (min c d) ^ p * ((n:ℝ) + 1) ^ p := hmono3
    calc corrOverK n ≤ 2 * C * ‖kfam n‖ ^ p := hcorr_le
      _ ≤ 2 * C * ((min c d) ^ p * ((n:ℝ) + 1) ^ p) :=
          mul_le_mul_of_nonneg_left hchain (by positivity)
      _ = g n := by rw [hgdef]; ring
  set u : ℕ → ℝ := fun n => g n + (if n ∈ Finset.range N then corrOverK n else 0) with hudef
  have hufin : Summable (fun n : ℕ => (if n ∈ Finset.range N then corrOverK n else 0)) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro b hb
    simp [hb]
  have hu : Summable u := hg.add hufin
  have hu_corr : ∀ n : ℕ, corrOverK n ≤ u n := by
    intro n
    rcases lt_or_ge n N with hn | hn
    · have hun : u n = g n + corrOverK n := by
        change g n + (if n ∈ Finset.range N then _ else 0) = _
        simp [Finset.mem_range.mpr hn]
      have hg_nonneg : 0 ≤ g n := by rw [hgdef]; positivity
      rw [hun]; linarith [hg_nonneg]
    · have hgb := hgN n hn
      have hun : g n ≤ u n := by
        change g n ≤ g n + (if n ∈ Finset.range N then _ else 0)
        have hthis : (if n ∈ Finset.range N then corrOverK n else (0:ℝ)) = 0 := by
          simp [Finset.mem_range, not_lt.mpr hn]
        linarith [hthis]
      linarith [hgb, hun]
  refine ⟨u, hu, fun n {y} hy => ?_⟩
  have hkpos : 0 < ‖kfam n‖ := by
    have h1 : (0:ℝ) < c * (n:ℝ) + d := by positivity
    linarith [hkfam_re n, h1]
  have hkim' : 0 ≤ (-(starRingEnd ℂ) (kfam n)).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hkfam_im n
  have hnormeq : ‖-(starRingEnd ℂ) (kfam n)‖ = ‖kfam n‖ := by rw [norm_neg, RCLike.norm_conj]
  have hstep : ‖Hterm eta sigma rho kfam n y‖ ≤ corrOverK n := by
    rw [hcorrdef]
    unfold Hterm
    calc ‖residue_term eta sigma rho y (kfam n) / (Complex.I * kfam n) +
        residue_term eta sigma rho y (-(starRingEnd ℂ) (kfam n)) /
          (Complex.I * (-(starRingEnd ℂ) (kfam n)))‖
        ≤ ‖residue_term eta sigma rho y (kfam n) / (Complex.I * kfam n)‖ +
          ‖residue_term eta sigma rho y (-(starRingEnd ℂ) (kfam n)) /
            (Complex.I * (-(starRingEnd ℂ) (kfam n)))‖ := norm_add_le _ _
      _ = ‖residue_term eta sigma rho y (kfam n)‖ / ‖kfam n‖ +
          ‖residue_term eta sigma rho y (-(starRingEnd ℂ) (kfam n))‖ / ‖kfam n‖ := by
          rw [norm_div, norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul, hnormeq]
      _ ≤ ‖residue_term eta sigma rho sigma (kfam n)‖ / ‖kfam n‖ +
          ‖residue_term eta sigma rho sigma (-(starRingEnd ℂ) (kfam n))‖ / ‖kfam n‖ := by
          gcongr
          · exact residue_term_norm_le_of_le (hkfam_im n) hy
          · exact residue_term_norm_le_of_le hkim' hy
      _ = (‖residue_term eta sigma rho sigma (kfam n)‖ +
          ‖residue_term eta sigma rho sigma (-(starRingEnd ℂ) (kfam n))‖) / ‖kfam n‖ := by ring
  linarith [hstep, hu_corr n]

/-- **`oz_linear_op`'s inner integral in closed form, down to the boundary `lo=σ`** (`OZFIX.4`,
`1.3`): the two-sided `h_explicit_series_integral` needs `HasDerivAt` at *every* point of
`[lo,hi]`, which fails exactly at `lo=σ` (`h_explicit_term`'s own series is not summable there —
the genuine PY hard-sphere contact discontinuity). This version uses Mathlib's *one-sided* FTC
(`integral_eq_sub_of_hasDerivAt_of_le`: continuous on the closed interval, differentiable only on
the open interior) instead: `Hterm`'s antiderivative series **is** continuous down to `σ`
(`Hterm_uniform_summable_bound_of_pole_family`, one power of `‖k‖` better than `h_explicit_term`'s
own decay), and the derivative fact only needs to hold on the *open* interior `(σ,hi)`
(`h_explicit_series_hasDerivAt`, instantiated with a threshold `(σ+x)/2` for each interior point
`x`). What remains genuinely open is `hint`: `IntervalIntegrable` of `h_explicit_term`'s own sum
on `[σ,hi]`. This is *not* a Lean-bookkeeping gap — a direct check shows even the worst-case
(triangle-inequality) magnitude bound on the sum fails to be integrable near `σ` (its own integral
diverges like `∑ 1/(n·ln n)`), so closing it needs genuine cancellation/oscillation structure in
the residue sum, comparable in depth to `oz_h_exterior_regularity` (`JumpAsymptotic.lean`) — which
covers the analogous fact for the opaque, already-identified `oz_h`, not the concrete `h_explicit`
construction used here (adapting that axiom's own proof technique, a Fourier–Tauberian jump-
asymptotic argument via `CONTACT.3`/`CONTACT.4`, would need an independent derivation of
`h_explicit`'s own large-`k` Fourier asymptotic — investigated and confirmed to be a genuinely
separate undertaking, not a quick reuse). Carried here as an explicit hypothesis, matching this
project's established pattern for hard, currently-open analytic gaps (`hstep`,
`oz_h_exterior_regularity`). -/
theorem h_explicit_series_integral_from_sigma {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    (hkfam_ne : ∀ n, kfam n ≠ 0)
    {hi : ℝ} (hhi : sigma < hi)
    (hint : IntervalIntegrable (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n)
      MeasureTheory.volume sigma hi) :
    ∫ s in sigma..hi, (∑' n, h_explicit_term eta sigma rho s kfam n) =
      (∑' n, Hterm eta sigma rho kfam n hi) - (∑' n, Hterm eta sigma rho kfam n sigma) := by
  obtain ⟨u, hu, hub⟩ := Hterm_uniform_summable_bound_of_pole_family heta0 heta1 hsigma hrho hc hd
    hkfam_zero hkfam_im hkfam_re
  have hcont_res : ∀ k : ℂ, Continuous (fun s : ℝ => residue_term eta sigma rho s k) := by
    intro k
    unfold residue_term
    fun_prop
  have hcont_term : ∀ n : ℕ, Continuous (fun s : ℝ => Hterm eta sigma rho kfam n s) := by
    intro n
    unfold Hterm
    exact (hcont_res (kfam n)).div_const _ |>.add
      ((hcont_res (-(starRingEnd ℂ) (kfam n))).div_const _)
  have hcontOn : ContinuousOn (fun s => ∑' n, Hterm eta sigma rho kfam n s)
      (Set.Icc sigma hi) :=
    continuousOn_tsum (fun n => (hcont_term n).continuousOn) hu (fun n y hy => hub n hy.1)
  have hderiv : ∀ x ∈ Set.Ioo sigma hi,
      HasDerivAt (fun z => ∑' n, Hterm eta sigma rho kfam n z)
        (∑' n, h_explicit_term eta sigma rho x kfam n) x := by
    intro x hx
    exact h_explicit_series_hasDerivAt heta0 heta1 hsigma hrho
      (show sigma < (sigma + x) / 2 by linarith [hx.1])
      (show (sigma + x) / 2 < x by linarith [hx.1]) hc hd hkfam_zero hkfam_im hkfam_re hkfam_ne
  exact integral_eq_sub_of_hasDerivAt_of_le hhi.le hcontOn hderiv hint

/-- **`oz_linear_op`'s inner integral of `s·h_explicit(s)` itself** (`OZFIX.3`): the `s` in
`oz_linear_op`'s `∫ s·h(s)` cancels against `h_explicit`'s own `1/(2πs)` prefactor
(`s·h_explicit(s) = (1/(2π))·Re[∑'n,h_explicit_term(n)(s)]`), and `Re` commutes with the interval
integral (`intervalIntegral_re`) — combined with `h_explicit_series_integral`, this gives
`oz_linear_op`'s inner integral directly, for `lo` strictly past the threshold `r0`. -/
theorem s_mul_h_explicit_integral {eta sigma rho r0 lo hi : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (hr0 : sigma < r0) (hlo : r0 < lo) (hloi : lo ≤ hi)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    (hkfam_ne : ∀ n, kfam n ≠ 0) :
    ∫ s in lo..hi, s * h_explicit eta sigma rho s kfam =
      (1 / (2 * Real.pi)) *
        ((∑' n, Hterm eta sigma rho kfam n hi) - (∑' n, Hterm eta sigma rho kfam n lo)).re := by
  have hlopos : 0 < lo := lt_trans (lt_trans hsigma hr0) hlo
  have hpt : ∀ s ∈ Set.uIcc lo hi, s * h_explicit eta sigma rho s kfam =
      (1 / (2 * Real.pi)) * (∑' n, h_explicit_term eta sigma rho s kfam n).re := by
    intro s hs
    rw [Set.uIcc_of_le hloi] at hs
    have hspos : (0:ℝ) < s := lt_of_lt_of_le hlopos hs.1
    unfold h_explicit
    field_simp
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_const_mul]
  have hintegrable : IntervalIntegrable (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n)
      MeasureTheory.volume lo hi := by
    apply ContinuousOn.intervalIntegrable
    obtain ⟨u, hu, hub⟩ := h_explicit_term_uniform_summable_bound_of_pole_family heta0 heta1
      hsigma hrho hr0 hc hd hkfam_zero hkfam_im hkfam_re
    have hcont_term : ∀ n : ℕ,
        Continuous (fun s : ℝ => h_explicit_term eta sigma rho s kfam n) := by
      intro n
      unfold h_explicit_term residue_term
      fun_prop
    have hcontOn : ContinuousOn (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n)
        (Set.Ici r0) := continuousOn_tsum (fun n => (hcont_term n).continuousOn) hu
      (fun n y hy => by unfold h_explicit_term; exact (norm_add_le _ _).trans (hub n hy))
    apply hcontOn.mono
    rw [Set.uIcc_of_le hloi]
    intro x hx
    exact le_trans hlo.le hx.1
  change 1 / (2 * Real.pi) *
      ∫ x in lo..hi, RCLike.re (∑' n, h_explicit_term eta sigma rho x kfam n) = _
  rw [intervalIntegral_re hintegrable,
    h_explicit_series_integral heta0 heta1 hsigma hrho hr0 hc hd hkfam_zero hkfam_im
      hkfam_re hkfam_ne hlo hloi]
  rfl

/-- **`oz_linear_op`'s inner integral of `s·h_explicit(s)`, down to the boundary `lo=σ`**
(`OZFIX.5`'s prerequisite): the `_from_sigma` counterpart of `s_mul_h_explicit_integral`, needed
because `oz_linear_op`'s inner integral's lower endpoint `max(r-t,σ)` equals `σ` exactly whenever
`r≤σ+t`. Same `Re`/integral-commutation technique, but built on
`h_explicit_series_integral_from_sigma` (one-sided FTC, `OZFIX.4`) instead of the two-sided
`h_explicit_series_integral`, so it inherits that theorem's `hint` hypothesis. -/
theorem s_mul_h_explicit_integral_from_sigma {eta sigma rho hi : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) (hhi : sigma < hi)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    (hkfam_ne : ∀ n, kfam n ≠ 0)
    (hint : IntervalIntegrable (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n)
      MeasureTheory.volume sigma hi) :
    ∫ s in sigma..hi, s * h_explicit eta sigma rho s kfam =
      (1 / (2 * Real.pi)) *
        ((∑' n, Hterm eta sigma rho kfam n hi) - (∑' n, Hterm eta sigma rho kfam n sigma)).re := by
  have hpt : ∀ s ∈ Set.uIcc sigma hi, s * h_explicit eta sigma rho s kfam =
      (1 / (2 * Real.pi)) * (∑' n, h_explicit_term eta sigma rho s kfam n).re := by
    intro s hs
    rw [Set.uIcc_of_le hhi.le] at hs
    have hspos : (0:ℝ) < s := lt_of_lt_of_le hsigma hs.1
    unfold h_explicit
    field_simp
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_const_mul]
  change 1 / (2 * Real.pi) *
      ∫ x in sigma..hi, RCLike.re (∑' n, h_explicit_term eta sigma rho x kfam n) = _
  rw [intervalIntegral_re hint,
    h_explicit_series_integral_from_sigma heta0 heta1 hsigma hrho hc hd hkfam_zero hkfam_im
      hkfam_re hkfam_ne hhi hint]
  rfl

end HardSphere

end FMSA
