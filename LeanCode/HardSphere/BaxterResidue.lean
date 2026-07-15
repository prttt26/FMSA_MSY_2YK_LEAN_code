/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterPoles
import LeanCode.HardSphere.RadialFourierCHSComplex

/-!
# Task BAXTER.12 — residue formula + `h_explicit` (in progress)

## Status

**B.1 — residue-at-a-simple-pole fact: DONE**, and considerably simpler than the original scope
anticipated. The plan called for deriving this from Cauchy's integral formula
(`DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul`) + the circle-integral API — both
confirmed present in this Mathlib snapshot but unused anywhere in this codebase. Turned out
**unnecessary**: the classical alternative characterization of a simple-pole residue,
`Res_{z0}[f] = lim_{z→z0} (z-z0)·f(z)`, is provable directly from `HasDerivAt`'s own definition
(`hasDerivAt_iff_tendsto_slope`) plus elementary limit algebra (`Filter.Tendsto.inv₀`,
`Filter.Tendsto.mul`) — no circle integrals, no Cauchy's formula, no new Mathlib subsystem
needed. `residue_of_simple_pole` below is fully general (`N`, `D : ℂ → ℂ`, `D` merely
differentiable with a simple zero at `z0`), not tied to `G_baxter`/`Qhat_complex` specifics.

**What's left for the rest of `BAXTER.12` (not attempted this pass, honestly larger than the
original scope suggested):**

1. **Assembling the actual physical residue formula needs a new complex-valued `Ĉ`.** The
   target residue is of `f(k) = k·Ĉ(k)·e^{ikr}/[(1-ρQ̂(k))(1-ρQ̂(-k))]` at each pole `k_n` of
   `1-ρQ̂(k)` (from `BAXTER.11`). `Ĉ(k) := radial_fourier (c_HS eta sigma) k` is currently only
   defined for **real** `k` (`RadialFourierCHS.lean`, Task OZ.8) — extending it to complex `k`
   in closed form, entire, is its own `BAXTER.9`-style undertaking (a new closed-form/entireness
   pair), not yet started. Without it, the residue formula can't even be *stated* precisely.
2. Given (1), derive `Res_n = N_res(k_n)/D_res'(k_n)` via `residue_of_simple_pole`, with
   `D_res(k) := 1-ρQ̂(k) = G_baxter(k)/(-ik)³` (`k≠0`) and `N_res(k) := k·Ĉ_complex(k)·e^{ikr}/
   (1-ρQ̂(-k))` — mechanical once (1) exists, using `baxter_cube_mul_F_eq_G` and
   `G_baxter`'s already-proven entireness/derivative structure.
3. **B.2 — mirror pole family.** `BAXTER.11`'s `Qhat_complex_zeros_infinite` only gives the
   upper-half-plane, positive-real-part family; the sine-transform inversion (closing the
   contour upward) also needs the mirrored family (negative real part, same positive imaginary
   part). Check the symmetry claim (`G_baxter`'s zero set closed under `k ↦ -k̄`-type reflection)
   numerically first, then either re-derive `BAXTER.11`'s argument for the mirror family or find
   a direct symmetry argument from `Npoly`/`Dpoly`'s coefficient structure.
4. **B.3 — `h_explicit` definition + convergence.** Define `h_explicit(r) := (1/2πr)·Re[Σ_n
   Res_n·e^{ik_n r}]` for `r>σ`; prove convergence via the pole-growth law (`Re(k_n)` spacing
   `=2π/σ` exact, `Im(k_n)~2ln(Re(k_n))`) combined with the residue-magnitude asymptotic this
   file's formula would give, matching the previously-validated `n^{1-2r}` numerical decay law —
   needs re-deriving that exponent symbolically from the now-exact residue formula, not just
   citing the earlier numerical fit.

None of 1–4 is expected to be *harder in kind* than what `BAXTER.9`–`11` already did (closed-form
complex extensions, `HasDerivAt`+FTC estimates, `Summable`/`tsum` convergence via comparison
tests) — but each is a genuine, multi-lemma undertaking in its own right, not a quick follow-on.
-/

open Filter Topology

namespace FMSA.HardSphere

/-- **Residue at a simple pole, via the elementary limit characterization** — no Cauchy integral
formula needed. For `f = N/D` with `D` having a simple zero at `z0` (`HasDerivAt D D' z0`,
`D z0 = 0`, `D' ≠ 0`) and `N` continuous at `z0`, `(z-z0)·f(z) → N(z0)/D'(z0)` as `z → z0`
(`z ≠ z0`) — the standard alternative definition of `Res_{z0}[f]` for a simple pole. -/
theorem residue_of_simple_pole (N D : ℂ → ℂ) (Dprime : ℂ) (z0 : ℂ) (hD : HasDerivAt D Dprime z0)
    (hDz0 : D z0 = 0) (hDprime : Dprime ≠ 0) (hNcont : ContinuousAt N z0) :
    Tendsto (fun z => (z - z0) * (N z / D z)) (𝓝[≠] z0) (𝓝 (N z0 / Dprime)) := by
  have hslope : Tendsto (slope D z0) (𝓝[≠] z0) (𝓝 Dprime) := hasDerivAt_iff_tendsto_slope.mp hD
  have hinv : Tendsto (fun z => (slope D z0 z)⁻¹) (𝓝[≠] z0) (𝓝 Dprime⁻¹) := hslope.inv₀ hDprime
  have heq : ∀ z ∈ ({z0}ᶜ : Set ℂ), (slope D z0 z)⁻¹ = (z - z0) / D z := by
    intro z _
    rw [slope_def_field, hDz0, sub_zero, inv_div]
  have hinv' : Tendsto (fun z => (z - z0) / D z) (𝓝[≠] z0) (𝓝 Dprime⁻¹) := by
    apply Tendsto.congr' _ hinv
    filter_upwards [self_mem_nhdsWithin] with z hz using heq z hz
  have hN : Tendsto N (𝓝[≠] z0) (𝓝 (N z0)) := hNcont.continuousWithinAt.tendsto
  have hprod := hN.mul hinv'
  have heq2 : ∀ z : ℂ, N z * ((z - z0) / D z) = (z - z0) * (N z / D z) := fun z => by ring
  have hfinal := hprod.congr heq2
  rwa [show N z0 * Dprime⁻¹ = N z0 / Dprime from (div_eq_mul_inv (N z0) Dprime).symm] at hfinal

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
(`hGneg_ne` — expected, since `BAXTER.11`'s poles are upper-half-plane and its construction
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

/-! ### `h_explicit` — the residue series (Task `BAXTER.12`, Phase B.3)

`h_explicit(r) := (1/2πr)·Re[Σ_n (Res_n + Res_n^mirror)]`, summing `Hhat_residue_at_pole`'s
residue value at each pole `k_n` (drawn from an abstract pole family `kfam : ℕ → ℂ` — e.g.
`BAXTER.11`'s witness function, not yet exposed as a standalone name; `h_explicit` is stated
generically over any `kfam` so it doesn't need that refactor to typecheck) together with its
mirror `-conj(k_n)` (`B.2`'s `G_baxter_conj`/`G_baxter_zero_mirror` — the conjugate-symmetric
partner needed for the sine-transform inversion contour to close over the *whole* pole set, not
just the upper-right family `BAXTER.11` constructs).

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
explicit hypothesis (mirroring `BAXTER.11`'s `hstep` pattern and `Hhat_residue_at_pole`'s two
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
/-- **`residue_term` magnitude bound** (Task `BAXTER.14`, A.4): at a zero `k` of `G_baxter` with
`Im(k)≥0` and `‖k‖` past an explicit threshold, `‖residue_term(k)‖ ≤ C·‖k‖^{1-2r/σ}` — the
rigorous (not just numerically-checked) version of the `n^{1-2r/σ}` decay law, assembled from
`abs_exp_ikr_upper_of_zero` (numerator exponential decay), `Chat_complex_norm_bound` +
`exists_D_for_exp_neg_bound` (numerator `Chat_complex` factor, `Θ(1)` via cancellation against
the `1/‖k‖²` in `Chat_complex_norm_bound`), and `G_baxter_neg_lower_bound` +
`G_baxter_deriv_lower_bound_of_zero` (denominator, `Θ(‖k‖⁶)`). `C`/the threshold are left
existential (not simplified to a closed form) — genuine but not claimed optimal. -/
theorem residue_term_norm_bound {eta sigma rho r : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : rho ≠ 0) (hr : sigma < r) :
    ∃ C M : ℝ, 0 < C ∧ 1 ≤ M ∧ ∀ {k : ℂ}, G_baxter eta sigma rho k = 0 → 0 ≤ k.im → M ≤ ‖k‖ →
      ‖residue_term eta sigma rho r k‖ ≤ C * ‖k‖ ^ (1 - 2 * r / sigma) := by
  obtain ⟨M0, hM0pos, hM0N, hM0T⟩ := exists_hkN_hkT_threshold eta sigma rho hsigma
  obtain ⟨D, hDpos, hD⟩ := exists_D_for_exp_neg_bound heta0 heta1 hsigma hrho
  have hmupos := baxterMu_pos heta0 heta1 hsigma hrho
  have hnupos := baxterNu_pos heta0 heta1 hrho
  set mu : ℝ := rho ^ 2 * q_prime_py eta sigma with hmudef
  set nu : ℝ := rho ^ 2 * q_doubleprime_py eta with hnudef
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

/-- **`h_explicit_term` magnitude bound** (Task `BAXTER.14`, A.4): at a zero `k` of `G_baxter`
with `Im(k)≥0` and `‖k‖` past an explicit threshold, `‖h_explicit_term(k)‖ ≤ 2C·‖k‖^{1-2r/σ}` —
`residue_term_norm_bound` applied to both `k` and its mirror `-conj(k)` (`G_baxter_zero_mirror`
for the zero condition; `‖-conj(k)‖=‖k‖` and `(-conj(k)).im=k.im` so the mirror needs no new
threshold). -/
theorem h_explicit_term_norm_bound {eta sigma rho r : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : rho ≠ 0) (hr : sigma < r) :
    ∃ C M : ℝ, 0 < C ∧ 1 ≤ M ∧ ∀ {k : ℂ}, G_baxter eta sigma rho k = 0 → 0 ≤ k.im → M ≤ ‖k‖ →
      ‖residue_term eta sigma rho r k + residue_term eta sigma rho r (-(starRingEnd ℂ) k)‖ ≤
        2 * C * ‖k‖ ^ (1 - 2 * r / sigma) := by
  obtain ⟨C, M, hCpos, hM1, hbound⟩ := residue_term_norm_bound heta0 heta1 hsigma hrho hr
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

/-- **`h_explicit_summable`, concrete instantiation** (Task `BAXTER.14`, A.5): given a pole
family `kfam` that is a zero set of `G_baxter` with `Im≥0` and `‖kfam n‖` growing at least
linearly (`c·n+d ≤ ‖kfam n‖`, matching `G_baxter_pole_family_exists`'s `hgmem`+`hk1re` data —
`c := 2π/σ`, `d` from the disk-membership offset), `h_explicit_term` is genuinely `Summable`.
Uses `residue_term_norm_bound`'s `Θ(‖k‖^{1-2r/σ})` bound (rigorous, `BAXTER.14`'s main result)
composed with the negative-exponent `rpow` antitone step (`Real.rpow_le_rpow_iff_of_neg`, same
technique as `abs_exp_ikr_upper_of_zero`) to convert to an `n`-indexed bound, then
`Summable.of_norm_bounded_eventually` (only finitely many small `n` need excluding, where the
linear lower bound might fall short of `residue_term_norm_bound`'s threshold `M`). -/
theorem h_explicit_summable_of_pole_family {eta sigma rho r : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : rho ≠ 0) (hr : sigma < r) {kfam : ℕ → ℂ}
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
  exact this

end HardSphere

end FMSA
