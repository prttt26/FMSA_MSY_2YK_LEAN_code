/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterZeros
import LeanCode.Analysis.BanachPoleFamily

/-!
# Task POLE.3 — pole existence for `1 - Qhat_complex`

Reduces the zero set of `1 - Qhat_complex eta sigma rho` (`k ≠ 0`) to the zero set of a clean
**exponential polynomial** `G(k) = Npoly(k) - Dpoly(k)·e^{-ikσ}`, `Npoly` cubic, `Dpoly` linear —
the classical Pólya/Titchmarsh form for this problem, and *far* easier to estimate than
`Qhat_complex`'s own `1/k,1/k²,1/k³`-laden closed form.

Note: `Qhat_complex eta sigma rho k := ∫₀^σ q0_poly(r)·e^{-ikr}dr` and `q0_poly` already carries
one factor of `ρ` (`q0_poly = ρ·Q` in Wertheim's notation, `BAXTER.1`), so the classical Baxter
pole condition `1-ρQ̂(k)=0` is `1-Qhat_complex(k)=0` — **no further `ρ`**. (2026-07-15: fixed a
double-counted-`ρ` bug where this file previously targeted `1-ρ·Qhat_complex(k)=0` instead; see
`proof_notes_pole.md`.)

## Derivation

`Qhat_complex_formula` (`BaxterZeros.lean`, Task `POLE.1`) gives `Qhat_complex(k) = A(k) +
B(k)·e^{-ikσ}` after regrouping (pure `ring`, no new analysis) into rational functions `A, B` of
`c := -ik`. Clearing denominators (`c³ · A(k)`, `c³ · B(k)`, each a short `field_simp`) and using
the algebraic identity `P0 + P1·σ + P2·σ² = 0` (`q0_poly_inner`'s own moment coefficients, already
used implicitly in `BaxterZeros.lean`) collapses `c³·(1-Q̂(k))` to `Npoly(k) - Dpoly(k)e^{-ikσ}`
with `Dpoly` **linear** (its own quadratic-in-`c` term cancels via that same identity) — this is
`baxter_F_eq_G_of_ne_zero` below, closed via a single `linear_combination`.

## Status

Infrastructure (this file so far): `Npoly`, `Dpoly`, `G_baxter`, the `F ↔ G` equivalence for
`k ≠ 0`, and `G_baxter`'s entireness (trivial: polynomial × entire exponential − polynomial).
Pole existence itself (via the log-fixed-point Banach contraction validated numerically in
`POLE.2`, `proof_notes_baxter.md`) is **in progress** — see that file for status.
-/

open MeasureTheory Real Set

namespace FMSA.HardSphere

/-! ### `Npoly`, `Dpoly` — the cleared-denominator cubic/linear exponential-polynomial pair -/

/-- Coefficients matching `Qhat_complex_formula`'s `A(k)+B(k)e^{-ikσ}` regrouping. -/
private noncomputable def baxterP0 (eta sigma rho : ℝ) : ℝ :=
  rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma

private noncomputable def baxterP1 (eta sigma rho : ℝ) : ℝ :=
  rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma

private noncomputable def baxterP2 (eta _sigma rho : ℝ) : ℝ :=
  rho * q_doubleprime_py eta / 2

/-- **Cubic** numerator polynomial: `Npoly(k) = ik³ - P0k² + iP1k + 2P2`. -/
noncomputable def Npoly (eta sigma rho : ℝ) (k : ℂ) : ℂ :=
  Complex.I * k ^ 3 - (baxterP0 eta sigma rho : ℂ) * k ^ 2 +
    Complex.I * (baxterP1 eta sigma rho : ℂ) * k +
    2 * (baxterP2 eta sigma rho : ℂ)

/-- **Linear** denominator polynomial: `Dpoly(k) = i(P1+2P2σ)k + 2P2` (its own `c²`-order term
vanishes identically via `P0+P1σ+P2σ²=0`, `baxterP0P1P2_sum_zero` below). -/
noncomputable def Dpoly (eta sigma rho : ℝ) (k : ℂ) : ℂ :=
  Complex.I *
      ((baxterP1 eta sigma rho : ℂ) + 2 * (baxterP2 eta sigma rho : ℂ) * sigma) * k +
    2 * (baxterP2 eta sigma rho : ℂ)

/-- **`G_baxter`**: the exponential polynomial whose zeros (for `k ≠ 0`) are exactly the zeros of
`1-Qhat_complex(k)`. -/
noncomputable def G_baxter (eta sigma rho : ℝ) (k : ℂ) : ℂ :=
  Npoly eta sigma rho k - Dpoly eta sigma rho k * Complex.exp (-Complex.I * k * sigma)

private theorem baxterP0P1P2_sum_zero (eta sigma rho : ℝ) :
    (baxterP0 eta sigma rho : ℂ) + (baxterP1 eta sigma rho : ℂ) * sigma +
      (baxterP2 eta sigma rho : ℂ) * sigma ^ 2 = 0 := by
  change
    ((rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma : ℝ) : ℂ) +
    ((rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma : ℝ) : ℂ) * sigma +
    ((rho * q_doubleprime_py eta / 2 : ℝ) : ℂ) * sigma ^ 2 = 0
  push_cast; ring

/-- **The key algebraic reduction.** `(-ik)³·(1-Q̂(k)) = G_baxter(k)` for `k ≠ 0` — clears
`Qhat_complex_formula`'s `1/c,1/c²,1/c³` denominators against the cubic/linear polynomial pair.
Proved by regrouping into `A(k)+B(k)e^{-ikσ}` first (pure `ring`), clearing each of `A`, `B`
separately (`field_simp`, no `exp` mixed in), then a single `linear_combination` against
`baxterP0P1P2_sum_zero`. -/
theorem baxter_cube_mul_F_eq_G (eta sigma rho : ℝ) (hsigma : 0 < sigma) {k : ℂ} (hk : k ≠ 0) :
    (-Complex.I * k) ^ 3 * (1 - Qhat_complex eta sigma rho k) =
      G_baxter eta sigma rho k := by
  set P0 : ℝ := rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma
    with hP0def
  set P1 : ℝ := rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma with hP1def
  set P2 : ℝ := rho * q_doubleprime_py eta / 2 with hP2def
  have hP0eq : P0 = baxterP0 eta sigma rho := rfl
  have hP1eq : P1 = baxterP1 eta sigma rho := rfl
  have hP2eq : P2 = baxterP2 eta sigma rho := rfl
  set c : ℂ := -Complex.I * k with hcdef
  have hc : c ≠ 0 := by simp [hcdef, Complex.I_ne_zero, hk]
  set Aq : ℂ := -(P0 : ℂ) / c + (P1 : ℂ) / c ^ 2 - 2 * (P2 : ℂ) / c ^ 3 with hAqdef
  set Bq : ℂ := (P0 : ℂ) / c + (P1 : ℂ) * ((sigma : ℂ) / c - 1 / c ^ 2) +
    (P2 : ℂ) * ((sigma : ℂ) ^ 2 / c - 2 * (sigma : ℂ) / c ^ 2 + 2 / c ^ 3) with hBqdef
  have hstep1 : Qhat_complex eta sigma rho k = Aq + Bq * Complex.exp (-Complex.I * k * sigma) := by
    rw [Qhat_complex_formula eta sigma rho hsigma hk]
    simp only [hAqdef, hBqdef]
    ring
  have hstep2 : c ^ 3 * Aq = -(P0 : ℂ) * c ^ 2 + (P1 : ℂ) * c - 2 * (P2 : ℂ) := by
    simp only [hAqdef]; field_simp
  have hstep3 : c ^ 3 * Bq = (P0 : ℂ) * c ^ 2 + (P1 : ℂ) * ((sigma : ℂ) * c ^ 2 - c) +
      (P2 : ℂ) * ((sigma : ℂ) ^ 2 * c ^ 2 - 2 * (sigma : ℂ) * c + 2) := by
    simp only [hBqdef]; field_simp
  have hP0P1P2 : (P0 : ℂ) + (P1 : ℂ) * sigma + (P2 : ℂ) * sigma ^ 2 = 0 :=
    baxterP0P1P2_sum_zero eta sigma rho
  have hc3 : c ^ 3 = Complex.I * k ^ 3 := by
    rw [hcdef]
    have hI3 : (-Complex.I) ^ 3 = Complex.I := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, neg_pow, Complex.I_sq]; ring
    calc (-Complex.I * k) ^ 3 = (-Complex.I) ^ 3 * k ^ 3 := by ring
      _ = Complex.I * k ^ 3 := by rw [hI3]
  have hc2 : c ^ 2 = -k ^ 2 := by
    rw [hcdef]
    have hI2 : (-Complex.I) ^ 2 = -1 := by rw [neg_pow, Complex.I_sq]; ring
    calc (-Complex.I * k) ^ 2 = (-Complex.I) ^ 2 * k ^ 2 := by ring
      _ = -k ^ 2 := by rw [hI2]; ring
  rw [hstep1]
  have expand1 : c ^ 3 * (1 - (Aq + Bq * Complex.exp (-Complex.I * k * sigma))) =
      (c ^ 3 - c ^ 3 * Aq) - (c ^ 3 * Bq) * Complex.exp (-Complex.I * k * sigma) := by
    ring
  rw [expand1, hstep2, hstep3, hc3, hc2]
  unfold G_baxter Npoly Dpoly
  rw [← hP0eq, ← hP1eq, ← hP2eq]
  linear_combination k ^ 2 * Complex.exp (-Complex.I * k * sigma) * hP0P1P2

/-- **`F ↔ G` equivalence.** For `k ≠ 0`, `1-Q̂(k)=0 ↔ G_baxter(k)=0`. -/
theorem Qhat_pole_iff_G_baxter_zero (eta sigma rho : ℝ) (hsigma : 0 < sigma) {k : ℂ} (hk : k ≠ 0) :
    1 - Qhat_complex eta sigma rho k = 0 ↔ G_baxter eta sigma rho k = 0 := by
  rw [← baxter_cube_mul_F_eq_G eta sigma rho hsigma hk]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have hc3ne : (-Complex.I * k) ^ 3 ≠ 0 := by
      apply pow_ne_zero; simp [Complex.I_ne_zero, hk]
    exact (mul_eq_zero.mp h).resolve_left hc3ne

/-! ### Conjugation symmetry (Task `POLE.4`, Phase B.2)

`Npoly`, `Dpoly`'s coefficients are all real, so `G_baxter` commutes with the reflection
`k ↦ -conj(k)` in the expected way for a "real" exponential polynomial: `conj(G(k)) = G(-conj(k))`.
This is the algebraic core of the classical "poles come in mirrored `±Re, same Im` pairs" fact
(`proof_notes_baxter.md`, `BAXTER.2`'s numerics: `k≈±6.058+1.437i`) — for `k=x+iy`,
`-conj(k) = -x+iy`, the mirror point across the imaginary axis. -/

/-- **Conjugation symmetry**: `conj(G_baxter(k)) = G_baxter(-conj(k))`. -/
theorem G_baxter_conj (eta sigma rho : ℝ) (k : ℂ) :
    (starRingEnd ℂ) (G_baxter eta sigma rho k) = G_baxter eta sigma rho (-(starRingEnd ℂ) k) := by
  unfold G_baxter Npoly Dpoly
  simp only [map_sub, map_add, map_mul, map_neg, map_pow, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal, ← Complex.exp_conj, map_neg]
  ring_nf

/-- **Mirror zeros**: if `k` is a zero of `G_baxter`, so is `-conj(k)` — the classical
"mirrored `±Re(k), same Im(k)` pole pair" fact, via `G_baxter_conj`. -/
theorem G_baxter_zero_mirror {eta sigma rho : ℝ} {k : ℂ} (hk : G_baxter eta sigma rho k = 0) :
    G_baxter eta sigma rho (-(starRingEnd ℂ) k) = 0 := by
  rw [← G_baxter_conj, hk, map_zero]

/-- `G_baxter` is entire (differentiable at every `k : ℂ`) — trivial: `Npoly` is a polynomial,
`Dpoly * exp(-ikσ)` is a polynomial times the (globally holomorphic) complex exponential
composed with an affine map. -/
theorem G_baxter_entire (eta sigma rho : ℝ) : Differentiable ℂ (G_baxter eta sigma rho) := by
  unfold G_baxter Npoly Dpoly
  fun_prop

/-! ### The log-fixed-point map and Banach-contraction existence machinery

`POLE.2`'s numerical feasibility check found a *log-fixed-point* contraction map with a
Lipschitz constant that **decays** like `C/n` (rather than converging to a fixed nonzero value,
as a chord-Newton map on `G_baxter` directly would) — see `proof_notes_baxter.md` Task
`POLE.3` for the full derivation and numerics. This section formalizes the map and the
generic Banach-fixed-point wrapper; the numerical bounds themselves (branch-safety, the explicit
Lipschitz estimate) are not yet formalized — see that file for the precise remaining scope. -/

/-- **The log-fixed-point map** for the `n`-th pole: solving `e^{-ikσ} = R(k) :=
Npoly(k)/Dpoly(k)` by `k = (i/σ)·Log(R(k)) + 2πn/σ` (principal branch). A fixed point of this
map is a zero of `G_baxter` — see `baxterPhi_fixedPt_implies_zero`. -/
noncomputable def baxterPhi (eta sigma rho : ℝ) (n : ℕ) (k : ℂ) : ℂ :=
  (Complex.I / sigma) * Complex.log (Npoly eta sigma rho k / Dpoly eta sigma rho k) +
    2 * Real.pi * n / sigma

/-- **Fixed point ⟹ zero of `G_baxter`, unconditionally** (no branch-safety needed for this
direction — only `Complex.exp_log`, `exp(log x) = x` for `x ≠ 0`, plus `2π`-periodicity of
`exp` along the imaginary axis to absorb the `+2πn/σ` shift). The *converse* direction (needed
to show `baxterPhi`'s domain restriction is genuinely self-mapping near a root) does need
branch-safety (`Re(R(k)) > 0` on the disk, keeping `arg(R(k))` away from `Complex.log`'s cut) —
not yet formalized, see `proof_notes_baxter.md`. -/
theorem baxterPhi_fixedPt_implies_zero (eta sigma rho : ℝ) (hsigma : 0 < sigma) (n : ℕ) {k : ℂ}
    (hN : Npoly eta sigma rho k ≠ 0) (hD : Dpoly eta sigma rho k ≠ 0)
    (hfp : Function.IsFixedPt (baxterPhi eta sigma rho n) k) :
    G_baxter eta sigma rho k = 0 := by
  unfold Function.IsFixedPt baxterPhi at hfp
  have hR_ne : Npoly eta sigma rho k / Dpoly eta sigma rho k ≠ 0 := div_ne_zero hN hD
  have hsigmaC : (sigma : ℂ) ≠ 0 := by exact_mod_cast hsigma.ne'
  have hlog_eq : Complex.log (Npoly eta sigma rho k / Dpoly eta sigma rho k) =
      -Complex.I * k * sigma + 2 * Real.pi * n * Complex.I := by
    have h1 : Complex.I * Complex.log (Npoly eta sigma rho k / Dpoly eta sigma rho k) +
        2 * Real.pi * n = k * sigma := by
      have := hfp
      field_simp at this
      linear_combination this
    have h2 := congrArg (fun z => Complex.I * z) h1
    have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination -h2 + Complex.log (Npoly eta sigma rho k / Dpoly eta sigma rho k) * hI2
  have hexp : Complex.exp (Complex.log (Npoly eta sigma rho k / Dpoly eta sigma rho k)) =
      Npoly eta sigma rho k / Dpoly eta sigma rho k := Complex.exp_log hR_ne
  rw [hlog_eq] at hexp
  have hexp2 : Complex.exp (-Complex.I * k * sigma + 2 * Real.pi * n * Complex.I) =
      Complex.exp (-Complex.I * k * sigma) := by
    rw [Complex.exp_add]
    have h1 : Complex.exp (2 * Real.pi * (n : ℂ) * Complex.I) = 1 := by
      rw [show (2 * Real.pi * (n : ℂ) * Complex.I) = ((n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
        by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1, mul_one]
  rw [hexp2] at hexp
  have hR_eq : Npoly eta sigma rho k / Dpoly eta sigma rho k =
      Complex.exp (-Complex.I * k * sigma) := hexp.symm
  unfold G_baxter
  have hcross := (div_eq_iff hD).mp hR_eq
  linear_combination hcross

/-- **Generic Banach-fixed-point existence wrapper.** Given a Lipschitz self-map `phi` of a
closed disk whose fixed points are zeros of `G_baxter` (the *only* direction needed for
existence — see `baxterPhi_fixedPt_implies_zero` above, which discharges this hypothesis
unconditionally for `phi = baxterPhi`), Banach's fixed-point theorem gives a genuine zero in the
disk. Mirrors `OzFixedPtDilute.lean`'s `ContractingWith`-based pattern. The two remaining
hypotheses (`hMapsTo`, `hLip`) are exactly `POLE.2`'s numerically-validated but not-yet-Lean-
formalized bounds — see `proof_notes_baxter.md` Task `POLE.3` for the precise scope. -/
theorem G_baxter_pole_exists_of_bounds (eta sigma rho : ℝ) (k1 : ℂ) (r : ℝ) (hr : 0 < r)
    (K : NNReal) (hK1 : K < 1) (phi : ℂ → ℂ)
    (hMapsTo : Set.MapsTo phi (Metric.closedBall k1 r) (Metric.closedBall k1 r))
    (hLip : LipschitzOnWith K phi (Metric.closedBall k1 r))
    (hFixedImpliesRoot : ∀ k ∈ Metric.closedBall k1 r,
      Function.IsFixedPt phi k → G_baxter eta sigma rho k = 0) :
    ∃ k ∈ Metric.closedBall k1 r, G_baxter eta sigma rho k = 0 := by
  have hsc : IsComplete (Metric.closedBall k1 r) := Metric.isClosed_closedBall.isComplete
  have hcontract : ContractingWith K (hMapsTo.restrict phi _ _) :=
    ⟨hK1, hLip.mapsToRestrict hMapsTo⟩
  have hx0 : k1 ∈ Metric.closedBall k1 r := Metric.mem_closedBall_self hr.le
  have hxfin : edist k1 (phi k1) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨y, hys, hfp, _, _⟩ := hcontract.exists_fixedPoint' hsc hMapsTo hx0 hxfin
  exact ⟨y, hys, hFixedImpliesRoot y hys hfp⟩

/-! ### Magnitude bounds for `Npoly`, `Dpoly` (Task `POLE.3`, Phase A.1)

Reverse-triangle-inequality ("half the leading term") bounds for `‖k‖` past an explicit
threshold, culminating in `R_deriv_ratio_bound` (`‖R'(k)/R(k)‖ ≤ C/‖k‖`, `R := Npoly/Dpoly`) —
the single estimate the rest of `POLE.3` builds on. -/

/-- `baxterP1 + 2·baxterP2·σ = ρ·q_prime_py(η,σ)` — collapses `Dpoly`'s naive
`iρ(P1+2P2σ)k` coefficient to `iρ²·q_prime_py(η,σ)·k`. -/
private theorem baxterP1_add_two_mul_baxterP2_mul_sigma (eta sigma rho : ℝ) :
    baxterP1 eta sigma rho + 2 * baxterP2 eta sigma rho * sigma = rho * q_prime_py eta sigma := by
  unfold baxterP1 baxterP2
  ring

/-- **`Dpoly` in clean affine form**: `Dpoly(k) = iμk + ν`, `μ := ρ²·q_prime_py(η,σ)`,
`ν := ρ²·q_doubleprime_py(η)`. -/
theorem Dpoly_eq_affine (eta sigma rho : ℝ) (k : ℂ) :
    Dpoly eta sigma rho k =
      Complex.I * (rho * q_prime_py eta sigma : ℝ) * k +
        (rho * q_doubleprime_py eta : ℝ) := by
  unfold Dpoly
  rw [show (baxterP1 eta sigma rho : ℂ) + 2 * (baxterP2 eta sigma rho : ℂ) * sigma =
      ((baxterP1 eta sigma rho + 2 * baxterP2 eta sigma rho * sigma : ℝ) : ℂ) by
        push_cast; ring,
    baxterP1_add_two_mul_baxterP2_mul_sigma]
  unfold baxterP2
  push_cast
  ring

private theorem q_prime_py_pos {eta sigma : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) : 0 < q_prime_py eta sigma := by
  unfold q_prime_py
  have h1 : (0:ℝ) < 1 - eta := by linarith
  positivity

private theorem q_doubleprime_py_pos {eta : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1) :
    0 < q_doubleprime_py eta := by
  unfold q_doubleprime_py
  have h1 : (0:ℝ) < 1 - eta := by linarith
  positivity

/-- `μ := ρ²·q_prime_py(η,σ) > 0` for `η∈(0,1), σ>0, ρ≠0`. -/
theorem baxterMu_pos {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 < rho) : 0 < rho * q_prime_py eta sigma :=
  mul_pos hrho (q_prime_py_pos heta0 heta1 hsigma)

/-- `ν := ρ²·q_doubleprime_py(η) > 0` for `η∈(0,1), ρ≠0`. -/
theorem baxterNu_pos {eta rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1) (hrho : 0 < rho) :
    0 < rho * q_doubleprime_py eta :=
  mul_pos hrho (q_doubleprime_py_pos heta0 heta1)

/-- Reverse-triangle-inequality helper: `‖iμk+ν‖ ≥ μ‖k‖-ν` for `μ>0, ν≥0`. -/
private theorem norm_affine_lower_bound (mu nu : ℝ) (k : ℂ) (hmu : 0 < mu) (hnu0 : 0 ≤ nu) :
    mu * ‖k‖ - nu ≤ ‖Complex.I * (mu : ℂ) * k + (nu : ℂ)‖ := by
  have h := norm_sub_le (Complex.I * (mu : ℂ) * k + (nu : ℂ)) (nu : ℂ)
  simp only [add_sub_cancel_right] at h
  have hnorm : ‖Complex.I * (mu : ℂ) * k‖ = mu * ‖k‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hmu]
    ring
  rw [hnorm] at h
  have hnu : ‖(nu : ℂ)‖ = nu := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnu0]
  rw [hnu] at h
  linarith

/-- **`Dpoly` lower bound**: `‖Dpoly(k)‖ ≥ μ‖k‖ - ν`. -/
theorem Dpoly_lower_bound {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (k : ℂ) :
    rho * q_prime_py eta sigma * ‖k‖ - rho * q_doubleprime_py eta ≤
      ‖Dpoly eta sigma rho k‖ := by
  rw [Dpoly_eq_affine]
  exact norm_affine_lower_bound _ _ k (baxterMu_pos heta0 heta1 hsigma hrho)
    (baxterNu_pos heta0 heta1 hrho).le

/-- Triangle-inequality helper: `‖iμk+ν‖ ≤ μ‖k‖+ν` for `μ,ν≥0`. -/
private theorem norm_affine_upper_bound (mu nu : ℝ) (k : ℂ) (hmu : 0 ≤ mu) (hnu0 : 0 ≤ nu) :
    ‖Complex.I * (mu : ℂ) * k + (nu : ℂ)‖ ≤ mu * ‖k‖ + nu := by
  calc ‖Complex.I * (mu : ℂ) * k + (nu : ℂ)‖
      ≤ ‖Complex.I * (mu : ℂ) * k‖ + ‖(nu : ℂ)‖ := norm_add_le _ _
    _ = mu * ‖k‖ + nu := by
        rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmu, abs_of_nonneg hnu0]
        ring

/-- **`Dpoly` upper bound**: `‖Dpoly(k)‖ ≤ μ‖k‖ + ν` (Task `POLE.5`). -/
theorem Dpoly_upper_bound {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (k : ℂ) :
    ‖Dpoly eta sigma rho k‖ ≤
      rho * q_prime_py eta sigma * ‖k‖ + rho * q_doubleprime_py eta := by
  rw [Dpoly_eq_affine]
  exact norm_affine_upper_bound _ _ k (baxterMu_pos heta0 heta1 hsigma hrho).le
    (baxterNu_pos heta0 heta1 hrho).le

/-- Reverse-triangle-inequality helper for a cubic: `‖ik³-Ak²+iBk+C‖ ≥ ‖k‖³/2` once
`‖k‖≥1` and `‖k‖≥2(|A|+|B|+|C|)` — the "half the leading term" technique. -/
private theorem norm_cubic_lower_bound (A B C : ℝ) (k : ℂ) (hk1 : 1 ≤ ‖k‖)
    (hkbig : 2 * (|A| + |B| + |C|) ≤ ‖k‖) :
    ‖k‖ ^ 3 / 2 ≤
      ‖Complex.I * k ^ 3 - (A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ)‖ := by
  set N : ℂ := Complex.I * k ^ 3 - (A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ) with hNdef
  have hrest : ‖-(A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ)‖ ≤
      |A| * ‖k‖ ^ 2 + |B| * ‖k‖ + |C| := by
    calc ‖-(A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ)‖
        ≤ ‖-(A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k‖ + ‖(C : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖-(A : ℂ) * k ^ 2‖ + ‖Complex.I * (B : ℂ) * k‖ + ‖(C : ℂ)‖ := by
          gcongr; exact norm_add_le _ _
      _ = |A| * ‖k‖ ^ 2 + |B| * ‖k‖ + |C| := by
          rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_pow, Complex.norm_real,
            Complex.norm_real, Complex.norm_real, Complex.norm_I]
          simp only [Real.norm_eq_abs]
          ring
  have hsplit : Complex.I * k ^ 3 = N - (-(A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ)) := by
    rw [hNdef]; ring
  have hIk3 : ‖Complex.I * k ^ 3‖ = ‖k‖ ^ 3 := by
    rw [norm_mul, Complex.norm_I, norm_pow]; ring
  have hlow : ‖k‖ ^ 3 - (|A| * ‖k‖ ^ 2 + |B| * ‖k‖ + |C|) ≤ ‖N‖ := by
    have h1 := norm_sub_le N (-(A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ))
    rw [← hsplit, hIk3] at h1
    linarith
  have hcollapse : |A| * ‖k‖ ^ 2 + |B| * ‖k‖ + |C| ≤ (|A| + |B| + |C|) * ‖k‖ ^ 2 := by
    have hB : |B| * ‖k‖ ≤ |B| * ‖k‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc ‖k‖ = ‖k‖ ^ 1 := (pow_one _).symm
        _ ≤ ‖k‖ ^ 2 := by
          apply pow_le_pow_right₀ hk1; norm_num
    have hC : |C| ≤ |C| * ‖k‖ ^ 2 := by
      calc |C| = |C| * 1 := (mul_one _).symm
        _ ≤ |C| * ‖k‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc (1:ℝ) = 1 ^ 2 := by norm_num
            _ ≤ ‖k‖ ^ 2 := by gcongr
    nlinarith [hB, hC]
  have hfinal : (|A| + |B| + |C|) * ‖k‖ ^ 2 ≤ ‖k‖ ^ 3 / 2 := by
    have h2 : |A| + |B| + |C| ≤ ‖k‖ / 2 := by linarith
    calc (|A| + |B| + |C|) * ‖k‖ ^ 2 ≤ (‖k‖ / 2) * ‖k‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right h2; positivity
      _ = ‖k‖ ^ 3 / 2 := by ring
  linarith [hlow, hcollapse, hfinal]

/-- **`Npoly` lower bound**: `‖Npoly(k)‖ ≥ ‖k‖³/2` once `‖k‖` exceeds the explicit threshold
`max(1, 2(|ρP0|+|ρP1|+2|ρP2|))`. -/
theorem Npoly_lower_bound (eta sigma rho : ℝ) (k : ℂ) (hk1 : 1 ≤ ‖k‖)
    (hkbig : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ ‖k‖) :
    ‖k‖ ^ 3 / 2 ≤ ‖Npoly eta sigma rho k‖ := by
  unfold Npoly
  have := norm_cubic_lower_bound (baxterP0 eta sigma rho) (baxterP1 eta sigma rho)
    (2 * baxterP2 eta sigma rho) k hk1 hkbig
  convert this using 2
  push_cast
  ring

/-- Triangle-inequality helper for a cubic: `‖ik³-Ak²+iBk+C‖ ≤ (1+|A|+|B|+|C|)‖k‖³` once
`‖k‖≥1` — the easy direction, no "half the leading term" trick needed. -/
private theorem norm_cubic_upper_bound (A B C : ℝ) (k : ℂ) (hk1 : 1 ≤ ‖k‖) :
    ‖Complex.I * k ^ 3 - (A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ)‖ ≤
      (1 + |A| + |B| + |C|) * ‖k‖ ^ 3 := by
  have h1 : ‖Complex.I * k ^ 3 - (A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ)‖ ≤
      ‖Complex.I * k ^ 3‖ + ‖(A : ℂ) * k ^ 2‖ + ‖Complex.I * (B : ℂ) * k‖ + ‖(C : ℂ)‖ := by
    calc ‖Complex.I * k ^ 3 - (A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ)‖
        ≤ ‖Complex.I * k ^ 3 - (A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k‖ + ‖(C : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ ‖Complex.I * k ^ 3 - (A : ℂ) * k ^ 2‖ + ‖Complex.I * (B : ℂ) * k‖ + ‖(C : ℂ)‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ ‖Complex.I * k ^ 3‖ + ‖(A : ℂ) * k ^ 2‖ + ‖Complex.I * (B : ℂ) * k‖ + ‖(C : ℂ)‖ := by
          gcongr
          exact norm_sub_le _ _
  have hn1 : ‖Complex.I * k ^ 3‖ = ‖k‖ ^ 3 := by rw [norm_mul, Complex.norm_I, norm_pow]; ring
  have hn2 : ‖(A : ℂ) * k ^ 2‖ = |A| * ‖k‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  have hn3 : ‖Complex.I * (B : ℂ) * k‖ = |B| * ‖k‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]; ring
  have hn4 : ‖(C : ℂ)‖ = |C| := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hn1, hn2, hn3, hn4] at h1
  have hk2 : ‖k‖ ^ 2 ≤ ‖k‖ ^ 3 := by
    calc ‖k‖ ^ 2 = ‖k‖ ^ (2 : ℕ) := rfl
      _ ≤ ‖k‖ ^ (3 : ℕ) := pow_le_pow_right₀ hk1 (by norm_num)
  have hk1' : ‖k‖ ≤ ‖k‖ ^ 3 := by
    calc ‖k‖ = ‖k‖ ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ ‖k‖ ^ (3 : ℕ) := pow_le_pow_right₀ hk1 (by norm_num)
  have hk0 : (1 : ℝ) ≤ ‖k‖ ^ 3 := le_trans hk1 hk1'
  nlinarith [mul_le_mul_of_nonneg_left hk2 (abs_nonneg A),
    mul_le_mul_of_nonneg_left hk1' (abs_nonneg B),
    mul_le_mul_of_nonneg_left hk0 (abs_nonneg C), h1]

/-- **`Npoly` upper bound**: `‖Npoly(k)‖ ≤ (1+|ρP0|+|ρP1|+2|ρP2|)‖k‖³` once `‖k‖≥1`
(Task `POLE.5`). -/
theorem Npoly_upper_bound (eta sigma rho : ℝ) (k : ℂ) (hk1 : 1 ≤ ‖k‖) :
    ‖Npoly eta sigma rho k‖ ≤
      (1 + |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) * ‖k‖ ^ 3 := by
  unfold Npoly
  have := norm_cubic_upper_bound (baxterP0 eta sigma rho) (baxterP1 eta sigma rho)
    (2 * baxterP2 eta sigma rho) k hk1
  convert this using 2
  push_cast
  ring

/-! ### Derivative bounds for `Npoly`, `Dpoly` -/

private theorem norm_cubic_deriv_bound (A B : ℝ) (k : ℂ) (hk1 : 1 ≤ ‖k‖) :
    ‖3 * Complex.I * k ^ 2 - 2 * (A : ℂ) * k + Complex.I * (B : ℂ)‖ ≤
      (3 + 2 * |A| + |B|) * ‖k‖ ^ 2 := by
  have hstep : ‖3 * Complex.I * k ^ 2 - 2 * (A : ℂ) * k + Complex.I * (B : ℂ)‖ ≤
      3 * ‖k‖ ^ 2 + 2 * |A| * ‖k‖ + |B| := by
    calc ‖3 * Complex.I * k ^ 2 - 2 * (A : ℂ) * k + Complex.I * (B : ℂ)‖
        ≤ ‖3 * Complex.I * k ^ 2 - 2 * (A : ℂ) * k‖ + ‖Complex.I * (B : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖3 * Complex.I * k ^ 2‖ + ‖(2 : ℂ) * (A : ℂ) * k‖ + ‖Complex.I * (B : ℂ)‖ := by
          gcongr; exact norm_sub_le _ _
      _ = 3 * ‖k‖ ^ 2 + 2 * |A| * ‖k‖ + |B| := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_I]
          simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
          ring
  have hk2 : (1 : ℝ) ≤ ‖k‖ ^ 2 := by nlinarith
  have hle : 2 * |A| * ‖k‖ + |B| ≤ (2 * |A| + |B|) * ‖k‖ ^ 2 := by
    have hAk : |A| * ‖k‖ ≤ |A| * ‖k‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      nlinarith
    have hBc : |B| ≤ |B| * ‖k‖ ^ 2 := by
      calc |B| = |B| * 1 := (mul_one _).symm
        _ ≤ |B| * ‖k‖ ^ 2 := mul_le_mul_of_nonneg_left hk2 (abs_nonneg _)
    linarith
  linarith [hstep, hle]

private theorem hasDerivAt_cubic (A B C : ℝ) (k0 : ℂ) :
    HasDerivAt
      (fun k : ℂ => Complex.I * k ^ 3 - (A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ))
      (3 * Complex.I * k0 ^ 2 - 2 * (A : ℂ) * k0 + Complex.I * (B : ℂ)) k0 := by
  have h1 : HasDerivAt (fun k : ℂ => k ^ 3) (3 * k0 ^ 2) k0 := by simpa using hasDerivAt_pow 3 k0
  have h2 : HasDerivAt (fun k : ℂ => k ^ 2) (2 * k0) k0 := by simpa using hasDerivAt_pow 2 k0
  have h3 : HasDerivAt (fun k : ℂ => k) (1 : ℂ) k0 := hasDerivAt_id k0
  have hI : HasDerivAt (fun k : ℂ => Complex.I * k ^ 3) (Complex.I * (3 * k0 ^ 2)) k0 :=
    h1.const_mul Complex.I
  have hA : HasDerivAt (fun k : ℂ => (A : ℂ) * k ^ 2) ((A : ℂ) * (2 * k0)) k0 :=
    h2.const_mul (A : ℂ)
  have hB : HasDerivAt (fun k : ℂ => Complex.I * (B : ℂ) * k) (Complex.I * (B : ℂ) * 1) k0 :=
    h3.const_mul (Complex.I * (B : ℂ))
  have hconst : HasDerivAt (fun _ : ℂ => (C : ℂ)) 0 k0 := hasDerivAt_const k0 _
  have hcombine := ((hI.sub hA).add hB).add hconst
  refine hcombine.congr_deriv ?_
  ring

/-- **`Npoly` is differentiable, with an explicit derivative.** -/
theorem Npoly_hasDerivAt (eta sigma rho : ℝ) (k0 : ℂ) :
    HasDerivAt (Npoly eta sigma rho)
      (3 * Complex.I * k0 ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k0 +
        Complex.I * (baxterP1 eta sigma rho : ℝ)) k0 := by
  have heq : Npoly eta sigma rho =
      fun k : ℂ => Complex.I * k ^ 3 - (baxterP0 eta sigma rho : ℝ) * k ^ 2 +
        Complex.I * (baxterP1 eta sigma rho : ℝ) * k +
        (2 * baxterP2 eta sigma rho : ℝ) := by
    funext k; unfold Npoly; push_cast; ring
  rw [heq]
  exact hasDerivAt_cubic (baxterP0 eta sigma rho) (baxterP1 eta sigma rho)
    (2 * baxterP2 eta sigma rho) k0

/-- **`Npoly'` upper bound.** -/
theorem Npoly_deriv_bound (eta sigma rho : ℝ) (k : ℂ) (hk1 : 1 ≤ ‖k‖) :
    ‖3 * Complex.I * k ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k +
        Complex.I * (baxterP1 eta sigma rho : ℝ)‖ ≤
      (3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) * ‖k‖ ^ 2 :=
  norm_cubic_deriv_bound (baxterP0 eta sigma rho) (baxterP1 eta sigma rho) k hk1

/-- **`Dpoly` is differentiable, with a CONSTANT derivative** `iμ` — no bound needed. -/
theorem Dpoly_hasDerivAt (eta sigma rho : ℝ) (k0 : ℂ) :
    HasDerivAt (Dpoly eta sigma rho)
      (Complex.I * (rho * q_prime_py eta sigma : ℝ)) k0 := by
  have heq : Dpoly eta sigma rho =
      fun k : ℂ => Complex.I * (rho * q_prime_py eta sigma : ℝ) * k +
        (rho * q_doubleprime_py eta : ℝ) := by
    funext k; exact Dpoly_eq_affine eta sigma rho k
  rw [heq]
  have hid : HasDerivAt (fun k : ℂ => k) (1 : ℂ) k0 := hasDerivAt_id k0
  have hlin : HasDerivAt (fun k : ℂ => Complex.I * (rho * q_prime_py eta sigma : ℝ) * k)
      (Complex.I * (rho * q_prime_py eta sigma : ℝ) * 1) k0 := hid.const_mul _
  have hconst : HasDerivAt (fun _ : ℂ => ((rho * q_doubleprime_py eta : ℝ) : ℂ)) 0 k0 :=
    hasDerivAt_const k0 _
  have hcombine := hlin.add hconst
  refine hcombine.congr_deriv ?_
  ring

/-- **`G_baxter`'s derivative**, named for reuse (`POLE.4`'s residue formula). -/
noncomputable def G_baxter_deriv (eta sigma rho : ℝ) (k : ℂ) : ℂ :=
  (3 * Complex.I * k ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k +
      Complex.I * (baxterP1 eta sigma rho : ℝ)) -
    ((Complex.I * (rho * q_prime_py eta sigma : ℝ)) * Complex.exp (-Complex.I * k * sigma) +
      Dpoly eta sigma rho k * (-Complex.I * sigma) * Complex.exp (-Complex.I * k * sigma))

/-- `G_baxter_deriv` is genuinely `G_baxter`'s derivative — via the product rule on
`Dpoly(k)·e^{-ikσ}` combined with `Npoly_hasDerivAt`/`Dpoly_hasDerivAt`. -/
theorem G_baxter_hasDerivAt (eta sigma rho : ℝ) (k0 : ℂ) :
    HasDerivAt (G_baxter eta sigma rho) (G_baxter_deriv eta sigma rho k0) k0 := by
  unfold G_baxter G_baxter_deriv
  have hN := Npoly_hasDerivAt eta sigma rho k0
  have hD := Dpoly_hasDerivAt eta sigma rho k0
  have hexp : HasDerivAt (fun k : ℂ => Complex.exp (-Complex.I * k * sigma))
      ((-Complex.I * sigma) * Complex.exp (-Complex.I * k0 * sigma)) k0 := by
    have h1 : HasDerivAt (fun k : ℂ => -Complex.I * k * sigma) (-Complex.I * sigma) k0 := by
      have h2 : HasDerivAt (fun k : ℂ => k * (sigma : ℂ)) (sigma : ℂ) k0 := by
        simpa using (hasDerivAt_id k0).mul_const (sigma : ℂ)
      have h3 := h2.const_mul (-Complex.I)
      simpa [mul_assoc] using h3
    have h4 := h1.cexp
    refine h4.congr_deriv ?_
    ring
  have hDexp := hD.mul hexp
  change HasDerivAt (fun k => Dpoly eta sigma rho k * Complex.exp (-Complex.I * k * sigma)) _ k0
    at hDexp
  refine (hN.sub hDexp).congr_deriv ?_
  ring

/-- Generic combination: given norm bounds on `N'` (above), `N` (below), `D'` (exact), `D`
(below), get the `‖N'/N - D'/D‖ ≤ C/‖k‖`-shaped bound. -/
private theorem norm_div_sub_div_bound (Nprime N Dprime D : ℂ) (X YN mu YD : ℝ)
    (hXnn : 0 ≤ X) (hNprime : ‖Nprime‖ ≤ X) (hN : YN ≤ ‖N‖) (hYN : 0 < YN)
    (hDprime : ‖Dprime‖ = mu) (hD : YD ≤ ‖D‖) (hYD : 0 < YD) :
    ‖Nprime / N - Dprime / D‖ ≤ X / YN + mu / YD := by
  have hNormNpos : 0 < ‖N‖ := lt_of_lt_of_le hYN hN
  have hNormDpos : 0 < ‖D‖ := lt_of_lt_of_le hYD hD
  have hstep : ‖Nprime / N - Dprime / D‖ ≤ ‖Nprime / N‖ + ‖Dprime / D‖ := norm_sub_le _ _
  have hNb : ‖Nprime / N‖ ≤ X / YN := by rw [norm_div]; gcongr
  have hDb : ‖Dprime / D‖ ≤ mu / YD := by
    rw [norm_div, hDprime]
    gcongr
    linarith [hDprime ▸ norm_nonneg Dprime]
  linarith [hstep, hNb, hDb]

/-- **`R'/R` bound** (`R := Npoly/Dpoly`): the single estimate the rest of `POLE.3`'s
Banach argument builds on. `a := |ρP0|`, `b := |ρP1|`, `c := 2|ρP2|`; valid once `‖k‖` exceeds
`max(1, 2(a+b+c), 2ν/μ)`. -/
theorem R_deriv_ratio_bound {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {k : ℂ} (hk1 : 1 ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ ‖k‖)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ ‖k‖) :
    ‖(3 * Complex.I * k ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k +
          Complex.I * (baxterP1 eta sigma rho : ℝ)) / Npoly eta sigma rho k -
        (Complex.I * (rho * q_prime_py eta sigma : ℝ)) / Dpoly eta sigma rho k‖ ≤
      (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) / ‖k‖ := by
  set mu : ℝ := rho * q_prime_py eta sigma with hmudef
  set nu : ℝ := rho * q_doubleprime_py eta with hnudef
  have hmupos : 0 < mu := baxterMu_pos heta0 heta1 hsigma hrho
  have hnupos : 0 < nu := baxterNu_pos heta0 heta1 hrho
  have hDprimenorm : ‖Complex.I * (mu : ℂ)‖ = mu := by
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmupos]; ring
  have hYD : 0 < mu * ‖k‖ / 2 := by positivity
  have hDbound : mu * ‖k‖ / 2 ≤ ‖Dpoly eta sigma rho k‖ := by
    have h1 := Dpoly_lower_bound (rho := rho) (eta := eta) (sigma := sigma) heta0 heta1 hsigma
      hrho k
    have h2 : nu ≤ mu * ‖k‖ / 2 := by
      rw [hnudef, hmudef] at hkD ⊢
      rw [div_le_iff₀ (baxterMu_pos heta0 heta1 hsigma hrho)] at hkD
      nlinarith [hkD]
    linarith
  have hYN : 0 < ‖k‖ ^ 3 / 2 := by positivity
  have hNbound : ‖k‖ ^ 3 / 2 ≤ ‖Npoly eta sigma rho k‖ := Npoly_lower_bound eta sigma rho k hk1 hkN
  have hXnn : 0 ≤ (3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) *
      ‖k‖ ^ 2 := by positivity
  have hcombo := norm_div_sub_div_bound
    (3 * Complex.I * k ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k +
      Complex.I * (baxterP1 eta sigma rho : ℝ))
    (Npoly eta sigma rho k) (Complex.I * (mu : ℂ)) (Dpoly eta sigma rho k)
    ((3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) * ‖k‖ ^ 2)
    (‖k‖ ^ 3 / 2) mu (mu * ‖k‖ / 2) hXnn (Npoly_deriv_bound eta sigma rho k hk1) hNbound hYN
    hDprimenorm hDbound hYD
  have hk0 : 0 < ‖k‖ := lt_of_lt_of_le one_pos hk1
  have heq : (3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) *
        ‖k‖ ^ 2 / (‖k‖ ^ 3 / 2) + mu / (mu * ‖k‖ / 2) =
      (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) / ‖k‖ := by
    have hk2 : ‖k‖ ^ 2 ≠ 0 := by positivity
    have hk3 : ‖k‖ ^ 3 ≠ 0 := by positivity
    field_simp
    ring
  linarith [hcombo, heq.le, heq.ge]

/-! ### Branch-safety: `Re(Npoly(k)·conj(Dpoly(k))) > 0` (Task `POLE.3`, Phase A.2)

Reuses the `A,B,C`-correction bound already proved inline for `norm_cubic_lower_bound`, but this
time bounds `Re` of the FULL product `Npoly(k)·conj(Dpoly(k))` — writing `Npoly = ik³+E1` (`E1`
the lower-order correction), `Dpoly = iμk+ν`, the product's leading term `μ·‖k‖²·k²` has real
part `μ‖k‖²·Re(k²)`; the remaining `bracket` term is bounded in *magnitude* only (no need to
separately expand into `Re`/`Im`), then `Re(z) ≥ -‖z‖` finishes it — much simpler than expanding
into `x,y` by hand. -/

private theorem norm_cubic_correction_bound (A B C : ℝ) (k : ℂ) (hk1 : 1 ≤ ‖k‖) :
    ‖-(A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ)‖ ≤ (|A| + |B| + |C|) * ‖k‖ ^ 2 := by
  have hrest : ‖-(A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ)‖ ≤
      |A| * ‖k‖ ^ 2 + |B| * ‖k‖ + |C| := by
    calc ‖-(A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ)‖
        ≤ ‖-(A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k‖ + ‖(C : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖-(A : ℂ) * k ^ 2‖ + ‖Complex.I * (B : ℂ) * k‖ + ‖(C : ℂ)‖ := by
          gcongr; exact norm_add_le _ _
      _ = |A| * ‖k‖ ^ 2 + |B| * ‖k‖ + |C| := by
          rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_pow, Complex.norm_real,
            Complex.norm_real, Complex.norm_real, Complex.norm_I]
          simp only [Real.norm_eq_abs]
          ring
  have hk2 : (1 : ℝ) ≤ ‖k‖ ^ 2 := by nlinarith
  nlinarith [hrest, abs_nonneg A, abs_nonneg B, abs_nonneg C,
    mul_le_mul_of_nonneg_left hk2 (abs_nonneg B), mul_le_mul_of_nonneg_left hk2 (abs_nonneg C)]

/-- **Branch-safety, generic form.** `Re[(ik³-Ak²+iBk+C)·conj(iμk+ν)] > 0` once `‖k‖` exceeds
the explicit threshold making `D‖k‖ < μ·Re(k²)`, `D := ν+μ(|A|+|B|+|C|)+ν(|A|+|B|+|C|)`. -/
private theorem norm_cubic_mul_conj_affine_re_pos (A B C mu nu : ℝ) (k : ℂ) (hk1 : 1 ≤ ‖k‖)
    (hmu : 0 < mu) (hnu0 : 0 ≤ nu)
    (hD : (nu + mu * (|A| + |B| + |C|) + nu * (|A| + |B| + |C|)) * ‖k‖ < mu * (k ^ 2).re) :
    0 < ((Complex.I * k ^ 3 - (A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ)) *
      (starRingEnd ℂ) (Complex.I * (mu : ℂ) * k + (nu : ℂ))).re := by
  set E1 : ℂ := -(A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ) with hE1def
  have hE1bound : ‖E1‖ ≤ (|A| + |B| + |C|) * ‖k‖ ^ 2 := norm_cubic_correction_bound A B C k hk1
  have hident : Complex.I * k ^ 3 - (A : ℂ) * k ^ 2 + Complex.I * (B : ℂ) * k + (C : ℂ) =
      Complex.I * k ^ 3 + E1 := by rw [hE1def]; ring
  have hconj : (starRingEnd ℂ) (Complex.I * (mu : ℂ) * k + (nu : ℂ)) =
      -Complex.I * (mu : ℂ) * (starRingEnd ℂ) k + (nu : ℂ) := by
    simp [map_add, map_mul, Complex.conj_I]
  rw [hident, hconj]
  have hkk : k * (starRingEnd ℂ) k = (Complex.normSq k : ℂ) := Complex.mul_conj k
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hexpand : (Complex.I * k ^ 3 + E1) * (-Complex.I * (mu : ℂ) * (starRingEnd ℂ) k + (nu : ℂ)) =
      (mu : ℂ) * (Complex.normSq k : ℂ) * k ^ 2 +
        (Complex.I * (nu : ℂ) * k ^ 3 - Complex.I * (mu : ℂ) * E1 * (starRingEnd ℂ) k +
          (nu : ℂ) * E1) := by
    rw [← hkk]
    linear_combination (-(mu : ℂ) * k ^ 3 * (starRingEnd ℂ) k) * hI2
  rw [hexpand]
  have hre1 : ((mu : ℂ) * (Complex.normSq k : ℂ) * k ^ 2).re =
      mu * Complex.normSq k * (k ^ 2).re := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [Complex.add_re, hre1]
  set bracket : ℂ := Complex.I * (nu : ℂ) * k ^ 3 - Complex.I * (mu : ℂ) * E1 * (starRingEnd ℂ) k +
    (nu : ℂ) * E1 with hbdef
  have hbracket_bound : ‖bracket‖ ≤
      (nu + mu * (|A| + |B| + |C|) + nu * (|A| + |B| + |C|)) * ‖k‖ ^ 3 := by
    have h1 : ‖Complex.I * (nu : ℂ) * k ^ 3‖ = nu * ‖k‖ ^ 3 := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hnu0, norm_pow]
      ring
    have h2 : ‖Complex.I * (mu : ℂ) * E1 * (starRingEnd ℂ) k‖ ≤
        mu * (|A| + |B| + |C|) * ‖k‖ ^ 3 := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hmu, Complex.norm_conj]
      calc 1 * mu * ‖E1‖ * ‖k‖ ≤ 1 * mu * ((|A| + |B| + |C|) * ‖k‖ ^ 2) * ‖k‖ := by gcongr
        _ = mu * (|A| + |B| + |C|) * ‖k‖ ^ 3 := by ring
    have h3 : ‖(nu : ℂ) * E1‖ ≤ nu * (|A| + |B| + |C|) * ‖k‖ ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnu0]
      calc nu * ‖E1‖ ≤ nu * ((|A| + |B| + |C|) * ‖k‖ ^ 2) := by gcongr
        _ = nu * (|A| + |B| + |C|) * ‖k‖ ^ 2 := by ring
    have hk2le3 : ‖k‖ ^ 2 ≤ ‖k‖ ^ 3 := by
      nlinarith [pow_le_pow_right₀ hk1 (by norm_num : 2 ≤ 3)]
    calc ‖bracket‖ ≤
          ‖Complex.I * (nu : ℂ) * k ^ 3 - Complex.I * (mu : ℂ) * E1 * (starRingEnd ℂ) k‖ +
            ‖(nu : ℂ) * E1‖ := by rw [hbdef]; exact norm_add_le _ _
      _ ≤ ‖Complex.I * (nu : ℂ) * k ^ 3‖ + ‖Complex.I * (mu : ℂ) * E1 * (starRingEnd ℂ) k‖ +
            ‖(nu : ℂ) * E1‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ nu * ‖k‖ ^ 3 + mu * (|A| + |B| + |C|) * ‖k‖ ^ 3 + nu * (|A| + |B| + |C|) * ‖k‖ ^ 2 := by
          rw [h1]; linarith [h2, h3]
      _ ≤ nu * ‖k‖ ^ 3 + mu * (|A| + |B| + |C|) * ‖k‖ ^ 3 + nu * (|A| + |B| + |C|) * ‖k‖ ^ 3 := by
          nlinarith [h1, h2, h3, hk2le3, mul_nonneg hnu0 (by positivity : (0:ℝ) ≤ |A|+|B|+|C|)]
      _ = (nu + mu * (|A| + |B| + |C|) + nu * (|A| + |B| + |C|)) * ‖k‖ ^ 3 := by ring
  have hbracket_re : -‖bracket‖ ≤ bracket.re := (abs_le.mp (Complex.abs_re_le_norm bracket)).1
  have hnormsqeq : Complex.normSq k = ‖k‖ ^ 2 := (Complex.sq_norm k).symm
  rw [hnormsqeq]
  have hk2pos : 0 < ‖k‖ ^ 2 := by nlinarith
  have hDmul : (nu + mu * (|A| + |B| + |C|) + nu * (|A| + |B| + |C|)) * ‖k‖ ^ 3 <
      mu * ‖k‖ ^ 2 * (k ^ 2).re := by nlinarith [mul_lt_mul_of_pos_right hD hk2pos]
  nlinarith [hbracket_re, hbracket_bound, hDmul]

/-- **`Npoly(k)·conj(Dpoly(k))` has positive real part**, hence (dividing by `‖Dpoly(k)‖²>0`)
`R(k) := Npoly(k)/Dpoly(k)` has `Re(R(k)) > 0`, giving `R(k) ∈ Complex.slitPlane` — the branch-
safety condition `Complex.log`/`baxterPhi` need. -/
theorem Npoly_mul_conj_Dpoly_re_pos {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {k : ℂ} (hk1 : 1 ≤ ‖k‖)
    (hD : ((rho * q_doubleprime_py eta) +
        (rho * q_prime_py eta sigma) * (|baxterP0 eta sigma rho| +
          |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|) +
        (rho * q_doubleprime_py eta) * (|baxterP0 eta sigma rho| +
          |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|)) * ‖k‖ <
      (rho * q_prime_py eta sigma) * (k ^ 2).re) :
    0 < (Npoly eta sigma rho k * (starRingEnd ℂ) (Dpoly eta sigma rho k)).re := by
  have heqN : Npoly eta sigma rho k =
      Complex.I * k ^ 3 - (baxterP0 eta sigma rho : ℝ) * k ^ 2 +
        Complex.I * (baxterP1 eta sigma rho : ℝ) * k +
        (2 * baxterP2 eta sigma rho : ℝ) := by
    unfold Npoly; push_cast; ring
  have heqD : Dpoly eta sigma rho k =
      Complex.I * (rho * q_prime_py eta sigma : ℝ) * k +
        (rho * q_doubleprime_py eta : ℝ) := Dpoly_eq_affine eta sigma rho k
  rw [heqN, heqD]
  exact norm_cubic_mul_conj_affine_re_pos (baxterP0 eta sigma rho)
    (baxterP1 eta sigma rho) (2 * baxterP2 eta sigma rho)
    (rho * q_prime_py eta sigma) (rho * q_doubleprime_py eta) k hk1
    (baxterMu_pos heta0 heta1 hsigma hrho) (baxterNu_pos heta0 heta1 hrho).le hD

/-- **`R(k) ∈ Complex.slitPlane`** — the actual branch-safety fact `baxterPhi`'s differentiability
needs. -/
theorem R_mem_slitPlane {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {k : ℂ} (hk1 : 1 ≤ ‖k‖)
    (hD : ((rho * q_doubleprime_py eta) +
        (rho * q_prime_py eta sigma) * (|baxterP0 eta sigma rho| +
          |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|) +
        (rho * q_doubleprime_py eta) * (|baxterP0 eta sigma rho| +
          |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|)) * ‖k‖ <
      (rho * q_prime_py eta sigma) * (k ^ 2).re)
    (hDne : Dpoly eta sigma rho k ≠ 0) :
    Npoly eta sigma rho k / Dpoly eta sigma rho k ∈ Complex.slitPlane := by
  have hpos := Npoly_mul_conj_Dpoly_re_pos heta0 heta1 hsigma hrho hk1 hD
  have hnormSqpos : 0 < Complex.normSq (Dpoly eta sigma rho k) := Complex.normSq_pos.mpr hDne
  have hdiv_eq : Npoly eta sigma rho k / Dpoly eta sigma rho k =
      (Npoly eta sigma rho k * (starRingEnd ℂ) (Dpoly eta sigma rho k)) *
        ((Complex.normSq (Dpoly eta sigma rho k))⁻¹ : ℝ) := by
    rw [div_eq_mul_inv, Complex.inv_def]; ring
  have hre : (Npoly eta sigma rho k / Dpoly eta sigma rho k).re =
      (Npoly eta sigma rho k * (starRingEnd ℂ) (Dpoly eta sigma rho k)).re *
        (Complex.normSq (Dpoly eta sigma rho k))⁻¹ := by
    rw [hdiv_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have : 0 < (Npoly eta sigma rho k / Dpoly eta sigma rho k).re := by
    rw [hre]; exact mul_pos hpos (inv_pos.mpr hnormSqpos)
  exact Complex.mem_slitPlane_iff.mpr (Or.inl this)

/-! ### Differentiability and derivative bound for `baxterPhi` (Task `POLE.3`, Phase A.3) -/

/-- **`baxterPhi` is differentiable at `k0`, with derivative `(i/σ)·(N'/N-D'/D)`** — combines
`HasDerivAt.div` (quotient rule for `R := Npoly/Dpoly`) with `HasDerivAt.clog` (needs
`R(k0) ∈ slitPlane`, i.e. `R_mem_slitPlane`/`Npoly_mul_conj_Dpoly_re_pos`, A.2). -/
theorem baxterPhi_hasDerivAt (eta sigma rho : ℝ) (n : ℕ) {k0 : ℂ}
    (hNne : Npoly eta sigma rho k0 ≠ 0) (hDne : Dpoly eta sigma rho k0 ≠ 0)
    (hslit : Npoly eta sigma rho k0 / Dpoly eta sigma rho k0 ∈ Complex.slitPlane) :
    HasDerivAt (baxterPhi eta sigma rho n)
      ((Complex.I / (sigma : ℂ)) *
        ((3 * Complex.I * k0 ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k0 +
            Complex.I * (baxterP1 eta sigma rho : ℝ)) / Npoly eta sigma rho k0 -
          (Complex.I * (rho * q_prime_py eta sigma : ℝ)) / Dpoly eta sigma rho k0)) k0 := by
  unfold baxterPhi
  have hN := Npoly_hasDerivAt eta sigma rho k0
  have hD := Dpoly_hasDerivAt eta sigma rho k0
  have hquot := hN.div hD hDne
  have hlog := hquot.clog hslit
  have hmul := hlog.const_mul (Complex.I / (sigma : ℂ))
  have hfinal := hmul.add_const (2 * Real.pi * n / sigma : ℂ)
  refine hfinal.congr_deriv ?_
  simp only [Pi.div_apply]
  have hDne2 : Dpoly eta sigma rho k0 ^ 2 ≠ 0 := pow_ne_zero 2 hDne
  field_simp

/-- **`‖deriv baxterPhi k‖` bound**: `≤ C/(σ‖k‖)` once `‖k‖` exceeds `A.1`'s thresholds. -/
theorem baxterPhi_deriv_bound {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (n : ℕ) {k : ℂ}
    (hNne : Npoly eta sigma rho k ≠ 0) (hDne : Dpoly eta sigma rho k ≠ 0)
    (hslit : Npoly eta sigma rho k / Dpoly eta sigma rho k ∈ Complex.slitPlane)
    (hk1 : 1 ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ ‖k‖)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ ‖k‖) :
    ‖deriv (baxterPhi eta sigma rho n) k‖ ≤
      (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
        (sigma * ‖k‖) := by
  rw [(baxterPhi_hasDerivAt eta sigma rho n hNne hDne hslit).deriv]
  rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsigma]
  have hbound := R_deriv_ratio_bound heta0 heta1 hsigma hrho hk1 hkN hkD
  have hsigmapos : 0 < sigma := hsigma
  calc 1 / sigma *
      ‖(3 * Complex.I * k ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k +
            Complex.I * (baxterP1 eta sigma rho : ℝ)) / Npoly eta sigma rho k -
          Complex.I * (rho * q_prime_py eta sigma : ℝ) / Dpoly eta sigma rho k‖
      ≤ 1 / sigma *
          ((8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
            ‖k‖) := by
        apply mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
          (sigma * ‖k‖) := by ring

/-- **`baxterPhi` is Lipschitz on `closedBall k1 r`** with an explicit constant, given: every
`k` in the ball satisfies `A.1`'s magnitude thresholds (`hMball`) and `A.2`'s branch-safety
threshold (`hDball`), and the whole ball avoids `‖k‖ < M` for the chosen `M ≥ 1`. Combines
`baxterPhi_hasDerivAt`/`Npoly_lower_bound`/`Dpoly_lower_bound`/`R_mem_slitPlane` (well-
definedness + differentiability throughout the ball) with `baxterPhi_deriv_bound` (the norm
bound) via Mathlib's mean-value inequality (`lipschitzOnWith_of_nnnorm_deriv_le` — a disk is
convex, so no sampling is needed, unlike `POLE.2`'s numerical check). -/
theorem baxterPhi_lipschitzOnWith {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (n : ℕ) (k1 : ℂ) (r : ℝ) (M : ℝ) (hM1 : 1 ≤ M)
    (hMball : ∀ k ∈ Metric.closedBall k1 r, M ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ M)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ M)
    (hDball : ∀ k ∈ Metric.closedBall k1 r,
      ((rho * q_doubleprime_py eta) +
          (rho * q_prime_py eta sigma) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|) +
          (rho * q_doubleprime_py eta) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|)) * ‖k‖ <
        (rho * q_prime_py eta sigma) * (k ^ 2).re) (C : NNReal)
    (hC : (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
        (sigma * M) ≤ C) :
    LipschitzOnWith C (baxterPhi eta sigma rho n) (Metric.closedBall k1 r) := by
  have hballfacts : ∀ k ∈ Metric.closedBall k1 r,
      Npoly eta sigma rho k ≠ 0 ∧ Dpoly eta sigma rho k ≠ 0 ∧
        Npoly eta sigma rho k / Dpoly eta sigma rho k ∈ Complex.slitPlane ∧ M ≤ ‖k‖ := by
    intro k hk
    have hk1' : 1 ≤ ‖k‖ := le_trans hM1 (hMball k hk)
    have hkN' : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ ‖k‖ := le_trans hkN (hMball k hk)
    have hkD' : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ ‖k‖ :=
      le_trans hkD (hMball k hk)
    have hNbound := Npoly_lower_bound eta sigma rho k hk1' hkN'
    have hNne : Npoly eta sigma rho k ≠ 0 := by
      intro h; rw [h, norm_zero] at hNbound; nlinarith [pow_pos (lt_of_lt_of_le one_pos hk1') 3]
    have hDbound := Dpoly_lower_bound (eta := eta) (sigma := sigma) (rho := rho) heta0 heta1
      hsigma hrho k
    have hDne : Dpoly eta sigma rho k ≠ 0 := by
      intro h
      rw [h, norm_zero] at hDbound
      have hmupos := baxterMu_pos heta0 heta1 hsigma hrho
      have hnupos := baxterNu_pos heta0 heta1 hrho
      have hkD2 : 2 * (rho * q_doubleprime_py eta) ≤
          (rho * q_prime_py eta sigma) * ‖k‖ := by
        rw [div_le_iff₀ hmupos] at hkD'
        linarith [hkD']
      nlinarith [hDbound, hkD2]
    have hslit : Npoly eta sigma rho k / Dpoly eta sigma rho k ∈ Complex.slitPlane :=
      R_mem_slitPlane heta0 heta1 hsigma hrho hk1' (hDball k hk) hDne
    exact ⟨hNne, hDne, hslit, hMball k hk⟩
  have hconv : Convex ℝ (Metric.closedBall k1 r) := convex_closedBall k1 r
  have hdiff : ∀ k ∈ Metric.closedBall k1 r, DifferentiableAt ℂ (baxterPhi eta sigma rho n) k := by
    intro k hk
    obtain ⟨hNne, hDne, hslit, _⟩ := hballfacts k hk
    exact (baxterPhi_hasDerivAt eta sigma rho n hNne hDne hslit).differentiableAt
  apply hconv.lipschitzOnWith_of_nnnorm_deriv_le hdiff
  intro k hk
  obtain ⟨hNne, hDne, hslit, hMk⟩ := hballfacts k hk
  have hk1' : 1 ≤ ‖k‖ := le_trans hM1 hMk
  have hkN' : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
      |2 * baxterP2 eta sigma rho|) ≤ ‖k‖ := le_trans hkN hMk
  have hkD' : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ ‖k‖ :=
    le_trans hkD hMk
  have hbound := baxterPhi_deriv_bound heta0 heta1 hsigma hrho n hNne hDne hslit hk1' hkN' hkD'
  have hCbound : (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
      (sigma * ‖k‖) ≤ (8 + 4 * |baxterP0 eta sigma rho| +
        2 * |baxterP1 eta sigma rho|) / (sigma * M) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hMk hsigma.le
  rw [← NNReal.coe_le_coe]
  push_cast
  calc ‖deriv (baxterPhi eta sigma rho n) k‖ ≤
      (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
        (sigma * ‖k‖) := hbound
    _ ≤ (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
          (sigma * M) := hCbound
    _ ≤ C := hC

/-! ### Self-map (`MapsTo`) lemma (Task `POLE.3`, Phase A.4) -/

/-- **Generic self-map fact**: a `K`-Lipschitz map on `closedBall k1 r` whose center moves by
at most `r(1-K)` maps the ball into itself — the standard sufficient condition for Banach's
fixed-point theorem. Reusable, not specific to `baxterPhi`/`G_baxter`. -/
theorem mapsTo_closedBall_of_lipschitzOnWith_of_dist_le (phi : ℂ → ℂ) (k1 : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (K : NNReal) (hLip : LipschitzOnWith K phi (Metric.closedBall k1 r))
    (hstep : dist k1 (phi k1) ≤ r * (1 - K)) :
    Set.MapsTo phi (Metric.closedBall k1 r) (Metric.closedBall k1 r) := by
  intro k hk
  rw [Metric.mem_closedBall] at hk ⊢
  have hk1mem : k1 ∈ Metric.closedBall k1 r := Metric.mem_closedBall_self hr
  have h1 : dist (phi k) (phi k1) ≤ K * dist k k1 :=
    hLip.dist_le_mul k (Metric.mem_closedBall.mpr hk) k1 hk1mem
  calc dist (phi k) k1 ≤ dist (phi k) (phi k1) + dist (phi k1) k1 := dist_triangle _ _ _
    _ ≤ K * dist k k1 + dist k1 (phi k1) := by rw [dist_comm (phi k1) k1]; linarith [h1]
    _ ≤ K * r + r * (1 - K) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hk (by positivity)
        · exact hstep
    _ = r := by ring

/-! ### Assembly (Task `POLE.3`, Phase A.5)

`baxter_G_zero_exists_for_n` gets a genuine zero of `G_baxter` in `disk(k1,r)` for a single `n`,
**conditional on a "good guess" hypothesis** (`hstep`) — the one piece of `POLE.3` not closed
in full generality this pass: the numerically-fitted asymptotic guess formula
`Im(k)≈2·ln(Re(k))−2.12` (`proof_notes_baxter.md`, `BAXTER.2`) was found by curve-fitting, not
derived, so a rigorous bound on its error is a separate undertaking from everything above (which
is all unconditional, general-`η` machinery). Matches this project's established pattern for
partially-open problems (`g0_HS_contact_value_of_oz_h_regularity`, `CONTACT.5`): a genuine,
`sorry`-free conditional theorem, with the remaining gap isolated to one explicit, numerically-
validated (`POLE.2`) hypothesis. -/

/-- **`POLE.3`, single-`n` existence**: combines `baxterPhi_lipschitzOnWith`,
`mapsTo_closedBall_of_lipschitzOnWith_of_dist_le`, `G_baxter_pole_exists_of_bounds`, and
`baxterPhi_fixedPt_implies_zero`. -/
theorem baxter_G_zero_exists_for_n (eta sigma rho : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (n : ℕ)
    (k1 : ℂ) (r M : ℝ) (hr : 0 < r) (hM1 : 1 ≤ M)
    (hMball : ∀ k ∈ Metric.closedBall k1 r, M ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ M)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ M)
    (hDball : ∀ k ∈ Metric.closedBall k1 r,
      ((rho * q_doubleprime_py eta) +
          (rho * q_prime_py eta sigma) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|) +
          (rho * q_doubleprime_py eta) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|)) * ‖k‖ <
        (rho * q_prime_py eta sigma) * (k ^ 2).re)
    (K : NNReal) (hK1 : (K : ℝ) < 1)
    (hC : (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
        (sigma * M) ≤ K)
    (hstep : dist k1 (baxterPhi eta sigma rho n k1) ≤ r * (1 - K)) :
    ∃ k ∈ Metric.closedBall k1 r, G_baxter eta sigma rho k = 0 := by
  have hLip := baxterPhi_lipschitzOnWith heta0 heta1 hsigma hrho n k1 r M hM1 hMball hkN hkD
    hDball K hC
  have hMapsTo := mapsTo_closedBall_of_lipschitzOnWith_of_dist_le (baxterPhi eta sigma rho n) k1 r
    hr.le K hLip hstep
  apply G_baxter_pole_exists_of_bounds eta sigma rho k1 r hr K hK1 (baxterPhi eta sigma rho n)
    hMapsTo hLip
  intro k hk hfp
  have hk1' : 1 ≤ ‖k‖ := le_trans hM1 (hMball k hk)
  have hkN' : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
      |2 * baxterP2 eta sigma rho|) ≤ ‖k‖ := le_trans hkN (hMball k hk)
  have hNbound := Npoly_lower_bound eta sigma rho k hk1' hkN'
  have hNne : Npoly eta sigma rho k ≠ 0 := by
    intro h; rw [h, norm_zero] at hNbound; nlinarith [pow_pos (lt_of_lt_of_le one_pos hk1') 3]
  have hDbound := Dpoly_lower_bound (eta := eta) (sigma := sigma) (rho := rho) heta0 heta1
    hsigma hrho k
  have hkD' : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ ‖k‖ :=
    le_trans hkD (hMball k hk)
  have hDne : Dpoly eta sigma rho k ≠ 0 := by
    intro h
    rw [h, norm_zero] at hDbound
    have hmupos := baxterMu_pos heta0 heta1 hsigma hrho
    have hnupos := baxterNu_pos heta0 heta1 hrho
    have hkD2 : 2 * (rho * q_doubleprime_py eta) ≤ (rho * q_prime_py eta sigma) * ‖k‖ := by
      rw [div_le_iff₀ hmupos] at hkD'
      linarith [hkD']
    nlinarith [hDbound, hkD2]
  exact baxterPhi_fixedPt_implies_zero eta sigma rho hsigma n hNne hDne hfp

/-- **`POLE.3`, standalone pole family**: extracts the witness-choice function that was
previously buried inside `G_baxter_zeros_infinite`'s proof (via an internal `choose`) as a
reusable named object — `POLE.4`'s `h_explicit` (`BaxterResidue.lean`) is stated generically
over an abstract `kfam : ℕ → ℂ`, but eventually needs a *concrete* instantiation, which this
theorem now supplies directly (`g`), together with the injectivity and membership/zero facts
needed to derive both `G_baxter_zeros_infinite` (below, now a thin corollary) and, downstream,
growth bounds on `‖g n‖` (via `hgmem`+`hk1re`, `(g n).re ≥ 2π(n+N)/σ - r`). -/
theorem G_baxter_pole_family_exists {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {r M : ℝ} (hr : 0 < r) (hrspace : r < Real.pi / sigma)
    (hM1 : 1 ≤ M) (N : ℕ) (k1 : ℕ → ℂ)
    (hk1re : ∀ n, N ≤ n → (k1 n).re = 2 * Real.pi * n / sigma)
    (hMball : ∀ n, N ≤ n → ∀ k ∈ Metric.closedBall (k1 n) r, M ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ M)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ M)
    (hDball : ∀ n, N ≤ n → ∀ k ∈ Metric.closedBall (k1 n) r,
      ((rho * q_doubleprime_py eta) +
          (rho * q_prime_py eta sigma) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|) +
          (rho * q_doubleprime_py eta) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|)) * ‖k‖ <
        (rho * q_prime_py eta sigma) * (k ^ 2).re)
    (K : NNReal) (hK1 : (K : ℝ) < 1)
    (hC : (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
        (sigma * M) ≤ K)
    (hstep : ∀ n, N ≤ n → dist (k1 n) (baxterPhi eta sigma rho n (k1 n)) ≤ r * (1 - K)) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧
      (∀ n, g n ∈ Metric.closedBall (k1 (n + N)) r) ∧ (∀ n, G_baxter eta sigma rho (g n) = 0) := by
  have hwitness : ∀ n : ℕ,
      ∃ k ∈ Metric.closedBall (k1 (n + N)) r, G_baxter eta sigma rho k = 0 := by
    intro n
    exact baxter_G_zero_exists_for_n eta sigma rho heta0 heta1 hsigma hrho (n + N) (k1 (n + N))
      r M hr hM1 (hMball (n + N) (Nat.le_add_left N n)) hkN hkD
      (hDball (n + N) (Nat.le_add_left N n)) K hK1 hC (hstep (n + N) (Nat.le_add_left N n))
  choose g hgmem hgzero using hwitness
  refine ⟨g, ?_, hgmem, hgzero⟩
  intro m m' hmm'
  by_contra hne
  have hdist2r : dist (k1 (m + N)) (k1 (m' + N)) ≤ 2 * r := by
    calc dist (k1 (m + N)) (k1 (m' + N)) ≤
        dist (k1 (m + N)) (g m) + dist (g m) (k1 (m' + N)) := dist_triangle _ _ _
      _ = dist (g m) (k1 (m + N)) + dist (g m') (k1 (m' + N)) := by
          rw [dist_comm (k1 (m + N)) (g m), hmm']
      _ ≤ r + r := by
          apply add_le_add
          · exact Metric.mem_closedBall.mp (hgmem m)
          · exact Metric.mem_closedBall.mp (hgmem m')
      _ = 2 * r := by ring
  have hspacing : Real.pi * 2 / sigma ≤ dist (k1 (m + N)) (k1 (m' + N)) := by
    have hre : (k1 (m + N)).re - (k1 (m' + N)).re =
        2 * Real.pi / sigma * ((m : ℝ) - (m' : ℝ)) := by
      rw [hk1re (m + N) (Nat.le_add_left N m), hk1re (m' + N) (Nat.le_add_left N m')]
      push_cast
      ring
    have hnat : (1 : ℝ) ≤ |((m : ℝ) - (m' : ℝ))| := by
      have hmm : (m : ℤ) - (m' : ℤ) ≠ 0 := by
        simpa using sub_ne_zero.mpr (fun h => hne (by exact_mod_cast h))
      have h1 : (1 : ℤ) ≤ |(m : ℤ) - (m' : ℤ)| := Int.one_le_abs hmm
      have h2 : ((|(m : ℤ) - (m' : ℤ)| : ℤ) : ℝ) = |((m : ℝ) - (m' : ℝ))| := by push_cast; ring
      rw [← h2]
      exact_mod_cast h1
    have hre2 : |((k1 (m + N)).re - (k1 (m' + N)).re)| = 2 * Real.pi / sigma *
        |((m : ℝ) - (m' : ℝ))| := by
      rw [hre, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi / sigma)]
    have hreabs : Real.pi * 2 / sigma ≤ |((k1 (m + N)).re - (k1 (m' + N)).re)| := by
      rw [hre2]
      calc Real.pi * 2 / sigma = 2 * Real.pi / sigma * 1 := by ring
        _ ≤ 2 * Real.pi / sigma * |((m:ℝ) - (m':ℝ))| := by
            apply mul_le_mul_of_nonneg_left hnat (by positivity)
    have hdistre : |((k1 (m + N) - k1 (m' + N)).re)| ≤ ‖k1 (m + N) - k1 (m' + N)‖ :=
      Complex.abs_re_le_norm _
    rw [Complex.sub_re] at hdistre
    rw [dist_eq_norm]
    linarith [hreabs, hdistre]
  have heq : Real.pi * 2 / sigma = 2 * (Real.pi / sigma) := by ring
  linarith [hdist2r, hspacing, hrspace, hr, heq]

/-- **`POLE.3`/`POLE.5` growth-rate corollary**:
`G_baxter_pole_family_exists`'s witness `g` satisfies a linear-in-`n` lower bound `c·n+d ≤ ‖g n‖`
— exactly the shape
`h_explicit_summable_of_pole_family`/`h_explicit_series_hasDerivAt` (`BaxterResidue.lean`) need to
be instantiated on a *concrete* pole family, not just an abstract one. Follows from `hgmem`
(`g n` lies in a ball of radius `r` around `k1(n+N)`) plus `hk1re` (`k1`'s real part grows
linearly) via the reverse triangle inequality: `‖g n‖ ≥ (k1(n+N)).re - r`. The extra hypothesis
`hN1 : 1 ≤ N` (mild — `N` is where the asymptotic regime starts, always chosen `≥1` in practice)
ensures the intercept `d := 2πN/σ - r` is strictly positive, using `hrspace : r < π/σ`. -/
theorem G_baxter_pole_family_exists_growth {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {r M : ℝ} (hr : 0 < r) (hrspace : r < Real.pi / sigma)
    (hM1 : 1 ≤ M) (N : ℕ) (hN1 : 1 ≤ N) (k1 : ℕ → ℂ)
    (hk1re : ∀ n, N ≤ n → (k1 n).re = 2 * Real.pi * n / sigma)
    (hMball : ∀ n, N ≤ n → ∀ k ∈ Metric.closedBall (k1 n) r, M ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ M)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ M)
    (hDball : ∀ n, N ≤ n → ∀ k ∈ Metric.closedBall (k1 n) r,
      ((rho * q_doubleprime_py eta) +
          (rho * q_prime_py eta sigma) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|) +
          (rho * q_doubleprime_py eta) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|)) * ‖k‖ <
        (rho * q_prime_py eta sigma) * (k ^ 2).re)
    (K : NNReal) (hK1 : (K : ℝ) < 1)
    (hC : (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
        (sigma * M) ≤ K)
    (hstep : ∀ n, N ≤ n → dist (k1 n) (baxterPhi eta sigma rho n (k1 n)) ≤ r * (1 - K)) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧
      (∀ n, g n ∈ Metric.closedBall (k1 (n + N)) r) ∧ (∀ n, G_baxter eta sigma rho (g n) = 0) ∧
      ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖g n‖ := by
  obtain ⟨g, hginj, hgmem, hgzero⟩ := G_baxter_pole_family_exists heta0 heta1 hsigma hrho hr
    hrspace hM1 N k1 hk1re hMball hkN hkD hDball K hK1 hC hstep
  refine ⟨g, hginj, hgmem, hgzero, 2 * Real.pi / sigma, 2 * Real.pi * N / sigma - r, ?_, ?_, ?_⟩
  · positivity
  · have h1 : Real.pi / sigma < 2 * Real.pi * (N:ℝ) / sigma := by
      have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
      rw [div_lt_div_iff_of_pos_right hsigma]
      nlinarith [Real.pi_pos, hN1']
    linarith [hrspace, h1]
  · intro n
    have hmem := hgmem n
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    have hre := hk1re (n + N) (Nat.le_add_left N n)
    have hstep1 : ‖k1 (n + N)‖ - ‖k1 (n + N) - g n‖ ≤ ‖g n‖ := by
      have h := norm_add_le (g n) (k1 (n + N) - g n)
      rw [show g n + (k1 (n + N) - g n) = k1 (n + N) from by ring] at h
      linarith [h]
    have hnormeq : ‖k1 (n + N) - g n‖ = ‖g n - k1 (n + N)‖ := by rw [← norm_neg]; ring_nf
    have hre_le : (k1 (n + N)).re ≤ ‖k1 (n + N)‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
    have hgn_norm : ‖g n - k1 (n + N)‖ ≤ r := hmem
    have hfinal : 2 * Real.pi * ((n:ℝ) + N) / sigma - r ≤ ‖g n‖ := by
      have hre' : 2 * Real.pi * ((n:ℝ) + N) / sigma = (k1 (n + N)).re := by
        rw [hre]; push_cast; ring
      calc 2 * Real.pi * ((n:ℝ) + N) / sigma - r = (k1 (n + N)).re - r := by rw [hre']
        _ ≤ ‖k1 (n + N)‖ - r := by linarith [hre_le]
        _ ≤ ‖k1 (n + N)‖ - ‖k1 (n + N) - g n‖ := by linarith [hgn_norm, hnormeq]
        _ ≤ ‖g n‖ := hstep1
    have heq : 2 * Real.pi * ((n:ℝ) + N) / sigma - r =
        2 * Real.pi / sigma * (n:ℝ) + (2 * Real.pi * (N:ℝ) / sigma - r) := by ring
    linarith [hfinal, heq]

/-- **`POLE.3`, infinitude of `G_baxter`'s zero set** — thin corollary of
`G_baxter_pole_family_exists` via `Set.infinite_of_injective_forall_mem`. -/
theorem G_baxter_zeros_infinite {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {r M : ℝ} (hr : 0 < r) (hrspace : r < Real.pi / sigma)
    (hM1 : 1 ≤ M) (N : ℕ) (k1 : ℕ → ℂ)
    (hk1re : ∀ n, N ≤ n → (k1 n).re = 2 * Real.pi * n / sigma)
    (hMball : ∀ n, N ≤ n → ∀ k ∈ Metric.closedBall (k1 n) r, M ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ M)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ M)
    (hDball : ∀ n, N ≤ n → ∀ k ∈ Metric.closedBall (k1 n) r,
      ((rho * q_doubleprime_py eta) +
          (rho * q_prime_py eta sigma) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|) +
          (rho * q_doubleprime_py eta) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|)) * ‖k‖ <
        (rho * q_prime_py eta sigma) * (k ^ 2).re)
    (K : NNReal) (hK1 : (K : ℝ) < 1)
    (hC : (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
        (sigma * M) ≤ K)
    (hstep : ∀ n, N ≤ n → dist (k1 n) (baxterPhi eta sigma rho n (k1 n)) ≤ r * (1 - K)) :
    {k : ℂ | G_baxter eta sigma rho k = 0}.Infinite := by
  obtain ⟨g, hinj, _hgmem, hgzero⟩ := G_baxter_pole_family_exists heta0 heta1 hsigma hrho hr
    hrspace hM1 N k1 hk1re hMball hkN hkD hDball K hK1 hC hstep
  apply Set.infinite_of_injective_forall_mem hinj
  intro n
  exact hgzero n

/-- **`POLE.3`, final statement**: `1-Q̂(k)` has infinitely many zeros — transfers
`G_baxter_zeros_infinite` through `Qhat_pole_iff_G_baxter_zero` (valid for `k≠0`; removing the
single point `k=0` from an infinite set leaves it infinite). This is `POLE.3`'s originally-
stated goal, conditional on the same "good guess" hypothesis as `G_baxter_zeros_infinite`. -/
theorem Qhat_complex_zeros_infinite {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {r M : ℝ} (hr : 0 < r) (hrspace : r < Real.pi / sigma)
    (hM1 : 1 ≤ M) (N : ℕ) (k1 : ℕ → ℂ)
    (hk1re : ∀ n, N ≤ n → (k1 n).re = 2 * Real.pi * n / sigma)
    (hMball : ∀ n, N ≤ n → ∀ k ∈ Metric.closedBall (k1 n) r, M ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ M)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ M)
    (hDball : ∀ n, N ≤ n → ∀ k ∈ Metric.closedBall (k1 n) r,
      ((rho * q_doubleprime_py eta) +
          (rho * q_prime_py eta sigma) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|) +
          (rho * q_doubleprime_py eta) * (|baxterP0 eta sigma rho| +
            |baxterP1 eta sigma rho| + |2 * baxterP2 eta sigma rho|)) * ‖k‖ <
        (rho * q_prime_py eta sigma) * (k ^ 2).re)
    (K : NNReal) (hK1 : (K : ℝ) < 1)
    (hC : (8 + 4 * |baxterP0 eta sigma rho| + 2 * |baxterP1 eta sigma rho|) /
        (sigma * M) ≤ K)
    (hstep : ∀ n, N ≤ n → dist (k1 n) (baxterPhi eta sigma rho n (k1 n)) ≤ r * (1 - K)) :
    {k : ℂ | 1 - Qhat_complex eta sigma rho k = 0}.Infinite := by
  have hGinf := G_baxter_zeros_infinite heta0 heta1 hsigma hrho hr hrspace hM1 N k1 hk1re hMball
    hkN hkD hDball K hK1 hC hstep
  have hsub : {k : ℂ | G_baxter eta sigma rho k = 0} \ {0} ⊆
      {k : ℂ | 1 - Qhat_complex eta sigma rho k = 0} := by
    intro k hk
    obtain ⟨hzero, hne⟩ := hk
    rw [Set.mem_singleton_iff] at hne
    exact (Qhat_pole_iff_G_baxter_zero eta sigma rho hsigma hne).mpr hzero
  exact (hGinf.sdiff (Set.finite_singleton 0)).mono hsub

/-! ### Non-degeneracy at a zero (Task `POLE.4`, discharging `Hhat_residue_at_pole`'s
hypotheses)

Both facts below are magnitude-bound estimates in the same style as `A.1`/`A.2` — no
asymptotic/logarithmic control on `Im(k)` needed, just `‖k‖` past an explicit threshold (plus,
for the second, the mild sign fact `0 ≤ k.im`, matching the upper-half-plane poles `POLE.3`
constructs). -/

/-- **`G_baxter_deriv` magnitude at a zero of `G_baxter`** (Task `POLE.5`): if
`G_baxter(k)=0` and `‖k‖` exceeds an explicit threshold, `‖G_baxter_deriv(k)‖ ≥ σ‖k‖³/8` — a
genuine, direct (non-contradiction) derivation. Substituting `Npoly(k)=Dpoly(k)e^{-ikσ}` (from
`G_baxter(k)=0`) into `G_baxter_deriv(k)=Npoly'(k)-Dpoly'(k)e^{-ikσ}+iσDpoly(k)e^{-ikσ}` gives
`G_baxter_deriv(k) = [Npoly'(k)-μi·e^{-ikσ}] + iσNpoly(k)`; bounding the bracketed correction
term by `(3+2a+b)‖k‖²+2‖Npoly(k)‖/‖k‖` and the main term below by `σ‖k‖³/2` (via `Npoly`'s
lower bound and `‖k‖` large) leaves `≥σ‖k‖³/8` once `‖k‖` clears a further explicit threshold.
`G_baxter_deriv_ne_zero_of_large` below is now a one-line corollary. -/
theorem G_baxter_deriv_lower_bound_of_zero {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {k : ℂ} (hzero : G_baxter eta sigma rho k = 0)
    (hk1 : 1 ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ ‖k‖)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ ‖k‖)
    (hkS : 4 / sigma ≤ ‖k‖)
    (hkT : 8 * (3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) / sigma
        ≤ ‖k‖) :
    sigma * ‖k‖ ^ 3 / 8 ≤ ‖G_baxter_deriv eta sigma rho k‖ := by
  set mu : ℝ := rho * q_prime_py eta sigma with hmudef
  set nu : ℝ := rho * q_doubleprime_py eta with hnudef
  have hmupos := baxterMu_pos heta0 heta1 hsigma hrho
  have hk0 : 0 < ‖k‖ := lt_of_lt_of_le one_pos hk1
  have hNbound := Npoly_lower_bound eta sigma rho k hk1 hkN
  have hDbound := Dpoly_lower_bound (eta := eta) (sigma := sigma) (rho := rho) heta0 heta1
    hsigma hrho k
  have hkD2 : 2 * nu ≤ mu * ‖k‖ := by
    rw [div_le_iff₀ hmupos] at hkD; linarith [hkD]
  have hDhalf : mu * ‖k‖ / 2 ≤ ‖Dpoly eta sigma rho k‖ := by linarith
  have hDpos : 0 < ‖Dpoly eta sigma rho k‖ := by nlinarith [hDhalf, hmupos, hk0]
  have hNeqD : Npoly eta sigma rho k =
      Dpoly eta sigma rho k * Complex.exp (-Complex.I * k * sigma) := by
    unfold G_baxter at hzero; linear_combination hzero
  have hratio : mu / ‖Dpoly eta sigma rho k‖ ≤ 2 / ‖k‖ := by
    rw [div_le_div_iff₀ hDpos hk0]; linarith [hDhalf]
  have hExpBound : ‖Complex.I * (mu : ℂ) * Complex.exp (-Complex.I * k * sigma)‖ ≤
      2 * ‖Npoly eta sigma rho k‖ / ‖k‖ := by
    have hnormI : ‖Complex.I * (mu : ℂ) * Complex.exp (-Complex.I * k * sigma)‖ =
        mu * ‖Complex.exp (-Complex.I * k * sigma)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hmupos]
      ring
    have hexpnorm : ‖Complex.exp (-Complex.I * k * sigma)‖ =
        ‖Npoly eta sigma rho k‖ / ‖Dpoly eta sigma rho k‖ := by
      rw [hNeqD, norm_mul]; field_simp
    rw [hnormI, hexpnorm,
      show mu * (‖Npoly eta sigma rho k‖ / ‖Dpoly eta sigma rho k‖) =
        ‖Npoly eta sigma rho k‖ * (mu / ‖Dpoly eta sigma rho k‖) by ring,
      show 2 * ‖Npoly eta sigma rho k‖ / ‖k‖ =
        ‖Npoly eta sigma rho k‖ * (2 / ‖k‖) by ring]
    exact mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
  have hNderivUpper := Npoly_deriv_bound eta sigma rho k hk1
  have hc2 : Dpoly eta sigma rho k * (-Complex.I * sigma) *
      Complex.exp (-Complex.I * k * sigma) = Npoly eta sigma rho k * (-Complex.I * sigma) := by
    rw [mul_comm (Dpoly eta sigma rho k) (-Complex.I * sigma), mul_assoc, ← hNeqD]
    ring
  have hkey : G_baxter_deriv eta sigma rho k =
      ((3 * Complex.I * k ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k +
          Complex.I * (baxterP1 eta sigma rho : ℝ)) -
        Complex.I * (mu : ℝ) * Complex.exp (-Complex.I * k * sigma)) +
      Npoly eta sigma rho k * (Complex.I * sigma) := by
    unfold G_baxter_deriv
    linear_combination -hc2
  have hsigmaNorm : ‖Npoly eta sigma rho k * (Complex.I * sigma)‖ =
      sigma * ‖Npoly eta sigma rho k‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsigma]
    ring
  have hcorrbound : ‖(3 * Complex.I * k ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k +
      Complex.I * (baxterP1 eta sigma rho : ℝ)) -
      Complex.I * (mu : ℝ) * Complex.exp (-Complex.I * k * sigma)‖ ≤
      (3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) * ‖k‖ ^ 2 +
        2 * ‖Npoly eta sigma rho k‖ / ‖k‖ := by
    calc ‖(3 * Complex.I * k ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k +
        Complex.I * (baxterP1 eta sigma rho : ℝ)) -
        Complex.I * (mu : ℝ) * Complex.exp (-Complex.I * k * sigma)‖
        ≤ ‖(3 * Complex.I * k ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k +
            Complex.I * (baxterP1 eta sigma rho : ℝ))‖ +
          ‖Complex.I * (mu : ℝ) * Complex.exp (-Complex.I * k * sigma)‖ := norm_sub_le _ _
      _ ≤ (3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) * ‖k‖ ^ 2 +
          2 * ‖Npoly eta sigma rho k‖ / ‖k‖ := by linarith [hNderivUpper, hExpBound]
  have hlow : sigma * ‖Npoly eta sigma rho k‖ -
      ((3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) * ‖k‖ ^ 2 +
        2 * ‖Npoly eta sigma rho k‖ / ‖k‖) ≤ ‖G_baxter_deriv eta sigma rho k‖ := by
    rw [hkey]
    set A : ℂ := (3 * Complex.I * k ^ 2 - 2 * (baxterP0 eta sigma rho : ℝ) * k +
        Complex.I * (baxterP1 eta sigma rho : ℝ)) -
      Complex.I * (mu : ℝ) * Complex.exp (-Complex.I * k * sigma) with hAdef
    set B : ℂ := Npoly eta sigma rho k * (Complex.I * sigma) with hBdef
    have h1 := norm_sub_le (A + B) A
    rw [show A + B - A = B by ring, hBdef, hsigmaNorm] at h1
    linarith [hcorrbound]
  have hSlarge : sigma / 2 ≤ sigma - 2 / ‖k‖ := by
    have h1 : 2 / ‖k‖ ≤ sigma / 2 := by
      rw [div_le_div_iff₀ hk0 (by norm_num : (0:ℝ) < 2)]
      rw [div_le_iff₀ hsigma] at hkS
      nlinarith [hkS]
    linarith
  have hNmain : sigma * ‖k‖ ^ 3 / 4 ≤
      sigma * ‖Npoly eta sigma rho k‖ - 2 * ‖Npoly eta sigma rho k‖ / ‖k‖ := by
    have hstep1 : sigma / 2 * ‖Npoly eta sigma rho k‖ ≤
        (sigma - 2 / ‖k‖) * ‖Npoly eta sigma rho k‖ :=
      mul_le_mul_of_nonneg_right hSlarge (norm_nonneg _)
    have hstep2 : sigma / 2 * (‖k‖ ^ 3 / 2) ≤ sigma / 2 * ‖Npoly eta sigma rho k‖ :=
      mul_le_mul_of_nonneg_left hNbound (by positivity)
    have hexpand : (sigma - 2 / ‖k‖) * ‖Npoly eta sigma rho k‖ =
        sigma * ‖Npoly eta sigma rho k‖ - 2 * ‖Npoly eta sigma rho k‖ / ‖k‖ := by ring
    nlinarith [hstep1, hstep2, hexpand]
  have hthresh : (3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) *
      ‖k‖ ^ 2 ≤ sigma * ‖k‖ ^ 3 / 8 := by
    rw [div_le_iff₀ hsigma] at hkT
    have hk2pos : 0 < ‖k‖ ^ 2 := by positivity
    nlinarith [hkT, hk2pos]
  nlinarith [hlow, hNmain, hthresh]

/-- **Simple-zero criterion**: if `G_baxter(k)=0` and `‖k‖` exceeds an explicit threshold,
the zero is simple (`G_baxter_deriv(k)≠0`) — one-line corollary of
`G_baxter_deriv_lower_bound_of_zero`. -/
theorem G_baxter_deriv_ne_zero_of_large {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {k : ℂ} (hzero : G_baxter eta sigma rho k = 0)
    (hk1 : 1 ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ ‖k‖)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ ‖k‖)
    (hkS : 4 / sigma ≤ ‖k‖)
    (hkT : 8 * (3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) / sigma
        ≤ ‖k‖) :
    G_baxter_deriv eta sigma rho k ≠ 0 := by
  have hbound := G_baxter_deriv_lower_bound_of_zero heta0 heta1 hsigma hrho hzero hk1 hkN hkD hkS
    hkT
  intro hcontra
  rw [hcontra, norm_zero] at hbound
  have hk0 : 0 < ‖k‖ := lt_of_lt_of_le one_pos hk1
  nlinarith [hbound, hsigma, pow_pos hk0 3]

/-- **`G_baxter(-k)` magnitude** (Task `POLE.5`): if `Im(k)≥0` and `‖k‖≥1` with `‖k‖` past
`Npoly`'s threshold, `‖G_baxter(-k)‖ ≥ ‖k‖³/2 - (μ‖k‖+ν)` — a genuine, unconditional derivation
(no zero-hypothesis on `k` or `-k` needed at all, unlike `G_baxter_deriv`'s case). Proof:
`|e^{-i(-k)σ}|=|e^{ikσ}|=e^{-σ\cdot Im(k)}≤1` since `Im(k)≥0` (**no** asymptotic control on
`Im(k)`'s growth needed), so `‖Dpoly(-k)e^{-i(-k)σ}‖ ≤ ‖Dpoly(-k)‖ ≤ μ‖k‖+ν` (affine upper
bound), and reverse-triangle-inequality against `Npoly(-k)`'s cubic lower bound `‖k‖³/2` gives
the result directly. `G_baxter_neg_ne_zero_of_large` below is now a one-line corollary. -/
theorem G_baxter_neg_lower_bound {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {k : ℂ} (hkim : 0 ≤ k.im) (hk1 : 1 ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ ‖k‖) :
    ‖k‖ ^ 3 / 2 - (rho * q_prime_py eta sigma * ‖k‖ + rho * q_doubleprime_py eta) ≤
      ‖G_baxter eta sigma rho (-k)‖ := by
  set mu : ℝ := rho * q_prime_py eta sigma with hmudef
  set nu : ℝ := rho * q_doubleprime_py eta with hnudef
  have hmupos := baxterMu_pos heta0 heta1 hsigma hrho
  have hnupos := baxterNu_pos heta0 heta1 hrho
  have hnegknorm : ‖-k‖ = ‖k‖ := norm_neg k
  have hNbound : ‖k‖ ^ 3 / 2 ≤ ‖Npoly eta sigma rho (-k)‖ := by
    have := Npoly_lower_bound eta sigma rho (-k) (by rw [hnegknorm]; exact hk1)
      (by rw [hnegknorm]; exact hkN)
    rwa [hnegknorm] at this
  have hDbound : ‖Dpoly eta sigma rho (-k)‖ ≤ mu * ‖k‖ + nu := by
    rw [Dpoly_eq_affine]
    calc ‖Complex.I * (mu : ℝ) * (-k) + (nu : ℝ)‖
        ≤ ‖Complex.I * (mu : ℝ) * (-k)‖ + ‖((nu : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = mu * ‖k‖ + nu := by
          rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmupos, abs_of_pos hnupos, norm_neg]
          ring
  have hexpbound : ‖Complex.exp (-Complex.I * (-k) * sigma)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    have hre : (-Complex.I * (-k) * sigma).re = -(sigma * k.im) := by
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [hre]
    have hnonneg : 0 ≤ sigma * k.im := mul_nonneg hsigma.le hkim
    calc Real.exp (-(sigma * k.im)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hDexpbound : ‖Dpoly eta sigma rho (-k) * Complex.exp (-Complex.I * (-k) * sigma)‖ ≤
      mu * ‖k‖ + nu := by
    rw [norm_mul]
    have hnn : 0 ≤ mu * ‖k‖ + nu := add_nonneg (mul_nonneg hmupos.le (norm_nonneg k)) hnupos.le
    calc ‖Dpoly eta sigma rho (-k)‖ * ‖Complex.exp (-Complex.I * (-k) * sigma)‖
        ≤ (mu * ‖k‖ + nu) * 1 := mul_le_mul hDbound hexpbound (norm_nonneg _) hnn
      _ = mu * ‖k‖ + nu := by ring
  have hkey : G_baxter eta sigma rho (-k) = Npoly eta sigma rho (-k) +
      (-(Dpoly eta sigma rho (-k) * Complex.exp (-Complex.I * (-k) * sigma))) := by
    unfold G_baxter; ring
  set A : ℂ := Npoly eta sigma rho (-k) with hAdef
  set B : ℂ := -(Dpoly eta sigma rho (-k) * Complex.exp (-Complex.I * (-k) * sigma)) with hBdef
  have hBbound : ‖B‖ ≤ mu * ‖k‖ + nu := by rw [hBdef, norm_neg]; exact hDexpbound
  have h1 := norm_sub_le (A + B) B
  rw [show A + B - B = A by ring] at h1
  rw [hkey]
  linarith [hNbound, hBbound, h1]

/-- **Lower-half-plane non-vanishing**: if `Im(k)≥0` and `‖k‖` exceeds an explicit threshold,
`G_baxter(-k)≠0` — one-line corollary of `G_baxter_neg_lower_bound`. -/
theorem G_baxter_neg_ne_zero_of_large {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {k : ℂ} (hkim : 0 ≤ k.im) (hk1 : 1 ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ ‖k‖)
    (hkU : rho * q_prime_py eta sigma * ‖k‖ + rho * q_doubleprime_py eta < ‖k‖ ^ 3 / 2) :
    G_baxter eta sigma rho (-k) ≠ 0 := by
  have hbound := G_baxter_neg_lower_bound heta0 heta1 hsigma hrho hkim hk1 hkN
  intro hcontra
  rw [hcontra, norm_zero] at hbound
  linarith [hbound, hkU]

/-! ### `|exp(-ikσ)|` bounds at a zero (Task `POLE.5`, A.2)

At a zero `k` of `G_baxter`, `Npoly(k)=Dpoly(k)e^{-ikσ}` gives `|e^{-ikσ}| =
‖Npoly(k)‖/‖Dpoly(k)‖` — a ratio of a cubic-growing numerator to a linear-growing denominator,
hence `Θ(‖k‖²)` both directions. Combined with `|e^{ikr}| = |e^{-ikσ}|^{-r/σ}` (via `Real.rpow`,
**no** `Complex.log`/branch-cut handling needed), the lower bound here gives the upper bound on
`|e^{ikr}|` that drives `residue_term`'s `n^{1-2r/σ}` decay. -/

/-- **`|exp(-ikσ)|` lower bound** at a zero of `G_baxter`: `Θ(‖k‖²)` from below. -/
theorem abs_exp_neg_ikn_sigma_lower {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {k : ℂ} (hzero : G_baxter eta sigma rho k = 0)
    (hk1 : 1 ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ ‖k‖)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ ‖k‖) :
    ‖k‖ ^ 2 / (4 * (rho * q_prime_py eta sigma)) ≤
      ‖Complex.exp (-Complex.I * k * sigma)‖ := by
  set mu : ℝ := rho * q_prime_py eta sigma with hmudef
  set nu : ℝ := rho * q_doubleprime_py eta with hnudef
  have hmupos := baxterMu_pos heta0 heta1 hsigma hrho
  have hk0 : 0 < ‖k‖ := lt_of_lt_of_le one_pos hk1
  have hNbound := Npoly_lower_bound eta sigma rho k hk1 hkN
  have hDub := Dpoly_upper_bound heta0 heta1 hsigma hrho k
  rw [← hmudef, ← hnudef] at hDub
  have hkD2 : 2 * nu ≤ mu * ‖k‖ := by
    rw [div_le_iff₀ hmupos] at hkD; linarith [hkD]
  have hmuknn : 0 ≤ mu * ‖k‖ := mul_nonneg hmupos.le hk0.le
  have hDub2 : ‖Dpoly eta sigma rho k‖ ≤ 2 * mu * ‖k‖ := by linarith [hDub, hkD2, hmuknn]
  have hDpos : 0 < ‖Dpoly eta sigma rho k‖ := by
    have hDlb := Dpoly_lower_bound (eta := eta) (sigma := sigma) (rho := rho) heta0 heta1
      hsigma hrho k
    rw [← hmudef, ← hnudef] at hDlb
    nlinarith [hDlb, hkD2]
  have hNeqD : Npoly eta sigma rho k =
      Dpoly eta sigma rho k * Complex.exp (-Complex.I * k * sigma) := by
    unfold G_baxter at hzero; linear_combination hzero
  have hexpnorm : ‖Complex.exp (-Complex.I * k * sigma)‖ =
      ‖Npoly eta sigma rho k‖ / ‖Dpoly eta sigma rho k‖ := by
    rw [hNeqD, norm_mul]; field_simp
  rw [hexpnorm, div_le_div_iff₀ (by positivity) hDpos]
  nlinarith [hNbound, hDub2, hk0, hmupos, sq_nonneg ‖k‖]

/-- **`|exp(-ikσ)|` upper bound** at a zero of `G_baxter`: `Θ(‖k‖²)` from above. -/
theorem abs_exp_neg_ikn_sigma_upper {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) {k : ℂ} (hzero : G_baxter eta sigma rho k = 0)
    (hk1 : 1 ≤ ‖k‖)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ ‖k‖) :
    ‖Complex.exp (-Complex.I * k * sigma)‖ ≤
      2 * (1 + |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) * ‖k‖ ^ 2 / (rho * q_prime_py eta sigma) := by
  set mu : ℝ := rho * q_prime_py eta sigma with hmudef
  set nu : ℝ := rho * q_doubleprime_py eta with hnudef
  have hmupos := baxterMu_pos heta0 heta1 hsigma hrho
  have hk0 : 0 < ‖k‖ := lt_of_lt_of_le one_pos hk1
  have hNub := Npoly_upper_bound eta sigma rho k hk1
  have hDlb := Dpoly_lower_bound (eta := eta) (sigma := sigma) (rho := rho) heta0 heta1
    hsigma hrho k
  have hkD2 : 2 * nu ≤ mu * ‖k‖ := by
    rw [div_le_iff₀ hmupos] at hkD; linarith [hkD]
  have hDlb2 : mu * ‖k‖ / 2 ≤ ‖Dpoly eta sigma rho k‖ := by linarith [hDlb, hkD2]
  have hDpos : 0 < ‖Dpoly eta sigma rho k‖ := by nlinarith [hDlb2, hmupos, hk0]
  have hNeqD : Npoly eta sigma rho k =
      Dpoly eta sigma rho k * Complex.exp (-Complex.I * k * sigma) := by
    unfold G_baxter at hzero; linear_combination hzero
  have hexpnorm : ‖Complex.exp (-Complex.I * k * sigma)‖ =
      ‖Npoly eta sigma rho k‖ / ‖Dpoly eta sigma rho k‖ := by
    rw [hNeqD, norm_mul]; field_simp
  rw [hexpnorm, div_le_div_iff₀ hDpos (by positivity)]
  have hcoeff_nn : (0:ℝ) ≤
      2 * (1 + |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) * ‖k‖ ^ 2 := by positivity
  have hstep1 := mul_le_mul_of_nonneg_left hDlb2 hcoeff_nn
  have hstep2 := mul_le_mul_of_nonneg_right hNub hmupos.le
  have hringeq : 2 * (1 + |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
      |2 * baxterP2 eta sigma rho|) * ‖k‖ ^ 2 * (mu * ‖k‖ / 2) =
      (1 + |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) * ‖k‖ ^ 3 * mu := by ring
  linarith [hstep1, hstep2, hringeq]

/-- **`|exp(ikr)| = |exp(-ikσ)|^{-r/σ}`**, purely via `Real.rpow` algebra on the real parts
(`(Ikr).re = -r·Im(k)`, `(-Ikσ).re = σ·Im(k)`) — no `Complex.log`/branch-cut manipulation
needed. -/
theorem abs_exp_ikr_eq_rpow (k : ℂ) (r sigma : ℝ) (hsigma : 0 < sigma) :
    ‖Complex.exp (Complex.I * k * r)‖ =
      ‖Complex.exp (-Complex.I * k * sigma)‖ ^ (-r / sigma) := by
  rw [Complex.norm_exp, Complex.norm_exp]
  have hre1 : (Complex.I * k * r).re = -r * k.im := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  have hre2 : (-Complex.I * k * sigma).re = sigma * k.im := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  rw [hre1, hre2, show (-r * k.im : ℝ) = (sigma * k.im) * (-r / sigma) by field_simp]
  exact Real.exp_mul (sigma * k.im) (-r / sigma)

/-- **`|exp(ikr)|` upper bound**, `r,σ>0`: combines `abs_exp_ikr_eq_rpow` (exact identity) with
`abs_exp_neg_ikn_sigma_lower` (lower bound feeds an upper bound via the negative exponent's
antitone `rpow`). -/
theorem abs_exp_ikr_upper_of_zero {eta sigma rho r : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (hr : 0 < r) {k : ℂ}
    (hzero : G_baxter eta sigma rho k = 0) (hk1 : 1 ≤ ‖k‖)
    (hkN : 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ ‖k‖)
    (hkD : 2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ ‖k‖) :
    ‖Complex.exp (Complex.I * k * r)‖ ≤
      (‖k‖ ^ 2 / (4 * (rho * q_prime_py eta sigma))) ^ (-r / sigma) := by
  rw [abs_exp_ikr_eq_rpow k r sigma hsigma]
  have hlow := abs_exp_neg_ikn_sigma_lower heta0 heta1 hsigma hrho hzero hk1 hkN hkD
  have hLpos : 0 < ‖k‖ ^ 2 / (4 * (rho * q_prime_py eta sigma)) := by
    have hmupos := baxterMu_pos heta0 heta1 hsigma hrho
    have hk0 : 0 < ‖k‖ := lt_of_lt_of_le one_pos hk1
    positivity
  have hEXPpos : 0 < ‖Complex.exp (-Complex.I * k * sigma)‖ := by
    rw [Complex.norm_exp]; exact Real.exp_pos _
  have hzneg : (-r / sigma) < 0 := div_neg_of_neg_of_pos (by linarith) hsigma
  exact (Real.rpow_le_rpow_iff_of_neg hEXPpos hLpos hzneg).mpr hlow

/-- **Existential threshold bundle** (Task `POLE.5`, A.4): the `hkN`/`hkT` thresholds several
lemmas above need are stated in terms of the `private` `baxterP0`/`baxterP1`/`baxterP2` — this
wraps their existence behind an `∃`, letting `BaxterResidue.lean` (which cannot name those
private defs) combine the magnitude bounds into `residue_term_norm_bound` without needing to
know their closed form. -/
theorem exists_hkN_hkT_threshold (eta sigma rho : ℝ) (hsigma : 0 < sigma) :
    ∃ M : ℝ, 0 < M ∧
      (∀ k : ℂ, M ≤ ‖k‖ → 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) ≤ ‖k‖) ∧
      (∀ k : ℂ, M ≤ ‖k‖ →
        8 * (3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) / sigma
          ≤ ‖k‖) := by
  set Q1 : ℝ := 2 * (|baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
    |2 * baxterP2 eta sigma rho|) with hQ1
  set Q2 : ℝ := 8 * (3 + 2 * |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho|) /
    sigma with hQ2
  refine ⟨max (max Q1 Q2) 1, ?_, ?_, ?_⟩
  · positivity
  · intro k hk
    calc Q1 ≤ max Q1 Q2 := le_max_left _ _
      _ ≤ max (max Q1 Q2) 1 := le_max_left _ _
      _ ≤ ‖k‖ := hk
  · intro k hk
    calc Q2 ≤ max Q1 Q2 := le_max_right _ _
      _ ≤ max (max Q1 Q2) 1 := le_max_left _ _
      _ ≤ ‖k‖ := hk

/-- **Existential `D` bundle** (Task `POLE.5`, A.4): `abs_exp_neg_ikn_sigma_upper`'s bound is
`Θ(‖k‖²)` with a `baxterP0`-involving constant factor — this wraps that factor behind an `∃ D`,
preserving the `‖k‖²` growth rate (needed so `BaxterResidue.lean` can cancel it against
`Chat_complex_norm_bound`'s `1/‖k‖²`) without needing to name `baxterP0`. -/
theorem exists_D_for_exp_neg_bound {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    ∃ D : ℝ, 0 < D ∧ ∀ {k : ℂ}, G_baxter eta sigma rho k = 0 → 1 ≤ ‖k‖ →
      2 * (rho * q_doubleprime_py eta) / (rho * q_prime_py eta sigma) ≤ ‖k‖ →
      ‖Complex.exp (-Complex.I * k * sigma)‖ ≤ D * ‖k‖ ^ 2 := by
  have hmupos := baxterMu_pos heta0 heta1 hsigma hrho
  refine ⟨2 * (1 + |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
    |2 * baxterP2 eta sigma rho|) / (rho * q_prime_py eta sigma), by positivity,
    fun {k} hzero hk1 hkD => ?_⟩
  have h := abs_exp_neg_ikn_sigma_upper heta0 heta1 hsigma hrho hzero hk1 hkD
  rw [show 2 * (1 + |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
      |2 * baxterP2 eta sigma rho|) / (rho * q_prime_py eta sigma) * ‖k‖ ^ 2 =
      2 * (1 + |baxterP0 eta sigma rho| + |baxterP1 eta sigma rho| +
        |2 * baxterP2 eta sigma rho|) * ‖k‖ ^ 2 / (rho * q_prime_py eta sigma) by ring]
  exact h

/-! ### POLE.3 via the shared `ChordPoleFamily` predicate (unified with MZERO.5) -/

/-- **POLE.3 (chord-Newton route), sharing MZERO.5's predicate.** `G_baxter` has infinitely many zeros
given a `ChordPoleFamily (G_baxter η σ ρ)` — the **same shared obligation** the mixture `det(Q̂₀_c)`
carries (`FMSA.MixtureHSPoles.Q0_det_c_zeros_infinite`). Constructing the family — the asymptotic
pole locations + chord contraction/decay bounds, i.e. POLE.3's still-open `hstep` — discharges *both*
at once (`G_baxter` and `det_c` are built from the same `mAux/nAux(sσⱼ)` Baxter auxiliaries). The
existing log-map `Qhat_complex_zeros_infinite` is a separate route; this one carries the shared
predicate (chord-Newton ⇒ no `Complex.log` branch-safety). `G_baxter`'s per-disk differentiability is
automatic (`G_baxter_entire`). -/
theorem G_baxter_zeros_infinite_of_chordPoleFamily {eta sigma rho : ℝ}
    (fam : FMSA.BanachPoleFamily.ChordPoleFamily (G_baxter eta sigma rho)) :
    {k : ℂ | G_baxter eta sigma rho k = 0}.Infinite :=
  FMSA.BanachPoleFamily.zeros_infinite_of_chordPoleFamily fam

end HardSphere

end FMSA
