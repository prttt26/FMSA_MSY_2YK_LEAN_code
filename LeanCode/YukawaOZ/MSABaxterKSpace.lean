/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSABlumHoyeSystem
import LeanCode.HardSphere.BaxterWienerHopf

/-!
# MSAEXACT.1 — the `k`-space (non-compact) Baxter factor `Q̂(ik)` and its `Dt`-affine split

Group **MSAEXACT** (`proof_notes_msa_exact.md`).  Numerical partner: `msaexact1_cside_check.py`.

The physical Baxter factor of hard-core Yukawa MSA is `Q̂(s) = φ₂(s)A + φ₁(s)q′ + tail(s)` (Blum &
Høye, `msa_exact.baxter_F`), with `A`, `q′` the amplitude-shifted moments and `tail` the Yukawa part
carrying the pole at `s = −z`.  At `σ = 1` and `s = ik`, `e^{−ik} = cos k − i sin k` and
`1/(ik + z) = (z − ik)/(z² + k²)`, so the real and imaginary parts of `ρ Q̂(ik)` are the closed forms
`msaQre`, `msaQim` below.  These are validated against `baxter_F` to machine zero
(`scratchpad/spike_numeric.py`).

⭐ **`Q̂(ik)` is affine in `Dt`** (every one of `A`, `q′`, `tail` is `Dt`-linear; `γ` has no `Dt`), so
`msaQre = ρReQh₀ + Dt·(…)` and likewise `msaQim`.  That is what lets the generic
`FMSA.MSAExact.msa_lhs_split` organise `|1 − ρQ̂(ik)|²` into its `Dt⁰` part (the hard-sphere factor,
`baxter_wiener_hopf_factorization`), an `O(Dt)` term, and an `O(Dt²)` term — the staged route to the
factorization, replacing the (provably impossible) compact single-`D` ansatz.

`reph1/imph1/reph2/imph2` are the real/imaginary parts of Blum & Høye's `φ₁(ik)`, `φ₂(ik)` at
`σ = 1`.
-/

open Real

namespace FMSA.MSAExact

variable (xi z : ℝ)

/-! ### Blum & Høye `φ₁(ik)`, `φ₂(ik)` at `σ = 1`, real and imaginary parts -/

/-- `Re φ₁(ik) = −(1 − cos k)/k²`. -/
noncomputable def reph1 (k : ℝ) : ℝ := -(1 - Real.cos k) / k ^ 2

/-- `Im φ₁(ik) = (k − sin k)/k²`. -/
noncomputable def imph1 (k : ℝ) : ℝ := (k - Real.sin k) / k ^ 2

/-- `Re φ₂(ik) = (k − sin k)/k³`. -/
noncomputable def reph2 (k : ℝ) : ℝ := (k - Real.sin k) / k ^ 3

/-- `Im φ₂(ik) = (1 − cos k − k²/2)/k³`. -/
noncomputable def imph2 (k : ℝ) : ℝ := (1 - Real.cos k - k ^ 2 / 2) / k ^ 3

/-! ### The amplitude-shifted moments `A`, `q′` as functions of `(Dt, G)` -/

/-- `A = A⁰(1 + M) − 4 B⁰ N`, with `M = Dt·Mtil`, `N = Dt·Ntil` (Blum & Høye Eq. 23). -/
noncomputable def msaA (Dt G : ℝ) : ℝ :=
  bA0 xi * (1 + Dt * Mtil xi z G) - 4 * bB0 xi * (Dt * Ntil xi z G)

/-- `q′ = q⁰′(1 + M) + A⁰ N` (Blum & Høye Eq. 24). -/
noncomputable def msaQp (Dt G : ℝ) : ℝ :=
  qp0 xi * (1 + Dt * Mtil xi z G) + bA0 xi * (Dt * Ntil xi z G)

/-! ### The Yukawa tail of `ρQ̂(ik)`: `u`, `w` and the two tail terms -/

/-- `u = 2πρ Dt G/z + γ Dt cos k` — the real combination in the tail's first term. -/
noncomputable def uT (Dt G k : ℝ) : ℝ :=
  2 * π * rhoOf xi * Dt * G / z + gam xi z G * Dt * Real.cos k

/-- `w = γ Dt sin k` — the imaginary combination in the tail's first term. -/
noncomputable def wT (Dt G k : ℝ) : ℝ := gam xi z G * Dt * Real.sin k

/-- `Re(ρ Q̂(ik))` at `σ = 1`: `ρ(A·Reφ₂ + q′·Reφ₁ + (uz − wk)/(z²+k²) + γ Dt sin k/k)`.  Validated
against `baxter_F` to machine zero. -/
noncomputable def msaQre (Dt G k : ℝ) : ℝ :=
  rhoOf xi * (msaA xi z Dt G * reph2 k + msaQp xi z Dt G * reph1 k
    + (uT xi z Dt G k * z - wT xi z Dt G k * k) / (z ^ 2 + k ^ 2)
    + gam xi z G * Dt * Real.sin k / k)

/-- `Im(ρ Q̂(ik))` at `σ = 1`: `ρ(A·Imφ₂ + q′·Imφ₁ − (uk + wz)/(z²+k²) − γ Dt (1−cos k)/k)`. -/
noncomputable def msaQim (Dt G k : ℝ) : ℝ :=
  rhoOf xi * (msaA xi z Dt G * imph2 k + msaQp xi z Dt G * imph1 k
    - (uT xi z Dt G k * k + wT xi z Dt G k * z) / (z ^ 2 + k ^ 2)
    - gam xi z G * Dt * (1 - Real.cos k) / k)

/-! ### The `Dt⁰` bridge to the hard-sphere Baxter transform

At `Dt = 0` the shifted moments collapse to `A⁰`, `q⁰′` and the Yukawa tail vanishes, so `ρQ̂(ik)`
is the hard-sphere Baxter transform.  Matching Blum & Høye's `(A⁰, q⁰′, φ)` form to the concurrent
session's `q0_poly` form — `bA0 = q″_py`, `qp0 = q′_py` — makes `msaQre`, `msaQim` at `Dt = 0` the
cosine and (negated) sine `q0_poly` integrals, so `baxter_wiener_hopf_factorization` supplies the
`Dt⁰` part of the split.  Pure algebra (`field_simp; ring`) once the closed forms are in play. -/

open FMSA.HardSphere in
/-- `Re(ρQ̂(ik))` at `Dt = 0` is the cosine `q0_poly` integral (the hard-sphere Baxter transform). -/
theorem msaQre_zero (G : ℝ) {k : ℝ} (hk : k ≠ 0) :
    msaQre xi z 0 G k = ∫ r in (0 : ℝ)..1, q0_poly xi 1 (rhoOf xi) r * Real.cos (k * r) := by
  rw [q0poly_cos_integral_formula xi 1 (rhoOf xi) k one_pos hk]
  simp only [msaQre, msaA, msaQp, uT, wT, reph1, reph2, gam, q_prime_py, q_doubleprime_py,
    bA0, bB0, qp0, mul_zero, zero_mul, add_zero, sub_zero, mul_one, one_pow]
  field_simp
  ring

open FMSA.HardSphere in
/-- `Im(ρQ̂(ik))` at `Dt = 0` is the negated sine `q0_poly` integral. -/
theorem msaQim_zero (G : ℝ) {k : ℝ} (hk : k ≠ 0) :
    msaQim xi z 0 G k = -∫ r in (0 : ℝ)..1, q0_poly xi 1 (rhoOf xi) r * Real.sin (k * r) := by
  rw [q0poly_sin_integral_formula xi 1 (rhoOf xi) k one_pos hk]
  simp only [msaQim, msaA, msaQp, uT, wT, imph1, imph2, gam, q_prime_py, q_doubleprime_py,
    bA0, bB0, qp0, mul_zero, zero_mul, add_zero, sub_zero, mul_one, one_pow]
  field_simp
  ring

end FMSA.MSAExact
