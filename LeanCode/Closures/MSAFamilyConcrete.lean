/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Closures.MSASolutionFamily
import LeanCode.YukawaOZ.MSAFullFactorization
import LeanCode.HardSphere.BaxterNoSpinodalEquiv

/-!
# MSAFAM.5/.6 — the *concrete* Baxter-transport family, reduced to a single factorization input

Records: `Lean_code/proof_notes_closures.md`, "Group MSAFAM", gap (C).

`MSASolutionFamily.lean` closes the **transport half** of MSAFAM.5/.6 abstractly:
`msaSolutionFamily_transport` / `msaFamily_taylor_eq_hierarchy` take an *abstract* smooth
non-vanishing pair `Qp, Qm : ℝ → ℂ` and produce the MSA pair `(H̃, C̃)` obeying OZ and the coupling
hierarchy at every order.  What remained was the **concrete input**: the `k`-space Baxter transform
`τ ↦ Q̂(±k, ψ(τ))` evaluated along the Blum–Høye root `ψ`, with `Q̂(k,0) ≠ 0`.

This file supplies that concrete input, **ring-free** (no closure-recovery core):

* `exists_contDiffAt_bhRoot` — the `C^∞` Blum–Høye root `ψ(K) = (Dt(K), G(K))` for the *concrete*
  `bhF`/`bhP` at `N = 1`, via the prod-domain `C^n` IFT (`exists_contDiffAt_root_of_prodDomain_ift`)
  on the coupling-scaled map `g(K, Dt, G) = (Dt·bhF − 2πK/z, 2π·G·bhF − bhP)` — the same map
  FOEQ.5's `msa_amplitude_differentiable_of_bh_shape` uses, but taking the *whole* smooth pair.
* `msaQre_contDiff` / `msaQim_contDiff` — the `k`-space Baxter parts are `C^∞` in `(Dt, G)`
  (degree-2 polynomials over constants), so they compose with `ψ` to a `C^∞` family.
* `msaQ0_normSq` — at the base point (`Dt = 0`) the modulus `|1 − ρQ̂₀(ik)|²` is the hard-sphere
  Baxter factor `1 − ρ𝓕[c_HS](k)`, which is **strictly positive**
  (`one_sub_rho_radial_fourier_c_HS_pos`, the no-spinodal fact) — so `Q̂(k,0)Q̂(−k,0) ≠ 0`.
* `msaFamily_taylor_eq_hierarchy_concrete` — the payoff: the Baxter-transport family built from the
  **physical** MSA root satisfies OZ `∀ᶠ` and the coupling hierarchy at every order, with **no
  abstract hypothesis** — the whole of MSAFAM.5/.6 is now reduced to the **single** remaining input.

⚠ **What is still open, stated precisely so it cannot drift.**  The family `C̃ = 1 − Q̂(k)Q̂(−k)`
here is built from the Baxter factor of the physical root; it obeys OZ and the hierarchy
*unconditionally*.
Certifying it as **the MSA solution** — i.e. that `1 − C̃ = 1 − ρĉ_MSA(k)` with `ĉ_MSA` the MSA
closure DCF — is exactly MSAEXACT.1's factorisation `|1 − ρQ̂(ik)|² = 1 − ρĉ_MSA`
(`FMSA.ExactMSA.factorization_of_core` once its `hcore` closure-recovery ring is discharged).  That
identity is the *sole* input separating this concrete family from the unconditional Theorem I.1 at
`N = 1`; per proof-note gap (C) it is consumed, not attempted, here.  Landing this file does **not**
license editing the paper's §"What is not formalized" Theorem-I.1 bullet.
-/

open Real Filter Topology
open scoped ContDiff

namespace FMSA.MSASolutionFamily

open FMSA.ExactMSA FMSA.FirstOrderEquivalence FMSA.HardSphere

/-! ### `ℝ → ℂ` smoothness helper and the complex conjugate-factor product identity -/

/-- Composition with the real-to-complex embedding preserves `ContDiffAt` (it is a continuous linear
map). -/
private theorem contDiffAt_ofReal_comp {f : ℝ → ℝ} {x : ℝ} {n : ℕ∞ω}
    (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun t => (↑(f t) : ℂ)) x := by
  have h : ContDiffAt ℝ n (fun t => Complex.ofRealCLM (f t)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  simpa only [Complex.ofRealCLM_apply] using h

/-- `(a − i b)(a + i b) = a² + b²` in `ℂ` — the conjugate-factor product that turns the Baxter pair
into a real modulus. -/
private theorem conj_factor_prod (a b : ℂ) :
    (a - Complex.I * b) * (a + Complex.I * b) = a ^ 2 + b ^ 2 := by
  linear_combination (-b ^ 2) * Complex.I_sq

/-! ### The `k`-space Baxter parts are `C^∞` in `(Dt, G)` -/

/-- `Re(ρQ̂(ik))` is `C^∞` in the amplitudes `(Dt, G)` (a degree-2 polynomial over constants). -/
theorem msaQre_contDiff (xi z k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => msaQre xi z p.1 p.2 k) := by
  simp only [msaQre, msaA, msaQp, uT, wT, gam, Mtil, Ntil, reph1, reph2, div_eq_mul_inv]
  fun_prop

/-- `Im(ρQ̂(ik))` is `C^∞` in the amplitudes `(Dt, G)`. -/
theorem msaQim_contDiff (xi z k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => msaQim xi z p.1 p.2 k) := by
  simp only [msaQim, msaA, msaQp, uT, wT, gam, Mtil, Ntil, imph1, imph2, div_eq_mul_inv]
  fun_prop

/-! ### The `Dt = 0` modulus is the hard-sphere Baxter factor -/

/-- At the base point (`Dt = 0`) the Baxter modulus `(1 − Re₀)² + Im₀²` is the hard-sphere structure
factor `1 − ρ𝓕[c_HS](k)` (the `Dt⁰` collapse of `msa_factor_split`). -/
theorem msaQ0_normSq (xi z G : ℝ) {k : ℝ} (hk : k ≠ 0) (hxi : xi < 1) :
    (1 - msaQre xi z 0 G k) ^ 2 + msaQim xi z 0 G k ^ 2
      = 1 - rhoOf xi * radial_fourier (c_HS xi 1) k := by
  have heta_def : xi = Real.pi * rhoOf xi * (1 : ℝ) ^ 3 / 6 := by rw [rhoOf]; field_simp
  rw [msaQre_zero xi z G hk, msaQim_zero xi z G hk, neg_sq,
    baxter_wiener_hopf_factorization xi 1 (rhoOf xi) k one_pos hk hxi heta_def]

/-! ### The concrete `C^∞` Blum–Høye root -/

/-- **The concrete `C^∞` Blum–Høye root at `N = 1`.**  The coupling-scaled residual map
`g(K, Dt, G) = (Dt·bhF − 2πK/z, 2π·G·bhF − bhP)` is `C^∞`, vanishes at the PY base point `(0, G₀)`
(base equation `bh_base_eq`), and has an invertible second-factor Jacobian there
(`bhResidualShape_hasFDerivAt` + `bhJacobianCLM_isInvertible`, using `bhF(0,G₀) ≠ 0`).  The
prod-domain `C^n` implicit function theorem (`exists_contDiffAt_root_of_prodDomain_ift`, MSAFAM.3)
then produces a root `ψ` that is `C^∞` at `0`, passes through `(0, G₀)`, and solves the two
Blum–Høye equations on a neighbourhood of `K = 0`.

This is `msa_amplitude_differentiable_of_bh_shape`'s construction taking the **whole** smooth pair
`ψ = (Dt, G)` (not just the amplitude `Dt`) and at `C^∞` (not just `C¹`) — the family MSAFAM.5
needs. -/
theorem exists_contDiffAt_bhRoot {xi z : ℝ} (hxi : xi ∈ Set.Ioo (0 : ℝ) 1) (hz : 0 < z) :
    ∃ ψ : ℝ → ℝ × ℝ, ψ 0 = (0, G0 xi z) ∧
      (∀ᶠ K in 𝓝 (0 : ℝ),
        (ψ K).1 * bhF xi z (ψ K) - 2 * π * K / z = 0 ∧
          2 * π * ((ψ K).2 * bhF xi z (ψ K)) - bhP xi z (ψ K) = 0) ∧
      ContDiffAt ℝ ∞ ψ 0 := by
  set g : ℝ × (ℝ × ℝ) → (ℝ × ℝ) :=
    fun Kp => (Kp.2.1 * bhF xi z Kp.2 - 2 * π * Kp.1 / z,
      2 * π * (Kp.2.2 * bhF xi z Kp.2) - bhP xi z Kp.2) with hgdef
  have hF := bhF_contDiff xi z
  have hP := bhP_contDiff xi z
  have hg : ContDiff ℝ ∞ g := by rw [hgdef]; fun_prop
  have cg : ContDiffAt ℝ ∞ g (0, (0, G0 xi z)) := hg.contDiffAt
  have hInftyNe : (∞ : ℕ∞ω) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (by exact_mod_cast le_top))
  have hbase0 : g (0, (0, G0 xi z)) = 0 := by
    have hgval : g (0, (0, G0 xi z))
        = (0 * bhF xi z (0, G0 xi z) - 2 * π * 0 / z,
          2 * π * (G0 xi z * bhF xi z (0, G0 xi z)) - bhP xi z (0, G0 xi z)) := by rw [hgdef]
    rw [hgval, Prod.mk_eq_zero]
    exact ⟨by ring, sub_eq_zero.mpr (bh_base_eq hxi hz)⟩
  have hFd : HasFDerivAt (bhF xi z) (fderiv ℝ (bhF xi z) (0, G0 xi z)) (0, G0 xi z) :=
    ((bhF_contDiff xi z).differentiable hInftyNe).differentiableAt.hasFDerivAt
  have hPd : HasFDerivAt (bhP xi z) (fderiv ℝ (bhP xi z) (0, G0 xi z)) (0, G0 xi z) :=
    ((bhP_contDiff xi z).differentiable hInftyNe).differentiableAt.hasFDerivAt
  have hshape := bhResidualShape_hasFDerivAt (F := bhF xi z) (P := bhP xi z) (G₀ := G0 xi z)
    (F₀ := bhF xi z (0, G0 xi z)) (kterm := 2 * π * 0 / z) hFd hPd
    (bhF_fderiv_snd xi z (G0 xi z)) (bhP_fderiv_snd xi z (G0 xi z)) rfl
  have hgd : HasFDerivAt g (fderiv ℝ g (0, (0, G0 xi z))) (0, (0, G0 xi z)) :=
    (hg.contDiffAt.differentiableAt hInftyNe).hasFDerivAt
  have hpartial : HasFDerivAt (fun p => g (0, p))
      ((fderiv ℝ g (0, (0, G0 xi z))) ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) (0, G0 xi z) :=
    hgd.comp (0, G0 xi z) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hJac : (fderiv ℝ g (0, (0, G0 xi z))) ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)
      = bhJacobianCLM (bhF xi z (0, G0 xi z))
        (2 * π * G0 xi z * fderiv ℝ (bhF xi z) (0, G0 xi z) (1, 0)
          - fderiv ℝ (bhP xi z) (0, G0 xi z) (1, 0)) :=
    hpartial.unique hshape
  have hinv := hJac ▸ bhJacobianCLM_isInvertible (bhF_base_ne_zero hxi hz)
  obtain ⟨ψ, hψ0, hψeq, hψcd⟩ :=
    exists_contDiffAt_root_of_prodDomain_ift hInftyNe cg hbase0 hinv
  refine ⟨ψ, hψ0, ?_, hψcd⟩
  filter_upwards [hψeq] with K hK
  simp only [hgdef, Prod.mk_eq_zero] at hK
  exact hK

/-! ### The payoff — the concrete Baxter-transport family satisfies Theorem I.1's conclusion -/

/-- ⭐⭐ **MSAFAM.5/.6, concrete — the physical MSA Baxter family satisfies OZ and the hierarchy.**
The pair `Qp(τ) = 1 − ρQ̂(ik, ψ(τ))`, `Qm(τ) = 1 − ρQ̂(−ik, ψ(τ))` — the `k`-space Baxter factor
evaluated along the *physical* Blum–Høye root `ψ` (`exists_contDiffAt_bhRoot`) — is `C^∞` at `0`
(the Baxter parts are polynomial in the amplitudes, composed with the smooth root) and non-vanishing
there (`Qp(0)Qm(0) = 1 − ρ𝓕[c_HS](k) > 0`, the no-spinodal fact).  Feeding it to the transport
capstone `msaFamily_taylor_eq_hierarchy` yields the MSA pair `(H̃, C̃)` obeying the Ornstein–Zernike
relation on a neighbourhood of `0` and the coupling hierarchy at **every** order — Theorem I.1's
conclusion, for a *constructed* family with **no abstract hypothesis**.

⚠ Still open (proof-note gap (C)): this certifies the family obeys OZ + the hierarchy, but *that*
the built `C̃ = 1 − Q̂Q̂` is the **MSA closure DCF** is MSAEXACT.1's factorisation
(`FMSA.ExactMSA.factorization_of_core` + its `hcore` ring) — the sole remaining input. -/
theorem msaFamily_taylor_eq_hierarchy_concrete {xi z : ℝ} (hxi : xi ∈ Set.Ioo (0 : ℝ) 1)
    (hz : 0 < z) {k : ℝ} (hk : k ≠ 0) :
    ∃ H C : ℝ → ℂ,
      (∀ᶠ τ in 𝓝 (0 : ℝ), (1 + H τ) * (1 - C τ) = 1) ∧
      ∀ m : ℕ, 1 ≤ m →
        ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℂ) * iteratedDeriv i (fun s => 1 + H s) 0
            * iteratedDeriv (m - i) (fun s => 1 - C s) 0 = 0 := by
  obtain ⟨ψ, hψ0, _, hψcd⟩ := exists_contDiffAt_bhRoot hxi hz
  have hqreC : ContDiffAt ℝ ∞ (fun τ => msaQre xi z (ψ τ).1 (ψ τ).2 k) 0 :=
    (msaQre_contDiff xi z k).contDiffAt.comp 0 hψcd
  have hqimC : ContDiffAt ℝ ∞ (fun τ => msaQim xi z (ψ τ).1 (ψ τ).2 k) 0 :=
    (msaQim_contDiff xi z k).contDiffAt.comp 0 hψcd
  set Qp : ℝ → ℂ := fun τ =>
    (↑(1 - msaQre xi z (ψ τ).1 (ψ τ).2 k) : ℂ) - Complex.I * ↑(msaQim xi z (ψ τ).1 (ψ τ).2 k)
    with hQpdef
  set Qm : ℝ → ℂ := fun τ =>
    (↑(1 - msaQre xi z (ψ τ).1 (ψ τ).2 k) : ℂ) + Complex.I * ↑(msaQim xi z (ψ τ).1 (ψ τ).2 k)
    with hQmdef
  have hQp : ContDiffAt ℝ ∞ Qp 0 := by
    rw [hQpdef]
    exact (contDiffAt_ofReal_comp (contDiffAt_const.sub hqreC)).sub
      ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => Complex.I) 0).mul
        (contDiffAt_ofReal_comp hqimC))
  have hQm : ContDiffAt ℝ ∞ Qm 0 := by
    rw [hQmdef]
    exact (contDiffAt_ofReal_comp (contDiffAt_const.sub hqreC)).add
      ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => Complex.I) 0).mul
        (contDiffAt_ofReal_comp hqimC))
  have hpos : 0 < 1 - rhoOf xi * radial_fourier (c_HS xi 1) k := by
    have hrho : 0 < rhoOf xi := by
      rw [rhoOf]; exact div_pos (by linarith [hxi.1]) Real.pi_pos
    have heta_def : xi = Real.pi * rhoOf xi * (1 : ℝ) ^ 3 / 6 := by rw [rhoOf]; field_simp
    exact one_sub_rho_radial_fourier_c_HS_pos hxi.1 hxi.2 one_pos hrho heta_def k
  have h0 : Qp 0 * Qm 0 ≠ 0 := by
    have hb1 : (ψ 0).1 = 0 := by rw [hψ0]
    have hb2 : (ψ 0).2 = G0 xi z := by rw [hψ0]
    have hEval : Qp 0 * Qm 0 = ((1 - rhoOf xi * radial_fourier (c_HS xi 1) k : ℝ) : ℂ) := by
      simp only [hQpdef, hQmdef, hb1, hb2]
      rw [conj_factor_prod, ← msaQ0_normSq xi z (G0 xi z) hk hxi.2]
      push_cast
      ring
    rw [hEval]
    exact_mod_cast ne_of_gt hpos
  exact msaFamily_taylor_eq_hierarchy hQp hQm h0

end FMSA.MSASolutionFamily
