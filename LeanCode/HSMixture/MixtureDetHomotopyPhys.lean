/-
Copyright (c) 2026. All rights reserved.
-/
import LeanCode.HSMixture.MixtureDetHomotopy
import LeanCode.HSMixture.MixtureNoSpinodal

/-!
# Physical density homotopy — `hreal` from `pyhs_mixture_no_spinodal` (`OZFIX.17` matrix)

The `Pscale` (linear-`rr`) family of `MixtureDetHomotopy.lean` is **not** a physical `(σ, ρ')` point,
so `pyhs_mixture_no_spinodal` (stated for `Q0_mat_c_phys`) does not cover its intermediate points.
This file re-bases the homotopy on the **physical density path** `Pdens σ ρ t` = the `MixParams` at
density `t·ρ` (coupling/contact from `rhoGeoPhys`/`Q0phys`/`Qppphys`), so every point is a genuine
physical state and no-spinodal applies along the whole path.

* `detF_Pdens_eq` — the bridge `detF(Pdens σ ρ t) = det Q̂₀-phys(σ, t·ρ)` (both are `det Q0_mat_c` with
  the same substituted PY coefficients).
* `etaMix_smul` — packing scales linearly, `η(t·ρ) = t·η(ρ)`, so `t ≤ 1 ⇒ η(t·ρ) < 1`.
* `detF_Pdens_ne_zero` — **`hreal` for `k ≠ 0`**: `detF(Pdens σ ρ t, I·k) ≠ 0` for real `k ≠ 0`,
  `t ∈ (0,1]`, directly from `pyhs_mixture_no_spinodal`. (Since HS has no spinodal at any density, the
  physical path is singularity-free throughout.)

Remaining for the full physical-path assembly: run the homotopy on the **entire** `detF` (its `s = 0`
singularity is removable — each `q0_entry_c` is entire; this needs the removable-singularity proof,
not yet in the MML track) rather than the monomial form `W` (which carries an artificial `z⁶` zero at
the origin, breaking `hreal` at `z = 0`); then the `z = 0` value `detF(Pdens t, 0) = det Q̂₀(0) ≠ 0`,
and a uniform-in-`t` escape radius.
-/

open Complex
namespace FMSA.MixtureHSPoles
noncomputable section

/-- **Physical density homotopy.**  The `MixParams` at density `t·ρ`: coupling, contact `Q'`, `Q''`
from the PY-mixture formulas (`rhoGeoPhys`/`Q0phys`/`Qppphys`).  Unlike `Pscale`, `Qp/Qpp` vary with
`t` (via the vacancy `1−η`), so `Pdens σ ρ t` IS a physical `(σ, t·ρ)` point — `pyhs_mixture_no_spinodal`
applies along it. -/
def Pdens (sigma rho : Fin 2 → ℝ) (t : ℝ) : MixParams where
  sig0 := sigma 0
  sig1 := sigma 1
  rr := fun i j => FMSA.MatrixQ0.rhoGeoPhys (t • rho) i j
  Qp := fun i j => FMSA.MatrixQ0.Q0phys (t • rho) sigma i j
  Qpp := fun i j => FMSA.MatrixQ0.Qppphys (t • rho) sigma i j

/-- **`etaMix` scales linearly with density.**  `etaMix(t·ρ) = t·etaMix(ρ)`. -/
theorem etaMix_smul (t : ℝ) (rho sigma : Fin 2 → ℝ) :
    FMSA.MatrixQ0.etaMix (t • rho) sigma = t * FMSA.MatrixQ0.etaMix rho sigma := by
  simp only [FMSA.MatrixQ0.etaMix, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The bridge — `detF(Pdens σ ρ t) = det Q̂₀-phys(σ, t·ρ)`.**  Both are `det Q0_mat_c` with the same
substituted physical coefficients, so `pyhs_mixture_no_spinodal` transfers to `MixParams.detF`. -/
theorem detF_Pdens_eq (sigma rho : Fin 2 → ℝ) (t : ℝ) (s : ℂ) :
    (Pdens sigma rho t).detF s
      = (FMSA.MixtureNoSpinodal.Q0_mat_c_phys s sigma (t • rho)).det := by
  have hsig : (fun i : Fin 2 => ((![sigma 0, sigma 1] : Fin 2 → ℝ) i : ℂ))
      = (fun i => (sigma i : ℂ)) := by funext i; fin_cases i <;> rfl
  unfold MixParams.detF Pdens FMSA.MixtureNoSpinodal.Q0_mat_c_phys detC
  rw [hsig]

/-- **`etaMix ≥ 0`** for positive density/diameters. -/
theorem etaMix_nonneg {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i) :
    0 ≤ FMSA.MatrixQ0.etaMix rho sigma := by
  unfold FMSA.MatrixQ0.etaMix
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
  exact mul_nonneg (hrho i).le (pow_nonneg (hsig i).le 3)

/-- **`hreal` for `k ≠ 0` along the physical density path.**  `detF(Pdens σ ρ t, I·k) ≠ 0` for real
`k ≠ 0` and `t ∈ (0,1]`, directly from `pyhs_mixture_no_spinodal` at density `t·ρ` (whose packing
`etaMix(t·ρ) = t·etaMix(ρ) ≤ etaMix(ρ) < 1`).  The physical density path — unlike `Pscale` — keeps
each point a genuine `(σ, t·ρ)` state, so the no-spinodal axiom applies at every `t`. -/
theorem detF_Pdens_ne_zero {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : FMSA.MatrixQ0.etaMix rho sigma < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {k : ℝ} (hk : k ≠ 0) :
    (Pdens sigma rho t).detF (Complex.I * (k : ℂ)) ≠ 0 := by
  rw [detF_Pdens_eq]
  have hetann := etaMix_nonneg hsig hrho
  refine FMSA.MixtureNoSpinodal.pyhs_mixture_no_spinodal hsig
    (fun i => by simpa [Pi.smul_apply] using mul_pos ht0 (hrho i)) ?_ hk
  rw [etaMix_smul]; nlinarith [heta, ht1, hetann, ht0]

end
end FMSA.MixtureHSPoles
