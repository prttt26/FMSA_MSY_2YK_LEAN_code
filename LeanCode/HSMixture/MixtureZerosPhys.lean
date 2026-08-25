/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.MixtureChordFamily
import LeanCode.HSMixture.MixtureDetUniform

/-!
# MZERO at the PHYSICAL Baxter coefficients — `det Q̂₀` really has infinitely many zeros

`MixtureChordFamily.detC_zeros_infinite_unconditional` / `detF_zeros_infinite` (MZERO.1/5)
prove that `det Q̂₀(s)` has infinitely many complex zeros for **any** `N = 2` parameter pack
satisfying `MixParams.Phys`.  ⚠ That predicate means *"ordered positive diameters and
entrywise positive matrices"* — it does **not** mean the Lebowitz PY coefficients.
`Q0phys` / `Qppphys` / `rhoGeoPhys` appear nowhere in `MixtureChordFamily.lean`,
`MixtureHSZeros.lean` or `MixtureHSCounting.lean`, so the MZERO group was never
instantiated at the physical mixture, and `hP : P.Phys` was easy to misread as if it had
been.  This file closes that gap.

**The positivity was already proved — in a different track, and never connected.**  The
`MixParams.Phys` hypotheses for the Lebowitz coefficients are `Q0phys_pos` / `Qppphys_pos`
/ `rhoGeoPhys_pos`, and they are even packaged as **`Pdens_Phys`**
(`MixtureDetUniform.lean`) — all built for the **density homotopy** of the
physics-axiom-retirement work (`MatrixDetPoleFree` / `MixtureDetHomotopyPhys`), where the
consumer is `hRunif_Pdens`, not MZERO.  Nobody ever pointed them at
`detF_zeros_infinite`.  So this file proves nothing new; it *connects* two finished pieces,
and the connection is one `Pdens_Phys` application at `t = 1` (`Pdens sigma rho 1` is
literally the physical pack, since `1 • rho = rho`).  This is the
`feedback_stale_blockers` pattern once more: the missing fact was already inside the tree,
merely unexported to the group that needed it.

**Why the instantiation is worth having at all.**  A statement true of a parameter superset
can still fail to apply to the object of interest, and this project has been bitten by
exactly that (`b4_origin_bc_abstract`, `b9_d_ij_nonzero_example`, GAP.8's
`poly_coeff_from_laurent` — all true, all about arbitrary reals, none about the physical
DCF).  MZERO's headline currently has **no Lean consumer** — MRS.3 removed the DCF one (the
`det Q̂₀` zeros never enter `Ĉ₁`) and the RDF one (MML.8) is open — so it had never met a
consumer that would expose a mis-instantiation.  This is the same "does it survive contact
with the physical parameters?" check that `MRS.0b` (`MixtureNoSpinodalN1.lean`) performed
for the mixture axiom, and like that one it found no defect.

**Numerical corroboration** (reference mixture `σ = [1,2]`, `x = [0.25,0.75]`,
`ρ* = 0.139` ⇒ `η = 0.4549`, `vac = 0.5451`): `min Q0phys = 19.03`, `min Qppphys = 26.53`,
`min rhoGeo = 0.0348`, and Newton from MZERO.5's anchor `i·2πn/σ₁` locates 8 zeros of
`detC` **at those physical coefficients** (`s = −0.417+3.389i, …, −2.362+25.075i`,
`|detC| ≤ 3.4e-15`, mean `Im` spacing `3.098` against the predicted `2π/σ₁ = 3.1416`) —
reproducing MZERO.2's recorded `Δ Im ≈ π` GO gate.

Layering: `HSMixture/`, so the statement is given at the `detC` / `Q0_mat_c` level.  The
`YukawaDCF/MixtureRealSpace.lean` alias `Qphys` is *definitionally* the matrix appearing in
`Q0_mat_c_phys_det_zeros_infinite`, so an `FMSA.MixtureBaxterCore`-side restatement is a one-liner if
ever wanted (it cannot live here — `HSMixture/` may not import `YukawaDCF/`).

Status: ✓ axiom-clean.
-/

open Set FMSA.MatrixQ0

namespace FMSA.MixtureHSPoles

/-- `Pdens sigma rho 1` **is** the physical parameter pack: the density homotopy at `t = 1`
carries `1 • rho = rho`.  The bridge between `MixtureDetUniform`'s homotopy packaging and
the plain physical coefficients. -/
theorem Pdens_one (sigma rho : Fin 2 → ℝ) :
    Pdens sigma rho 1 =
      { sig0 := sigma 0, sig1 := sigma 1,
        rr := fun i j => rhoGeoPhys rho i j,
        Qp := fun i j => Q0phys rho sigma i j,
        Qpp := fun i j => Qppphys rho sigma i j } := by
  unfold Pdens; simp

/-- **MZERO.1/5 at the PHYSICAL Lebowitz PY coefficients.**  For an `N = 2` mixture with
positive ordered diameters, positive densities, and packing fraction below close-packing
(`η < 1`), the Baxter determinant `det Q̂₀` has **infinitely many** complex zeros.

The three `MixParams.Phys` positivity hypotheses are supplied by `Pdens_Phys` at `t = 1`
(`MixtureDetUniform.lean`), so this is the instantiation `detF_zeros_infinite` never
received — not new analysis. -/
theorem detC_zeros_infinite_phys {sigma rho : Fin 2 → ℝ}
    (hsig : ∀ i, 0 < sigma i) (hsord : sigma 0 < sigma 1) (hrho : ∀ i, 0 < rho i)
    (heta : etaMix rho sigma < 1) :
    {s : ℂ | detC ![sigma 0, sigma 1]
        (fun i j => ((rhoGeoPhys rho i j : ℝ) : ℂ))
        (fun i j => ((Q0phys rho sigma i j : ℝ) : ℂ))
        (fun i j => ((Qppphys rho sigma i j : ℝ) : ℂ)) s = 0}.Infinite := by
  have hP : (Pdens sigma rho 1).Phys :=
    Pdens_Phys hsig hsord hrho heta (by norm_num) one_pos
  have h := detF_zeros_infinite (Pdens sigma rho 1) hP
  rwa [Pdens_one sigma rho] at h

/-- The same conclusion stated on the matrix itself — `Q0_mat_c` carrying the physical
`rhoGeoPhys`/`Q0phys`/`Qppphys`, i.e. **definitionally the `Qphys` of
`YukawaDCF/MixtureRealSpace.lean` (MRS.7)**.  This is the form a consumer wants: *the
physical Baxter matrix's determinant vanishes at infinitely many complex `s`*.  Only
bookkeeping separates it from `detC_zeros_infinite_phys` — `![sigma 0, sigma 1] = sigma`
on `Fin 2`. -/
theorem Q0_mat_c_phys_det_zeros_infinite {sigma rho : Fin 2 → ℝ}
    (hsig : ∀ i, 0 < sigma i) (hsord : sigma 0 < sigma 1) (hrho : ∀ i, 0 < rho i)
    (heta : etaMix rho sigma < 1) :
    {s : ℂ | (FMSA.Q0Complex.Q0_mat_c s (fun i => ((sigma i : ℝ) : ℂ))
        (fun i j => ((rhoGeoPhys rho i j : ℝ) : ℂ))
        (fun i j => ((Q0phys rho sigma i j : ℝ) : ℂ))
        (fun i j => ((Qppphys rho sigma i j : ℝ) : ℂ))).det = 0}.Infinite := by
  have hsigeq : (![sigma 0, sigma 1] : Fin 2 → ℝ) = sigma := by
    funext i; fin_cases i <;> simp
  have h := detC_zeros_infinite_phys hsig hsord hrho heta
  unfold detC at h
  rwa [hsigeq] at h

/-! ### Non-vacuity certificate

The hypotheses must be *simultaneously* satisfiable, or the theorems above would be true
and empty — the failure mode of `b4_origin_bc_abstract` / `b9_d_ij_nonzero_example` /
GAP.8, and the reason `MML.13` recorded its degenerate case as a Lean `example` rather
than asserting it.  Here the witness is the project's own reference mixture: `σ = [1,2]`,
`ρ = [0.03475, 0.10425]` (`x = [0.25,0.75]`, `ρ* = 0.139`), whose packing fraction is
`η = (π/6)(ρ₀ + 8ρ₁) = (π/6)(0.86875) ≈ 0.4549 < 1`.  The `η < 1` check needs only
`π < 4`. -/
example : {s : ℂ | (FMSA.Q0Complex.Q0_mat_c s
      (fun i => ((![(1 : ℝ), 2] i : ℝ) : ℂ))
      (fun i j => ((rhoGeoPhys ![0.03475, 0.10425] i j : ℝ) : ℂ))
      (fun i j => ((Q0phys ![0.03475, 0.10425] ![1, 2] i j : ℝ) : ℂ))
      (fun i j => ((Qppphys ![0.03475, 0.10425] ![1, 2] i j : ℝ) : ℂ))).det
      = 0}.Infinite := by
  refine Q0_mat_c_phys_det_zeros_infinite (fun i => by fin_cases i <;> norm_num) (by norm_num)
    (fun i => by fin_cases i <;> norm_num) ?_
  unfold etaMix
  rw [Fin.sum_univ_two]
  norm_num
  nlinarith [Real.pi_lt_four, Real.pi_pos]

end FMSA.MixtureHSPoles
