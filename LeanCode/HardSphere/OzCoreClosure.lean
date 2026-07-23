/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRenewal
import LeanCode.HardSphere.PYOZ_GHS
import LeanCode.HardSphere.OZExteriorBridge
import LeanCode.HardSphere.OzBaxterFixedPt
import LeanCode.HardSphere.BaxterExteriorRegularityGeneral
import LeanCode.HardSphere.BaxterRenewalDecay
import LeanCode.HardSphere.OzExteriorIntegrability
import LeanCode.HardSphere.OzExteriorSmooth
import LeanCode.HardSphere.OzExteriorConvIntegrable

/-!
# Task OZFIX.22 — retiring `oz_core_closure` via OZ★ and the Baxter bridge

`oz_core_closure` (Task OZ.9a, `PYOZ_GHS.lean`) is a physics axiom: for `0 < r < σ`,

    `oz_h(r) = c_HS(r) + ρ · radial3d_conv c_HS oz_h (r)`,

i.e. the Ornstein–Zernike convolution equation holds **inside** the hard core (not just the known
value `oz_h(r) = -1`).  This file reduces it to the **single bridge** `oz_h = baxterPsi/·`:

* **OZ★** (`baxterPsi_eq_phi_add_rho_conv`, `BaxterRenewal.lean`) is the *same* OZ equation for the
  **constructed** `baxterPsi`: `baxterPsi(r) = r·c_HS(r) + ρ·r·radial3d_conv(c_HS, baxterPsi/·)(r)`,
  proved (conditionally, decay-free) for every `r > 0`.  Dividing by `r` turns it into the
  `oz_core_closure` shape for `baxterPsi/·`.
* The convolution `radial3d_conv c_HS g (r)` reads `g` only on `(0, r+σ)` (`c_HS` is supported on
  `[0,σ]`, the shell reaches at most `r+σ`), so it is unchanged when `g` is swapped for anything
  agreeing there (`radial3d_conv_cHS_congr`).  Hence `radial3d_conv c_HS oz_h = radial3d_conv c_HS
  (baxterPsi/·)` once `oz_h = baxterPsi/·` on `(0, r+σ)`.

`oz_core_closure_of_bridge` combines the two: **decay-free, axiom-clean**.  It shows the physics
closure is not independent input — it is `OZ★` transported across the bridge.

## The bridge `oz_h = baxterPsi/·` and the (now-retired) OZ axioms

The bridge itself is *not* decay-free: `oz_h` is the unique bounded, exterior-continuous OZ fixed
point (`oz_fixed_pt_unique_thm`, formerly the physics axiom `oz_fixed_pt_unique`), so matching it to
`baxterPsi/·` needs `baxterPsi` bounded on `[σ,∞)` — the exterior **decay** of the Baxter solution.
Bounded uniqueness of the OZ operator is genuinely Wiener–Hopf (simple `L¹` contraction is REFUTED:
`∫₀^σ|q0| ≥ 1` for `η ≳ 0.13`), so this decay input cannot be removed; it is exactly the content the
OZ axioms all funnelled through.

The honest ceiling first reached was a **net 3 → 2** consolidation (keep `oz_fixed_pt_unique`
irreducibly Wiener–Hopf, add ONE explicit decay axiom about the *constructed* `baxterPsi`, and retire
both `oz_core_closure` via this file and `oz_h_exterior_regularity` via the same bridge).  Since then
**both** remaining inputs have themselves been retired to **theorems**: uniqueness is now the theorem
`oz_fixed_pt_unique_thm` (`OzWienerHopfBounded.lean`, via the L∞ Wiener–Hopf math axiom
`oz_linear_op_bounded_injective` + coercivity from `pyhs_no_spinodal`), and the decay/regularity is
now the theorem `baxter_exterior_regularity` (below).  So the OZ physics axioms are fully gone — the
lone surviving physics axiom in the codebase is `pyhs_no_spinodal`.  Full *decay-free* retirement was
never on the table — an earlier "decay-free 3→2 merge" design was over-optimistic (converting the OZ
convolution equation to a causal Volterra renewal for a *general* fixed point needs the factorization,
not just the general OZFIX.18/19/20 machinery).
-/

open MeasureTheory Set Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- **Domain-locality of `radial3d_conv` against `c_HS` (decay-free brick).**

`radial3d_conv (c_HS eta sigma) g r` depends on `g` only through its values on `(0, r+σ)`: `c_HS` is
supported on `[0,σ]` (`c_HS_outer`), so the outer `t`-integral only sees `t ∈ (0,σ)`, and for such
`t` the inner shell `[|r-t|, r+t]` lies in `[0, r+t] ⊆ [0, r+σ)`.  Values at `s = 0` are irrelevant
(the integrand carries a factor `s`).  Hence two functions agreeing on `Ioo 0 (r+σ)` give equal
convolutions. -/
theorem radial3d_conv_cHS_congr {eta sigma : ℝ} (hsigma : 0 < sigma) {r : ℝ} (hr : 0 < r)
    {g1 g2 : ℝ → ℝ} (h : Set.EqOn g1 g2 (Set.Ioo (0:ℝ) (r + sigma))) :
    radial3d_conv (c_HS eta sigma) g1 r = radial3d_conv (c_HS eta sigma) g2 r := by
  unfold radial3d_conv
  rw [if_neg (not_le.mpr hr), if_neg (not_le.mpr hr)]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rcases lt_or_ge t sigma with htσ | htσ
  · -- `t < σ`: the inner shell integrals agree (they only sample `s ∈ [0, r+σ)`)
    have hinner : (∫ s in Set.Icc (|r - t|) (r + t), s * g1 s)
        = ∫ s in Set.Icc (|r - t|) (r + t), s * g2 s := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
      show s * g1 s = s * g2 s
      have hs0 : (0:ℝ) ≤ s := (abs_nonneg (r - t)).trans hs.1
      rcases eq_or_lt_of_le hs0 with hs0' | hs0'
      · rw [← hs0']; ring
      · have hslt : s < r + sigma := lt_of_le_of_lt hs.2 (by linarith)
        rw [h ⟨hs0', hslt⟩]
    show t * c_HS eta sigma t * (∫ s in Set.Icc (|r - t|) (r + t), s * g1 s)
      = t * c_HS eta sigma t * (∫ s in Set.Icc (|r - t|) (r + t), s * g2 s)
    rw [hinner]
  · -- `t ≥ σ`: `c_HS t = 0` kills the term
    show t * c_HS eta sigma t * (∫ s in Set.Icc (|r - t|) (r + t), s * g1 s)
      = t * c_HS eta sigma t * (∫ s in Set.Icc (|r - t|) (r + t), s * g2 s)
    rw [c_HS_outer htσ]; ring

/-- **`OZFIX.22` — `oz_core_closure` as a theorem, conditional on the bridge `oz_h = baxterPsi/·`.**

Given the bridge `∀ s > 0, oz_h s = baxterPsi s / s` and OZ★ at the point `r ∈ (0,σ)`, the PY core
closure `oz_h(r) = c_HS(r) + ρ·radial3d_conv(c_HS, oz_h)(r)` follows by pure algebra:

* `radial3d_conv_cHS_congr` (the bridge holds on `(0, r+σ) ⊆ (0,∞)`) replaces `oz_h` by `baxterPsi/·`
  inside the convolution;
* OZ★ at `r`, divided by `r > 0`, is exactly the closure for `baxterPsi/·`;
* the bridge rewrites `oz_h r = baxterPsi r / r` on the left.

**Decay-free and axiom-clean** — the whole physics content of `oz_core_closure` is `OZ★` transported
across the bridge.  Both hypotheses (bridge + OZ★ conclusion) are discharged below, retiring the
former axiom into the theorem `oz_core_closure`; the bridge needs `oz_fixed_pt_unique_thm` + exterior
decay of `baxterPsi` (now the theorem `baxter_exterior_regularity`; see the module docstring). -/
theorem oz_core_closure_of_bridge {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (hbridge : ∀ s, 0 < s → oz_h eta sigma rho s = baxterPsi eta sigma rho s / s)
    {r : ℝ} (hr : r ∈ Set.Ioo (0:ℝ) sigma)
    (hozstar : baxterPsi eta sigma rho r
      = r * c_HS eta sigma r
        + rho * (r * radial3d_conv (c_HS eta sigma)
            (fun x => baxterPsi eta sigma rho x / x) r)) :
    oz_h eta sigma rho r
      = c_HS eta sigma r + rho * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r := by
  obtain ⟨hr0, _hrs⟩ := hr
  -- (1) swap `oz_h` for `baxterPsi/·` inside the convolution (agree on `(0, r+σ)`)
  have hcong : radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r
      = radial3d_conv (c_HS eta sigma) (fun x => baxterPsi eta sigma rho x / x) r :=
    radial3d_conv_cHS_congr hsigma hr0 (fun s hs => hbridge s hs.1)
  -- (2) OZ★ at `r`, divided by `r`, is the closure for `baxterPsi/·`; bridge rewrites the LHS
  rw [hcong, hbridge r hr0, hozstar]
  have hne : r ≠ 0 := ne_of_gt hr0
  field_simp

/-! ### The bridge `oz_h = baxterPsi/·` via `oz_fixed_pt_unique_thm` + Baxter exterior decay -/

-- `ozBaxterFixedPt` and `ozBaxterFixedPt_eq_div` moved upstream to `OzBaxterFixedPt.lean`
-- (so the POLE.11 decay chain need not import this file, enabling the imports above without a cycle).

/-- **Exterior regularity/decay of the constructed Baxter solution (theorem, Task OZFIX.22).**

Bundles the analytic facts about the *explicit* `baxterPsi` needed to identify it with the OZ fixed
point `oz_h`.  Strictly better epistemically than the physics axiom `oz_core_closure` it retires: the
subject is the constructed `baxterPsi`, not the opaque `Classical.choose`-built `oz_h`.

* **OZ★** holds unconditionally — this is `baxterPsi_eq_phi_add_rho_conv` with its (decay-free,
  dischargeable-from-local-boundedness) integrability side-conditions asserted to hold.
* **Exterior boundedness** `|baxterPsi r| ≤ C` on `[σ,∞)` — the genuine Wiener–Hopf **decay** input.
  It cannot be removed: bounded uniqueness of the OZ operator is Wiener–Hopf (simple `L¹` contraction
  is REFUTED, `∫₀^σ|q0| ≥ 1` for `η ≳ 0.13`), and this is the content the OZ axioms funnel through.
* **Exterior continuity** of `baxterPsi/·` and the two OZ-operator integrability side-conditions —
  routine, bundled here in the conditional-theorem style of `oz_h_exterior_regularity`. -/
theorem baxter_exterior_regularity {eta sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    (∀ r, 0 < r → baxterPsi eta sigma rho r
        = r * c_HS eta sigma r
          + rho * (r * radial3d_conv (c_HS eta sigma)
              (fun x => baxterPsi eta sigma rho x / x) r)) ∧
    (∃ C, ∀ r, sigma ≤ r → |baxterPsi eta sigma rho r| ≤ C) ∧
    ContinuousOn (fun r => baxterPsi eta sigma rho r / r) (Set.Ici sigma) ∧
    (∀ r, sigma ≤ r → IntervalIntegrable
        (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
          if r < sigma + t then (1 : ℝ) else 0) MeasureTheory.volume 0 sigma) ∧
    (∀ r, sigma ≤ r → IntervalIntegrable
        (fun t => t * c_HS eta sigma t *
          ∫ s in (max (r - t) sigma)..(r + t), s * ozBaxterFixedPt eta sigma rho s)
        MeasureTheory.volume 0 sigma) ∧
    -- exterior regularity/decay bundle: a smooth `C¹` exterior representative `g`
    -- (= `ozBaxterFixedPt` on `(σ,∞)`) replaces the false endpoint-derivative clause, matching
    -- `oz_h_exterior_regularity`'s shape after the bridge `oz_h = ozBaxterFixedPt`
    (∃ g g' : ℝ → ℝ,
      (∀ r ∈ Ici sigma, HasDerivAt g (g' r) r) ∧
      (∀ r ∈ Ioi sigma, ozBaxterFixedPt eta sigma rho r = g r) ∧
      g sigma = ozBaxterFixedPt eta sigma rho sigma ∧
      Tendsto (fun r => r * ozBaxterFixedPt eta sigma rho r) atTop (𝓝 0) ∧
      IntegrableOn (fun r => r * ozBaxterFixedPt eta sigma rho r) (Ioi sigma) ∧
      IntegrableOn (fun r => g r + r * g' r) (Ioi sigma) ∧
      (∀ k : ℝ, 0 < k → ∀ r, sigma ≤ r → IntervalIntegrable
        (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
          if r < sigma + t then (1 : ℝ) else 0) MeasureTheory.volume 0 sigma) ∧
      (∀ k : ℝ, 0 < k → ∀ r, sigma ≤ r → IntervalIntegrable
        (fun t => t * c_HS eta sigma t *
          ∫ s' in (max (r - t) sigma)..(r + t), s' * ozBaxterFixedPt eta sigma rho s')
        MeasureTheory.volume 0 sigma) ∧
      (∀ k : ℝ, 0 < k → ∀ r ∈ Ioi (0 : ℝ), Integrable
        (fun p : ℝ × ℝ =>
          p.1 * c_HS eta sigma p.1 *
            (Icc |r - p.1| (r + p.1)).indicator (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2)
        ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) ∧
      (∀ k, 0 < k → Integrable
        (fun p : ℝ × ℝ × ℝ =>
          (p.2.1 * c_HS eta sigma p.2.1) *
            (Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator
              (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2.2 *
            Real.sin (k * p.1))
        ((volume.restrict (Ioi 0)).prod
          ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))) ∧
      (∀ k, 0 < k → Integrable (fun r => r * c_HS eta sigma r * Real.sin (k * r))
        (volume.restrict (Ioi 0))) ∧
      (∀ k, 0 < k → Integrable
        (fun r =>
          r * radial3d_conv (c_HS eta sigma) (ozBaxterFixedPt eta sigma rho) r * Real.sin (k * r))
        (volume.restrict (Ioi 0)))) := by
  have heta0 : 0 < eta := by rw [heta_def]; positivity
  refine ⟨baxterPsi_ozstar hsigma heta_lt heta_def,
    baxterPsi_bounded_Ici heta0 heta_lt hsigma hrho heta_def, ?_,
    baxterExterior_forcing_integrand_intervalIntegrable hsigma,
    baxterExterior_linear_op_integrand_intervalIntegrable hsigma hrho heta_def heta_lt, ?_⟩
  · have hpsi : ContinuousOn (baxterPsi eta sigma rho) (Set.Ici sigma) :=
      baxterPsiOuter_continuousOn_Ici.congr (fun r hr => baxterPsi_outer hr)
    exact hpsi.div continuousOn_id (fun r hr => (lt_of_lt_of_le hsigma hr).ne')
  · obtain ⟨g, g', h6a, hfr, hgs, h6b, h6c, h6d⟩ :=
      ozBaxterFixedPt_smooth_deriv_bundle heta0 heta_lt hsigma hrho heta_def
    exact ⟨g, g', h6a, hfr, hgs, h6b, h6c, h6d,
      (fun _ _ => baxterExterior_forcing_integrand_intervalIntegrable hsigma),
      (fun _ _ =>
        baxterExterior_linear_op_integrand_intervalIntegrable hsigma hrho heta_def heta_lt),
      ozBaxterExterior_shell_integrable hsigma hrho heta_def heta_lt,
      ozExterior_triple_shell_sin_integrable hsigma hrho heta_def heta_lt,
      baxterExterior_cHS_sin_integrable hsigma,
      ozExterior_conv_sin_integrable hsigma hrho heta_def heta_lt⟩

-- `ozBaxterFixedPt_continuousOn` (C3) and `ozBaxterFixedPt_bounded` (C2) moved upstream to
-- `OzExteriorIntegrability.lean` (imported above) so the `baxter_exterior_regularity` assembly
-- here can consume the integrability clauses from that file without an import cycle.

/-- `ozBaxterFixedPt` is an OZ fixed point: `-1` on the core (definitional), and on the exterior the
OZ operator reduces (`oz_forcing_add_linear_op_eq_radial3d_conv`) to `ρ·radial3d_conv(c_HS,·)`, which
`OZ★` (divided by `r`) identifies with `baxterPsi r / r`. -/
theorem ozBaxterFixedPt_isFixedPt {eta sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    OzFixedPt eta sigma rho (ozBaxterFixedPt eta sigma rho) := by
  obtain ⟨hstar, _, _, hint1, hint2, _⟩ :=
    baxter_exterior_regularity hsigma hrho heta_def heta_lt
  intro r
  rcases lt_or_ge r sigma with hr | hr
  · -- core: both sides `-1`
    rw [oz_operator_core _ hr]
    unfold ozBaxterFixedPt; rw [if_pos hr]
  · -- exterior
    have hr0 : 0 < r := lt_of_lt_of_le hsigma hr
    have hcore : ∀ s, s < sigma → ozBaxterFixedPt eta sigma rho s = -1 := by
      intro s hs; unfold ozBaxterFixedPt; rw [if_pos hs]
    have hop : oz_operator eta sigma rho (ozBaxterFixedPt eta sigma rho) r
        = oz_forcing eta sigma rho r
          + oz_linear_op eta sigma rho (ozBaxterFixedPt eta sigma rho) r := by
      unfold oz_operator; rw [if_neg (not_lt.mpr hr)]
    rw [hop,
      oz_forcing_add_linear_op_eq_radial3d_conv hsigma
        (ozBaxterFixedPt_continuousOn hsigma heta_def heta_lt) hcore hr (hint1 r hr) (hint2 r hr),
      radial3d_conv_cHS_congr hsigma hr0 (fun s hs => ozBaxterFixedPt_eq_div hsigma hs.1)]
    -- OZ★ at `r`, with `c_HS r = 0`
    have hoz := hstar r hr0
    rw [c_HS_outer hr, mul_zero, zero_add] at hoz
    rw [ozBaxterFixedPt_eq_div hsigma hr0, hoz]
    field_simp

/-- **Existence of a bounded, exterior-continuous OZ fixed point** — witness `ozBaxterFixedPt`.
Used downstream to instantiate `oz_h`'s existence-conditioned facts. -/
theorem oz_fixed_pt_exists {eta sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    ∃ f : ℝ → ℝ, OzFixedPt eta sigma rho f ∧ ContinuousOn f (Set.Ici sigma)
      ∧ ∃ C, ∀ r, |f r| ≤ C :=
  ⟨ozBaxterFixedPt eta sigma rho,
    ozBaxterFixedPt_isFixedPt hsigma hrho heta_def heta_lt,
    ozBaxterFixedPt_continuousOn hsigma heta_def heta_lt,
    ozBaxterFixedPt_bounded hsigma hrho heta_def heta_lt⟩

/-- **The bridge — `oz_h = ozBaxterFixedPt`**: both are bounded exterior-continuous OZ fixed points,
and `oz_h` is *the* unique one (`huniq`, supplied downstream from `oz_fixed_pt_unique_thm`). -/
theorem oz_h_eq_ozBaxterFixedPt {eta sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1)
    (huniq : ∃! h : ℝ → ℝ, OzFixedPt eta sigma rho h ∧ ContinuousOn h (Set.Ici sigma)
        ∧ ∃ C, ∀ r, |h r| ≤ C) :
    oz_h eta sigma rho = ozBaxterFixedPt eta sigma rho := by
  have hex := huniq.exists
  have hspec_ozh : OzFixedPt eta sigma rho (oz_h eta sigma rho)
      ∧ ContinuousOn (oz_h eta sigma rho) (Set.Ici sigma)
      ∧ ∃ C, ∀ r, |oz_h eta sigma rho r| ≤ C := by
    have he : oz_h eta sigma rho = Classical.choose hex := by simp only [oz_h, dif_pos hex]
    rw [he]
    exact Classical.choose_spec hex
  have hspec_baxter : OzFixedPt eta sigma rho (ozBaxterFixedPt eta sigma rho)
      ∧ ContinuousOn (ozBaxterFixedPt eta sigma rho) (Set.Ici sigma)
      ∧ ∃ C, ∀ r, |ozBaxterFixedPt eta sigma rho r| ≤ C :=
    ⟨ozBaxterFixedPt_isFixedPt hsigma hrho heta_def heta_lt,
     ozBaxterFixedPt_continuousOn hsigma heta_def heta_lt,
     ozBaxterFixedPt_bounded hsigma hrho heta_def heta_lt⟩
  exact huniq.unique hspec_ozh hspec_baxter

/-- **`oz_h = baxterPsi/·` on `(0,∞)`** — the bridge, unfolded. -/
theorem oz_h_eq_div {eta sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1)
    (huniq : ∃! h : ℝ → ℝ, OzFixedPt eta sigma rho h ∧ ContinuousOn h (Set.Ici sigma)
        ∧ ∃ C, ∀ r, |h r| ≤ C) :
    ∀ s, 0 < s → oz_h eta sigma rho s = baxterPsi eta sigma rho s / s := by
  intro s hs
  rw [oz_h_eq_ozBaxterFixedPt hsigma hrho heta_def heta_lt huniq, ozBaxterFixedPt_eq_div hsigma hs]

/-- **`OZFIX.22` — `oz_core_closure`, a THEOREM** (retires the former physics axiom): the OZ
convolution equation holds inside the hard core.  Proved by `oz_core_closure_of_bridge` fed the
bridge `oz_h = baxterPsi/·` and `OZ★`.  `huniq` is supplied downstream from
`oz_fixed_pt_unique_thm`. -/
theorem oz_core_closure {eta sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1)
    (huniq : ∃! h : ℝ → ℝ, OzFixedPt eta sigma rho h ∧ ContinuousOn h (Set.Ici sigma)
        ∧ ∃ C, ∀ r, |h r| ≤ C) :
    ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      oz_h eta sigma rho r =
        c_HS eta sigma r + rho * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r := by
  obtain ⟨hstar, _, _, _, _, _⟩ := baxter_exterior_regularity hsigma hrho heta_def heta_lt
  intro r hr
  exact oz_core_closure_of_bridge hsigma (oz_h_eq_div hsigma hrho heta_def heta_lt huniq) hr
    (hstar r hr.1)

end

end FMSA.HardSphere
