import LeanCode.YukawaOZ.MSAMultiTailOZ
import LeanCode.Analysis.Volterra
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# RDF reconstruction: necessary conditions and an exact noncanonical BH root

These results distinguish c-side factorization from a physical RDF. At nonzero
density a finite OZ Fourier solution requires a nonzero structure denominator.
A real BH root only constrains finitely many Laplace points, and need not be
the normalized causal factor: the explicit zero-strength, one-tail example
below has positive density and a positive-real Laplace zero. It is an all-pass
modification of the PY factor, not a counterexample to the canonical PY RDF.
-/
noncomputable section
open MeasureTheory Set Real Filter Topology FMSA.HardSphere
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

theorem oz_denominator_ne_zero {ρ ch hh : ℝ}
    (hoz : hh = ch + ρ * ch * hh) : 1 - ρ * ch ≠ 0 := by
  intro h
  have hd : ρ * ch = 1 := by linarith
  rw [hd, one_mul] at hoz
  have hc : ch = 0 := by linarith
  simp [hc] at hd

theorem oz_structure_identity {ρ ch hh : ℝ}
    (hoz : hh = ch + ρ * ch * hh) :
    1 + ρ * hh = 1 / (1 - ρ * ch) := by
  field_simp [oz_denominator_ne_zero hoz]
  linear_combination ρ * hoz

theorem no_finite_oz_solution_at_zero (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    {k : ℝ} (hk : k ≠ 0)
    (hzero : 1 - rhoOf xi * radial_fourier (correlation xi z Dt G) k = 0) :
    ¬ ∃ hh : ℝ, hh = radial_fourier (correlation xi z Dt G) k +
      rhoOf xi * radial_fourier (correlation xi z Dt G) k * hh := by
  rintro ⟨hh, he⟩
  exact oz_denominator_ne_zero he hzero

/-- A BH root forces nonvanishing at each active tail's rate only. -/
theorem root_factor_ne_zero_at_active_rate (xi : ℝ) (z K Dt G : ι → ℝ)
    (hz : ∀ t, 0 < z t) (hroot : IsRoot xi z K Dt G) (t : ι) (hK : K t ≠ 0) :
    factor xi z Dt G (z t) ≠ 0 := by
  intro h
  have he := hroot.1 t
  rw [h, mul_zero] at he
  have hn : 2 * π * K t / z t ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hK) (hz t).ne'
  exact hn he.symm

namespace Noncanonical

def rate : Fin 1 → ℝ := fun _ => 1
def strength : Fin 1 → ℝ := fun _ => 0
def Dt : Fin 1 → ℝ := fun _ => 4 * π * (9 * exp (-1) - 2) / 3
def G : Fin 1 → ℝ := fun _ => 3 / (9 * exp (-1) - 2)

theorem denominator_pos : 0 < 9 * exp (-1 : ℝ) - 2 := by
  linarith [exp_neg_one_gt_d9]

theorem pieces :
    amplitudeA (1 / 4) rate Dt G = -16 * π / 3 ∧
    amplitudeQp (1 / 4) rate Dt G = 20 * π / 3 ∧
    W (1 / 4) rate Dt G 0 = 12 * π ∧ C (1 / 4) rate Dt G 0 = -8 * π / 3 := by
  have hn := denominator_pos.ne'
  repeat' constructor
  all_goals simp [amplitudeA, amplitudeQp, momentM, momentN, W, C, rate, Dt, G,
    bA0, bB0, qp0, rhoOf, Mtil, Ntil, gam]
  all_goals field_simp [hn, pi_ne_zero]
  all_goals ring

theorem factor_allpass (s : ℝ) (hs : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    factor (1 / 4) rate Dt G s = (s - 1) / (s + 1) * F0 (1 / 4) s := by
  rcases pieces with ⟨hA, hq, hW, hC⟩
  unfold factor Qhat
  rw [hA, hq]
  simp only [Fin.sum_univ_one, rate, hW, hC]
  unfold F0 Qhat0 phi1 phi2 bA0 qp0 rhoOf
  field_simp [hs, hs1, pi_ne_zero]
  ring

theorem source_allpass (s : ℝ) (hs : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    secondRHS (1 / 4) rate Dt G s = (s - 1) / (s + 1) * bhP0 (1 / 4) s := by
  rcases pieces with ⟨hA, hq, _, hC⟩
  unfold secondRHS
  rw [hA, hq]
  simp only [Fin.sum_univ_one, rate, hC]
  unfold bhP0 bA0 qp0
  field_simp [hs, hs1]
  ring

theorem factor_one : factor (1 / 4) rate Dt G 1 = 0 := by
  rw [factor_allpass 1 (by norm_num) (by norm_num)]
  norm_num

theorem source_one : secondRHS (1 / 4) rate Dt G 1 = 0 := by
  rw [source_allpass 1 (by norm_num) (by norm_num)]
  norm_num

theorem fourier_allpass_real {k : ℝ} (hk : k ≠ 0) :
    1 - rhoOf (1 / 4) * Qre (1 / 4) rate Dt G k =
      (k ^ 2 - 1) / (k ^ 2 + 1) * (1 - rhoOf (1 / 4) * Blocks.polyRe (16 * π / 3) (4 * π) k) +
      2 * k / (k ^ 2 + 1) * (rhoOf (1 / 4) * Blocks.polyIm (16 * π / 3) (4 * π) k) := by
  rcases pieces with ⟨hA, hq, hW, hC⟩
  unfold Qre
  rw [hA, hq]
  simp only [Fin.sum_univ_one, rate, hW, hC]
  unfold Blocks.polyRe Blocks.polyIm Blocks.tailRe rhoOf
  field_simp [hk, show k ^ 2 + 1 ≠ 0 by positivity, show 1 + k ^ 2 ≠ 0 by positivity, pi_ne_zero]
  ring

theorem fourier_allpass_imag {k : ℝ} (hk : k ≠ 0) :
    rhoOf (1 / 4) * Qim (1 / 4) rate Dt G k =
      (k ^ 2 - 1) / (k ^ 2 + 1) * (rhoOf (1 / 4) * Blocks.polyIm (16 * π / 3) (4 * π) k) -
      2 * k / (k ^ 2 + 1) * (1 - rhoOf (1 / 4) * Blocks.polyRe (16 * π / 3) (4 * π) k) := by
  rcases pieces with ⟨hA, hq, hW, hC⟩
  unfold Qim
  rw [hA, hq]
  simp only [Fin.sum_univ_one, rate, hW, hC]
  unfold Blocks.polyRe Blocks.polyIm Blocks.tailIm rhoOf
  field_simp [hk, show k ^ 2 + 1 ≠ 0 by positivity, show 1 + k ^ 2 ≠ 0 by positivity, pi_ne_zero]
  ring

/-- The noncanonical factor has exactly the same nonzero-k structure
denominator as the PY factor. Fourier positivity cannot select its phase. -/
theorem fourier_denominator_eq_hs {k : ℝ} (hk : k ≠ 0) :
    (1 - rhoOf (1 / 4) * Qre (1 / 4) rate Dt G k) ^ 2 +
      (rhoOf (1 / 4) * Qim (1 / 4) rate Dt G k) ^ 2 =
      (1 - rhoOf (1 / 4) * Blocks.polyRe (16 * π / 3) (4 * π) k) ^ 2 +
      (rhoOf (1 / 4) * Blocks.polyIm (16 * π / 3) (4 * π) k) ^ 2 := by
  rw [fourier_allpass_real hk, fourier_allpass_imag hk]
  field_simp [show k ^ 2 + 1 ≠ 0 by positivity]
  ring

/-- A nontrivial-density real BH root with zero tail strength and nonzero Dt. -/
theorem isRoot : IsRoot (1 / 4) rate strength Dt G := by
  constructor
  · intro t
    simp only [rate, strength, factor_one, mul_zero, zero_div]
  · intro t
    simp only [rate, factor_one, source_one, mul_zero]

theorem moment_mismatch : 2 * π * G 0 * F0 (1 / 4) 1 ≠ bhP0 (1 / 4) 1 := by
  intro he
  have hn := denominator_pos.ne'
  simp [G, F0, Qhat0, phi1, phi2, bA0, qp0, rhoOf, bhP0] at he
  field_simp [hn, pi_ne_zero] at he
  nlinarith [pi_pos]

/-- Therefore the root amplitudes do not equal the canonical hard-sphere seed. -/
theorem G_ne_hs_seed : G 0 ≠ G0 (1 / 4) 1 := by
  intro he
  have hb := bh_base_eq (xi := (1 / 4)) (z := (1 : ℝ))
    (by norm_num : (1/4 : ℝ) ∈ Ioo 0 1) (by norm_num : (0 : ℝ) < 1)
  rw [bhF_base, bhP_base] at hb
  apply moment_mismatch
  rw [he]
  simpa only [mul_assoc, F0] using hb

/-- A continuous Laplace-moment family satisfying the full g-side identity
cannot have the root's labelled moment G at its positive-axis zero. This
identifies a genuine missing reconstruction interface, without assuming h=-1. -/
theorem no_continuous_moment_family (m : ℝ → ℝ) (hm : ContinuousAt m 1)
    (hid : m 1 = G 0)
    (hoz : ∀ s, 1 < s → 2 * π * m s * factor (1 / 4) rate Dt G s =
      secondRHS (1 / 4) rate Dt G s) : False := by
  let f : ℝ → ℝ := fun s => 2 * π * m s * F0 (1 / 4) s - bhP0 (1 / 4) s
  have hfc : ContinuousAt f 1 := by
    have hF : ContinuousAt (F0 (1 / 4)) 1 := by
      unfold F0 Qhat0 phi1 phi2
      fun_prop (disch := norm_num)
    have hP : ContinuousAt (bhP0 (1 / 4)) 1 := by
      unfold bhP0
      fun_prop (disch := norm_num)
    exact ((continuousAt_const.mul hm).mul hF).sub hP
  have he : f =ᶠ[𝓝[>] (1 : ℝ)] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    change 1 < s at hs
    have h := hoz s hs
    rw [factor_allpass s (by linarith) (by linarith),
      source_allpass s (by linarith) (by linarith)] at h
    have ha : (s - 1) / (s + 1) ≠ 0 := div_ne_zero (by linarith) (by linarith)
    have hh : 2 * π * m s * F0 (1 / 4) s = bhP0 (1 / 4) s := by
      apply mul_left_cancel₀ ha
      linear_combination h
    exact sub_eq_zero.mpr hh
  have ht : Tendsto f (𝓝[>] (1 : ℝ)) (𝓝 0) := tendsto_const_nhds.congr' he.symm
  have hzero : f 1 = 0 := tendsto_nhds_unique (hfc.mono_left nhdsWithin_le_nhds) ht
  apply moment_mismatch
  simpa [f, hid, sub_eq_zero] using hzero

end Noncanonical

/-- A real BH root does not imply nonvanishing on the positive Laplace axis.
This already fails with one labelled zero-strength tail at positive density. -/
theorem real_root_not_imply_positive_axis_nonvanishing :
    ∃ (xi : ℝ) (z K Dt G : Fin 1 → ℝ), xi ∈ Ioo (0 : ℝ) 1 ∧
      (∀ t, 0 < z t) ∧ IsRoot xi z K Dt G ∧
      ∃ s : ℝ, 0 < s ∧ factor xi z Dt G s = 0 := by
  refine ⟨1/4, Noncanonical.rate, Noncanonical.strength, Noncanonical.Dt,
    Noncanonical.G, by norm_num, ?_, Noncanonical.isRoot, 1, by norm_num,
    Noncanonical.factor_one⟩
  intro t
  norm_num [Noncanonical.rate]

/-- Continuity of actual RDF Laplace moments follows from an integrable
exponential majorant at a smaller rate; it is not an additional physics axiom. -/
theorem rdf_moment_continuousAt (g : ℝ → ℝ) (hg : Measurable g)
    {a s : ℝ} (has : a < s)
    (hi : IntegrableOn (fun u => exp (-a * u) * (u * g u)) (Ioi (0 : ℝ))) :
    ContinuousAt (GSide.rdfLaplaceMoment g) s := by
  unfold GSide.rdfLaplaceMoment
  apply continuousAt_of_dominated (bound := fun u => ‖exp (-a * u) * (u * g u)‖)
  · exact Filter.Eventually.of_forall (fun t =>
      (((by fun_prop : Continuous (fun u => exp (-t * u))).measurable).mul
        (measurable_id.mul hg)).aestronglyMeasurable)
  · filter_upwards [eventually_gt_nhds has] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0 < u at hu
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by nlinarith))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · exact hi.norm
  · exact Filter.Eventually.of_forall (fun u => by fun_prop)

/-- The concrete noncanonical real root cannot be reconstructed with its
labelled moment from an RDF having a continuous Laplace moment and the full
g-side moment equation. No hard-core condition is assumed in this obstruction. -/
theorem Noncanonical.no_rdf_moment_reconstruction (g : ℝ → ℝ) (hg : Measurable g)
    (hi : IntegrableOn (fun u => exp (-(1 / 2 : ℝ) * u) * (u * g u)) (Ioi (0 : ℝ)))
    (hid : GSide.rdfLaplaceMoment g 1 = Noncanonical.G 0)
    (hoz : ∀ s, 1 < s → 2 * π * GSide.rdfLaplaceMoment g s *
      factor (1 / 4) Noncanonical.rate Noncanonical.Dt Noncanonical.G s =
      secondRHS (1 / 4) Noncanonical.rate Noncanonical.Dt Noncanonical.G s) : False :=
  Noncanonical.no_continuous_moment_family (GSide.rdfLaplaceMoment g)
    (rdf_moment_continuousAt g hg (by norm_num : (1 / 2 : ℝ) < 1) hi) hid hoz

/-- The obstruction above applies to the actual integral OZ primitive, not
merely to an independently supplied algebraic moment equation. -/
theorem Noncanonical.no_rdf_full_gside (g : ℝ → ℝ) (hg : Measurable g)
    (hsupp : ∀ u, u < 0 → g u = 0)
    (hi : IntegrableOn (fun u => exp (-(1 / 2 : ℝ) * u) * (u * g u)) (Ioi (0 : ℝ)))
    (hL1 : ∀ s, 1 < s → Integrable (fun u => exp (-s * u) * (u * g u)))
    (hid : GSide.rdfLaplaceMoment g 1 = Noncanonical.G 0)
    (hoz : ∀ s, 1 < s → 2 * π * GSide.rdfLaplaceMoment g s =
      (∫ u in Ioi (0 : ℝ), gsource (1 / 4) Noncanonical.rate Noncanonical.Dt Noncanonical.G u * exp (-s * u)) +
      2 * π * rhoOf (1 / 4) * (∫ r in Ioi (0 : ℝ), exp (-s * r) *
        ∫ u in Ioi (0 : ℝ), (r - u) * g (r - u) *
          q (1 / 4) Noncanonical.rate Noncanonical.Dt Noncanonical.G u)) : False := by
  apply Noncanonical.no_rdf_moment_reconstruction g hg hi hid
  intro s hs
  exact moment_identity_of_gside (1 / 4) Noncanonical.rate Noncanonical.Dt Noncanonical.G
    (by intro t; norm_num [Noncanonical.rate]) g (by linarith) hsupp (hL1 s hs) (hoz s hs)

/-- A continuous extension of the actual Baxter kernel from the nonnegative
half-line, used by the finite-window Volterra construction. -/
def qRight (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  if r ≤ 1 then qCore xi z Dt G r else qTail xi z Dt G r

theorem qRight_continuous (xi : ℝ) (z Dt G : ι → ℝ) : Continuous (qRight xi z Dt G) := by
  unfold qRight
  have hc : Continuous (qCore xi z Dt G) := by unfold qCore; fun_prop
  have ht : Continuous (qTail xi z Dt G) := by unfold qTail; fun_prop
  exact hc.if_le ht continuous_id continuous_const (fun r hr => by
    change r = 1 at hr
    subst r
    exact q_contact xi z Dt G)

theorem qRight_eq_q (xi : ℝ) (z Dt G : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    qRight xi z Dt G r = q xi z Dt G r := by
  simp only [qRight, q, if_neg (not_lt.mpr hr)]

/-- The actual source and Baxter kernel construct a unique continuous moment
density on every finite causal window. This proves existence, without assuming
a hard-core RDF. Global decay/L1, moment identification and the full radial OZ
and hard-core bridge are separate obligations. -/
theorem existsUnique_causal_moment_window (xi : ℝ) (z Dt G : ι → ℝ)
    {L : ℝ} (hL : 0 ≤ L) :
    ∃! y : C(Icc (0 : ℝ) L, ℝ), ∀ r : Icc (0 : ℝ) L,
      y r = gsource xi z Dt G r / (2 * π) +
        ∫ t in (0 : ℝ)..(r : ℝ), rhoOf xi * q xi z Dt G ((r : ℝ) - t) *
          Set.IccExtend hL y t := by
  have hg : Continuous (fun r => gsource xi z Dt G r / (2 * π)) := by
    unfold gsource
    fun_prop
  obtain ⟨y, hy, hu⟩ := volterra_convolution_existsUnique hL
    (fun r => rhoOf xi * qRight xi z Dt G r) _
    ((qRight_continuous xi z Dt G).const_mul _) hg
  have hc (f : C(Icc (0 : ℝ) L, ℝ)) (r : Icc (0 : ℝ) L) :
      (∫ t in (0 : ℝ)..(r : ℝ), rhoOf xi * qRight xi z Dt G ((r : ℝ) - t) * Set.IccExtend hL f t) =
      ∫ t in (0 : ℝ)..(r : ℝ), rhoOf xi * q xi z Dt G ((r : ℝ) - t) * Set.IccExtend hL f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le r.2.1] at ht
    dsimp only
    rw [qRight_eq_q xi z Dt G (by linarith [ht.2])]
  refine ⟨y, ?_, ?_⟩
  · intro r
    simpa only [hc] using hy r
  · intro f hf
    apply hu f
    intro r
    simpa only [hc] using hf r

end FMSA.ExactMSA.MultiTail
