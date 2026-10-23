import LeanCode.YukawaOZ.MSAMultiTailRDFBoundary
import LeanCode.Analysis.VolterraBanach

/-!
# Actual global causal moment density

The Volterra construction uses the concrete finite-tail Baxter kernel and
source. Existence on the entire half-line does not assert decay or positivity.
Its Laplace equation is proved from the actual renewal equation, under the
explicit weighted L1 condition. The physical RDF candidate has a hard core by
construction; certification as an OZ solution is a separate obligation.
-/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.VolterraBanach
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

theorem gsource_continuous (xi : ℝ) (z Dt G : ι → ℝ) :
    Continuous (gsource xi z Dt G) := by unfold gsource; fun_prop

def causalMoment (xi : ℝ) (z Dt G : ι → ℝ) : ℝ → ℝ :=
  volterraGlobalE 0 (fun r => rhoOf xi * qRight xi z Dt G r)
    (fun r => gsource xi z Dt G r / (2 * π))
    ((qRight_continuous xi z Dt G).const_mul _)
    ((gsource_continuous xi z Dt G).div_const _)

theorem causalMoment_zero (xi : ℝ) (z Dt G : ι → ℝ) {r : ℝ} (hr : r < 0) :
    causalMoment xi z Dt G r = 0 := by
  simp [causalMoment, volterraGlobalE, not_le.mpr hr]

theorem causalMoment_continuousOn (xi : ℝ) (z Dt G : ι → ℝ) :
    ContinuousOn (causalMoment xi z Dt G) (Ici 0) :=
  volterraGlobalE_continuousOn_Ici _ _ _ _ _

theorem causalMoment_renewal (xi : ℝ) (z Dt G : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    causalMoment xi z Dt G r = gsource xi z Dt G r / (2 * π) +
      ∫ t in (0 : ℝ)..r, rhoOf xi * q xi z Dt G (r - t) * causalMoment xi z Dt G t := by
  have h := volterraGlobalE_spec 0 (fun r => rhoOf xi * qRight xi z Dt G r)
    (fun r => gsource xi z Dt G r / (2 * π))
    ((qRight_continuous xi z Dt G).const_mul _)
    ((gsource_continuous xi z Dt G).div_const _) hr
  change causalMoment xi z Dt G r = _ at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hr] at ht
  dsimp only
  rw [qRight_eq_q xi z Dt G (by linarith [ht.2])]
  rfl

/-- There is one continuous solution on the half-line, not a different
solution for each integration window. -/
theorem causalMoment_unique (xi : ℝ) (z Dt G : ι → ℝ) (y : ℝ → ℝ)
    (hy : ContinuousOn y (Ici 0))
    (heq : ∀ r, 0 ≤ r → y r = gsource xi z Dt G r / (2 * π) +
      ∫ t in (0 : ℝ)..r, rhoOf xi * q xi z Dt G (r - t) * y t)
    {r : ℝ} (hr : 0 ≤ r) : y r = causalMoment xi z Dt G r := by
  let v : C(Icc (0 : ℝ) r, ℝ) :=
    ⟨fun t => y t, (hy.mono (fun _ ht => ht.1)).restrict⟩
  have hv : ∀ x : Icc (0 : ℝ) r, v x = gsource xi z Dt G x / (2 * π) +
      ∫ t in (0 : ℝ)..(x : ℝ), rhoOf xi * qRight xi z Dt G ((x : ℝ) - t) *
        IccExtend hr v t := by
    intro x
    change y x = _
    rw [heq x x.2.1]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le x.2.1] at ht
    dsimp only
    rw [IccExtend_of_mem hr v ⟨ht.1, le_trans ht.2 x.2.2⟩,
      qRight_eq_q xi z Dt G (by linarith [ht.2])]
    rfl
  have hu := volterraSolE_unique hr (fun r => rhoOf xi * qRight xi z Dt G r)
    (fun r => gsource xi z Dt G r / (2 * π))
    ((qRight_continuous xi z Dt G).const_mul _)
    ((gsource_continuous xi z Dt G).div_const _) v hv
  change v ⟨r, ⟨hr, le_rfl⟩⟩ = _
  rw [hu]
  exact (volterraGlobalE_eq_sol hr _ _ _ _ r ⟨hr, le_rfl⟩).symm

/-- Actual causal convolution, with the same globally constructed density. -/
theorem causalMoment_convolution (xi : ℝ) (z Dt G : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ t in (0 : ℝ)..r, q xi z Dt G (r - t) * causalMoment xi z Dt G t) =
      ∫ t : ℝ, q xi z Dt G (r - t) * causalMoment xi z Dt G t := by
  rw [intervalIntegral.integral_of_le hr]
  rw [← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rcases lt_or_ge r t with h | h
  · simp [q, show r - t < 0 by linarith]
  · have ht0 : t < 0 := by
      by_contra hh
      exact ht ⟨le_of_not_gt hh, h⟩
    rw [causalMoment_zero xi z Dt G ht0, mul_zero]

def candidateRDF (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  if r < 1 then 0 else causalMoment xi z Dt G (r - 1) / r

theorem candidateRDF_core (xi : ℝ) (z Dt G : ι → ℝ) {r : ℝ} (hr : r < 1) :
    candidateRDF xi z Dt G r = 0 := by simp [candidateRDF, hr]

theorem candidateRDF_shifted_moment (xi : ℝ) (z Dt G : ι → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (u + 1) * candidateRDF xi z Dt G (u + 1) = causalMoment xi z Dt G u := by
  simp only [candidateRDF, if_neg (show ¬ u + 1 < 1 by linarith), add_sub_cancel_right]
  field_simp [show u + 1 ≠ 0 by linarith]

def causalLaplace (xi : ℝ) (z Dt G : ι → ℝ) (s : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), exp (-s * u) * causalMoment xi z Dt G u

theorem gsource_weighted_integrable (xi : ℝ) (z Dt G : ι → ℝ)
    (hz : ∀ t, 0 < z t) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u => exp (-s * u) * gsource xi z Dt G u) (Ioi 0) := by
  have he : (fun u => exp (-s * u) * gsource xi z Dt G u) = fun u =>
      amplitudeA xi z Dt G * (u * exp (-s * u)) +
      amplitudeQp xi z Dt G * exp (-s * u) +
      ∑ t, (z t * C xi z Dt G t) * exp (-(s + z t) * u) := by
    funext u
    unfold gsource
    rw [mul_add, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro t _
      rw [show -(s + z t) * u = -s * u + -z t * u by ring, exp_add]
      ring
  rw [he]
  exact ((integrableOn_Ioi_id_mul_exp_neg hs).const_mul _).add
    ((integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0).const_mul _) |>.add
    (integrable_finsetSum _ (fun t _ =>
      (integrableOn_exp_mul_Ioi (by linarith [hz t] : -(s + z t) < 0) 0).const_mul _))

/-- The full transfer relation is derived from the constructed global density,
not postulated as an RDF moment equation. Weighted L1 is the remaining input. -/
theorem causalMoment_laplace_identity (xi : ℝ) (z Dt G : ι → ℝ)
    (hz : ∀ t, 0 < z t) {s : ℝ} (hs : 0 < s)
    (hy : IntegrableOn (fun u => exp (-s * u) * causalMoment xi z Dt G u) (Ioi 0)) :
    2 * π * causalLaplace xi z Dt G s * factor xi z Dt G s = secondRHS xi z Dt G s := by
  let yw := fun u => exp (-s * u) * causalMoment xi z Dt G u
  let qw := fun u => exp (-s * u) * q xi z Dt G u
  have hqw : IntegrableOn qw (Ioi 0) := (q_weighted_integrable xi z Dt G hz hs).integrableOn
  have hw (r : ℝ) :
      exp (-s * r) * (∫ t in (0 : ℝ)..r, q xi z Dt G (r - t) * causalMoment xi z Dt G t) =
        ∫ t in (0 : ℝ)..r, yw t * qw (r - t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [yw, qw]
    have he : exp (-s * t) * exp (-s * (r - t)) = exp (-s * r) := by
      rw [← exp_add]; congr 1; ring
    linear_combination -(causalMoment xi z Dt G t * q xi z Dt G (r - t)) * he
  have hiv : IntegrableOn (fun r => exp (-s * r) *
      ∫ t in (0 : ℝ)..r, q xi z Dt G (r - t) * causalMoment xi z Dt G t) (Ioi 0) := by
    refine (integrable_posConvolution hy hqw (ContinuousLinearMap.mul ℝ ℝ)).integrableOn.congr_fun
      (fun r hr => ?_) measurableSet_Ioi
    simp only [posConvolution, indicator_of_mem hr, ContinuousLinearMap.mul_apply']
    exact (hw r).symm
  have hie := (gsource_weighted_integrable xi z Dt G hz hs).div_const (2 * π)
  have he : causalLaplace xi z Dt G s =
      secondRHS xi z Dt G s / (2 * π) + rhoOf xi *
        (causalLaplace xi z Dt G s * Qhat xi z Dt G s) := by
    unfold causalLaplace
    calc
      (∫ r in Ioi (0 : ℝ), exp (-s * r) * causalMoment xi z Dt G r) =
          ∫ r in Ioi (0 : ℝ), exp (-s * r) * gsource xi z Dt G r / (2 * π) +
            rhoOf xi * (exp (-s * r) *
              ∫ t in (0 : ℝ)..r, q xi z Dt G (r - t) * causalMoment xi z Dt G t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        dsimp only
        rw [causalMoment_renewal xi z Dt G hr.le]
        have ec : (fun t => rhoOf xi * q xi z Dt G (r - t) * causalMoment xi z Dt G t) =
            fun t => rhoOf xi * (q xi z Dt G (r - t) * causalMoment xi z Dt G t) := by
          funext t; ring
        rw [ec, intervalIntegral.integral_const_mul]
        ring
      _ = _ := by
        rw [integral_add hie (hiv.const_mul _), integral_div, integral_const_mul]
        have hg : (∫ r in Ioi (0 : ℝ), exp (-s * r) * gsource xi z Dt G r) =
            secondRHS xi z Dt G s := by
          simpa only [mul_comm] using gsource_laplace xi z Dt G hz hs
        rw [hg]
        simp_rw [hw]
        have hpc := integral_posConvolution hy hqw (ContinuousLinearMap.mul ℝ ℝ)
        simp only [ContinuousLinearMap.mul_apply'] at hpc
        rw [hpc]
        congr 2
        rw [← laplaceQ_eq_Qhat xi z Dt G hz hs, laplaceQ_eq_integral xi z Dt G hz hs]
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        ring
  unfold factor
  field_simp [pi_ne_zero] at he
  linear_combination he

/-- Under nonvanishing at a tail rate, the constructed density recovers the
actual labelled BH moment, including inactive tails if their factor is regular. -/
theorem causalMoment_labelled_moment (xi : ℝ) (z K Dt G : ι → ℝ)
    (hz : ∀ t, 0 < z t) (hroot : IsRoot xi z K Dt G) (t : ι)
    (hF : factor xi z Dt G (z t) ≠ 0)
    (hy : IntegrableOn (fun u => exp (-z t * u) * causalMoment xi z Dt G u) (Ioi 0)) :
    causalLaplace xi z Dt G (z t) = G t := by
  have he := causalMoment_laplace_identity xi z Dt G hz (hz t) hy
  rw [← hroot.2 t] at he
  exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hF)
    (by linear_combination he)

end FMSA.ExactMSA.MultiTail
