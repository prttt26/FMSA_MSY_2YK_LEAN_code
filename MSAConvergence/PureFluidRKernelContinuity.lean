import MSAConvergence.PureFluidRWeightIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option linter.style.header false

/-! A rate-independent integrable bound for the positive-frequency
pure-fluid squarefree kernel. -/
noncomputable section
open Real Set MeasureTheory Filter Topology
namespace FMSA.Convergence.PureFluidRKernelContinuity
open FMSA.Convergence.PureFluidRKernelIntegral
open FMSA.Convergence.PureFluidRWeightIntegral
open FMSA.Convergence.PureFluidRWeightPositivity
open FMSA.Convergence.PureFluidRWeightOddPart
open FMSA.Convergence.PureFluidRSquarefreeGeometric
open FMSA.Convergence.PureFluidRSquarefreePoleSpan
open FMSA.Convergence.PureFluidRFormalDispersion
variable {T : Type*} [DecidableEq T]

def kernelProduct (s : Finset T) (z : T → ℝ) (x k : ℝ) : ℝ :=
  k ^ 2 / ((k ^ 2 + x ^ 2) * ∏ i ∈ s, (k ^ 2 + z i ^ 2))

/-- A fixed selected positive rate supplies an integrable Cauchy
majorant, uniformly for all positive evaluation frequencies. -/
theorem kernelProduct_le_cauchy_majorant
    (s : Finset T) (z : T → ℝ)
    (hz : ∀ i ∈ s, 0 < z i)
    (i₀ : T) (hi₀ : i₀ ∈ s)
    (x : ℝ) (hx : 0 < x) (k : ℝ) :
    0 ≤ kernelProduct s z x k ∧
    kernelProduct s z x k ≤
      (∏ i ∈ s.erase i₀, z i ^ 2)⁻¹ * (k ^ 2 + z i₀ ^ 2)⁻¹ := by
  classical
  let q : ℝ := ∏ i ∈ s.erase i₀, (k ^ 2 + z i ^ 2)
  let c : ℝ := ∏ i ∈ s.erase i₀, z i ^ 2
  have hqpos : 0 < q := by
    dsimp [q]
    apply Finset.prod_pos
    intro i hi
    exact add_pos_of_nonneg_of_pos (sq_nonneg k) (sq_pos_of_pos (hz i (Finset.mem_of_mem_erase hi)))
  have hcpos : 0 < c := by
    dsimp [c]
    apply Finset.prod_pos
    intro i hi
    exact sq_pos_of_pos (hz i (Finset.mem_of_mem_erase hi))
  have hcq : c ≤ q := by
    dsimp [c, q]
    apply Finset.prod_le_prod
    · intro i hi
      exact (sq_nonneg (z i))
    · intro i hi
      exact le_add_of_nonneg_left (sq_nonneg k)
  have hipos : 0 < k ^ 2 + z i₀ ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg k) (sq_pos_of_pos (hz i₀ hi₀))
  have hxpos : 0 < k ^ 2 + x ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg k) (sq_pos_of_pos hx)
  have hsplit : (∏ i ∈ s, (k ^ 2 + z i ^ 2)) =
      (k ^ 2 + z i₀ ^ 2) * q := by
    exact (Finset.mul_prod_erase s (fun i => k ^ 2 + z i ^ 2) hi₀).symm
  have hPpos : 0 < ∏ i ∈ s, (k ^ 2 + z i ^ 2) := by
    rw [hsplit]
    exact mul_pos hipos hqpos
  have hdenpos : 0 < (k ^ 2 + x ^ 2) * ∏ i ∈ s, (k ^ 2 + z i ^ 2) :=
    mul_pos hxpos hPpos
  constructor
  · exact div_nonneg (sq_nonneg k) hdenpos.le
  · have hfirst : kernelProduct s z x k ≤
        (∏ i ∈ s, (k ^ 2 + z i ^ 2))⁻¹ := by
      unfold kernelProduct
      rw [div_eq_mul_inv, mul_inv_rev]
      have hratio : k ^ 2 * (k ^ 2 + x ^ 2)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact (div_le_one hxpos).2 (le_add_of_nonneg_right (sq_nonneg x))
      calc
        k ^ 2 * ((∏ i ∈ s, (k ^ 2 + z i ^ 2))⁻¹ * (k ^ 2 + x ^ 2)⁻¹) =
            (k ^ 2 * (k ^ 2 + x ^ 2)⁻¹) *
              (∏ i ∈ s, (k ^ 2 + z i ^ 2))⁻¹ := by ring
        _ ≤ 1 * (∏ i ∈ s, (k ^ 2 + z i ^ 2))⁻¹ :=
          mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr hPpos.le)
        _ = _ := one_mul _
    have hPbound : (k ^ 2 + z i₀ ^ 2) * c ≤
        ∏ i ∈ s, (k ^ 2 + z i ^ 2) := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hcq hipos.le
    have hinv := one_div_le_one_div_of_le (mul_pos hipos hcpos) hPbound
    have hsecond : (∏ i ∈ s, (k ^ 2 + z i ^ 2))⁻¹ ≤
        c⁻¹ * (k ^ 2 + z i₀ ^ 2)⁻¹ := by
      simpa only [one_div, mul_inv_rev, mul_comm] using hinv
    exact hfirst.trans hsecond

omit [DecidableEq T] in
/-- The squared-rate kernel has a genuine half-line integral for any
nonempty positive-rate family, even with coincident selected rates and
with the evaluation frequency equal to a selected rate. -/
theorem kernelProduct_integrableOn_Ioi
    (s : Finset T) (z : T → ℝ)
    (hz : ∀ i ∈ s, 0 < z i)
    (hs : s.Nonempty) (x : ℝ) (hx : 0 < x) :
    IntegrableOn (kernelProduct s z x) (Set.Ioi 0) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  let c : ℝ := (∏ i ∈ s.erase i₀, z i ^ 2)⁻¹
  have hc : 0 ≤ c := by
    dsimp [c]
    apply inv_nonneg.mpr
    exact Finset.prod_nonneg (fun i hi => sq_nonneg (z i))
  have hdom : IntegrableOn
      (fun k : ℝ => c * (k ^ 2 + z i₀ ^ 2)⁻¹) (Set.Ioi 0) :=
    (integrableOn_Ioi_inv_sq_add_sq (z i₀) (hz i₀ hi₀)).const_mul c
  have hmeas : AEStronglyMeasurable (kernelProduct s z x)
      (volume.restrict (Set.Ioi 0)) := by
    have hm : Measurable (kernelProduct s z x) := by
      unfold kernelProduct
      fun_prop
    exact hm.aestronglyMeasurable
  apply Integrable.mono' hdom hmeas
  filter_upwards [] with k
  obtain ⟨h0, hle⟩ := kernelProduct_le_cauchy_majorant s z hz i₀ hi₀ x hx k
  have hden : 0 ≤ (k ^ 2 + z i₀ ^ 2)⁻¹ := by
    exact inv_nonneg.mpr (add_nonneg (sq_nonneg k) (sq_nonneg (z i₀)))
  simpa only [Real.norm_eq_abs, abs_of_nonneg h0,
    abs_of_nonneg (mul_nonneg hc hden), c] using hle

omit [DecidableEq T] in
/-- The honest half-line kernel integral varies continuously with
every positive evaluation frequency, including at a selected rate. -/
theorem kernelProduct_integral_continuousAt
    (s : Finset T) (z : T → ℝ)
    (hz : ∀ i ∈ s, 0 < z i)
    (hs : s.Nonempty) (x : ℝ) (hx : 0 < x) :
    ContinuousAt
      (fun y : ℝ => ∫ k in Set.Ioi (0 : ℝ), kernelProduct s z y k) x := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  let bound : ℝ → ℝ := fun k =>
    (∏ i ∈ s.erase i₀, z i ^ 2)⁻¹ * (k ^ 2 + z i₀ ^ 2)⁻¹
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi 0)) :=
    (integrableOn_Ioi_inv_sq_add_sq (z i₀) (hz i₀ hi₀)).const_mul _
  have hmeas (y : ℝ) : AEStronglyMeasurable (kernelProduct s z y)
      (volume.restrict (Set.Ioi 0)) := by
    have hm : Measurable (kernelProduct s z y) := by
      unfold kernelProduct
      fun_prop
    exact hm.aestronglyMeasurable
  have hbound : ∀ᶠ y in 𝓝 x, ∀ᵐ k ∂(volume.restrict (Set.Ioi 0)),
      ‖kernelProduct s z y k‖ ≤ bound k := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    filter_upwards [] with k
    obtain ⟨h0, hle⟩ :=
      kernelProduct_le_cauchy_majorant s z hz i₀ hi₀ y hy k
    have hc : 0 ≤ (∏ i ∈ s.erase i₀, z i ^ 2)⁻¹ := by
      apply inv_nonneg.mpr
      exact Finset.prod_nonneg (fun i hi => sq_nonneg (z i))
    have hden : 0 ≤ (k ^ 2 + z i₀ ^ 2)⁻¹ :=
      inv_nonneg.mpr (add_nonneg (sq_nonneg k) (sq_nonneg (z i₀)))
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0,
      abs_of_nonneg (mul_nonneg hc hden), bound] using hle
  have hlim : ∀ᵐ k ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun y => kernelProduct s z y k) (𝓝 x)
        (𝓝 (kernelProduct s z x k)) := by
    filter_upwards [] with k
    have hPpos : 0 < ∏ i ∈ s, (k ^ 2 + z i ^ 2) := by
      apply Finset.prod_pos
      intro i hi
      exact add_pos_of_nonneg_of_pos (sq_nonneg k) (sq_pos_of_pos (hz i hi))
    have hden : (k ^ 2 + x ^ 2) *
        ∏ i ∈ s, (k ^ 2 + z i ^ 2) ≠ 0 :=
      (mul_pos (add_pos_of_nonneg_of_pos (sq_nonneg k) (sq_pos_of_pos hx)) hPpos).ne'
    change ContinuousAt (fun y : ℝ => kernelProduct s z y k) x
    unfold kernelProduct
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact hden
  exact tendsto_integral_filter_of_dominated_convergence
    bound (Filter.Eventually.of_forall hmeas) hbound hbound_int hlim

/-- A lower positive rate box gives one fixed integrable majorant
for all rate families in that box. -/
theorem kernelProduct_le_rate_box_majorant
    (s : Finset T) (z z' : T → ℝ)
    (hz : ∀ i ∈ s, 0 < z i)
    (hlower : ∀ i ∈ s, z i / 2 ≤ z' i)
    (i₀ : T) (hi₀ : i₀ ∈ s)
    (x : ℝ) (hx : 0 < x) (k : ℝ) :
    0 ≤ kernelProduct s z' x k ∧
    kernelProduct s z' x k ≤
      (∏ i ∈ s.erase i₀, (z i / 2) ^ 2)⁻¹ *
        (k ^ 2 + (z i₀ / 2) ^ 2)⁻¹ := by
  classical
  have hz' : ∀ i ∈ s, 0 < z' i := by
    intro i hi
    exact lt_of_lt_of_le (half_pos (hz i hi)) (hlower i hi)
  obtain ⟨h0, hfirst⟩ :=
    kernelProduct_le_cauchy_majorant s z' hz' i₀ hi₀ x hx k
  have hsq (i : T) (hi : i ∈ s) : (z i / 2) ^ 2 ≤ (z' i) ^ 2 := by
    have ha : 0 ≤ z i / 2 := (half_pos (hz i hi)).le
    have hb : z i / 2 ≤ z' i := hlower i hi
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (add_nonneg ha (hz' i hi).le)]
  have hprod : (∏ i ∈ s.erase i₀, (z i / 2) ^ 2) ≤
      ∏ i ∈ s.erase i₀, (z' i) ^ 2 := by
    apply Finset.prod_le_prod
    · intro i hi
      exact sq_nonneg _
    · intro i hi
      exact hsq i (Finset.mem_of_mem_erase hi)
  have hbasepos : 0 < ∏ i ∈ s.erase i₀, (z i / 2) ^ 2 := by
    apply Finset.prod_pos
    intro i hi
    exact sq_pos_of_pos (half_pos (hz i (Finset.mem_of_mem_erase hi)))
  have hprod_inv : (∏ i ∈ s.erase i₀, (z' i) ^ 2)⁻¹ ≤
      (∏ i ∈ s.erase i₀, (z i / 2) ^ 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hbasepos hprod
  have hres_inv : (k ^ 2 + (z' i₀) ^ 2)⁻¹ ≤
      (k ^ 2 + (z i₀ / 2) ^ 2)⁻¹ := by
    have ha : 0 < k ^ 2 + (z i₀ / 2) ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg k)
        (sq_pos_of_pos (half_pos (hz i₀ hi₀)))
    have hb : k ^ 2 + (z i₀ / 2) ^ 2 ≤ k ^ 2 + (z' i₀) ^ 2 := by
      simpa only [add_comm] using add_le_add_right (hsq i₀ hi₀) (k ^ 2)
    simpa only [one_div] using one_div_le_one_div_of_le ha hb
  have hres_nonneg : 0 ≤ (k ^ 2 + (z' i₀) ^ 2)⁻¹ := by positivity
  have hbase_inv_nonneg :
      0 ≤ (∏ i ∈ s.erase i₀, (z i / 2) ^ 2)⁻¹ :=
    (inv_pos.mpr hbasepos).le
  constructor
  · exact h0
  · exact hfirst.trans <| (mul_le_mul_of_nonneg_right hprod_inv hres_nonneg).trans
      (mul_le_mul_of_nonneg_left hres_inv hbase_inv_nonneg)

omit [DecidableEq T] in
/-- At every strictly positive finite rate family, the half-line
kernel integral is continuous in all rate parameters. Coincident
rates are allowed at the base point and along the approaching net. -/
theorem kernelProduct_integral_continuousAt_rate
    [Finite T] (s : Finset T) (z : T → ℝ)
    (hz : ∀ i ∈ s, 0 < z i)
    (hs : s.Nonempty) (x : ℝ) (hx : 0 < x) :
    ContinuousAt
      (fun z' : T → ℝ => ∫ k in Set.Ioi (0 : ℝ), kernelProduct s z' x k) z := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  let bound : ℝ → ℝ := fun k =>
    (∏ i ∈ s.erase i₀, (z i / 2) ^ 2)⁻¹ *
      (k ^ 2 + (z i₀ / 2) ^ 2)⁻¹
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi 0)) :=
    (integrableOn_Ioi_inv_sq_add_sq (z i₀ / 2)
      (half_pos (hz i₀ hi₀))).const_mul _
  have hlocal : ∀ᶠ z' : T → ℝ in 𝓝 z,
      ∀ i ∈ s, z i / 2 ≤ z' i := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    have hhalf : z i / 2 < z i := by linarith [hz i hi]
    have hcont : ContinuousAt (fun w : T → ℝ => w i) z :=
      continuousAt_apply i z
    exact (hcont.tendsto.eventually (isOpen_Ioi.mem_nhds hhalf)).mono
      (fun w hw => hw.le)
  have hmeas (z' : T → ℝ) : AEStronglyMeasurable
      (kernelProduct s z' x) (volume.restrict (Set.Ioi 0)) := by
    have hm : Measurable (kernelProduct s z' x) := by
      unfold kernelProduct
      fun_prop
    exact hm.aestronglyMeasurable
  have hbound : ∀ᶠ z' : T → ℝ in 𝓝 z,
      ∀ᵐ k ∂(volume.restrict (Set.Ioi 0)),
        ‖kernelProduct s z' x k‖ ≤ bound k := by
    filter_upwards [hlocal] with z' hlower
    filter_upwards [] with k
    obtain ⟨h0, hle⟩ :=
      kernelProduct_le_rate_box_majorant s z z' hz hlower i₀ hi₀ x hx k
    have hc : 0 ≤ (∏ i ∈ s.erase i₀, (z i / 2) ^ 2)⁻¹ := by
      apply inv_nonneg.mpr
      exact Finset.prod_nonneg (fun i hi => sq_nonneg (z i / 2))
    have hden : 0 ≤ (k ^ 2 + (z i₀ / 2) ^ 2)⁻¹ :=
      inv_nonneg.mpr (add_nonneg (sq_nonneg k) (sq_nonneg (z i₀ / 2)))
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0,
      abs_of_nonneg (mul_nonneg hc hden), bound] using hle
  have hlim : ∀ᵐ k ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun z' : T → ℝ => kernelProduct s z' x k) (𝓝 z)
        (𝓝 (kernelProduct s z x k)) := by
    filter_upwards [] with k
    have hPcont : ContinuousAt
        (fun z' : T → ℝ => ∏ i ∈ s, (k ^ 2 + (z' i) ^ 2)) z := by
      apply tendsto_finsetProd s
      intro i hi
      exact continuousAt_const.add ((continuousAt_apply i z).pow 2)
    have hPpos : 0 < ∏ i ∈ s, (k ^ 2 + z i ^ 2) := by
      apply Finset.prod_pos
      intro i hi
      exact add_pos_of_nonneg_of_pos (sq_nonneg k) (sq_pos_of_pos (hz i hi))
    change ContinuousAt (fun z' : T → ℝ => kernelProduct s z' x k) z
    unfold kernelProduct
    apply ContinuousAt.div
    · fun_prop
    · exact continuousAt_const.mul hPcont
    · exact (mul_pos
        (add_pos_of_nonneg_of_pos (sq_nonneg k) (sq_pos_of_pos hx)) hPpos).ne'
  exact tendsto_integral_filter_of_dominated_convergence
    bound (Filter.Eventually.of_forall hmeas) hbound hbound_int hlim

/-- The distinct-rate squarefree weight equals its positive kernel
integral at every positive evaluation frequency, including `x=z_i`.
The node collision is handled by a genuine dominated-continuity
argument, not by totalized partial fractions at the collision. -/
theorem multilinearWeight_eq_kernel_integral_all_x
    (s : Finset T) (z : T → ℝ)
    (hs : s.Nonempty) (hz : ∀ i ∈ s, 0 < z i)
    (hinj : Set.InjOn z s) (x : ℝ) (hx : 0 < x) :
    multilinearWeight s z x =
      (2 ^ (s.card - 1) * ∏ i ∈ s, z i) *
        ((2 / Real.pi) *
          (∫ k in Set.Ioi (0 : ℝ), kernelProduct s z x k)) := by
  classical
  let d : Set ℝ := (↑(s.image z) : Set ℝ)ᶜ
  let t : Set ℝ := Set.Ioi 0
  have hdense : Dense d :=
    Set.Countable.dense_compl ℝ (s.image z).finite_toSet.countable
  have hfcont : ContinuousOn (fun y => multilinearWeight s z y) t := by
    intro y hy
    have hypos : 0 < y := hy
    change ContinuousWithinAt (fun y => multilinearWeight s z y) t y
    apply ContinuousAt.continuousWithinAt
    unfold multilinearWeight
    apply tendsto_finsetSum s
    intro i hi
    have hden : y + z i ≠ 0 := (add_pos hypos (hz i hi)).ne'
    exact ((continuousAt_const.div
      (continuousAt_id.add continuousAt_const) hden).mul continuousAt_const)
  have hgcont : ContinuousOn
      (fun y => (2 ^ (s.card - 1) * ∏ i ∈ s, z i) *
        ((2 / Real.pi) *
          (∫ k in Set.Ioi (0 : ℝ), kernelProduct s z y k))) t := by
    intro y hy
    have hI := kernelProduct_integral_continuousAt s z hz hs y hy
    exact ((continuousAt_const.mul (continuousAt_const.mul hI)).continuousWithinAt)
  have heq : Set.EqOn
      (fun y => multilinearWeight s z y)
      (fun y => (2 ^ (s.card - 1) * ∏ i ∈ s, z i) *
        ((2 / Real.pi) *
          (∫ k in Set.Ioi (0 : ℝ), kernelProduct s z y k)))
      (t ∩ d) := by
    intro y hy
    have hxn : ∀ i ∈ s, y ≠ z i := by
      intro i hi h
      exact hy.2 (Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨i, hi, h.symm⟩))
    have h := multilinearWeight_eq_extended_integral s z y hs hy.1 hz hinj hxn
    simpa only [extendedNodes_kernel_prod, kernelProduct] using h
  have hcl : t ⊆ closure (t ∩ d) := by
    intro y hy
    exact isOpen_Ioi.inter_closure ⟨hy, hdense y⟩
  exact heq.of_subset_closure hfcont hgcont (inter_subset_left) hcl hx

/-- The actual distinct-rate squarefree r coefficient has the positive
kernel formula at every positive frequency, including every selected
rate node. -/
theorem physicalFormalR_squarefree_eq_kernel_all_x
    [Fintype T] (s : Finset T) (z : T → ℝ)
    (hz : ∀ t, 0 < z t) (hinj : Set.InjOn z s)
    (hs : s.Nonempty) (x : ℝ) (hx : 0 < x) :
    MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x) =
      (Nat.factorial s.card : ℝ) *
        ((2 ^ (s.card - 1) * ∏ i ∈ s, z i) *
          ((2 / Real.pi) *
            (∫ k in Set.Ioi (0 : ℝ), kernelProduct s z x k))) := by
  have hplus : ∀ t ∈ s, x + z t ≠ 0 := by
    intro t _
    exact (add_pos hx (hz t)).ne'
  rw [physicalFormalR_squarefree_eq_weight_all s z hz hinj x hplus]
  rw [multilinearWeight_eq_kernel_integral_all_x s z hs
    (fun i _ => hz i) hinj x hx]

omit [DecidableEq T] in
/-- The kernel integral itself is strictly positive at all positive
frequencies and positive rates, without any rate-distinctness
assumption. -/
theorem kernelProduct_integral_pos
    (s : Finset T) (z : T → ℝ)
    (hz : ∀ i ∈ s, 0 < z i)
    (hs : s.Nonempty) (x : ℝ) (hx : 0 < x) :
    0 < ∫ k in Set.Ioi (0 : ℝ), kernelProduct s z x k := by
  classical
  let f : ℝ → ℝ := kernelProduct s z x
  obtain ⟨i₀, hi₀⟩ := hs
  have hf_nonneg : 0 ≤ f := by
    intro k
    exact (kernelProduct_le_cauchy_majorant s z hz i₀ hi₀ x hx k).1
  have hf_cont : Continuous f := by
    dsimp [f, kernelProduct]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro k
      have hP : 0 < ∏ i ∈ s, (k ^ 2 + z i ^ 2) := by
        apply Finset.prod_pos
        intro i hi
        exact add_pos_of_nonneg_of_pos (sq_nonneg k) (sq_pos_of_pos (hz i hi))
      exact (mul_pos
        (add_pos_of_nonneg_of_pos (sq_nonneg k) (sq_pos_of_pos hx)) hP).ne'
  have hf_int : IntegrableOn f (Set.Ioi 0) :=
    kernelProduct_integrableOn_Ioi s z hz ⟨i₀, hi₀⟩ x hx
  have hf_one : f 1 ≠ 0 := by
    dsimp [f, kernelProduct]
    have hP : 0 < ∏ i ∈ s, ((1 : ℝ) ^ 2 + z i ^ 2) := by
      apply Finset.prod_pos
      intro i hi
      exact add_pos_of_nonneg_of_pos (sq_nonneg (1 : ℝ)) (sq_pos_of_pos (hz i hi))
    exact ne_of_gt (div_pos (by norm_num)
      (mul_pos (add_pos_of_nonneg_of_pos (by norm_num) (sq_pos_of_pos hx)) hP))
  have hμ : 0 < volume (Function.support f ∩ Set.Ioi (0 : ℝ)) :=
    (hf_cont.isOpen_support.inter isOpen_Ioi).measure_pos volume
      ⟨1, hf_one, by norm_num⟩
  exact (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall hf_nonneg) hf_int).2 hμ

/-- Distinct selected rates give strictly positive actual squarefree
r coefficients even when the evaluation frequency equals a selected
rate. -/
theorem physicalFormalR_squarefree_coeff_pos_all_x
    [Fintype T] (s : Finset T) (z : T → ℝ)
    (hz : ∀ t, 0 < z t) (hinj : Set.InjOn z s)
    (hs : s.Nonempty) (x : ℝ) (hx : 0 < x) :
    0 < MvPowerSeries.coeff (squarefreeMonomial s) (physicalFormalR z x) := by
  rw [physicalFormalR_squarefree_eq_kernel_all_x s z hz hinj hs x hx]
  have hprod : 0 < ∏ i ∈ s, z i :=
    Finset.prod_pos (fun i _ => hz i)
  have hint := kernelProduct_integral_pos s z (fun i _ => hz i) hs x hx
  have hfac : (0 : ℝ) < Nat.factorial s.card := by
    exact_mod_cast Nat.factorial_pos s.card
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

/-- At a positive-rate node, the independently recursive r series
has a strictly positive coefficient for every nonempty squarefree
set of pairwise distinct selected rates. -/
theorem RSeries_squarefree_coeff_pos_at_node
    [Fintype T] (s : Finset T) (z : T → ℝ)
    (hz : ∀ t, 0 < z t) (hinj : Set.InjOn z s)
    (hs : s.Nonempty) (t : T) :
    0 < MvPowerSeries.coeff (squarefreeMonomial s)
      (FMSA.Convergence.PureFluidRFormalSolution.RSeries z t) := by
  rw [← physicalFormalR_at_node z t]
  exact physicalFormalR_squarefree_coeff_pos_all_x s z hz hinj hs
    (z t) (hz t)

end FMSA.Convergence.PureFluidRKernelContinuity

/-- info: 'FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_le_cauchy_majorant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_le_cauchy_majorant
/-- info: 'FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_integrableOn_Ioi' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_integrableOn_Ioi
/-- info: 'FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_integral_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_integral_continuousAt
/-- info: 'FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_le_rate_box_majorant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_le_rate_box_majorant
/-- info: 'FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_integral_continuousAt_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_integral_continuousAt_rate
/-- info: 'FMSA.Convergence.PureFluidRKernelContinuity.multilinearWeight_eq_kernel_integral_all_x' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelContinuity.multilinearWeight_eq_kernel_integral_all_x
/-- info: 'FMSA.Convergence.PureFluidRKernelContinuity.physicalFormalR_squarefree_eq_kernel_all_x' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelContinuity.physicalFormalR_squarefree_eq_kernel_all_x
/-- info: 'FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_integral_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelContinuity.kernelProduct_integral_pos
/-- info: 'FMSA.Convergence.PureFluidRKernelContinuity.physicalFormalR_squarefree_coeff_pos_all_x' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelContinuity.physicalFormalR_squarefree_coeff_pos_all_x
/-- info: 'FMSA.Convergence.PureFluidRKernelContinuity.RSeries_squarefree_coeff_pos_at_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRKernelContinuity.RSeries_squarefree_coeff_pos_at_node
