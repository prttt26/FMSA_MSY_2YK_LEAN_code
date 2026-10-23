import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairMoments
import LeanCode.Analysis.IntervalIntegralSwap

/-! Actual half-line HS-pair renewal transforms and the compact source
triangle identity. No finite-core seed identity or radial OZ is assumed here. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

theorem hsPair_compact_weighted_integrableOn (f : ℝ → ℝ) (hf : Continuous f)
    (x : ℝ) (hfzero : ∀ u, x ≤ u → f u=0) (s : ℂ) :
    IntegrableOn (fun u => (f u : ℂ)*Complex.exp (-s*u)) (Ioi 0) := by
  have hc : Continuous (fun u => (f u : ℂ)*Complex.exp (-s*u)) := by fun_prop
  have hi := (hc.integrableOn_Icc (μ := volume) (a := 0) (b := x)).integrable_indicator measurableSet_Icc
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro u hu
  by_cases hb : u ≤ x
  · exact indicator_of_mem (show u ∈ Icc (0 : ℝ) x from ⟨hu.le, hb⟩) _
  · rw [indicator_of_notMem (show u ∉ Icc (0 : ℝ) x from fun h => hb h.2)]
    dsimp only
    rw [hfzero u (not_le.mp hb).le]
    simp

theorem hsPair_tail_source_continuous (q : ℝ → ℝ) (hq : Continuous q) (x R : ℝ) :
    Continuous (fun u => ∫ v in min u x..x, q v*(v-u-R)) := by
  have hi : Continuous (Function.uncurry (fun u v : ℝ => q v*(v-u-R))) := by fun_prop
  have hh : Continuous (fun u => ∫ v in x..min u x, q v*(v-u-R)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hi
      (continuous_id.min continuous_const)
  exact hh.neg.congr (fun u => by rw [intervalIntegral.integral_symm, neg_neg])

theorem hsPair_compact_causal_laplace (f : ℝ → ℝ) (hf : Continuous f)
    (x : ℝ) (hx : 0 ≤ x) (hfzero : ∀ u, x ≤ u → f u=0) (s : ℂ) :
    FMSA.causalComplexLaplace f s =
      ∫ u in (0 : ℝ)..x, (f u : ℂ)*Complex.exp (-s*u) := by
  unfold FMSA.causalComplexLaplace
  have he : (∫ u in Ioi (0 : ℝ), (f u : ℂ)*Complex.exp (-s*u)) =
      ∫ u in Ioi (0 : ℝ), (Icc (0 : ℝ) x).indicator
        (fun u => (f u : ℂ)*Complex.exp (-s*u)) u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    by_cases hb : u ≤ x
    · rw [indicator_of_mem (show u ∈ Icc (0 : ℝ) x from ⟨hu.le, hb⟩)]
    · rw [indicator_of_notMem (show u ∉ Icc (0 : ℝ) x from fun h => hb h.2)]
      dsimp only
      rw [hfzero u (not_le.mp hb).le]
      simp
  rw [he, setIntegral_indicator measurableSet_Icc]
  have hset : Ioi (0 : ℝ) ∩ Icc 0 x=Ioc 0 x := by
    ext u
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨hu, _, hux⟩; exact ⟨hu, hux⟩
    · rintro ⟨hu, hux⟩; exact ⟨hu, hu.le, hux⟩
  rw [hset, intervalIntegral.integral_of_le hx]

theorem rdfHSCoreSource_entry_integrableOn (ρ σ : Fin N → ℝ) (i j : Fin N) :
    IntegrableOn (fun u => rdfHSCoreSource ρ σ u i j) (Ioi 0) := by
  have hi := (((rdfHSCoreSource_continuous ρ σ).matrix_elem i j).integrableOn_Icc
    (μ := volume) (a := 0) (b := rdfHSSupportCeiling σ)).integrable_indicator measurableSet_Icc
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro u hu
  by_cases hb : u ≤ rdfHSSupportCeiling σ
  · exact indicator_of_mem (show u ∈ Icc 0 (rdfHSSupportCeiling σ) from ⟨hu.le, hb⟩) _
  · rw [indicator_of_notMem (show u ∉ Icc 0 (rdfHSSupportCeiling σ) from fun h => hb h.2)]
    dsimp only
    rw [rdfHSCoreSource_zero_above ρ σ u (not_le.mp hb).le]
    rfl

theorem rdfHSPairExterior_laplace (ρ σ : Fin N → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1)
    (s : ℂ) (hs : 0 ≤ s.re) :
    (rdfRecenteredFactor ρ σ s).transpose*rdfMatrixLaplace (rdfHSPairExterior ρ σ) s =
      rdfMatrixLaplace (rdfHSCoreSource ρ σ) s := by
  have he := matrixCausalRenewal_laplace
    (fun t => (rdfCausalKernel ρ σ t).transpose) (rdfHSCoreSource ρ σ) (rdfHSPairExterior ρ σ)
    (rdfCausalKernelTranspose_continuous ρ σ) (rdfHSCoreSource_continuous ρ σ)
    (rdfHSPairExterior_continuous ρ σ)
    (fun i j => rdfCausalKernel_entry_integrableOn ρ σ j i)
    (rdfHSCoreSource_entry_integrableOn ρ σ)
    (rdfHSPairExterior_integrable_of_weighted_budget ρ σ δ hδ hb)
    (rdfHSPairExterior_renewal ρ σ) s hs
  simpa only [rdfRecenteredFactor, Matrix.transpose_sub, Matrix.transpose_one,
    rdfMatrixLaplace_transpose] using he

theorem hsPair_affine_exp_integral (v R : ℝ) (s : ℂ) (hs : s ≠ 0) :
    (∫ u in (0 : ℝ)..v, ((v-u-R : ℝ) : ℂ)*Complex.exp (-s*u)) =
      ((v-R : ℝ) : ℂ)/s-1/s^2+((R : ℂ)/s+1/s^2)*Complex.exp (-s*v) := by
  let F := fun u : ℝ => (-((v-u-R : ℝ) : ℂ)/s+1/s^2)*Complex.exp (-s*u)
  have hd : ∀ u ∈ uIcc (0 : ℝ) v, HasDerivAt F
      (((v-u-R : ℝ) : ℂ)*Complex.exp (-s*u)) u := by
    intro u _
    have hid : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have hlin : HasDerivAt (fun u : ℝ => ((v-u-R : ℝ) : ℂ)) (-1) u := by
      convert! (hid.const_sub (v : ℂ)).sub_const (R : ℂ) using 1
      funext u
      push_cast
      rfl
    have ha : HasDerivAt (fun u : ℝ => -((v-u-R : ℝ) : ℂ)/s+1/s^2) (1/s) u := by
      convert! (hlin.neg.div_const s).add_const (1/s^2) using 1 <;>
        simp only [Pi.neg_apply, neg_neg]
    have he : HasDerivAt (fun u : ℝ => Complex.exp (-s*u))
        (-s*Complex.exp (-s*u)) u := by
      simpa only [mul_one, mul_comm] using (hid.const_mul (-s)).cexp
    exact (ha.mul he).congr_deriv (by push_cast; field_simp [hs]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) 0 v)]
  dsimp only [F]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  push_cast
  ring

theorem hsPair_source_triangle (q : ℝ → ℝ) (hq : Continuous q) (x R : ℝ)
    (hx : 0 ≤ x) (s : ℂ) :
    (∫ u in (0 : ℝ)..x, ((∫ v in u..x, q v*(v-u-R) : ℝ) : ℂ)*Complex.exp (-s*u)) =
      ∫ v in (0 : ℝ)..x, (q v : ℂ)*∫ u in (0 : ℝ)..v,
        ((v-u-R : ℝ) : ℂ)*Complex.exp (-s*u) := by
  let f := fun u v : ℝ => (q v : ℂ)*((v-u-R : ℝ) : ℂ)*Complex.exp (-s*u)
  have hc : Continuous (Function.uncurry f) := by dsimp only [f]; fun_prop
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have hi : Integrable (Function.uncurry fun u v => (Ioi u).indicator (f u) v)
      ((volume.restrict (Ioc 0 x)).prod (volume.restrict (Ioc 0 x))) := by
    have hbase : IntegrableOn (Function.uncurry f) ((Icc (0 : ℝ) x) ×ˢ Icc 0 x)
        (volume.prod volume) := hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hind := hbase.indicator hm
    have hres : IntegrableOn ({p : ℝ × ℝ | p.1 < p.2}.indicator (Function.uncurry f))
        ((Ioc (0 : ℝ) x) ×ˢ Ioc 0 x) (volume.prod volume) :=
      hind.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    rw [Measure.prod_restrict] at ⊢
    apply hres.congr
    filter_upwards [] with p
    by_cases hp : p.1 < p.2 <;> simp [Function.uncurry, hp]
  calc
    _ = ∫ u in (0 : ℝ)..x, ∫ v in u..x, f u v := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro v _
      dsimp only [f]
      push_cast
      ring
    _ = ∫ v in (0 : ℝ)..x, ∫ u in (0 : ℝ)..v, f u v :=
      FMSA.intervalIntegral_triangle_swap_gen hx f hi
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro v _
      dsimp only
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only [f]
      ring

theorem hsPair_source_finite_laplace (q : ℝ → ℝ) (hq : Continuous q) (x R : ℝ)
    (hx : 0 ≤ x) (s : ℂ) (hs : s ≠ 0) :
    (∫ u in (0 : ℝ)..x, ((∫ v in u..x, q v*(v-u-R) : ℝ) : ℂ)*Complex.exp (-s*u)) =
      (((∫ v in (0 : ℝ)..x, v*q v : ℝ) : ℂ)-
        (R : ℂ)*((∫ v in (0 : ℝ)..x, q v : ℝ) : ℂ))/s-
      ((∫ v in (0 : ℝ)..x, q v : ℝ) : ℂ)/s^2+
        ((R : ℂ)/s+1/s^2)*(∫ v in (0 : ℝ)..x, (q v : ℂ)*Complex.exp (-s*v)) := by
  rw [hsPair_source_triangle q hq x R hx s]
  simp_rw [hsPair_affine_exp_integral _ R s hs]
  have he : (∫ v in (0 : ℝ)..x, (q v : ℂ)*
      (((v-R : ℝ) : ℂ)/s-1/s^2+((R : ℂ)/s+1/s^2)*Complex.exp (-s*v))) =
      ∫ v in (0 : ℝ)..x,
        (((v*q v : ℝ) : ℂ)-(R : ℂ)*(q v : ℂ))/s-
          (q v : ℂ)/s^2+((R : ℂ)/s+1/s^2)*((q v : ℂ)*Complex.exp (-s*v)) := by
    apply intervalIntegral.integral_congr
    intro v _
    push_cast
    ring
  rw [he, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 x)
    (Continuous.intervalIntegrable (by fun_prop) 0 x),
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 x)
      (Continuous.intervalIntegrable (by fun_prop) 0 x)]
  simp only [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) 0 x)
    (Continuous.intervalIntegrable (by fun_prop) 0 x),
    intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_ofReal]

theorem hsPair_tail_source_laplace (q : ℝ → ℝ) (hq : Continuous q) (x R : ℝ)
    (hx : 0 ≤ x) (s : ℂ) (hs : s ≠ 0) :
    FMSA.causalComplexLaplace (fun u => ∫ v in min u x..x, q v*(v-u-R)) s =
      (((∫ v in (0 : ℝ)..x, v*q v : ℝ) : ℂ)-
        (R : ℂ)*((∫ v in (0 : ℝ)..x, q v : ℝ) : ℂ))/s-
      ((∫ v in (0 : ℝ)..x, q v : ℝ) : ℂ)/s^2+
        ((R : ℂ)/s+1/s^2)*(∫ v in (0 : ℝ)..x, (q v : ℂ)*Complex.exp (-s*v)) := by
  have hc := hsPair_tail_source_continuous q hq x R
  rw [hsPair_compact_causal_laplace _ hc x hx
    (fun u hu => by rw [min_eq_right hu]; exact intervalIntegral.integral_same) s]
  have he : (∫ u in (0 : ℝ)..x, ((∫ v in min u x..x, q v*(v-u-R) : ℝ) : ℂ)*
      Complex.exp (-s*u)) =
      ∫ u in (0 : ℝ)..x, ((∫ v in u..x, q v*(v-u-R) : ℝ) : ℂ)*Complex.exp (-s*u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    dsimp only
    rw [min_eq_left hu.2]
  rw [he]
  exact hsPair_source_finite_laplace q hq x R hx s hs

theorem rdfRecenteredHSQ_laplace_closed (ρ σ : Fin N → ℝ) (i j : Fin N)
    (hσ : 0 ≤ σ i) (s : ℂ) (hs : s ≠ 0) :
    FMSA.causalComplexLaplace (rdfRecenteredHSQ ρ σ i j) s =
      hsPairSymbolP (σ i) (Complex.exp (-s*σ i)) s*(Qppphys ρ σ j j : ℂ)+
        hsPairSymbolT (σ i) (Complex.exp (-s*σ i)) s*((Real.pi*σ j/vacMix ρ σ : ℝ) : ℂ) := by
  rw [hsPair_compact_causal_laplace _ (rdfRecenteredHSQ_continuous ρ σ i j) (σ i) hσ
    (fun u hu => by simp [rdfRecenteredHSQ, min_eq_right hu]) s]
  have he : (∫ u in (0 : ℝ)..σ i,
      (rdfRecenteredHSQ ρ σ i j u : ℂ)*Complex.exp (-s*u)) =
      ∫ u in (0 : ℝ)..((0 : ℝ)+σ i), Complex.exp (-(s*u))*
        ((Q0phys ρ σ i j : ℂ)*((u : ℂ)-((0 : ℝ)+σ i : ℝ))+
          (Qppphys ρ σ j j : ℂ)*((u : ℂ)-((0 : ℝ)+σ i : ℝ))^2/2) := by
    simp only [zero_add]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hσ] at hu
    simp only [rdfRecenteredHSQ, min_eq_left hu.2]
    push_cast
    ring
  rw [he, FMSA.MixtureBaxter.laplace_baxter_quad_c s 0 (σ i)
    (Q0phys ρ σ i j) (Qppphys ρ σ j j) hs, hsPair_Q0_decomposition]
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  unfold hsPairSymbolP hsPairSymbolT
  push_cast
  simp only [neg_mul]
  field_simp [hs]
  ring

theorem rdfHSCoreSource_laplace_moments (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (s : ℂ) (hs : s ≠ 0) (i j : Fin N) :
    rdfMatrixLaplace (rdfHSCoreSource ρ σ) s i j = ∑ m, (ρ m : ℂ)*
      (((((∫ v in (0 : ℝ)..σ m, v*rdfRecenteredHSQ ρ σ m i v : ℝ) : ℂ)-
        (edgeHi σ m j : ℂ)*((∫ v in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m i v : ℝ) : ℂ))/s-
        ((∫ v in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m i v : ℝ) : ℂ)/s^2)+
        ((edgeHi σ m j : ℂ)/s+1/s^2)*
          FMSA.causalComplexLaplace (rdfRecenteredHSQ ρ σ m i) s) := by
  let f := fun m u => ∫ v in min u (σ m)..σ m,
    rdfRecenteredHSQ ρ σ m i v*(v-u-edgeHi σ m j)
  have hi (m : Fin N) : IntegrableOn (fun u => (ρ m : ℂ)*((f m u : ℂ)*Complex.exp (-s*u)))
      (Ioi 0) :=
    (hsPair_compact_weighted_integrableOn (f m)
      (hsPair_tail_source_continuous _ (rdfRecenteredHSQ_continuous ρ σ m i) _ _) (σ m)
      (fun u hu => by dsimp only [f]; rw [min_eq_right hu]; exact intervalIntegral.integral_same) s).const_mul _
  change (∫ u in Ioi (0 : ℝ), (rdfHSCoreSource ρ σ u i j : ℂ)*Complex.exp (-s*u)) = _
  have he : (∫ u in Ioi (0 : ℝ), (rdfHSCoreSource ρ σ u i j : ℂ)*Complex.exp (-s*u)) =
      ∫ u in Ioi (0 : ℝ), ∑ m, (ρ m : ℂ)*((f m u : ℂ)*Complex.exp (-s*u)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [rdfHSCoreSource_eq_tail_windows]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    dsimp only [f]
    ring
  rw [he, integral_finsetSum _ (fun m _ => hi m)]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_const_mul]
  change (ρ m : ℂ)*FMSA.causalComplexLaplace (f m) s = _
  rw [hsPair_tail_source_laplace _ (rdfRecenteredHSQ_continuous ρ σ m i)
    (σ m) (edgeHi σ m j) (hσ m) s hs,
    hsPair_compact_causal_laplace _ (rdfRecenteredHSQ_continuous ρ σ m i)
      (σ m) (hσ m) (fun u hu => by simp [rdfRecenteredHSQ, min_eq_right hu]) s]

end FMSA.ExactMSA.MultiTailMixture
