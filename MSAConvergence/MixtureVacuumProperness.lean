import MSAConvergence.MixtureCanonicalProperness

/-! Full-vacuum finite-mixture properness from the original explicit affine
root. This is separate from a partially zero-density retained tracer face. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.MixtureVacuumProperness
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture
variable {N : ℕ} {T : Type*} [Fintype T]

/-- All ORIGINAL vacuum roots are uniformly bounded over bounded strengths,
for arbitrary finite species count and nonzero signed/repeated tail rates. -/
theorem vacuum_roots_uniformly_bounded (z : T → ℝ) (hz : ∀ u, z u ≠ 0)
    (σ : Fin N → ℝ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : TailMatrix T N, ∀ p : TailMatrix T N × TailMatrix T N,
      ‖K‖ ≤ B → IsRoot z 0 σ K p.1 p.2 → ‖p‖ ≤ C := by
  let V : TailMatrix T N → TailMatrix T N × TailMatrix T N := fun K =>
    (nonlinearZeroDensityDt z K,nonlinearZeroDensityG z σ K)
  have hV : Continuous V := by
    dsimp only [V]
    unfold nonlinearZeroDensityDt nonlinearZeroDensityG
    fun_prop
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : TailMatrix T N) (max B 0)).exists_bound_of_continuousOn hV.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro K p hK hr
  obtain ⟨hD,hG⟩ := (nonlinearRoot_zero_density_iff z σ K p.1 p.2 hz).mp hr
  have hp : p=V K := Prod.ext (funext (fun u => funext (fun i => funext (hD u i))))
    (funext (fun u => funext (fun i => funext (hG u i))))
  rw [hp]
  exact (hC K (by simpa only [Metric.mem_closedBall,dist_zero_right] using hK.trans (le_max_left B 0))).trans
    (le_max_left _ _)

/-- No finite ORIGINAL vacuum root prefix can escape. Canonicity, reciprocity,
continuity and a supplied bound are not required for this affine special case. -/
theorem no_finite_vacuum_amplitude_escape (z : T → ℝ) (hz : ∀ u, z u ≠ 0)
    (σ : Fin N → ℝ) (K : TailMatrix T N) (p : ℝ → TailMatrix T N × TailMatrix T N)
    (b : ℝ) (hb : 0 < b)
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z 0 σ (t • K) (p t).1 (p t).2) :
    ¬∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖p t‖ := by
  obtain ⟨C,_hC,hbound⟩ := vacuum_roots_uniformly_bounded z hz σ (b*‖K‖)
  intro hescape
  obtain ⟨t,ht,_hc,hlarge⟩ := hescape C 0 hb
  apply (not_lt_of_ge (hbound (t • K) (p t) _ (hroot t ht))) hlarge
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  exact mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)

end FMSA.Convergence.MixtureVacuumProperness
/-- info: 'FMSA.Convergence.MixtureVacuumProperness.vacuum_roots_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureVacuumProperness.vacuum_roots_uniformly_bounded
/-- info: 'FMSA.Convergence.MixtureVacuumProperness.no_finite_vacuum_amplitude_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureVacuumProperness.no_finite_vacuum_amplitude_escape
