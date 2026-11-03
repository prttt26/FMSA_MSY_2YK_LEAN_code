import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Exact finite left-endpoint alternatives in proper normed spaces. Failure
of norm escape constructs a finite approaching cluster; full cluster limits
therefore leave only a finite limit or genuine norm divergence. -/

noncomputable section
open Set Filter Topology
namespace FMSA.Convergence.EndpointEscape
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- Without any continuity, failure of norm escape along a finite positive
left endpoint produces an approaching sequence with a finite cluster. -/
theorem norm_escape_or_finite_cluster (p : ℝ → E) (b : ℝ) (hb : 0<b) :
    Tendsto (fun t => ‖p t‖) (𝓝[<] b) atTop ∨
      ∃ a : E, ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ico 0 b) ∧
        Tendsto u atTop (𝓝 b) ∧ Tendsto (fun n => p (u n)) atTop (𝓝 a) := by
  classical
  by_cases hescape : Tendsto (fun t => ‖p t‖) (𝓝[<] b) atTop
  · exact Or.inl hescape
  right
  have hfreq : ∃ B : ℝ, ∃ᶠ t in 𝓝[<] b, ‖p t‖<B := by
    rw [tendsto_atTop] at hescape
    push Not at hescape
    exact hescape
  obtain ⟨B,hB⟩ := hfreq
  have hseq (n : ℕ) : ∃ t ∈ Ico 0 b, b-1/(n+1 : ℝ)<t ∧ ‖p t‖≤B := by
    have hlo : max 0 (b-1/(n+1 : ℝ))<b := max_lt hb (sub_lt_self b (by positivity))
    have hevent : ∀ᶠ t : ℝ in 𝓝[<] b, max 0 (b-1/(n+1 : ℝ))<t :=
      (show ∀ᶠ t : ℝ in 𝓝 b, max 0 (b-1/(n+1 : ℝ))<t from Ioi_mem_nhds hlo).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨t,htB,htlo,hthi⟩ := (hB.and_eventually (hevent.and self_mem_nhdsWithin)).exists
    exact ⟨t,⟨(le_max_left _ _).trans htlo.le,hthi⟩,(le_max_right _ _).trans_lt htlo,htB.le⟩
  choose u hu hlo hbound using hseq
  have hlow : Tendsto (fun n : ℕ => b-1/(n+1 : ℝ)) atTop (𝓝 b) := by
    simpa only [sub_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b)).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/(n+1 : ℝ)) atTop (𝓝 0))
  have ht : Tendsto u atTop (𝓝 b) := tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlow tendsto_const_nhds (fun n => (hlo n).le) (fun n => (hu n).2.le)
  obtain ⟨a,_,v,hv,hpv⟩ := (isCompact_closedBall (0 : E) B).tendsto_subseq
    (fun n => show p (u n) ∈ Metric.closedBall 0 B by simpa only [Metric.mem_closedBall,dist_zero_right] using hbound n)
  exact ⟨a,u ∘ v,fun n => hu (v n),ht.comp hv.tendsto_atTop,hpv⟩

/-- Once all finite approaching clusters are full limits, the only remaining
endpoint alternative is genuine norm divergence, not merely unboundedness. -/
theorem full_limit_or_norm_escape (p : ℝ → E) (b : ℝ) (hb : 0<b)
    (hcluster : ∀ (a : E) (u : ℕ → ℝ), (∀ n, u n ∈ Ico 0 b) →
      Tendsto u atTop (𝓝 b) → Tendsto (fun n => p (u n)) atTop (𝓝 a) →
      Tendsto p (𝓝[<] b) (𝓝 a)) :
    (∃ a : E, Tendsto p (𝓝[<] b) (𝓝 a)) ∨
      Tendsto (fun t => ‖p t‖) (𝓝[<] b) atTop := by
  rcases norm_escape_or_finite_cluster p b hb with he|⟨a,u,hu,ht,ha⟩
  · exact Or.inr he
  · exact Or.inl ⟨a,hcluster a u hu ht ha⟩

/-- info: 'FMSA.Convergence.EndpointEscape.norm_escape_or_finite_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EndpointEscape.norm_escape_or_finite_cluster

/-- info: 'FMSA.Convergence.EndpointEscape.full_limit_or_norm_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EndpointEscape.full_limit_or_norm_escape
end FMSA.Convergence.EndpointEscape
