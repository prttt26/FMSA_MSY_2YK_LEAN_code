import FMSAPaper.FiniteBasisJets
import Mathlib

/-! The paper's fixed polynomial/exponential space, with a dimension upper
bound valid without any distinct-rate assumption. -/
noncomputable section
open Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Paper.SpatialDictionary

variable {T : Type*} [Fintype T]
abbrev Index (T : Type*) := Fin 5 ⊕ (T ⊕ T)

def dictionary (z : T → ℝ) : Index T → ℝ → ℝ
  | .inl k, r => r ^ (k : ℕ)
  | .inr (.inl u), r => Real.exp (-z u * r)
  | .inr (.inr u), r => Real.exp (z u * r)

def space (z : T → ℝ) (s : Set ℝ) : Submodule ℝ (s → ℝ) :=
  Submodule.span ℝ (Set.range (fun b : Index T => fun r : s => dictionary z b r))

def HasForm (z : T → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  (fun r : s => f r) ∈ space z s

theorem space_finiteDimensional (z : T → ℝ) (s : Set ℝ) : FiniteDimensional ℝ (space z s) :=
  Module.Finite.span_of_finite ℝ (Set.finite_range _)

theorem space_finrank_le (z : T → ℝ) (s : Set ℝ) :
    Module.finrank ℝ (space z s) <= 5 + 2 * Fintype.card T := by
  classical
  unfold space
  calc
    _ <= (Set.range (fun b : Index T => fun r : s => dictionary z b r)).toFinset.card :=
      finrank_span_le_card _
    _ <= Fintype.card (Index T) := by
      rw [Set.toFinset_card]
      exact Fintype.card_range_le _
    _ = 5 + 2 * Fintype.card T := by simp [Index]; omega

omit [Fintype T] in
theorem dictionary_hasForm (z : T → ℝ) (s : Set ℝ) (b : Index T) :
    HasForm z s (dictionary z b) := Submodule.subset_span ⟨b, rfl⟩

omit [Fintype T] in
theorem HasForm.add {z : T → ℝ} {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : HasForm z s f) (hg : HasForm z s g) : HasForm z s (fun r => f r + g r) :=
  (space z s).add_mem hf hg

omit [Fintype T] in
theorem HasForm.const_mul {z : T → ℝ} {s : Set ℝ} {f : ℝ → ℝ}
    (hf : HasForm z s f) (c : ℝ) : HasForm z s (fun r => c * f r) :=
  (space z s).smul_mem c hf

omit [Fintype T] in
theorem HasForm.congr {z : T → ℝ} {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : HasForm z s f) (h : Set.EqOn f g s) : HasForm z s g := by
  have he : (fun r : s => f r) = (fun r : s => g r) := funext fun r => h r.property
  unfold HasForm at *
  rwa [← he]

omit [Fintype T] in
theorem finite_sum_hasForm {I : Type*} [Fintype I] (z : T → ℝ) (s : Set ℝ)
    (f : I → ℝ → ℝ) (hf : ∀ i, HasForm z s (f i)) :
    HasForm z s (fun r => ∑ i, f i r) := by
  have h := (space z s).sum_mem (fun i (_ : i ∈ Finset.univ) => hf i)
  have he : (∑ i, fun r : s => f i r) = (fun r : s => ∑ i, f i r) := by
    funext r
    simp only [Finset.sum_apply]
  rw [he] at h
  exact h

theorem linear_hasForm (z : T → ℝ) (s : Set ℝ) (c : Index T → ℝ) :
    HasForm z s (fun r => FiniteBasis.linear c (fun b => dictionary z b r)) := by
  exact finite_sum_hasForm z s _ (fun b => (dictionary_hasForm z s b).const_mul (c b))

theorem HasForm.contDiffOn {z : T → ℝ} {s : Set ℝ} {f : ℝ → ℝ}
    (hf : HasForm z s f) : ContDiffOn ℝ ∞ f s := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf
  have hb (b : Index T) : ContDiff ℝ ∞ (dictionary z b) := by
    rcases b with k | (u | u)
    · change ContDiff ℝ ∞ (fun r : ℝ => r ^ (k : ℕ))
      fun_prop
    · change ContDiff ℝ ∞ (fun r : ℝ => Real.exp (-z u * r))
      fun_prop
    · change ContDiff ℝ ∞ (fun r : ℝ => Real.exp (z u * r))
      fun_prop
  have hg : ContDiff ℝ ∞ (fun r => FiniteBasis.linear c (fun b => dictionary z b r)) :=
    ContDiff.sum (fun b _ => contDiff_const.mul (hb b))
  apply hg.contDiffOn.congr
  intro r hr
  have h := congrFun hc (⟨r, hr⟩ : s)
  simpa only [FiniteBasis.linear, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm

/-- Local finite coefficient representations suffice to retain the space at
every coupling order; convergence of the full series is not needed. -/
theorem jet_hasForm_of_representation (z : T → ℝ) (s : Set ℝ)
    (f : ℝ → ℝ → ℝ) (c : ℝ → Index T → ℝ) (n : ℕ)
    (hc : ∀ b, ContDiffAt ℝ n (fun t => c t b) 0)
    (heq : ∀ r ∈ s, (fun t => f t r) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => FiniteBasis.linear (c t) (fun b => dictionary z b r))) :
    HasForm z s (fun r => ExactMSA.BSource.jet (fun t => f t r) n) := by
  apply (linear_hasForm z s (fun b => ExactMSA.BSource.jet (fun t => c t b) n)).congr
  intro r hr
  have h := congrArg (fun a : ℝ => a / (n.factorial : ℝ)) ((heq r hr).iteratedDeriv_eq n)
  change ExactMSA.BSource.jet (fun t => f t r) n =
    ExactMSA.BSource.jet (fun t => FiniteBasis.linear (c t) (fun b => dictionary z b r)) n at h
  rw [FiniteBasis.jet_linear c _ n hc] at h
  exact h.symm

end FMSA.Paper.SpatialDictionary

/-- info: 'FMSA.Paper.SpatialDictionary.space_finiteDimensional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialDictionary.space_finiteDimensional

/-- info: 'FMSA.Paper.SpatialDictionary.space_finrank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialDictionary.space_finrank_le

/-- info: 'FMSA.Paper.SpatialDictionary.dictionary_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialDictionary.dictionary_hasForm

/-- info: 'FMSA.Paper.SpatialDictionary.HasForm.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialDictionary.HasForm.add

/-- info: 'FMSA.Paper.SpatialDictionary.HasForm.const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialDictionary.HasForm.const_mul

/-- info: 'FMSA.Paper.SpatialDictionary.HasForm.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialDictionary.HasForm.congr

/-- info: 'FMSA.Paper.SpatialDictionary.finite_sum_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialDictionary.finite_sum_hasForm

/-- info: 'FMSA.Paper.SpatialDictionary.linear_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialDictionary.linear_hasForm

/-- info: 'FMSA.Paper.SpatialDictionary.HasForm.contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialDictionary.HasForm.contDiffOn

/-- info: 'FMSA.Paper.SpatialDictionary.jet_hasForm_of_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialDictionary.jet_hasForm_of_representation
