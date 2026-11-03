import MSAConvergence.PureFluidCandidateResidueLimit

set_option linter.style.header false

/-! An even finite sum of simple poles at distinct negative positive
rates has zero residue at every pole. -/
noncomputable section
open Filter Topology Set
namespace FMSA.Convergence.PureFluidRSimplePoleUniqueness
open FMSA.Convergence.PureFluidCandidateResidueLimit
variable {T : Type*} [Fintype T]

def simplePoleSum (z a : T → ℝ) (x : ℝ) : ℝ :=
  ∑ t, a t / (x + z t)

theorem simplePoleSum_negative_reflection_continuousAt
    (z a : T → ℝ) (hz : ∀ t, 0 < z t) (t : T) :
    ContinuousAt (fun s => simplePoleSum z a (-s)) (-z t) := by
  classical
  have hterm (u : T) :
      ContinuousAt (fun s : ℝ => a u / (-s + z u)) (-z t) := by
    have hden : -(-z t) + z u ≠ 0 := by
      have hp := add_pos (hz t) (hz u)
      simpa only [neg_neg] using hp.ne'
    exact continuousAt_const.div (by fun_prop) hden
  change ContinuousAt (fun s : ℝ => ∑ u, a u / (-s + z u)) (-z t)
  exact tendsto_finsetSum Finset.univ (fun u _ => (hterm u).tendsto)

/-- Eventual evenness at one negative pole forces its coefficient to
vanish; this local form can be used when equality holds only off poles. -/
theorem simplePoleSum_coeff_zero_of_eventually_even
    (z a : T → ℝ) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z) (t : T)
    (heven : (fun s => simplePoleSum z a s) =ᶠ[𝓝[≠] (-z t)]
      (fun s => simplePoleSum z a (-s))) :
    a t = 0 := by
  have hres : Tendsto (fun s => (s + z t) * simplePoleSum z a s)
      (𝓝[≠] (-z t)) (𝓝 (a t)) := by
    have h := finite_simple_pole_tendsto z (fun u _ => a u)
      (fun _ => 0) t hzinj (by fun_prop) (fun _ => by fun_prop)
    simpa only [simplePoleSum, zero_add] using h
  have hzero : Tendsto (fun s : ℝ => s + z t)
      (𝓝[≠] (-z t)) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt (fun s : ℝ => s + z t) (-z t) := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hreg := simplePoleSum_negative_reflection_continuousAt z a hz t
  have hscaled : Tendsto
      (fun s => (s + z t) * simplePoleSum z a (-s))
      (𝓝[≠] (-z t)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using
      hzero.mul (hreg.tendsto.mono_left nhdsWithin_le_nhds)
  have heq : (fun s => (s + z t) * simplePoleSum z a s) =ᶠ[𝓝[≠] (-z t)]
      (fun s => (s + z t) * simplePoleSum z a (-s)) := by
    filter_upwards [heven] with s hs
    rw [hs]
  have hsame := tendsto_nhds_unique (hres.congr' heq) hscaled
  simpa using hsame

/-- Global evenness of a finite simple-pole sum with distinct positive
rates forces every residue coefficient to vanish. -/
theorem simplePoleSum_even_implies_zero
    (z a : T → ℝ) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (heven : ∀ s : ℝ, simplePoleSum z a s = simplePoleSum z a (-s)) :
    ∀ t, a t = 0 := by
  intro t
  exact simplePoleSum_coeff_zero_of_eventually_even z a hz hzinj t
    (Eventually.of_forall heven)

omit [Fintype T] in
/-- Local evenness for a finite subset is enough to kill its residue at
one selected negative pole. -/
theorem simplePoleSum_subset_coeff_zero_of_eventually_even
    (s : Finset T) (z a : T → ℝ)
    (hz : ∀ u ∈ s, 0 < z u) (hzinj : Set.InjOn z s)
    (t : T) (ht : t ∈ s)
    (heven : (fun x => ∑ u ∈ s, a u / (x + z u)) =ᶠ[𝓝[≠] (-z t)]
      (fun x => ∑ u ∈ s, a u / (-x + z u))) :
    a t = 0 := by
  classical
  let z' : {u // u ∈ s} → ℝ := fun u => z u
  let a' : {u // u ∈ s} → ℝ := fun u => a u
  have hz' : ∀ u, 0 < z' u := fun u => hz u u.property
  have hinj' : Function.Injective z' := by
    intro u v huv
    apply Subtype.ext
    exact hzinj u.property v.property huv
  have hsum (x : ℝ) : simplePoleSum z' a' x =
      ∑ u ∈ s, a u / (x + z u) := by
    change (∑ u : {u // u ∈ s}, a u / (x + z u)) = _
    simpa only [Finset.univ_eq_attach] using
      (Finset.sum_attach s (fun u => a u / (x + z u)))
  have heven' : (fun x => simplePoleSum z' a' x) =ᶠ[𝓝[≠] (-z t)]
      (fun x => simplePoleSum z' a' (-x)) := by
    filter_upwards [heven] with x hx
    simpa only [hsum] using hx
  exact simplePoleSum_coeff_zero_of_eventually_even
    z' a' hz' hinj' ⟨t, ht⟩ heven'

omit [Fintype T] in
/-- Only the rates actually used in the finite pole sum need be
distinct; unrelated tails may have coincident rates. -/
theorem simplePoleSum_subset_even_implies_zero
    (s : Finset T) (z a : T → ℝ)
    (hz : ∀ t ∈ s, 0 < z t) (hzinj : Set.InjOn z s)
    (heven : ∀ x : ℝ,
      (∑ t ∈ s, a t / (x + z t)) =
        ∑ t ∈ s, a t / (-x + z t)) :
    ∀ t ∈ s, a t = 0 := by
  intro t ht
  exact simplePoleSum_subset_coeff_zero_of_eventually_even
    s z a hz hzinj t ht (Eventually.of_forall heven)

omit [Fintype T] in
/-- The odd part uniquely determines all coefficients of a finite
simple-pole expansion at distinct positive rates. -/
theorem simplePoleSum_odd_injective_on
    (s : Finset T) (z a b : T → ℝ)
    (hz : ∀ t ∈ s, 0 < z t) (hzinj : Set.InjOn z s)
    (hodd : ∀ x : ℝ,
      (∑ t ∈ s, a t / (x + z t)) -
        (∑ t ∈ s, a t / (-x + z t)) =
      (∑ t ∈ s, b t / (x + z t)) -
        (∑ t ∈ s, b t / (-x + z t))) :
    ∀ t ∈ s, a t = b t := by
  let d : T → ℝ := fun t => a t - b t
  have hd (x : ℝ) : (∑ t ∈ s, d t / (x + z t)) =
      (∑ t ∈ s, a t / (x + z t)) -
        (∑ t ∈ s, b t / (x + z t)) := by
    simp only [d, sub_div, Finset.sum_sub_distrib]
  have heven (x : ℝ) :
      (∑ t ∈ s, d t / (x + z t)) =
        ∑ t ∈ s, d t / (-x + z t) := by
    rw [hd x, hd (-x)]
    linarith [hodd x]
  have hzero := simplePoleSum_subset_even_implies_zero s z d hz hzinj heven
  intro t ht
  exact sub_eq_zero.mp (hzero t ht)

/-- Near a selected negative rate, every pole denominator in the
selected distinct-rate family is eventually nonzero away from the
center, and every reflected denominator is nonzero nearby. -/
theorem eventually_subset_two_sided_pole_domain
    (s : Finset T) (z : T → ℝ)
    (hz : ∀ u ∈ s, 0 < z u) (hzinj : Set.InjOn z s)
    (t : T) (ht : t ∈ s) :
    ∀ᶠ x : ℝ in 𝓝[≠] (-z t),
      (∀ u ∈ s, x + z u ≠ 0) ∧
        (∀ u ∈ s, -x + z u ≠ 0) := by
  have hplus : ∀ᶠ x : ℝ in 𝓝[≠] (-z t),
      ∀ u ∈ s, x + z u ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro u
    by_cases hu : u ∈ s
    · by_cases hsame : z u = z t
      · have h_eq : u = t := hzinj hu ht hsame
        subst u
        filter_upwards [self_mem_nhdsWithin] with x hx
        intro _
        have hne : x ≠ -z t := by
          simpa only [mem_compl_iff, mem_singleton_iff] using hx
        intro hzero
        apply hne
        linarith
      · have hpoint : -z t + z u ≠ 0 := by
          intro hzero
          apply hsame
          linarith
        have hc : ContinuousAt (fun x : ℝ => x + z u) (-z t) := by fun_prop
        filter_upwards [(hc.eventually_ne hpoint).filter_mono nhdsWithin_le_nhds]
          with x hx
        exact fun _ => hx
    · exact Eventually.of_forall (fun x h => False.elim (hu h))
  have hminus : ∀ᶠ x : ℝ in 𝓝[≠] (-z t),
      ∀ u ∈ s, -x + z u ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro u
    by_cases hu : u ∈ s
    · have hpoint : -(-z t) + z u ≠ 0 := by
        simpa only [neg_neg] using (add_pos (hz t ht) (hz u hu)).ne'
      have hc : ContinuousAt (fun x : ℝ => -x + z u) (-z t) := by fun_prop
      filter_upwards [(hc.eventually_ne hpoint).filter_mono nhdsWithin_le_nhds]
        with x hx
      exact fun _ => hx
    · exact Eventually.of_forall (fun x h => False.elim (hu h))
  exact hplus.and hminus

/-- The odd part determines a selected simple-pole expansion when its
identity is known only away from the finite set of poles. -/
theorem simplePoleSum_odd_injective_on_off_poles
    (s : Finset T) (z a b : T → ℝ)
    (hz : ∀ t ∈ s, 0 < z t) (hzinj : Set.InjOn z s)
    (hodd : ∀ x : ℝ,
      (∀ t ∈ s, x + z t ≠ 0) →
      (∀ t ∈ s, -x + z t ≠ 0) →
      (∑ t ∈ s, a t / (x + z t)) -
        (∑ t ∈ s, a t / (-x + z t)) =
      (∑ t ∈ s, b t / (x + z t)) -
        (∑ t ∈ s, b t / (-x + z t))) :
    ∀ t ∈ s, a t = b t := by
  let d : T → ℝ := fun t => a t - b t
  have hd (x : ℝ) : (∑ u ∈ s, d u / (x + z u)) =
      (∑ u ∈ s, a u / (x + z u)) -
        (∑ u ∈ s, b u / (x + z u)) := by
    simp only [d, sub_div, Finset.sum_sub_distrib]
  intro t ht
  have heven : (fun x => ∑ u ∈ s, d u / (x + z u)) =ᶠ[𝓝[≠] (-z t)]
      (fun x => ∑ u ∈ s, d u / (-x + z u)) := by
    filter_upwards [eventually_subset_two_sided_pole_domain
      s z hz hzinj t ht] with x hx
    rw [hd x, hd (-x)]
    linarith [hodd x hx.1 hx.2]
  exact sub_eq_zero.mp
    (simplePoleSum_subset_coeff_zero_of_eventually_even
      s z d hz hzinj t ht heven)

/-- Multiplying two different negative simple poles stays in their
simple-pole span. -/
theorem two_simple_poles_split
    (a b x : ℝ) (hab : a ≠ b)
    (hxa : x + a ≠ 0) (hxb : x + b ≠ 0) :
    (x + a)⁻¹ * (x + b)⁻¹ =
      ((x + a)⁻¹ - (x + b)⁻¹) / (b - a) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp [hxa, hxb, hba]
  ring

omit [Fintype T] in
/-- A fresh pole can be multiplied into a finite distinct-rate
simple-pole sum without creating double poles. -/
theorem simplePoleSum_mul_fresh_pole
    (s : Finset T) (z a : T → ℝ) (t : T)
    (hfresh : ∀ u ∈ s, z t ≠ z u)
    (x : ℝ) (htx : x + z t ≠ 0)
    (hsx : ∀ u ∈ s, x + z u ≠ 0) :
    (∑ u ∈ s, a u / (x + z u)) * (x + z t)⁻¹ =
      (∑ u ∈ s, a u / (z u - z t)) / (x + z t) +
        ∑ u ∈ s, (a u / (z t - z u)) / (x + z u) := by
  classical
  rw [Finset.sum_mul]
  calc
    (∑ u ∈ s, (a u / (x + z u)) * (x + z t)⁻¹) =
      ∑ u ∈ s,
        ((a u / (z u - z t)) / (x + z t) +
          (a u / (z t - z u)) / (x + z u)) := by
            apply Finset.sum_congr rfl
            intro u hu
            have hzu : z u ≠ z t := (hfresh u hu).symm
            field_simp [htx, hsx u hu, sub_ne_zero.mpr hzu,
              sub_ne_zero.mpr (hfresh u hu)]
            ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_div]

end FMSA.Convergence.PureFluidRSimplePoleUniqueness

/-- info: 'FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_negative_reflection_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_negative_reflection_continuousAt
/-- info: 'FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_coeff_zero_of_eventually_even' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_coeff_zero_of_eventually_even
/-- info: 'FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_even_implies_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_even_implies_zero
/-- info: 'FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_subset_coeff_zero_of_eventually_even' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_subset_coeff_zero_of_eventually_even
/-- info: 'FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_subset_even_implies_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_subset_even_implies_zero
/-- info: 'FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_odd_injective_on' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_odd_injective_on
/-- info: 'FMSA.Convergence.PureFluidRSimplePoleUniqueness.eventually_subset_two_sided_pole_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSimplePoleUniqueness.eventually_subset_two_sided_pole_domain
/-- info: 'FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_odd_injective_on_off_poles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_odd_injective_on_off_poles
/-- info: 'FMSA.Convergence.PureFluidRSimplePoleUniqueness.two_simple_poles_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSimplePoleUniqueness.two_simple_poles_split
/-- info: 'FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_mul_fresh_pole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSimplePoleUniqueness.simplePoleSum_mul_fresh_pole
