import MSAConvergence.ImplicitContourCurvature

/-! Exact local level intersections and signs near a genuine analytic
nondegenerate minimum. No external root count is assumed. -/

noncomputable section
open Set Real Filter Topology
set_option maxHeartbeats 2000000
namespace FMSA.Convergence.LocalMinimumLevels

/-- Positive true curvature gives strict monotonicity on the two sides of
an analytic stationary point, at arbitrarily small radius. -/
theorem monotone_sides (ψ : ℝ → ℝ) (b k R : ℝ)
    (ha : AnalyticAt ℝ ψ b) (h1 : HasDerivAt ψ 0 b)
    (h2 : HasDerivAt (deriv ψ) k b) (hk : 0 < k) (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ContinuousOn ψ (Icc (b-δ) (b+δ)) ∧
      StrictAntiOn ψ (Icc (b-δ) b) ∧ StrictMonoOn ψ (Icc b (b+δ)) := by
  have hpos : ∀ᶠ t in 𝓝 b, 0 < deriv (deriv ψ) t :=
    ha.deriv.deriv.continuousAt.eventually (Ioi_mem_nhds (by
      change 0 < deriv (deriv ψ) b
      rw [h2.deriv]
      exact hk))
  have hgood : ∀ᶠ t in 𝓝 b, AnalyticAt ℝ ψ t ∧ 0 < deriv (deriv ψ) t :=
    ha.eventually_analyticAt.and hpos
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hgood
  let δ := min (r/2) (R/2)
  have hd : 0 < δ := lt_min (by linarith) (by linarith)
  have hdr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdR : δ < R := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hp (t : ℝ) (ht : t ∈ Ioo (b-r) (b+r)) :
      AnalyticAt ℝ ψ t ∧ 0 < deriv (deriv ψ) t := by
    apply hball
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hm : StrictMonoOn (deriv ψ) (Ioo (b-r) (b+r)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · intro t ht
      exact (hp t ht).1.deriv.continuousAt.continuousWithinAt
    · intro t ht
      exact (hp t (interior_subset ht)).2
  have hb : b ∈ Ioo (b-r) (b+r) := ⟨by linarith,by linarith⟩
  have hs (t : ℝ) (ht : t ∈ Icc (b-δ) (b+δ)) : t ∈ Ioo (b-r) (b+r) :=
    ⟨by linarith [ht.1],by linarith [ht.2]⟩
  refine ⟨δ,hd,hdR,?_,?_,?_⟩
  · intro t ht
    exact (hp t (hs t ht)).1.continuousAt.continuousWithinAt
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro t ht
      exact (hp t (hs t ⟨ht.1,by linarith [ht.2]⟩)).1.continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Ioo (b-δ) b := by simpa only [interior_Icc] using ht
      have hlt := hm (hs t ⟨ht'.1.le,by linarith [ht'.2]⟩) hb ht'.2
      rwa [h1.deriv] at hlt
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro t ht
      exact (hp t (hs t ⟨by linarith [ht.1],ht.2⟩)).1.continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Ioo b (b+δ) := by simpa only [interior_Icc] using ht
      have hlt := hm hb (hs t ⟨by linarith [ht'.1],ht'.2.le⟩) ht'.1
      rwa [h1.deriv] at hlt

/-- Exactly zero/one/two intersections of a local analytic minimum with a
nearby horizontal level, stated by explicit roots and exhaustive iff. -/
def LevelPicture (ψ : ℝ → ℝ) (b δ ε : ℝ) : Prop :=
  0 < δ ∧ 0 < ε ∧
  (∀ t ∈ Ioo (b-δ) (b+δ), ψ b ≤ ψ t) ∧
  (∀ w, w < ψ b → ∀ t ∈ Ioo (b-δ) (b+δ), ψ t ≠ w) ∧
  (∀ t ∈ Ioo (b-δ) (b+δ), ψ t = ψ b ↔ t = b) ∧
  (∀ w, ψ b < w → w < ψ b+ε →
    ∃ l r : ℝ, l ∈ Ioo (b-δ) b ∧ r ∈ Ioo b (b+δ) ∧ ψ l = w ∧ ψ r = w ∧
      (∀ t ∈ Ioo (b-δ) (b+δ), ψ t = w ↔ t = l ∨ t = r) ∧
      (∀ t ∈ Ioo l r, ψ t < w) ∧
      (∀ t ∈ Ioo (b-δ) (b+δ), t < l ∨ r < t → w < ψ t))

theorem local_level_picture (ψ : ℝ → ℝ) (b k R : ℝ)
    (ha : AnalyticAt ℝ ψ b) (h1 : HasDerivAt ψ 0 b)
    (h2 : HasDerivAt (deriv ψ) k b) (hk : 0 < k) (hR : 0 < R) :
    ∃ δ ε : ℝ, δ < R ∧ ε < R ∧ LevelPicture ψ b δ ε := by
  obtain ⟨δ,hd,hdR,hcont,hleft,hright⟩ := monotone_sides ψ b k R ha h1 h2 hk hR
  have hbL : b ∈ Icc (b-δ) b := ⟨by linarith,le_rfl⟩
  have hbR : b ∈ Icc b (b+δ) := ⟨le_rfl,by linarith⟩
  have hgL : ψ b < ψ (b-δ) := hleft ⟨le_rfl,by linarith⟩ hbL (by linarith)
  have hgR : ψ b < ψ (b+δ) := hright hbR ⟨by linarith,le_rfl⟩ (by linarith)
  let ε := min ((ψ (b-δ)-ψ b)/2) (min ((ψ (b+δ)-ψ b)/2) (R/2))
  have he : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have heL : ε ≤ (ψ (b-δ)-ψ b)/2 := min_le_left _ _
  have heR : ε ≤ (ψ (b+δ)-ψ b)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have heRR : ε < R := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  have hbase (t : ℝ) (ht : t ∈ Icc (b-δ) (b+δ)) :
      ψ b ≤ ψ t ∧ (ψ t = ψ b ↔ t = b) := by
    rcases le_total t b with htb | hbt
    · have htl : t ∈ Icc (b-δ) b := ⟨ht.1,htb⟩
      exact ⟨hleft.antitoneOn htl hbL htb,(hleft.eq_iff_eq htl hbL).trans eq_comm⟩
    · have htr : t ∈ Icc b (b+δ) := ⟨hbt,ht.2⟩
      exact ⟨hright.monotoneOn hbR htr hbt,hright.eq_iff_eq htr hbR⟩
  refine ⟨δ,ε,hdR,heRR,hd,he,?_,?_,?_,?_⟩
  · intro t ht
    exact (hbase t ⟨ht.1.le,ht.2.le⟩).1
  · intro w hw t ht heq
    have h := (hbase t ⟨ht.1.le,ht.2.le⟩).1
    rw [heq] at h
    exact (not_le_of_gt hw) h
  · intro t ht
    exact (hbase t ⟨ht.1.le,ht.2.le⟩).2
  · intro w hwlo hwhi
    have hwL : w < ψ (b-δ) := by linarith
    have hwR : w < ψ (b+δ) := by linarith
    have hcL : ContinuousOn ψ (Icc (b-δ) b) := hcont.mono (by
      intro t ht; exact ⟨ht.1,by linarith [ht.2]⟩)
    have hcR : ContinuousOn ψ (Icc b (b+δ)) := hcont.mono (by
      intro t ht; exact ⟨by linarith [ht.1],ht.2⟩)
    obtain ⟨l,hl,hlv⟩ := intermediate_value_Icc' (by linarith : b-δ ≤ b) hcL ⟨hwlo.le,hwL.le⟩
    obtain ⟨r,hr,hrv⟩ := intermediate_value_Icc (by linarith : b ≤ b+δ) hcR ⟨hwlo.le,hwR.le⟩
    have hls : l ∈ Ioo (b-δ) b := by
      constructor
      · by_contra hn
        have hle : l = b-δ := by linarith [hl.1]
        rw [hle] at hlv
        linarith
      · by_contra hn
        have hle : l = b := by linarith [hl.2]
        rw [hle] at hlv
        linarith
    have hrs : r ∈ Ioo b (b+δ) := by
      constructor
      · by_contra hn
        have hre : r = b := by linarith [hr.1]
        rw [hre] at hrv
        linarith
      · by_contra hn
        have hre : r = b+δ := by linarith [hr.2]
        rw [hre] at hrv
        linarith
    refine ⟨l,r,hls,hrs,hlv,hrv,?_,?_,?_⟩
    · intro t ht
      constructor
      · intro heq
        rcases le_total t b with htb | hbt
        · exact Or.inl (((hleft.eq_iff_eq ⟨ht.1.le,htb⟩ hl).mp (heq.trans hlv.symm)).symm)
        · exact Or.inr ((hright.eq_iff_eq ⟨hbt,ht.2.le⟩ hr).mp (heq.trans hrv.symm))
      · rintro (rfl | rfl)
        · exact hlv
        · exact hrv
    · intro t ht
      rcases le_total t b with htb | hbt
      · have hh := hleft hl ⟨by linarith [hls.1,ht.1],htb⟩ ht.1
        rwa [hlv] at hh
      · have hh := hright ⟨hbt,by linarith [hrs.2,ht.2]⟩ hr ht.2
        rwa [hrv] at hh
    · intro t ht hout
      rcases hout with htl | hrt
      · have hh := hleft ⟨ht.1.le,by linarith [hls.2]⟩ hl htl
        rwa [hlv] at hh
      · have hh := hright hr ⟨by linarith [hrs.1],ht.2.le⟩ hrt
        rwa [hrv] at hh

end FMSA.Convergence.LocalMinimumLevels

/-- info: 'FMSA.Convergence.LocalMinimumLevels.monotone_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.LocalMinimumLevels.monotone_sides

/-- info: 'FMSA.Convergence.LocalMinimumLevels.local_level_picture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.LocalMinimumLevels.local_level_picture
