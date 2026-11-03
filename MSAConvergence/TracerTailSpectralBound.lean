import MSAConvergence.CompactSpectralTest

/-! The actual MSA exterior Yukawa tail has a uniform spectral square bound.
The pointwise hard-core/exterior split uses the genuine ordered DCF and h fields. -/
noncomputable section
open FMSA.HardSphere FMSA.ExactMSA
namespace FMSA.Convergence.TracerTailSpectralBound

private theorem trig_bound (z sigma k : ℝ) (hz : 0 < z) (hs : 0 < sigma) :
    |k*Real.cos (k*sigma)+z*Real.sin (k*sigma)| ≤ |k| *(1+z*sigma) := by
  have hc := Real.abs_cos_le_one (k*sigma)
  have hsin := Real.abs_sin_le_abs (x := k*sigma)
  have hz0 : 0 ≤ z := hz.le
  have hs0 : 0 ≤ sigma := hs.le
  calc
    _ ≤ |k*Real.cos (k*sigma)|+|z*Real.sin (k*sigma)| := abs_add_le _ _
    _ = |k| *|Real.cos (k*sigma)|+z*|Real.sin (k*sigma)| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hz0]
    _ ≤ |k| *1+z*|k*sigma| := by gcongr
    _ = |k| *(1+z*sigma) := by rw [abs_mul,abs_of_nonneg hs0]; ring

/-- The exact exterior Yukawa Fourier transform decays rationally. -/
theorem tail_fourier_decay (z sigma : ℝ) (hz : 0 < z) (hs : 0 < sigma)
    (K k : ℝ) (hk : k ≠ 0) :
    |radial_fourier (cMSAtail K z sigma) k| ≤
      (4*Real.pi*|K| *(1+z*sigma))/(z^2+k^2) := by
  rw [radial_fourier_cMSAtail hz hs]
  have hQ : 0 < z^2+k^2 := by positivity
  have hka : 0 < |k| := abs_pos.mpr hk
  have ht := trig_bound z sigma k hz hs
  have hpos : 0 ≤ 4*Real.pi*|K| := by positivity
  rw [abs_mul,abs_div,abs_div,abs_of_pos hQ]
  have hnum : |4*Real.pi*K|=4*Real.pi*|K| := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),abs_of_pos Real.pi_pos]
  rw [hnum]
  calc
    _ = (4*Real.pi*|K| *|k*Real.cos (k*sigma)+z*Real.sin (k*sigma)|/|k|)/(z^2+k^2) := by ring
    _ ≤ (4*Real.pi*|K| *(1+z*sigma))/(z^2+k^2) := by
      apply div_le_div_of_nonneg_right _ hQ.le
      apply (div_le_iff₀ hka).mpr
      nlinarith [mul_le_mul_of_nonneg_left ht hpos]
/-- A bound with a fixed (1+k²) denominator. -/
theorem tail_fourier_standard_decay (z sigma : ℝ) (hz : 0 < z) (hs : 0 < sigma)
    (K k : ℝ) (hk : k ≠ 0) :
    let m := min (z^2) 1
    |radial_fourier (cMSAtail K z sigma) k| ≤
      (4*Real.pi*|K| *(1+z*sigma)/m)/(1+k^2) := by
  dsimp only
  let m := min (z^2) 1
  let A := 4*Real.pi*|K| *(1+z*sigma)
  let B := A/m
  have hm : 0 < m := lt_min (sq_pos_of_pos hz) zero_lt_one
  have hfreq : 0 < 1+k^2 := by positivity
  have hQ : 0 < z^2+k^2 := by positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := div_nonneg hA hm.le
  have hden : m*(1+k^2) ≤ z^2+k^2 := by
    have h1 : m ≤ z^2 := min_le_left _ _
    have h2 : m*k^2 ≤ k^2 := mul_le_of_le_one_left (sq_nonneg k) (min_le_right _ _)
    nlinarith
  have hAB : B*m=A := by dsimp only [B]; exact div_mul_cancel₀ A hm.ne'
  calc
    _ ≤ A/(z^2+k^2) := tail_fourier_decay z sigma hz hs K k hk
    _ ≤ B/(1+k^2) := by
      apply (div_le_div_iff₀ hQ hfreq).mpr
      nlinarith [mul_le_mul_of_nonneg_left hden hB]

/-- A single exterior tail is dominated by the compact test spectrum. -/
theorem tail_fourier_square_dominated (z sigma R : ℝ) (hz : 0 < z)
    (hs : 0 < sigma) (hR : 0 < R) (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℝ, k ≠ 0 →
      |radial_fourier (cMSAtail K z sigma) k|^2 ≤
        C*radial_fourier (fun r => CompactSpectralTest.profile (r/R)) k := by
  obtain ⟨c,hc,hφ⟩ := CompactSpectralTest.scaled_profile_radial_fourier_lower R hR
  let m := min (z^2) 1
  let B := 4*Real.pi*|K| *(1+z*sigma)/m
  let C := B^2/c
  have hm : 0 < m := lt_min (sq_pos_of_pos hz) zero_lt_one
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := div_nonneg (sq_nonneg B) hc.le
  refine ⟨C,hC,?_⟩
  intro k hk
  let f := |radial_fourier (cMSAtail K z sigma) k|
  let q := 1+k^2
  have hq : 0 < q := by dsimp [q]; positivity
  have hf : 0 ≤ f := abs_nonneg _
  have hb : 0 ≤ B/q := div_nonneg hB hq.le
  have hdecay : f ≤ B/q := by
    simpa only [f,q,B,m] using tail_fourier_standard_decay z sigma hz hs K k hk
  have hsq : f^2 ≤ (B/q)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdecay) (add_nonneg hf hb)]
  calc
    _ ≤ (B/q)^2 := hsq
    _ = C*(c/q^2) := by dsimp only [C]; field_simp [hc.ne']
    _ ≤ C*radial_fourier (fun r => CompactSpectralTest.profile (r/R)) k :=
      mul_le_mul_of_nonneg_left (hφ k hk) hC

/-- The domination constant is uniform over bounded strengths. -/
theorem tail_fourier_square_dominated_uniform (z sigma R : ℝ)
    (hz : 0 < z) (hs : 0 < sigma) (hR : 0 < R) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℝ, |K| ≤ B → ∀ k : ℝ, k ≠ 0 →
      |radial_fourier (cMSAtail K z sigma) k|^2 ≤
        C*radial_fourier (fun r => CompactSpectralTest.profile (r/R)) k := by
  obtain ⟨c,hc,hφ⟩ := CompactSpectralTest.scaled_profile_radial_fourier_lower R hR
  let m := min (z^2) 1
  let L := max B 0
  let A := 4*Real.pi*L*(1+z*sigma)/m
  let C := A^2/c
  have hm : 0 < m := lt_min (sq_pos_of_pos hz) zero_lt_one
  have hL : 0 ≤ L := le_max_right B 0
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := div_nonneg (sq_nonneg A) hc.le
  refine ⟨C,hC,?_⟩
  intro K hK k hk
  let f := |radial_fourier (cMSAtail K z sigma) k|
  let q := 1+k^2
  have hq : 0 < q := by dsimp [q]; positivity
  have hf : 0 ≤ f := abs_nonneg _
  have ha : 0 ≤ A/q := div_nonneg hA hq.le
  have hdecay : f ≤ A/q := by
    calc
      f ≤ (4*Real.pi*|K| *(1+z*sigma)/m)/q := by
        simpa only [f,q,m] using tail_fourier_standard_decay z sigma hz hs K k hk
      _ ≤ A/q := by
        apply div_le_div_of_nonneg_right _ hq.le
        apply div_le_div_of_nonneg_right _ hm.le
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (hK.trans (le_max_left _ _)) (by positivity)
  have hsq : f^2 ≤ (A/q)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdecay) (add_nonneg hf ha)]
  calc
    _ ≤ (A/q)^2 := hsq
    _ = C*(c/q^2) := by dsimp only [C]; field_simp [hc.ne']
    _ ≤ C*radial_fourier (fun r => CompactSpectralTest.profile (r/R)) k :=
      mul_le_mul_of_nonneg_left (hφ k hk) hC

/-- Finite sum of the individually normalized exterior radial transforms. -/
def tailSymbol {T : Type*} [Fintype T] (z : T → ℝ) (sigma : ℝ)
    (K : T → ℝ) (k : ℝ) : ℝ :=
  ∑ u, radial_fourier (cMSAtail (K u) (z u) sigma) k

/-- A finite signed, repeated-rate Yukawa sum has the same square bound. -/
theorem tail_symbol_square_dominated {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma R : ℝ)
    (hs : 0 < sigma) (hR : 0 < R) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : T → ℝ, (∀ u, |K u| ≤ B) →
      ∀ k : ℝ, k ≠ 0 →
        |tailSymbol z sigma K k|^2 ≤
          C*radial_fourier (fun r => CompactSpectralTest.profile (r/R)) k := by
  obtain ⟨c,hc,hφ⟩ := CompactSpectralTest.scaled_profile_radial_fourier_lower R hR
  let L := max B 0
  let a : T → ℝ := fun u => 4*Real.pi*L*(1+z u*sigma)/min ((z u)^2) 1
  let A := ∑ u, a u
  let C := A^2/c
  have hL : 0 ≤ L := le_max_right B 0
  have ha : ∀ u, 0 ≤ a u := by
    intro u
    dsimp [a]
    have hm : 0 < min ((z u)^2) 1 := lt_min (sq_pos_of_pos (hz u)) zero_lt_one
    apply div_nonneg _ hm.le
    have hp : 0 ≤ 1+z u*sigma := by nlinarith [mul_pos (hz u) hs]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hL) hp
  have hA : 0 ≤ A := Finset.sum_nonneg (fun u _ => ha u)
  have hC : 0 ≤ C := div_nonneg (sq_nonneg A) hc.le
  refine ⟨C,hC,?_⟩
  intro K hK k hk
  let f := |tailSymbol z sigma K k|
  let q := 1+k^2
  have hq : 0 < q := by dsimp [q]; positivity
  have hf : 0 ≤ f := abs_nonneg _
  have hAq : 0 ≤ A/q := div_nonneg hA hq.le
  have hterm (u : T) :
      |radial_fourier (cMSAtail (K u) (z u) sigma) k| ≤ a u/q := by
    have hm : 0 < min ((z u)^2) 1 := lt_min (sq_pos_of_pos (hz u)) zero_lt_one
    calc
      _ ≤ (4*Real.pi*|K u| *(1+z u*sigma)/min ((z u)^2) 1)/q := by
        simpa only [q] using tail_fourier_standard_decay (z u) sigma (hz u) hs (K u) k hk
      _ ≤ a u/q := by
        apply div_le_div_of_nonneg_right _ hq.le
        apply div_le_div_of_nonneg_right _ hm.le
        apply mul_le_mul_of_nonneg_right _ (by nlinarith [mul_pos (hz u) hs])
        exact mul_le_mul_of_nonneg_left ((hK u).trans (le_max_left _ _)) (by positivity)
  have hdecay : f ≤ A/q := by
    calc
      f ≤ ∑ u, |radial_fourier (cMSAtail (K u) (z u) sigma) k| := by
        dsimp only [f,tailSymbol]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u, a u/q := Finset.sum_le_sum (fun u _ => hterm u)
      _ = A/q := by rw [← Finset.sum_div]
  have hsq : f^2 ≤ (A/q)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdecay) (add_nonneg hf hAq)]
  calc
    _ ≤ (A/q)^2 := hsq
    _ = C*(c/q^2) := by dsimp only [C]; field_simp [hc.ne']
    _ ≤ C*radial_fourier (fun r => CompactSpectralTest.profile (r/R)) k :=
      mul_le_mul_of_nonneg_left (hφ k hk) hC

open FMSA.ExactMSA.MultiTailMixture MSAMixture
variable {N : ℕ} {T : Type*} [Fintype T]
/-- At an actual reciprocal root the ordered DCF exterior is the prescribed tail. -/
theorem actual_c_exterior_eq_tail_sum (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 < sigma i)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hr : IsRoot z rho sigma K D G) (i j : Fin N) (r : ℝ)
    (houter : edgeHi sigma i j < r) :
    orderedRadialCorrelation z rho sigma K D G i j r =
      ∑ u, cMSAtail (K u i j) (z u) (edgeHi sigma i j) r := by
  have hσ : ∀ i, 0 ≤ sigma i := fun i => (hs i).le
  have hR : edgeHi sigma j i=edgeHi sigma i j := by unfold edgeHi; ring
  unfold orderedRadialCorrelation
  split_ifs with ho
  · rw [correlation_exterior_of_root z hz rho sigma K D G hσ hr i j r houter]
    apply Finset.sum_congr rfl
    intro u _
    simp only [cMSAtail,if_pos houter]
  · rw [correlation_exterior_of_root z hz rho sigma K D G hσ hr j i r (by rw [hR]; exact houter)]
    apply Finset.sum_congr rfl
    intro u _
    rw [hR,hK u j i]
    simp only [cMSAtail,if_pos houter]

/-- Fixed hard-core comparison profile on positive radii. -/
def coreValue (R r : ℝ) : ℝ := if r < R then -1 else 0

/-- Actual MSA spatial c h pairing splits pointwise at all noncontact radii. -/
theorem actual_pair_product_split (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 < sigma i)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hr : IsRoot z rho sigma K D G) (i j : Fin N) (r : ℝ)
    (hr0 : 0 < r) (hcontact : r ≠ edgeHi sigma i j) :
    orderedRadialCorrelation z rho sigma K D G i j r * nonlinearH z rho sigma D G i j r =
      orderedRadialCorrelation z rho sigma K D G i j r * coreValue (edgeHi sigma i j) r +
        (∑ u, cMSAtail (K u i j) (z u) (edgeHi sigma i j) r) * nonlinearH z rho sigma D G i j r := by
  rcases lt_or_gt_of_ne hcontact with hinner | houter
  · rw [nonlinearH_hardcore z rho sigma D G i j r hr0 hinner]
    have htail : (∑ u, cMSAtail (K u i j) (z u) (edgeHi sigma i j) r)=0 := by
      apply Finset.sum_eq_zero
      intro u _
      simp only [cMSAtail,if_neg (not_lt.mpr hinner.le)]
    simp only [coreValue,if_pos hinner,htail,zero_mul,add_zero]
  · rw [actual_c_exterior_eq_tail_sum z hz rho sigma hs K D G hK hr i j r houter]
    simp only [coreValue,if_neg (not_lt.mpr houter.le),mul_zero,zero_add]

end FMSA.Convergence.TracerTailSpectralBound
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.tail_fourier_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.tail_fourier_decay
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.tail_fourier_standard_decay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.tail_fourier_standard_decay
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.tail_fourier_square_dominated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.tail_fourier_square_dominated
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.tail_fourier_square_dominated_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.tail_fourier_square_dominated_uniform
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.tail_symbol_square_dominated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.tail_symbol_square_dominated
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.actual_c_exterior_eq_tail_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.actual_c_exterior_eq_tail_sum
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.actual_pair_product_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.actual_pair_product_split
