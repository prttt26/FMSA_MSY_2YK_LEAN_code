import MSAConvergence.PureFluidCoincidentPoleLimits

set_option linter.style.header false

/-! The candidate pure-fluid dressing has the required normalization at
infinity and an exact polar cancellation identity at the origin. The
identity holds pointwise for arbitrary real dressing values U,g; the
finite-sum candidate is continuous at the origin for nonzero rates.
Individual BH moment-coefficient matching remains separate. -/

noncomputable section
open Real Filter Topology Set
namespace FMSA.Convergence.PureFluidCandidateOriginConstraint
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidDressingCandidates
variable {T : Type*} [Fintype T]

/-- The polynomial polar-shape identity evaluated directly for arbitrary
real U,g at every nonzero frequency; no analytic-jet hypothesis is used. -/
theorem dressing_master_origin_identity (xi s U g : ℝ) (hs : s ≠ 0) :
    2*candidateRational xi s U g+
      (2-2*s+s^2)*candidateExponential xi s U g =
      (hardQ xi+2)*U+(hardA xi/2-hardQ xi-2+s)*g := by
  unfold candidateRational candidateExponential hardP hardShat
  field_simp [hs]
  ring

/-- The finite-sum candidate U is regular at the origin for nonzero rates. -/
theorem candidateU_continuousAt_zero (z w : T → ℝ)
    (hz : ∀ t, z t ≠ 0) : ContinuousAt (candidateU z w) 0 := by
  unfold candidateU
  fun_prop (disch := simp [hz])

/-- The finite-sum candidate g is regular at the origin for nonzero rates. -/
theorem candidateG_continuousAt_zero (z w r : T → ℝ)
    (hz : ∀ t, z t ≠ 0) : ContinuousAt (candidateG z w r) 0 := by
  unfold candidateG
  fun_prop (disch := simp [hz])

/-- The candidate reciprocal H factor tends to one at positive infinity. -/
theorem candidateU_tendsto_one_atTop (z w : T → ℝ) :
    Tendsto (candidateU z w) atTop (𝓝 (1 : ℝ)) := by
  have hterm (t : T) : Tendsto (fun s : ℝ => w t/(s+z t))
      atTop (𝓝 (0 : ℝ)) := by
    have hden : Tendsto (fun s : ℝ => s+z t) atTop atTop :=
      tendsto_atTop_add_const_right atTop (z t) tendsto_id
    have hinv : Tendsto (fun s : ℝ => (s+z t)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def] using (tendsto_inv_atTop_zero.comp hden)
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds (x := w t)).mul hinv
  have hsum : Tendsto (fun s : ℝ => ∑ t, w t/(s+z t))
      atTop (𝓝 (0 : ℝ)) := by
    convert tendsto_finsetSum Finset.univ (fun t _ => hterm t) using 1
    simp
  convert tendsto_const_nhds.sub hsum using 1
  · funext s
    rfl
  · ring_nf

/-- The candidate off-diagonal dressing tends to zero at positive infinity. -/
theorem candidateG_tendsto_zero_atTop (z w r : T → ℝ) :
    Tendsto (candidateG z w r) atTop (𝓝 (0 : ℝ)) := by
  have hterm (t : T) : Tendsto
      (fun s : ℝ => w t*(z t-r t)/(s+z t)) atTop (𝓝 (0 : ℝ)) := by
    have hden : Tendsto (fun s : ℝ => s+z t) atTop atTop :=
      tendsto_atTop_add_const_right atTop (z t) tendsto_id
    have hinv : Tendsto (fun s : ℝ => (s+z t)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def] using (tendsto_inv_atTop_zero.comp hden)
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds (x := w t*(z t-r t))).mul hinv
  have hsum : Tendsto (fun s : ℝ => ∑ t, w t*(z t-r t)/(s+z t))
      atTop (𝓝 (0 : ℝ)) := by
    convert tendsto_finsetSum Finset.univ (fun t _ => hterm t) using 1
    simp
  change Tendsto (fun s : ℝ => ∑ t, w t*(z t-r t)/(s+z t))
    atTop (𝓝 (0 : ℝ))
  exact hsum

/-- The actual PY rational basis tends to one whenever inverse frequency tends to zero. -/
theorem hardP_tendsto_of_inv
    (xi : ℝ) {α : Type*} {l : Filter α} (f : α → ℝ)
    (hinv : Tendsto (fun x => (f x)⁻¹) l (𝓝 (0 : ℝ))) :
    Tendsto (fun x => hardP xi (f x)) l (𝓝 (1 : ℝ)) := by
  have hc : ContinuousAt (fun y : ℝ =>
      1-hardA xi*y^3+(hardA xi-hardQ xi)*y^2+
        (hardQ xi-hardA xi/2)*y) 0 := by fun_prop
  have hlim := hc.tendsto.comp hinv
  convert hlim using 1
  · funext x
    simp [hardP,div_eq_mul_inv,inv_pow]
  · ring_nf

/-- The actual PY exponential basis tends to zero under the same condition. -/
theorem hardShat_tendsto_of_inv
    (xi : ℝ) {α : Type*} {l : Filter α} (f : α → ℝ)
    (hinv : Tendsto (fun x => (f x)⁻¹) l (𝓝 (0 : ℝ))) :
    Tendsto (fun x => hardShat xi (f x)) l (𝓝 (0 : ℝ)) := by
  have hc : ContinuousAt (fun y : ℝ => hardA xi*y^3+hardQ xi*y^2) 0 := by
    fun_prop
  have hlim := hc.tendsto.comp hinv
  convert hlim using 1
  · funext x
    simp [hardShat,div_eq_mul_inv,inv_pow]
  · ring_nf

/-- The candidate rational BH factor has its required infinity normalization. -/
theorem candidateRational_tendsto_one_atTop
    (xi : ℝ) (z w r : T → ℝ) :
    Tendsto (fun s => candidateRational xi s
      (candidateU z w s) (candidateG z w r s)) atTop (𝓝 (1 : ℝ)) := by
  have hinv : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hP := hardP_tendsto_of_inv xi (fun s : ℝ => s) hinv
  have hSn := hardShat_tendsto_of_inv xi (fun s : ℝ => -s) (by
    simpa only [inv_neg,neg_zero] using hinv.neg)
  have hU := candidateU_tendsto_one_atTop z w
  have hG := candidateG_tendsto_zero_atTop z w r
  have hGinv := hG.mul hinv
  have hlim := ((hU.sub hGinv).mul hP).add (hGinv.mul hSn)
  convert hlim using 1
  · funext s
    simp only [candidateRational,div_eq_mul_inv]
  · ring_nf

/-- The candidate exponential BH factor vanishes at infinity. -/
theorem candidateExponential_tendsto_zero_atTop
    (xi : ℝ) (z w r : T → ℝ) :
    Tendsto (fun s => candidateExponential xi s
      (candidateU z w s) (candidateG z w r s)) atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hS := hardShat_tendsto_of_inv xi (fun s : ℝ => s) hinv
  have hPn := hardP_tendsto_of_inv xi (fun s : ℝ => -s) (by
    simpa only [inv_neg,neg_zero] using hinv.neg)
  have hU := candidateU_tendsto_one_atTop z w
  have hG := candidateG_tendsto_zero_atTop z w r
  have hGinv := hG.mul hinv
  have hlim := ((hU.sub hGinv).mul hS).add (hGinv.mul hPn)
  convert hlim using 1
  · funext s
    simp only [candidateExponential,div_eq_mul_inv]
  · ring_nf

/-- The candidate polar combination has a finite punctured real-axis origin
limit determined by U(0) and g(0). -/
theorem candidate_master_origin_limit (xi : ℝ) (z w r : T → ℝ)
    (hz : ∀ t, z t ≠ 0) :
    Tendsto (fun s =>
      2*candidateRational xi s (candidateU z w s) (candidateG z w r s)+
        (2-2*s+s^2)*
          candidateExponential xi s (candidateU z w s) (candidateG z w r s))
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((hardQ xi+2)*candidateU z w 0+
        (hardA xi/2-hardQ xi-2)*candidateG z w r 0)) := by
  have hU := candidateU_continuousAt_zero z w hz
  have hG := candidateG_continuousAt_zero z w r hz
  have hc : ContinuousAt
      (fun s => (hardQ xi+2)*candidateU z w s+
        (hardA xi/2-hardQ xi-2+s)*candidateG z w r s) 0 := by
    fun_prop
  have hlim : Tendsto
      (fun s => (hardQ xi+2)*candidateU z w s+
        (hardA xi/2-hardQ xi-2+s)*candidateG z w r s)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((hardQ xi+2)*candidateU z w 0+
        (hardA xi/2-hardQ xi-2)*candidateG z w r 0)) := by
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1
    ring_nf
  have heq : (fun s =>
      2*candidateRational xi s (candidateU z w s) (candidateG z w r s)+
        (2-2*s+s^2)*
          candidateExponential xi s (candidateU z w s) (candidateG z w r s))
      =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun s => (hardQ xi+2)*candidateU z w s+
        (hardA xi/2-hardQ xi-2+s)*candidateG z w r s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hs
    exact dressing_master_origin_identity xi s (candidateU z w s)
      (candidateG z w r s) hs0
  exact hlim.congr' heq.symm

end FMSA.Convergence.PureFluidCandidateOriginConstraint
/-- info: 'FMSA.Convergence.PureFluidCandidateOriginConstraint.dressing_master_origin_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateOriginConstraint.dressing_master_origin_identity
/-- info: 'FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateU_continuousAt_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateU_continuousAt_zero
/-- info: 'FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateG_continuousAt_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateG_continuousAt_zero
/-- info: 'FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateU_tendsto_one_atTop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateU_tendsto_one_atTop
/-- info: 'FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateG_tendsto_zero_atTop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateG_tendsto_zero_atTop
/-- info: 'FMSA.Convergence.PureFluidCandidateOriginConstraint.hardP_tendsto_of_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateOriginConstraint.hardP_tendsto_of_inv
/-- info: 'FMSA.Convergence.PureFluidCandidateOriginConstraint.hardShat_tendsto_of_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateOriginConstraint.hardShat_tendsto_of_inv
/-- info: 'FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateRational_tendsto_one_atTop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateRational_tendsto_one_atTop
/-- info: 'FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateExponential_tendsto_zero_atTop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateOriginConstraint.candidateExponential_tendsto_zero_atTop
/-- info: 'FMSA.Convergence.PureFluidCandidateOriginConstraint.candidate_master_origin_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidateOriginConstraint.candidate_master_origin_limit
