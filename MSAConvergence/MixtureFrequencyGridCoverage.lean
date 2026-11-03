import MSAConvergence.MixtureSampleInverseCertificate

/-! A finite, evenly spaced frequency mesh proves the quantified coverage
condition used by the actual mixture noescape grid theorem. -/
noncomputable section
open Real
open scoped BigOperators
namespace FMSA.Convergence.MixtureFrequencyGridCoverage
open FMSA.Convergence.MixtureAxisFrequencyGrid
open FMSA.Convergence.MixtureMomentCoefficientBudget
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Paper FMSA.MatrixQ0 FMSA.Paper.StableIntervalRadius
open FMSA.Convergence.MixtureAxisHighFrequency
open FMSA.Convergence.MixtureCoefficientBudget
open FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.MixtureSampleInverseCertificate
variable {N : ℕ} {T : Type*} [Fintype T]

def uniformSamples (L h : ℝ) (n : ℕ) : Finset ℝ :=
  (Finset.range (n+1)).image (fun j : ℕ => -L + (j : ℝ)*h)

/-- Every frequency in a bounded symmetric window lies less than one mesh
step to the right of a member of an explicit finite sample set. -/
theorem uniformSamples_cover
    (L h : ℝ) (n : ℕ) (hh : 0 < h)
    (hspan : 2*L ≤ (n : ℝ)*h) (k : ℝ) (hk : |k| ≤ L) :
    ∃ a ∈ uniformSamples L h n, |k-a| < h := by
  have hklo : -L ≤ k := (abs_le.mp hk).1
  have hkhi : k ≤ L := (abs_le.mp hk).2
  let x : ℝ := (k+L)/h
  let j : ℕ := Nat.floor x
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hh.le
  have hxn : x ≤ (n : ℝ) := by
    dsimp [x]
    apply (div_le_iff₀ hh).mpr
    nlinarith [hspan]
  have hjn : j ≤ n := Nat.floor_le_of_le hxn
  have hjlo : (j : ℝ)*h ≤ k+L := by
    have hh' := mul_le_mul_of_nonneg_right (Nat.floor_le hx0) hh.le
    dsimp [j,x] at hh'
    rwa [div_mul_cancel₀ _ hh.ne'] at hh'
  have hjhi : k+L < ((j : ℝ)+1)*h := by
    have hh' := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one x) hh
    dsimp [x] at hh'
    rwa [div_mul_cancel₀ _ hh.ne'] at hh'
  refine ⟨-L+(j : ℝ)*h,?_ ,?_⟩
  · exact Finset.mem_image.mpr
      ⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le hjn),rfl⟩
  · have hlo : 0 ≤ k-(-L+(j : ℝ)*h) := by linarith
    have hhi : k-(-L+(j : ℝ)*h) < h := by linarith
    simpa only [abs_of_nonneg hlo] using hhi

/-- One nonnegative global inverse budget and one mesh-step inequality
discharge the all-frequency coverage premise by finitely many samples. -/
theorem uniformSamples_perturbation_cover
    (L h : ℝ) (n : ℕ) (hh : 0 < h)
    (hspan : 2*L ≤ (n : ℝ)*h)
    (R : ℝ → ℝ) (Rbar Bmom : ℝ)
    (hR0 : ∀ a ∈ uniformSamples L h n, 0 ≤ R a)
    (hRbar : ∀ a ∈ uniformSamples L h n, R a ≤ Rbar)
    (hB : 0 ≤ Bmom)
    (hstep : Rbar * (h*Bmom) < 1) :
    ∀ k : ℝ, |k| ≤ L →
      ∃ a ∈ uniformSamples L h n,
        R a * (|k-a| * Bmom) < 1 := by
  intro k hk
  obtain ⟨a,ha,hnear⟩ := uniformSamples_cover L h n hh hspan k hk
  refine ⟨a,ha,?_⟩
  have hdist : 0 ≤ |k-a| * Bmom := mul_nonneg (abs_nonneg _) hB
  have hstep' : |k-a| * Bmom ≤ h*Bmom :=
    mul_le_mul_of_nonneg_right hnear.le hB
  calc
    R a * (|k-a| * Bmom) ≤ Rbar * (|k-a| * Bmom) :=
      mul_le_mul_of_nonneg_right (hRbar a ha) hdist
    _ ≤ Rbar*(h*Bmom) :=
      mul_le_mul_of_nonneg_left hstep' ((hR0 a ha).trans (hRbar a ha))
    _ < 1 := hstep

/-- A constant inverse budget over all mesh samples reduces coverage to
the single strict inequality `Rbar*h*Bmom<1`. -/
theorem uniformSamples_constant_cover
    (L h : ℝ) (n : ℕ) (hh : 0 < h)
    (hspan : 2*L ≤ (n : ℝ)*h)
    (Rbar Bmom : ℝ) (hR : 0 ≤ Rbar) (hB : 0 ≤ Bmom)
    (hstep : Rbar*(h*Bmom) < 1) :
    ∀ k : ℝ, |k| ≤ L →
      ∃ a ∈ uniformSamples L h n,
        Rbar * (|k-a| * Bmom) < 1 := by
  exact uniformSamples_perturbation_cover L h n hh hspan
    (fun _ => Rbar) Rbar Bmom
    (fun _ _ => hR) (fun _ _ => le_rfl) hB hstep

/-- The explicit negative-Laplace moment budget is nonnegative, so its
arithmetic mesh bound needs no extra sign premise from a certificate. -/
theorem transformMomentBudget_nonneg
    (z : T → ℝ) (rho sigma Abar : Fin N → ℝ)
    (Qbar : Fin N → Fin N → ℝ) (Wbar Cbar : TailMatrix T N)
    (hσ : ∀ i, 0 ≤ sigma i)
    (hA : ∀ j, 0 ≤ Abar j) (hQ : ∀ i j, 0 ≤ Qbar i j)
    (hW : ∀ u i j, 0 ≤ Wbar u i j)
    (hC : ∀ u i j, 0 ≤ Cbar u i j)
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u) :
    0 ≤ momentBudget rho
      (transformMomentUpper z sigma Abar Qbar Wbar Cbar δ) := by
  unfold momentBudget
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (transformMomentUpper_nonneg z sigma Abar Qbar Wbar Cbar
      hσ hA hQ hW hC δ hδ hrate i j)

def explicitWindow (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N) : ℝ :=
  rateCutoff z + explicitBudget z rho sigma Abar Qbar Wbar Cbar + 1

/-- The actual HS-seeded mixture amplitudes are uniformly bounded from
four coefficient caps, finitely many evenly spaced sample bounds, and two
scalar mesh inequalities. The all-frequency coverage quantifier is proved. -/
theorem hs_uniform_mesh_amplitude_bound
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = (0,baseSeed z rho sigma))
    (hp : ContinuousOn p (Set.Ico 0 b))
    (hroot : ∀ t ∈ Set.Ico 0 b,
      IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA0 : ∀ j, 0 ≤ Abar j) (hQ0 : ∀ i j, 0 ≤ Qbar i j)
    (hW0 : ∀ u i j, 0 ≤ Wbar u i j)
    (hC0 : ∀ u i j, 0 ≤ Cbar u i j)
    (hA : ∀ t ∈ Set.Ico 0 b, ∀ j,
      |amplitudeA z rho sigma (p t).1 (p t).2 j| ≤ Abar j)
    (hQ : ∀ t ∈ Set.Ico 0 b, ∀ i j,
      |amplitudeQp z rho sigma (p t).1 (p t).2 i j| ≤ Qbar i j)
    (hW : ∀ t ∈ Set.Ico 0 b, ∀ u i j,
      |W z rho (p t).1 (p t).2 u i j| ≤ Wbar u i j)
    (hC : ∀ t ∈ Set.Ico 0 b, ∀ u i j,
      |FMSA.ExactMSA.MultiTailMixture.C z rho sigma
        (p t).1 (p t).2 u i j| ≤ Cbar u i j)
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u)
    (h : ℝ) (hh : 0 < h) (n : ℕ)
    (hspan : 2*explicitWindow z rho sigma Abar Qbar Wbar Cbar ≤ (n : ℝ)*h)
    (Rbar : ℝ) (hR0 : 0 ≤ Rbar)
    (hbase : ∀ t ∈ Set.Ico 0 b,
      ∀ a ∈ uniformSamples (explicitWindow z rho sigma Abar Qbar Wbar Cbar) h n,
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) a).det ≠ 0)
    (hR : ∀ t ∈ Set.Ico 0 b,
      ∀ a ∈ uniformSamples (explicitWindow z rho sigma Abar Qbar Wbar Cbar) h n,
      complexNormSum ((fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) a)⁻¹) ≤ Rbar)
    (hstep : Rbar * (h * momentBudget rho
      (transformMomentUpper z sigma Abar Qbar Wbar Cbar δ)) < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ico 0 b, ‖p t‖ ≤ B := by
  apply hs_transform_grid_uniform_amplitude_bound z hz rho sigma hρ hσ hη
    K hK p b hb hp0 hp hroot Abar Qbar Wbar Cbar
    hA0 hQ0 hW0 hC0 hA hQ hW hC δ hδ hrate
    (uniformSamples (explicitWindow z rho sigma Abar Qbar Wbar Cbar) h n)
    (fun _ => Rbar) hbase hR
  intro k hk
  exact uniformSamples_constant_cover
    (explicitWindow z rho sigma Abar Qbar Wbar Cbar) h n hh hspan
    Rbar (momentBudget rho (transformMomentUpper z sigma Abar Qbar Wbar Cbar δ))
    hR0 (transformMomentBudget_nonneg z rho sigma Abar Qbar Wbar Cbar
      (fun i => (hσ i).le) hA0 hQ0 hW0 hC0 δ hδ hrate) hstep
    k hk

/-- A fully finite spatial-frequency certificate for mixture amplitude
noescape: four BH caps, a mesh span and step test, plus uniform determinant
margins and adjugate bounds at finitely many mesh samples. -/
theorem hs_uniform_mesh_adjugate_amplitude_bound
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hσ : ∀ i, 0 < sigma i) (hη : etaMix rho sigma < 1)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp0 : p 0 = (0,baseSeed z rho sigma))
    (hp : ContinuousOn p (Set.Ico 0 b))
    (hroot : ∀ t ∈ Set.Ico 0 b,
      IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (Abar : Fin N → ℝ) (Qbar : Fin N → Fin N → ℝ)
    (Wbar Cbar : TailMatrix T N)
    (hA0 : ∀ j, 0 ≤ Abar j) (hQ0 : ∀ i j, 0 ≤ Qbar i j)
    (hW0 : ∀ u i j, 0 ≤ Wbar u i j)
    (hC0 : ∀ u i j, 0 ≤ Cbar u i j)
    (hA : ∀ t ∈ Set.Ico 0 b, ∀ j,
      |amplitudeA z rho sigma (p t).1 (p t).2 j| ≤ Abar j)
    (hQ : ∀ t ∈ Set.Ico 0 b, ∀ i j,
      |amplitudeQp z rho sigma (p t).1 (p t).2 i j| ≤ Qbar i j)
    (hW : ∀ t ∈ Set.Ico 0 b, ∀ u i j,
      |W z rho (p t).1 (p t).2 u i j| ≤ Wbar u i j)
    (hC : ∀ t ∈ Set.Ico 0 b, ∀ u i j,
      |FMSA.ExactMSA.MultiTailMixture.C z rho sigma
        (p t).1 (p t).2 u i j| ≤ Cbar u i j)
    (δ : ℝ) (hδ : 0 < δ) (hrate : ∀ u, δ < z u)
    (h : ℝ) (hh : 0 < h) (n : ℕ)
    (hspan : 2*explicitWindow z rho sigma Abar Qbar Wbar Cbar ≤ (n : ℝ)*h)
    (m Bbar : ℝ) (hm : 0 < m) (hB0 : 0 ≤ Bbar)
    (hdet : ∀ t ∈ Set.Ico 0 b,
      ∀ a ∈ uniformSamples (explicitWindow z rho sigma Abar Qbar Wbar Cbar) h n,
      m ≤ ‖(fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) a).det‖)
    (hadj : ∀ t ∈ Set.Ico 0 b,
      ∀ a ∈ uniformSamples (explicitWindow z rho sigma Abar Qbar Wbar Cbar) h n,
      complexNormSum (fourierFactor z rho sigma
        (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2)
        (W z rho (p t).1 (p t).2)
        (FMSA.ExactMSA.MultiTailMixture.C z rho sigma
          (p t).1 (p t).2) a).adjugate ≤ Bbar)
    (hstep : (Bbar/m) * (h * momentBudget rho
      (transformMomentUpper z sigma Abar Qbar Wbar Cbar δ)) < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ico 0 b, ‖p t‖ ≤ B := by
  apply hs_uniform_mesh_amplitude_bound z hz rho sigma hρ hσ hη
    K hK p b hb hp0 hp hroot Abar Qbar Wbar Cbar
    hA0 hQ0 hW0 hC0 hA hQ hW hC δ hδ hrate h hh n hspan
    (Bbar/m) (div_nonneg hB0 hm.le)
  · intro t ht a ha hzero
    have hh' := lt_of_lt_of_le hm (hdet t ht a ha)
    simp [hzero] at hh'
  · intro t ht a ha
    exact inverse_normSum_le_adjugate_over_margin _ m Bbar hm
      (hdet t ht a ha) (hadj t ht a ha)
  · exact hstep

end FMSA.Convergence.MixtureFrequencyGridCoverage
/-- info: 'FMSA.Convergence.MixtureFrequencyGridCoverage.uniformSamples_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureFrequencyGridCoverage.uniformSamples_cover
/-- info: 'FMSA.Convergence.MixtureFrequencyGridCoverage.uniformSamples_perturbation_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureFrequencyGridCoverage.uniformSamples_perturbation_cover
/-- info: 'FMSA.Convergence.MixtureFrequencyGridCoverage.uniformSamples_constant_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureFrequencyGridCoverage.uniformSamples_constant_cover
/-- info: 'FMSA.Convergence.MixtureFrequencyGridCoverage.transformMomentBudget_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureFrequencyGridCoverage.transformMomentBudget_nonneg
/-- info: 'FMSA.Convergence.MixtureFrequencyGridCoverage.hs_uniform_mesh_amplitude_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureFrequencyGridCoverage.hs_uniform_mesh_amplitude_bound
/-- info: 'FMSA.Convergence.MixtureFrequencyGridCoverage.hs_uniform_mesh_adjugate_amplitude_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureFrequencyGridCoverage.hs_uniform_mesh_adjugate_amplitude_bound
