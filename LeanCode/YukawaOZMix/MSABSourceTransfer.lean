import LeanCode.YukawaOZ.MSABHJetRecurrence
import LeanCode.YukawaOZMix.MSAMixtureFiniteBSource
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearRadialOZ
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearAutomaticAdmissibility

/-! Transfer of the actual finite excess-renewal source. The density weights
occur on the ROW of the causal kernel, and the renewal multiplication is on
the RIGHT. Physical radial OZ uses the proved automatic root admissibility
with an explicit decay budget; the lower-level certificate interface is retained. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture.FiniteBSource
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem actual_source_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ ≤ z u)
    (i j : Fin N) : IntegrableOn (fun r => nonlinearExcessSource z ρ σ D G r i j) (Ioi 0) := by
  obtain ⟨B, _, hB⟩ := nonlinearExcessSource_weighted_bounded z ρ σ D G hz hσ hv δ hδz
  have hi : IntegrableOn (fun r => B * exp (-δ * r)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -δ < 0) 0).const_mul B
  apply hi.mono' ((nonlinearExcessSource_continuous z ρ σ D G).matrix_elem i j).measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs]
  have he : exp (δ * r) * exp (-δ * r)=1 := by rw [← exp_add]; simp
  calc
    |nonlinearExcessSource z ρ σ D G r i j| ≤ FMSA.matrixAbsSum (nonlinearExcessSource z ρ σ D G r) :=
      FMSA.matrixAbsSum_entry_le _ i j
    _ = (exp (δ * r) * FMSA.matrixAbsSum (nonlinearExcessSource z ρ σ D G r)) * exp (-δ * r) := by
      linear_combination -FMSA.matrixAbsSum (nonlinearExcessSource z ρ σ D G r) * he
    _ ≤ _ := mul_le_mul_of_nonneg_right (hB r hr.le) (exp_pos _).le

/-- Necessary integrability version; it does not impose a contraction budget.
The source and Q integrability are discharged by their actual dictionaries. -/
theorem actual_excess_source_renewal_of_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hE : ∀ i j, IntegrableOn (fun r => nonlinearRDFExcess z ρ σ D G r i j) (Ioi 0))
    (s : ℂ) (hs : 0 ≤ s.re) :
    rdfMatrixLaplace (nonlinearRDFExcess z ρ σ D G) s*
      (1 - rdfMatrixLaplace (nonlinearCausalKernel z ρ σ D G) s) =
        rdfMatrixLaplace (nonlinearExcessSource z ρ σ D G) s := by
  apply complexMatrixLaplace_right_renewal _ _ _
    (nonlinearCausalKernel_continuous z ρ σ D G)
    (nonlinearExcessSource_continuous z ρ σ D G)
    (nonlinearRDFExcess_continuous z ρ σ D G) s
  · intro i j
    apply realLaplace_weight_integrable_of_L1 _ _ s.re hs
    change Integrable (fun t => ρ i * nonlinearRecenteredQ z ρ σ D G i j t) (volume.restrict (Ioi 0))
    exact (nonlinearRecenteredQ_integrable z ρ σ D G hz hσ i j).const_mul (ρ i)
  · intro i j
    exact realLaplace_weight_integrable_of_L1 _
      (actual_source_integrable z ρ σ D G hz hσ hv δ hδ (fun u => (hδz u).le) i j) s.re hs
  · intro i j
    exact realLaplace_weight_integrable_of_L1 _ (hE i j) s.re hs
  · intro i j r hr
    simpa only [causalIntervalConv, mul_comm] using nonlinearRDFExcess_renewal z ρ σ D G i j r hr

/-- Valid on the closed right half-plane, including the finite-k Fourier axis.
The RHS is the transform of the ACTUAL evaluated finite spatial source. -/
theorem actual_excess_source_complex_renewal (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ D G δ < 1) (s : ℂ) (hs : 0 ≤ s.re) :
    rdfMatrixLaplace (nonlinearRDFExcess z ρ σ D G) s*
      (1 - rdfMatrixLaplace (nonlinearCausalKernel z ρ σ D G) s) =
        rdfMatrixLaplace (nonlinearExcessSource z ρ σ D G) s := by
  apply complexMatrixLaplace_right_renewal _ _ _
    (nonlinearCausalKernel_continuous z ρ σ D G)
    (nonlinearExcessSource_continuous z ρ σ D G)
    (nonlinearRDFExcess_continuous z ρ σ D G) s
  · intro i j
    apply realLaplace_weight_integrable_of_L1 _ _ s.re hs
    change Integrable (fun t => ρ i * nonlinearRecenteredQ z ρ σ D G i j t) (volume.restrict (Ioi 0))
    exact (nonlinearRecenteredQ_integrable z ρ σ D G hz hσ i j).const_mul (ρ i)
  · intro i j
    exact realLaplace_weight_integrable_of_L1 _
      (actual_source_integrable z ρ σ D G hz hσ hv δ hδ (fun u => (hδz u).le) i j) s.re hs
  · intro i j
    exact realLaplace_weight_integrable_of_L1 _
      (nonlinearRDFExcess_integrable_of_weighted_budget z ρ σ D G hz hσ hv δ hδ hδz hb i j) s.re hs
  · intro i j r hr
    simpa only [causalIntervalConv, mul_comm] using nonlinearRDFExcess_renewal z ρ σ D G i j r hr

def normalizedMomentSymbol (z : ι → ℝ) (ρ σ : Fin N → ℝ) (D G : TailMatrix ι N)
    (k : ℝ) (i j : Fin N) : ℂ :=
  ((sqrt (ρ i) * sqrt (ρ j) : ℝ): ℂ) * (2 * π / (Complex.I * k))*
    (FMSA.causalComplexLaplace (nonlinearRDFMoment z ρ σ D G i j) (-(Complex.I * k))-
      FMSA.causalComplexLaplace (nonlinearRDFMoment z ρ σ D G i j) (Complex.I * k))

theorem actual_normalized_radial_transfer (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ D G δ < 1) (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    ((sqrt (ρ i) * sqrt (ρ j) * FMSA.HardSphere.radial_fourier (nonlinearH z ρ σ D G i j) k : ℝ): ℂ) =
      normalizedMomentSymbol z ρ σ D G k i j := by
  rw [Complex.ofReal_mul, nonlinearH_radial_fourier z ρ σ D G i j hz hσ hv δ hδ hδz hb k hk]
  unfold normalizedMomentSymbol
  ring

/-- Reconstructing E from its source uses a right inverse and the stated order.
This retains every lower-order term of the normalized renewal equation. -/
theorem source_order_reconstruction (E Q U : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (Q0inv : Matrix (Fin N) (Fin N) ℂ) (n : ℕ)
    (hQ : Q 0 * Q0inv = 1)
    (hline : E n * Q 0 + E 0 * Q n+
      BHierarchy.lowerSource E Q n = U n) :
    E n = (U n - E 0 * Q n - BHierarchy.lowerSource E Q n) * Q0inv := by
  have he : E n * Q 0 = U n - E 0 * Q n - BHierarchy.lowerSource E Q n := by
    rw [← hline]
    abel
  calc
    _ = E n * Q 0 * Q0inv := by rw [Matrix.mul_assoc, hQ, Matrix.mul_one]
    _ = _ := by rw [he]

/-- The evaluated source and radial OZ belong to the same actual constructed
RDF/DCF. Existing finite admissibility certificates are retained explicitly. -/
theorem actual_finite_source_radial_OZ_bridge [DecidableEq ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K D G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i)
    (hv : vacMix ρ σ ≠ 0) (hroot : IsRoot z ρ σ K D G) (hK : ∀ u i j, K u i j = K u j i)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ D G δ < 1)
    (hrc : NonlinearFiniteReciprocityCertificate z ρ σ D G)
    (hwc : NonlinearFiniteWronskianCertificate z ρ σ D G)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    (nonlinearExcessSource z ρ σ D G r i j =
      ∑ b : SourceIndex ι N, sourceCoefficient z ρ σ D G i j b * sourceBasis z σ i j r b) ∧
    (nonlinearH z ρ σ D G i j =ᵐ[volume.restrict (Ioi 0)] fun s =>
      orderedRadialCorrelation z ρ σ K D G i j s+
        radialMixtureConv (orderedRadialCorrelation z ρ σ K D G) (nonlinearH z ρ σ D G) ρ i j s) :=
  ⟨actual_source_eq_finite z ρ σ D G hz (fun i => (hσ i).le) i j r hr,
    nonlinearH_actual_radial_OZ_of_finite_certificates z ρ σ K D G hz hσ hv hroot hK
      δ hδ hδz hb hrc hwc i j⟩

/-- On the established analytic-budget domain the actual BH root automatically
discharges both algebraic certificates. No finite-B or projection hypothesis. -/
theorem actual_finite_source_radial_OZ_automatic [DecidableEq ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K D G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i)
    (hρ : ∀ i, 0 ≤ ρ i) (hv : vacMix ρ σ ≠ 0) (hroot : IsRoot z ρ σ K D G)
    (hK : ∀ u i j, K u i j=K u j i) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ D G δ < 1)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    (nonlinearExcessSource z ρ σ D G r i j =
      ∑ b : SourceIndex ι N, sourceCoefficient z ρ σ D G i j b*sourceBasis z σ i j r b) ∧
    (nonlinearH z ρ σ D G i j =ᵐ[volume.restrict (Ioi 0)] fun s =>
      orderedRadialCorrelation z ρ σ K D G i j s+
        radialMixtureConv (orderedRadialCorrelation z ρ σ K D G) (nonlinearH z ρ σ D G) ρ i j s) := by
  have h := nonlinearMixtureRDF_automatic_admissibility_certificate z ρ σ K D G
    hz hσ hρ hv hroot hK δ hδ hδz hb
  exact ⟨actual_source_eq_finite z ρ σ D G hz (fun i => (hσ i).le) i j r hr,
    h.1.2.2.2.2 i j⟩

theorem actual_hardcore_positive_jet (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : ℝ → TailMatrix ι N) (i j : Fin N) (r : ℝ)
    (hr : 0 < r) (hR : r < edgeHi σ i j) (n : ℕ) (hn : 0 < n) :
    BSource.jet (fun t => nonlinearH z ρ σ (D t) (G t) i j r) n = 0 := by
  have he : (fun t => nonlinearH z ρ σ (D t) (G t) i j r)=fun _ : ℝ => -1 := by
    funext t
    exact nonlinearH_hardcore z ρ σ (D t) (G t) i j r hr hR
  rw [he]
  simp [BSource.jet, iteratedDeriv_const, hn.ne']

theorem actual_ordered_DCF_exterior (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K D G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K D G) (hK : ∀ u i j, K u i j = K u j i)
    (i j : Fin N) (r : ℝ) (hR : edgeHi σ i j < r) :
    orderedRadialCorrelation z ρ σ K D G i j r =
      ∑ u, K u i j * exp (-z u * (r - edgeHi σ i j)) / r := by
  unfold orderedRadialCorrelation
  split_ifs
  · exact correlation_exterior_of_root z hz ρ σ K D G hσ hroot i j r hR
  · have he : edgeHi σ j i = edgeHi σ i j := by unfold edgeHi; ring
    rw [correlation_exterior_of_root z hz ρ σ K D G hσ hroot j i r (by rwa [he])]
    simp_rw [he, ← hK _ i j]

/-- The actual MSA outer closure terminates at first order; this is obtained
from the BH root and exterior convolution theorem, not supplied as a premise. -/
theorem actual_exterior_DCF_jet (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (D G : ℝ → TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : ∀ᶠ t in 𝓝 (0: ℝ), IsRoot z ρ σ (t • K) (D t) (G t))
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) (r : ℝ) (hR : edgeHi σ i j < r) (n : ℕ) :
    BSource.jet (fun t => orderedRadialCorrelation z ρ σ (t • K) (D t) (G t) i j r) n =
      if n = 1 then ∑ u, K u i j * exp (-z u * (r - edgeHi σ i j)) / r else 0 := by
  have he : (fun t => orderedRadialCorrelation z ρ σ (t • K) (D t) (G t) i j r)=ᶠ[𝓝 (0: ℝ)]
      fun t => t * (∑ u, K u i j * exp (-z u * (r - edgeHi σ i j)) / r) := by
    filter_upwards [hroot] with t ht
    rw [actual_ordered_DCF_exterior z ρ σ (t • K) (D t) (G t) hz hσ ht
      (by intro u a b; simp only [Pi.smul_apply, smul_eq_mul, hK u a b]) i j r hR, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h := congrArg (fun x : ℝ => x / (n.factorial: ℝ)) (he.iteratedDeriv_eq n)
  exact h.trans (BSource.jet_linear_coupling _ n)

end FMSA.ExactMSA.MultiTailMixture.FiniteBSource

open Matrix
namespace FMSA.ExactMSA.BSource

def complexJet (f : ℝ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / (n.factorial: ℂ)

theorem normalized_complex_mul (f g : ℝ → ℂ) (n : ℕ)
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0) :
    complexJet (fun t => f t * g t) n =
      ∑ j ∈ Finset.range (n + 1), complexJet f j * complexJet g (n - j) := by
  unfold complexJet
  rw [iteratedDeriv_fun_mul hf hg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hc : (n.choose j : ℂ) * (j.factorial: ℂ) * ((n - j).factorial: ℂ)=(n.factorial: ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  have hjf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hnf : ((n - j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - j)
  have hnn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  linear_combination (iteratedDeriv j f 0 * iteratedDeriv (n - j) g 0) * hc

def matrixJet {N : ℕ} (X : ℝ → Matrix (Fin N) (Fin N) ℂ) (n : ℕ) :
    Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j => complexJet (fun t => X t i j) n)

theorem normalized_matrix_mul {N : ℕ} (Y Q : ℝ → Matrix (Fin N) (Fin N) ℂ) (n : ℕ)
    (hY : ∀ i j, ContDiffAt ℝ n (fun t => Y t i j) 0)
    (hQ : ∀ i j, ContDiffAt ℝ n (fun t => Q t i j) 0) :
    matrixJet (fun t => Y t * Q t) n =
      ∑ j ∈ Finset.range (n + 1), matrixJet Y j * matrixJet Q (n - j) := by
  ext a b
  simp only [matrixJet, Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply]
  have hs : complexJet (fun t => ∑ l : Fin N, Y t a l * Q t l b) n =
      ∑ l : Fin N, complexJet (fun t => Y t a l * Q t l b) n := by
    unfold complexJet
    rw [iteratedDeriv_fun_sum (fun l _ => (hY a l).mul (hQ l b)), Finset.sum_div]
  rw [hs]
  simp_rw [normalized_complex_mul _ _ n (hY _ _) (hQ _ _)]
  rw [Finset.sum_comm]

/-- A local actual renewal identity automatically supplies its normalized
coefficient equation. No independently supplied order-n line is required. -/
theorem normalized_renewal_line {N : ℕ} (Y Q U : ℝ → Matrix (Fin N) (Fin N) ℂ) (n : ℕ)
    (hn : 0 < n)
    (hY : ∀ i j, ContDiffAt ℝ n (fun t => Y t i j) 0)
    (hQ : ∀ i j, ContDiffAt ℝ n (fun t => Q t i j) 0)
    (heq : ∀ᶠ t in 𝓝 (0: ℝ), Y t * Q t = U t) :
    matrixJet Y n * matrixJet Q 0 + matrixJet Y 0 * matrixJet Q n+
      BHierarchy.lowerSource (matrixJet Y) (matrixJet Q) n = matrixJet U n := by
  have h : matrixJet (fun t => Y t * Q t) n = matrixJet U n := by
    ext a b
    have he : (fun t => (Y t * Q t) a b) =ᶠ[𝓝 (0: ℝ)] fun t => U t a b :=
      heq.mono (fun t ht => congrFun (congrFun ht a) b)
    exact congrArg (fun x : ℂ => x / (n.factorial: ℂ)) (he.iteratedDeriv_eq n)
  rw [normalized_matrix_mul Y Q n hY hQ] at h
  have hsplit : (∑ j ∈ Finset.range (n + 1), matrixJet Y j * matrixJet Q (n - j)) =
      matrixJet Y n * matrixJet Q 0 + matrixJet Y 0 * matrixJet Q n+
        BHierarchy.lowerSource (matrixJet Y) (matrixJet Q) n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [BHierarchy.lowerSource, Nat.succ_sub_succ_eq_sub, Nat.sub_self,
      Nat.succ_sub_one, Nat.add_sub_cancel_left, Nat.sub_zero]
    abel
  exact hsplit.symm.trans h

end FMSA.ExactMSA.BSource
