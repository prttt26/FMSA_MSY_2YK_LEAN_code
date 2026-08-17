import LeanCode.HSMixture.MatrixQ0

/-!
# Hard-sphere mixture RDF contact value (Tang & Lu eq (25))

The hard-sphere part of the mixture radial distribution function at contact, `g⁰ᵢⱼ(Rᵢⱼ)`, from the
Lebowitz/Percus–Yevick solution as quoted by Tang & Lu (Mol. Phys. 84, 89 (1995), eq (25)).  Validated
here two ways: the **equal-diameter reduction** to the scalar PY-HS contact `(1+η/2)/(1−η)²`
(`gHS_contact_equalDiam`, proved), and numerically against Tang & Lu's Table 1 (the `g⁰` values sit below
the full first-order `g = g⁰ + g¹` for the attractive Yukawa mixture — `scratchpad/contact_check.py`).
This is the `γ = 0` (hard-sphere) baseline of the first-order mixture RDF; the Yukawa correction `g¹`
comes from the residue expansion (eqs 21–24), which builds on the closed-form `[Q̂₀]⁻¹`.
-/

namespace FMSA.MixtureRDFContact
open FMSA.MatrixQ0

/-- **Tang & Lu eq (25) — the hard-sphere mixture RDF contact value** `g⁰ᵢⱼ(Rᵢⱼ)`.
`g⁰ᵢⱼ(Rᵢⱼ) = (1/(Rᵢⱼ·Δ))·(Rᵢⱼ + π·σᵢ·σⱼ·ξ₂/(4Δ))`, with `Rᵢⱼ = (σᵢ+σⱼ)/2`, `Δ = vacMix = 1−η`,
`ξ₂ = xi2`.  The Lebowitz/PY hard-sphere-mixture contact value. -/
noncomputable def gHS_contact {N : ℕ} (rho sigma : Fin N → ℝ) (i j : Fin N) : ℝ :=
  (1 / ((sigma i + sigma j) / 2 * vacMix rho sigma)) *
    ((sigma i + sigma j) / 2 + Real.pi * sigma i * sigma j * xi2 rho sigma / (4 * vacMix rho sigma))

/-- **Equal-diameter reduction — the mixture HS contact collapses to the scalar PY-HS contact.**
When every diameter equals `s`, `g⁰ᵢⱼ(Rᵢⱼ) = (1 + η/2)/(1 − η)²` — exactly the single-component
Percus–Yevick hard-sphere contact value (`BaxterRealSpace`: `q'_py/(2πσ) = (1+η/2)/(1−η)²`).  Validates
the eq (25) formula against the scalar theory. -/
theorem gHS_contact_equalDiam {N : ℕ} (rho sigma : Fin N → ℝ) {s : ℝ} (hs : 0 < s)
    (hsig : ∀ k, sigma k = s) (heta : etaMix rho sigma < 1) (i j : Fin N) :
    gHS_contact rho sigma i j
      = (1 + etaMix rho sigma / 2) / (1 - etaMix rho sigma) ^ 2 := by
  have hkey : Real.pi * s * xi2 rho sigma = 6 * etaMix rho sigma := by
    unfold xi2 etaMix
    simp_rw [hsig, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hvac : (0 : ℝ) < 1 - etaMix rho sigma := by linarith
  unfold gHS_contact vacMix
  rw [hsig i, hsig j,
    show Real.pi * s * s * xi2 rho sigma = s * (Real.pi * s * xi2 rho sigma) from by ring, hkey]
  field_simp
  ring

end FMSA.MixtureRDFContact
