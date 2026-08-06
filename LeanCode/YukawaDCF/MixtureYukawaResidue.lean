import LeanCode.YukawaDCF.MixtureYukawaTransform

/-!
# Residue extraction at the Yukawa poles (Tang & Lu eq (20)→(21))

The mixture first-order RDF `Ĥ₁(k) = [Q̂₀ᵀ(k)]⁻¹B₁(k)[Q̂₀(k)]⁻¹` (eq 15) reduces, through the
Hilbert transform / space-split of eq (14), to a residue operation on `B₁(k)` (eq 19):

`B₁(k) = −E(k) Res_{y(s)}( E(−y)[Q̂₀(−y)]⁻¹U₁(y)[Q̂₀ᵀ(−y)]⁻¹E(−y) / (y−k) ) E(k)`.

The residue is taken "with respect to each element of `U₁(y)`", i.e. at the *Yukawa poles* of
`U₁`.  With `U₁(y)ᵢⱼ = Kᵢⱼ e^{−iyRᵢⱼ}/(iy + zᵢⱼ)` (eq 18) and `[Q̂₀(−y)]⁻¹ = I + A(−iy)` (the
closed-form inverse `Q0_mat_phys_inv_eq`), every entry of the eq (20) integrand is a finite sum
of terms of the shape

`g(y) / ((y − k)(iy + z))`,

with `g` analytic (a product of `K` factors and `A(−iy)` factors) and a **simple** pole at `y = i z`
(because `iy + z = i(y − iz)`).  This file computes that residue once and for all:

`Res_{y=iz}[ g(y)/((y−k)(iy+z)) ] = −g(iz)/(ik + z)`   (`residue_yukawa_pole_general`).

This single lemma supplies, uniformly for all four term-types of eq (20):
* the Yukawa denominator `1/(ik + z_{αβ})` of eq (21);
* the argument evaluation `A(−iy)|_{y=iz} = A(z)` (`neg_I_mul_I_mul`), giving `Aⱼₙ(zᵢₙ)`,
  `Aᵢₘ(zₘⱼ)`, `Aᵢₘ(zₘₙ)Aⱼₙ(zₘₙ)` of eq (21);
* the overall `−E(k)…E(k)` sign that turns `−g(iz)/(ik+z)` into the `+K/(ik+z)` of `b_{ij}`
  (`residue_yukawa_first_term`).

The only hypothesis is `iz ≠ k` (physically `z = z_{ij} > 0` real and `k` real ⇒ automatic),
which by itself already forces `ik + z ≠ 0`, so no separate non-vanishing assumption on the
Yukawa denominator is needed.  Everything here is `Tendsto`-level complex analysis — axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`), no contour axiom, since a *single* simple pole's
residue is just the punctured-limit of `(y − iz)·f(y)`.
-/

open Filter Topology

namespace FMSA.MixtureRDF

/-- Argument substitution behind eq (21): the analytic numerators of eq (20) carry `A(−iy)`, and
at the Yukawa pole `y = i z` this becomes `A(z)` since `−i·(i z) = z`. -/
theorem neg_I_mul_I_mul (z : ℂ) : -Complex.I * (Complex.I * z) = z := by
  rw [← mul_assoc, show -Complex.I * Complex.I = 1 from by
    rw [neg_mul, Complex.I_mul_I]; ring, one_mul]

/-- **Tang & Lu eq (20)→(21) core residue.**  Every term of the eq (20) integrand has the shape
`g(y)/((y−k)(iy+z))` with `g` analytic (a product of `K` and `A(−iy)` factors) and a *simple*
Yukawa pole at `y = i z` (because `iy + z = i(y − iz)`).  Its residue — the punctured limit of
`(y−iz)·f(y)` — is `Res_{y=iz}[g(y)/((y−k)(iy+z))] = −g(iz)/(ik+z)`, supplying both the `1/(ik+z)`
factor and the `g(iz)` argument evaluation of eq (21).  Only hypothesis: `iz ≠ k` (physically
`z = z_{ij} > 0` real, `k` real ⇒ automatic), which already forces `ik + z ≠ 0`. -/
theorem residue_yukawa_pole_general {k z : ℂ} {g : ℂ → ℂ}
    (hne : Complex.I * z ≠ k) (hg : ContinuousAt g (Complex.I * z)) :
    Tendsto (fun y => (y - Complex.I * z) * (g y * ((y - k) * (Complex.I * y + z))⁻¹))
      (𝓝[≠] (Complex.I * z)) (𝓝 (-(g (Complex.I * z) * (Complex.I * k + z)⁻¹))) := by
  have hden : (Complex.I * z - k) * Complex.I ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hne) Complex.I_ne_zero
  -- eventual simplification on the punctured neighbourhood: `(y−iz)/(iy+z) = 1/i` cancels the pole
  have heq : (fun y => (y - Complex.I * z) * (g y * ((y - k) * (Complex.I * y + z))⁻¹))
      =ᶠ[𝓝[≠] (Complex.I * z)] (fun y => g y * ((y - k) * Complex.I)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y - Complex.I * z ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hy)
    have h1 : Complex.I * y + z = Complex.I * (y - Complex.I * z) := by
      linear_combination z * Complex.I_sq
    rw [h1, ← mul_assoc (y - k) Complex.I (y - Complex.I * z), mul_inv]
    have hrw : (y - Complex.I * z) * (g y * (((y - k) * Complex.I)⁻¹ * (y - Complex.I * z)⁻¹))
        = g y * ((y - k) * Complex.I)⁻¹ * ((y - Complex.I * z) * (y - Complex.I * z)⁻¹) := by
      ring
    rw [hrw, mul_inv_cancel₀ hy', mul_one]
  -- the simplified function is continuous at the pole
  have htend : Tendsto (fun y => g y * ((y - k) * Complex.I)⁻¹)
      (𝓝[≠] (Complex.I * z)) (𝓝 (g (Complex.I * z) * ((Complex.I * z - k) * Complex.I)⁻¹)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact hg.mul (((continuousAt_id.sub continuousAt_const).mul continuousAt_const).inv₀ hden)
  -- rewrite the limit value into `−g(iz)/(ik+z)` via `(iz−k)i = −(ik+z)`
  have hval : g (Complex.I * z) * ((Complex.I * z - k) * Complex.I)⁻¹
      = -(g (Complex.I * z) * (Complex.I * k + z)⁻¹) := by
    rw [show (Complex.I * z - k) * Complex.I = -(Complex.I * k + z) from by
      linear_combination z * Complex.I_sq, inv_neg, mul_neg]
  rw [hval] at htend
  exact htend.congr' heq.symm

/-- Numerator-free specialization: `Res_{y=iz}[1/((y−k)(iy+z))] = −1/(ik+z)`. -/
theorem residue_yukawa_pole {k z : ℂ} (hne : Complex.I * z ≠ k) :
    Tendsto (fun y => (y - Complex.I * z) * ((y - k) * (Complex.I * y + z))⁻¹)
      (𝓝[≠] (Complex.I * z)) (𝓝 (-(Complex.I * k + z)⁻¹)) := by
  have := residue_yukawa_pole_general (g := fun _ => (1 : ℂ)) hne continuousAt_const
  simpa using this

/-- **Tang & Lu eq (21), the diagonal `K_{ij}` term.**  With the overall `−E(k) Res(…) E(k)` sign of
eq (19), the residue of the first eq (20) term produces `b_{ij}`'s leading contribution
`K_{ij}/(ik + z_{ij})`. -/
theorem residue_yukawa_first_term {K k z : ℂ} (hne : Complex.I * z ≠ k) :
    Tendsto (fun y => -(K * ((y - Complex.I * z) * ((y - k) * (Complex.I * y + z))⁻¹)))
      (𝓝[≠] (Complex.I * z)) (𝓝 (K / (Complex.I * k + z))) := by
  have h := (residue_yukawa_pole hne).const_mul (-K)
  rw [show -K * -(Complex.I * k + z)⁻¹ = K / (Complex.I * k + z) from by
    rw [div_eq_mul_inv]; ring] at h
  refine h.congr (fun y => ?_)
  ring

end FMSA.MixtureRDF
