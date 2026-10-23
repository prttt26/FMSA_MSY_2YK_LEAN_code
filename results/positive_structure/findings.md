# Positive-system structure of the exact-MSA coupling branch (2026-10-23)

Question: is there a positive-system form `w = τβ + Φ(w)` (all coefficients
nonnegative) of the Blum–Høye system that forces the coupling-series
coefficients to have fixed signs, so that Pringsheim puts the radius on the
real fold? Scripts in `scripts/positive_structure/`; logs next to this file.
Engine: `msa_exact_mix.py` (main repository). All results are numerical, not
proofs.

## 1. One species, one tail: the raw BH system is already positive

`positive_system.py`. `P` is cubic and its Taylor expansion at the HS seed is
exact, so `v = τβ + Φ(v)` with `β = J₀⁻¹b` and `Φ = −J₀⁻¹(½H + ⅙T)`. In
`(D̃, G̃ − G̃₀)` with signs `(+,+)`, every coefficient is nonnegative.

| η | β | Φ monomials |
|---|---|---|
| 0.2 | 2.129, 0.0384 | D², D²G; D², DG, D²G, DG² |
| 0.4 | 1.136, 0.0031 | same monomials, same signs |

The worst coefficient is −1e-16, i.e. round-off.

Positivity of all branch coefficients then follows by fixed-point iteration
alone. This is a much shorter route than the Lean proof (parametrization,
absolute monotonicity, Faà di Bruno), but it is not yet proved for all
`(η, z)`.

## 2. Multi-tail and mixtures: no positive form of this kind exists

`positive_lp.py`. The search allows:

* a variable sign change `v = Rw` (all `2ⁿ` diagonal `R`);
* a preconditioner and a nonnegative linear part, `w = τCb + Mw − C[Q₂ + Q₃](Rw)`
  with `C = (I − M)(J₀R)⁻¹`, `M ≥ 0` and row sums `≤ 1 − δ`.

Under these choices every positivity condition is linear in `M`, row by row,
so each case reduces to a set of LPs and the answer is exact, not an
optimiser's best effort.

* One tail: feasible at `M = 0`. This is the control: the LP reproduces §1.
* Two attractive tails (`z = (1.8, 4)` and `(1.8, 0.8)`), 2YK, and F5:
  infeasible for every `R`. The best margin is `−c·δ`, i.e. it reaches 0 only
  in the degenerate limit where a row of `C` vanishes.

In raw signs, the two-attractive-tail obstruction is only two cross-tail
monomials: `G₁ ← D₀G₀` and `G₀ ← D₁G₁`. One-tail binaries show more than 100
small (1–2 %) negative entries. The best sign pattern reaches `2.8e-3` but
not 0.

An earlier unconstrained bound of `1 − 10⁻⁶` on the row sums made even F5 look
feasible. That bound admits the degenerate limit `M_ii → 1`, so the test was
vacuous. It was replaced by a margin that scales with `δ`.

## 3. The positive structure lives in the Baxter factor

`dw_system.py` gives an exact reduction for `N = 1`:

* `D_ν f_ν = τ k_ν`
* `2πG_ν f_ν = S_ν/z_ν²`

where `f_ν = F(z_ν)` and `S_ν` are affine in `X = (D_μ, W_μ)`. The reduction
reproduces the BH solution to 1e-16. It is not itself a positive form:
`∂S/∂W < 0` already for one tail.

`baxter_F_signs.py` and `mix_F_signs.py` test the τ-coefficients of
`F(s; τ) = 1 − ρQ̂(s)` at `s = 0, 0.5, 1, 1.8, 3, 6, 12, 30`, for orders
`1 … 36`:

* all ≤ 0 for one tail (η = 0.2, 0.4), two attractive tails, and 2YK
  (competing tails);
* in binaries (Berthelot; equal σ with `K12 = 0.2` and `−0.3`; two attractive
  tails), every entry of `F̃` keeps a fixed sign, and `det F̃(s)` has all
  coefficients ≤ 0 at every `s`;
* F5: mixed signs at every `s`.

`det F(0)` is the spinodal indicator, so this is a basis-free invariant.

## 4. The sharp boundary is geometric, not a tail-sign condition

Family `z = (1.8, 12)`, `K = (1, w)`, `η = 0.3` (`boundary_scan.py`,
`boundary_fine.py`, `boundary_finer.py`):

| w | real fold τ_f | F(s) coefficients | radius vs fold |
|---|---|---|---|
| 0 … −2.0 | 1.307 … 2.686 | all ≤ 0 | `R/τ_f = 1.0000`, exponent ½ |
| −2.5 | 4.479 | positive at orders 1–2 for `s ≥ 1.8` | `R/τ_f = 1.0002` (fold still binds) |
| −2.60 … −2.625 | 5.81 … 6.65 | eventual signs constant; the last flip moves from order 7–28 to 16–62 | corrected root test `≈ τ_f` |
| −2.630 | 6.957 | flips to order ~58 | `R ≈ 6.89 ≈ τ_f` (crossing) |
| **−2.635** | **7.518** | flips to order ~60 | **`R ≈ 6.9 < τ_f`: a real fold exists but does not bind** |
| ≤ −2.64 | none to 60 | flips throughout | complex singularity, `|τ*| ≈ 6.8–6.9` |

Two consequences:

1. Low-order positivity of `F(s)` is not necessary: at `w = −2.5` it fails at
   order 1 while the fold still binds.
2. Existence of a real fold is not sufficient: at `w = −2.635` the
   complex-singularity modulus (≈ 6.9, nearly constant across the scan) is
   below `τ_f`.

So "radius = fold" is decided by which is nearer, the real fold or the
nearest complex singularity on the physical sheet. Any condition on the tails
alone can only be sufficient.

## Next

* Prove the one-tail positivity of §1 for all `(η, z)`, symbolically.
* Look for a function-space positive formulation that would give `F(s; τ)`
  coefficients ≤ 0 for every `s ≥ 0` under a sufficient tail condition (for
  example, all tails attractive). The Baxter equations are a candidate
  quadratic operator equation.
* For the sharp criterion, go back to future plan (a): locate the nearest
  complex singularity on the physical sheet and certify it.
