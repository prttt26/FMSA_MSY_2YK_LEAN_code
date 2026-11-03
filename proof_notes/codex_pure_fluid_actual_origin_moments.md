# Actual BH origin moment algebra

`PureFluidActualOriginMoments.lean` connects the ORIGINAL pure-fluid
Blum–Høye moment definitions to four real constants naturally read from
the regular parts of the finite-tail rational and exponential pieces.
For each nonzero Yukawa rate it proves the per-tail `D*Mtil` and
`D*Ntil` identities in terms of the actual `W,C` coefficients, then sums
them over any finite tail type. The resulting identities are

    M = p0 + v0 - 1 - c,
    N = p1 + v1 - v0 + c/2,

where `c = Σ rho*C`, `p0 = 1 - Σ rho*W/z`, `v0 = -Σ rho*C/z`,
`p1 = Σ rho*W/z²`, and `v1 = Σ rho*C/z²`.

The same module proves four finite algebra identities for the possible
`s⁻²` and `s⁻¹` coefficients of the inverse dressing `g_actual` and
`U_actual`. The `s⁻¹` identities vanish directly. The `s⁻²` identities
are multiples of `a² - 4aq - 8a + 4q² + 8q`, which is zero for the
actual PY hard-sphere basis when `xi ≠ 1`. The final theorem substitutes
the actual BH amplitudes `rho*A,rho*q`, not free moment parameters. No
root equation is needed.

**Scope:** The four expressions are candidate Laurent principal-part
coefficients. `PureFluidActualOriginExpansion` now proves the exact
first-order regular-part decomposition of the true BH `P,Shat` with
continuous remainders. Substitution into the inverse PY formulas is
still pending. These modules therefore do not yet claim
`U_actual` or `g_actual` is regular at the origin, nor global equality
with the finite-sum H-function candidate. The next step is an exact
inverse-dressing algebra and a continuity or rational-identity
argument identifying these coefficients with the actual local principal
parts.

`python3 scripts/check_pure_fluid_origin_principal.py` independently
expands the formal inverse PY formulas with exact SymPy arithmetic and
checks the four coefficient formulas, plus structural cancellation of
higher negative powers. It is diagnostic evidence only; the Lean algebra
theorem and its guarded dependencies carry the formal claim.

Full checker PASS: 1849 exact standard-three theorem guards /201 research
modules; foundation 1.0.17 unchanged. No TeX file was written.
