# Exact origin expansion of the actual BH pieces

`PureFluidActualOriginExpansion.lean` proves the rational identity

    1/(s+z) = 1/z - s/z² + s²/(z²(s+z))

for nonzero `z` and `s+z`. Applying it to each finite Yukawa term of
the ORIGINAL BH formulas gives exact pointwise decompositions

    P_actual(s) = -A/s³ + (A-Q)/s² + (Q-A/2-c)/s
                  + p0 + p1*s + s²*Rp(s),
    Shat_actual(s) = A/s³ + Q/s² + c/s
                     + v0 + v1*s + s²*Rv(s),

where `A=rho*amplitudeA`, `Q=rho*amplitudeQp`, and `c,p0,v0,p1,v1`
are exactly the finite sums in `PureFluidActualOriginMoments`.
`Rp,Rv` are explicit finite rational sums and Lean proves both are
continuous at zero when all rates are nonzero. No root equation is used.

This validates that the constants in the preceding moment theorem are
the actual first regular coefficients of the BH factor pieces. The
remaining inverse-dressing step is to substitute these exact expansions
into `dressingU,dressingG`, apply the four vanishing principal-part
identities, and construct continuous extensions at zero. The current
module does **not** yet claim `U_actual,g_actual` are regular at zero
or globally equal the finite-sum H-function candidates.

Full checker PASS: 1854 exact standard-three theorem guards /202 research
modules; foundation 1.0.17 unchanged. No TeX file was written.
