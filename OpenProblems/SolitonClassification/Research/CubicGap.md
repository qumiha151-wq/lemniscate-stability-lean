# A strict cubic moment inequality for closed similarity expanders

Consider a periodic arclength support profile with period `L>0`, curvature
`k`, support coordinates `p,q`, dilation coefficient `a` and rotation
coefficient `b`. The sign convention is

    F = k″ + k³/2 = −ap−bq,     p′=−kq,     q′=1+kp.

Set `B=∫k²`, `C=∫k³`, `S=∫k` over a period. Every such profile satisfies

    (2LC−BS)² ≤ LB³.

Equality characterizes the centered round profiles. For a closed curve this
includes both orientations and all covering numbers. The proof also applies
to periodic support data whose tangent frame returns with a nonintegral angle.

## The square identity and equality

The support equations give `∫F=C/2`, `∫kF=aL` and `∫F²=aB/2`. Hence

    L∫[4LF−Bk−(2LC−BS)/L]² = LB³−(2LC−BS)².

At equality, continuity and periodicity give an affine law `F=λk+μ` with
`λ=B/(4L)>0`. In fact any nonzero slope is enough for rigidity.
For `H=aq−bp`, the support equations give `F′=Hk−b`. A nonconstant
profile has curvature of both signs by the half-RMS curvature theorem.
Choose a zero `t` and set `w(s)=exp(−∫_t^s H/λ)`. Then
`(wk)′=−(b/λ)w` and `wk` vanishes at both ends of a period.
Rolle's theorem and positivity of `w` imply `b=0`. Now `wk` vanishes
everywhere, contradicting the positive bending of a periodic support
profile. Constant curvature fixes the supports to `p=−1/k, q=0` and gives
`k⁴=2a`. Conversely constant nonzero curvature gives equality by integration.

Writing `h=LC/(B√(LB))` and `s=S/√(LB)`, every noncircular profile thus
satisfies `|2h−s|<1`.

## A uniform quantitative gap under an energy cap

The following estimates give an explicit gap even for a periodic support
orbit without position closure. The claim is invariant under dilation, so
work on a period of length one. Concretely use the new arclength parameter
`u=s/L`, curvature `Lk(Lu)`, supports `p(Lu)/L,q(Lu)/L` and coefficients
`L⁴a,L⁴b`. In this normalization `B` equals the original value of
`L∫k²=2EL`. Suppose the normalized `B≤K`, taking `K≥1` by enlargement.
All norms below are on one period.

1. For nonconstant curvature, the two opposite half-RMS excursions give
   `osc k>√B`. Write `M=max|k|` and `Y=∫k′²`. By integration by parts,
   `Y=∫k⁴/2−a≤M²B/2`. Thus `√B<osc k≤√Y≤M√(B/2)`, forcing `M>√2`.
   There exists a point with `|k|≤√B`; integrating from that point gives
   `M≤√B+√Y≤√B+M√(B/2)`. If `B≤1/2`, this would give `M≤√2`.
   Consequently `B>1/2`. Integrating the derivative of `k²` from the same
   point gives `M²≤B+2√(BY)≤B+√2 BM`, hence `M≤√B+√2 B≤3K`.
2. The support identities and Cauchy–Schwarz give `0<a≤B²/2` and
   `||F||₂≤B^(3/2)/2`. The established strict pitch inequality at curvature
   center zero gives `16(b/a)²<B`, so `|b|≤B^(5/2)/8`. The auxiliary
   variable `H=aq−bp` satisfies `H′=a−kF`. Its oscillation is at most
   `a+√B ||F||₂≤B²`. Periodic integration of `kF′=k²H−bk` gives

       |∫k²H|/B ≤ |b|/√B + ||F||₂√Y/B ≤ B²/8+MB/(2√2).

   The weighted average lies between the minimum and maximum of `H`. Hence
   `||H||∞≤3K²`. From `F′=kH−b` we obtain `||F′||∞≤10K³`.
3. Put `λ=B/4`, `g=F−λk−∫(F−λk)`, `σ=||g||₂`, `ε=||g||∞`.
   The square identity gives

       σ²=λ²B(1−(2h−s)²),       σ≤K^(3/2)/4.

   The bounds above give `||g′||₂≤||F′||∞+λ√Y≤11K³`. Integrating
   `(g²)′` from a point with `|g|≤σ` then yields
   `ε²≤σ²+2σ||g′||₂≤23K³σ`.
4. Set `P=24K²`, so `||H/λ||∞≤P`, and `X=λk+g`. Differentiation gives

       X′=(H/λ)X−b−(H/λ)g.

   Start at any zero `t` of `k` and let `w(s)=exp(−∫_t^s H/λ)`.
   On `[t,t+1]` one has `exp(−P)≤w≤exp(P)` and
   `X(t+1)=X(t)=g(t)`. Integrating `(wX)′` over the period therefore gives

       |b| ≤ (2 exp(2P)+P)ε.

   Variation of constants starting at the same zero gives, on that interval,
   `|X(s)|≤exp(P)(ε+|b|+Pε)`. It follows that

       λ√B ≤ λM ≤ J ε,      J=1+exp(P)(1+2P+2 exp(2P)).

   As `B>1/2`, this shows `ε²≥1/(128J²)` and
   `σ≥1/(2944 K³ J²)`.

Combining steps 3 and 4 and using `1−|x|≥(1−x²)/2` for `|x|≤1` proves

    |2h−s| ≤ 1 − 8/(2944² K⁹ J⁴).

This choice of constants is deliberately coarse. It gives a strictly
positive margin for every finite cap and uses neither a shooting
compactness assumption nor an unproved classification of rotating profiles.

## Fixed total turning, without an energy cap

Fix any finite number `T>=0`. There is a number `delta(T)>0` such that
every noncircular periodic support profile with `|S|<=T` satisfies

    |2h-s| <= 1 - delta(T).

In particular this gives a gap for all noncircular closed similarity
solutions of a prescribed turning number. The conclusion also applies
to periodic support data with nonintegral frame holonomy.

To see this, use the universal constant `0<eps<1/2` in the
[periodic curvature estimate](../../LengthGrowth/Research/CurvatureMomentGap/StrictHalfThreshold.md).
Its hypothesis concerns a smooth periodic function, so it applies
before imposing position closure. Use a length-one period as above.
The profile identities give `int F²=(B/2)int kF`. With the RMS
rescaling in that estimate the normalized dissipation defect is thus
exactly zero. If `|s|<=eps`, the estimate gives `|h|<=1/2-eps`, hence
`|2h-s|<=1-eps`. Otherwise `B=S²/s²<=T²/eps²`. Apply the preceding
explicit finite-energy gap with `K=max(1,T²/eps²)`. The smaller of the
two positive margins works for every profile in the stated class.
For zero total turning the first case alone gives `|h|<=1/2-eps`.

## Verification scope and dependencies

The Lean module `SolitonClassification.CubicGap` covers the exact square,
the weak and strict inequalities for all periods, rigidity under an affine
force law, and the equality characterization. The explicit uniform margin
under an energy cap is a human proof. The fixed-turning conclusion also
uses the human static compactness argument in the linked note. The
finite-energy estimate uses the independently
verified theorem `PeriodicSupportProfile.rotation_pitch_sq_lt` from
`SolitonClassification.RotationPitch`.
