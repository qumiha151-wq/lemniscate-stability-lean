# The quartic period numerator

The four Lean modules in the independent LengthGrowth project prove the
positivity of the full-angle numerator in the quartic period formula. With
`V(x)=(x⁴−x²−2x)/8`, the final theorem assumes `r>0` and equal potential
values at the two endpoints `c−r` and `c+r`. Its conclusion is

    ∫₀^π (c+r cos θ)/√((2c+r cos θ)²+2c²+r²−1) dθ > 0.

The proof derives the midpoint range and turning equation from equality of
the potential, pairs the two halves of the integral, and treats the two
ranges of the midpoint separately. When `0<c≤1/2`, the reduced angular
integral and its half-angle integral on `[0,1]` both exceed `4π/385`. The
pointwise estimates and the integral bounds are analytic. The scalar
quadrature used in the argument is an exact identity for all `A,B>0`,

    ∫₀^(π/2) dθ/(A² cos² θ+B² sin² θ) = π/(2AB).

For `c≥1/2` the paired terms have nonnegative sum throughout the half
interval, with strict positivity at its right endpoint.

Build `LengthGrowth.OscillatorPeriodNumerator` to check the full result.
The direct imports are `OscillatorPeriodNumerator → OscillatorMean →
{OscillatorMeanBounds, OscillatorScalarIntegral}`. All four modules belong
to the `LengthGrowth` namespace and the last two use only Mathlib.
The theorem `LengthGrowth.OscillatorMean.period_numerator_pos_of_equal_potential`
depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

Identification of the period integral with the time average of a solution
of the second-order oscillator equation uses the energy quadrature in the
accompanying mathematical proof. The subsequent compactness argument for a
universal threshold below one half is also given there as a human proof.
