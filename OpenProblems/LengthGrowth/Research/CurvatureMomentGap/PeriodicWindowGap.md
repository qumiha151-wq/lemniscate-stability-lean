# From a deterministic window comparison to the scalar strict half-gap

For a smooth real function \(u\) of arbitrary positive period \(P\), write \(\langle f\rangle=P^{-1}\int_0^P f\), \(v=u''+u^3/2\), \(R=v-u/4-1/4\), and \(e=\langle v^2\rangle-\langle uv\rangle/2\). All translates use the function on the real line, so a window can cross any number of periods.

## Formal statement

Fix \(0<m\le1\), \(T>0\), and \(\tau>0\). Define
\[
 \epsilon=\min\{1/8,\ m/16,\ m^2\tau^2/(1024T^2)\}.
\]
The theorem `scalar_strict_half_gap` proves \(0<\epsilon<1/2\) via its two companion lemmas and gives
\[
 \langle u^2\rangle=1,\quad |\langle u\rangle|\le\epsilon,\quad e\le\epsilon
 \quad\Longrightarrow\quad |\langle u^3\rangle|\le1/2-\epsilon
\]
under the single deterministic hypothesis `OscillatorWindowComparison m T (τ²/T)`. This hypothesis quantifies over smooth real functions. At each origin \(x\), put \(M=\int_x^{x+1}(u^2+R^2)\), \(B=\int_x^{x+T}R^2\), and \(a=T^{-1}\int_x^{x+T}u\). If \(M\le512/m^2\) and \(B\le\tau^2/T\), it requires \(a\ge-m/8\), strengthened to \(a\ge7m/8\) when \(M\le8\). The companion oscillator and ODE comparison results are meant to supply this hypothesis.

## Verified integral estimates

- Fubini and translation invariance over a period give \(\langle a\rangle=\langle u\rangle\). Integrating nonnegative variance gives \(\langle a^2\rangle\le\langle u^2\rangle\).
- Normalised indicator integrals equal the restricted Lebesgue measure divided by the period. Markov bounds control both the unit local mass and the residual integrated over the length-\(T\) window.
- Given the corresponding global bounds, the bad fraction is at most \(m^2/64\). The fraction with \(M\le8\) and both window tests passing is at least \(1/2\). Completing a square bounds the bad contribution to \(\langle a\rangle\) below by \(-m/8\). Thus \(\langle u\rangle\ge m/4\).
- The proof uses the actual second derivative in \(v\). Periodicity of \(u'\) and the fundamental theorem of calculus give \(\langle v\rangle=\langle u^3\rangle/2\). Expansion yields
  \[
  \langle R^2\rangle=e+(1-2\langle u^3\rangle+\langle u\rangle)/8
  \]
  at \(\langle u^2\rangle=1\). A violation of the positive cubic bound implies \(\langle R^2\rangle\le2\epsilon\), so the global window argument contradicts the small signed mean. Applying the same argument to \(-u\) proves the absolute cubic bound.

The deterministic comparison covers one window and has no origin-fraction, periodic-average, or global cubic-gap premise. The module imports the established derivative-periodicity theorem from the length-growth project. The translation from these scalar quantities to material-coordinate curve integrals belongs to its geometric adapter.

The integrated flow theorem supplies this deterministic comparison in `actual_window_comparison` and proves the material estimate in `static_gap`. [Integrated Lean theorems](../../LengthGrowth/ActualFlow/ExplicitCubicThreshold.lean)
