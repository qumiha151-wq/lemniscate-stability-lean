# From a static curvature gap to the actual flow

The four theorems in this module concern `LengthGrowth.ActualFlow.ForwardImmersion` with its existing `IsNormalFEF` condition. They use the material length $L$, energy $E$, squared-force integral $D$, length-variation integral $V$, signed curvature integral $S$ and signed cubic integral $C$ evaluated on the actual slice. Write $U=EL$, $b=2U$ and $G=|LC/(2E\sqrt b)|$.

The sole additional analytic input, `StrictHalfSliceGap ε`, quantifies over every smooth, regular, periodic material **position**. It asserts
$$
 |S|/\sqrt b\le\epsilon,\quad L^4(LD-EV)\le\epsilon b^3
 \quad\Longrightarrow\quad G\le1/2-\epsilon .
$$
This is the material-coordinate consequence of the spatial estimate in the strict-threshold manuscript. In RMS arclength, $s_0=S/\sqrt b$, $|h|=G$ and $e=L^4(LD-EV)/b^3$. The finite-window proof now supplies this spatial estimate for the explicit constant in Lean. The final flow theorems apply the transfer to that proved estimate. [Final flow theorems](../../LengthGrowth/ActualFlow/ExplicitCubicThreshold.lean)

For $g=1/2-\epsilon$, Lean checks the following implications.

- An entire tail with $G(t)>g$ implies `HasQuarterLengthBound` and `HasQuarterEnergyBound`. These provide constants specific to the given solution and bounds valid from $t=0$.
- The same conclusion follows from $\liminf G>g$, with the liminf taken in the extended reals.
- If $S(0)=0$, then $\liminf G\le g$.
- Existence of a single universal spatial $\epsilon\in(0,1/2)$ supplies one and the same $g\in(0,1/2)$ for both conclusions and all forward normal free elastic flows.

To prove the first implication, use an arbitrarily high, late maximum of $U$ if the length estimate fails. At that record $U'\ge0$, while $|S|/\sqrt b\le\epsilon$ and $G>g$ imply $L^4(-U')>\epsilon b^3$. This contradicts the sign of the derivative. At zero turning the latter inequality holds on the entire high-moment tail. The actual closed-curve bending lower bound $b\ge1$ suffices. If $L\le A(1+t)^{1/4}$, then $U+(\epsilon/A^4)\log(1+t)$ is nonincreasing on that tail. Its nonnegative energy-length contribution and its divergent logarithmic contribution contradict this.
