# The signed cubic half-threshold for a genuine length bound

For any smooth closed immersed planar free elastic flow use physical time and write
\[
E=\tfrac12\int k^2ds,\quad L=\int ds,\quad U=EL,\quad
R=\sqrt{2U},\quad C=\int k^3ds,\quad S=\int k\,ds .
\]
The signed turning integral $S$ is constant. The scale-invariant signed cubic ratio is $h=LC/(2ER)$. Equivalently, on the length-one rescaling, letting $B=2U$, it is $h=(L^2 C)/B^{3/2}$.

If $|h(t)|\ge g>1/2$ for every $t>T$, then
\[
EL(t)\le\max\left\{\max_{[0,T]} EL,\
                   \frac{S^2}{2(2g-1)^2}\right\}
\qquad (t\ge0).
\]
A finite product bound is equivalent on this flow to a global quarter-power length bound. Thus $\liminf_{t\to\infty}|h(t)|>1/2$ suffices. The proof uses neither a fixed sign for $h$ nor eventual pointwise curvature control.

For the proof let $A=2E$, $F=k_{ss}+k^3/2$, $D=\int F^2ds$ and $v=\int kF\,ds=L'$. The integral of $F$ is $C/2$ by periodicity. Write $G=4LF-Ak$ and $Z=L^{-1}\int G\,ds=(2LC-AS)/L$. Nonnegativity of $L\int(G-Z)^2\,ds$ gives the exact force estimate
\[
(2LC-AS)^2\le16L^2(LD-Ev)+LA^3.
\]
At a positive time which maximises $U$ over its entire past, its left difference quotients give $U'=Ev-LD\ge0$. Since $R^2=AL$, the estimate implies $|2LC-AS|\le AR$. The triangle inequality then gives
\[
2R|h|\le R+|S|.
\]
For records after $T$, this bounds $R\le|S|/(2g-1)$. Maximising over each finite prefix proves the barrier. The identical argument shows that any counterexample to the quarter-power upper bound has arbitrarily late record times with arbitrarily large $U$ and
\[
|h|\le \tfrac12+\frac{|S|}{2\sqrt{2U}}.
\]
In particular, for any prescribed $K,T$ and $\varepsilon>0$ a record can be chosen with $t>T, U>K, |h|<1/2+\varepsilon$.

The Lean module gives these results in the actual arbitrary-speed material parameter. Its geometric inputs are previously proved identities for the same flow. It supplies both the eventual-margin statement and the extended-real lower-limit statement, which includes an infinite lower limit.
