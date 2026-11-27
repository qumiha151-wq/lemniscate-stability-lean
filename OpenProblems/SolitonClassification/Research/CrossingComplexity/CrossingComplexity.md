# A polynomial bound for self-intersections of closed elastic expanders

Let \(X:\mathbb R/L\mathbb Z\to\mathbb R^2\) be a smooth unit-speed closed free-elastic similarity expander. Translate its similarity centre to the origin and normalize its positive dilation coefficient to one. Let \(L\) be its least positive geometric arclength period. With \(T=X_s,\ N=JT,\ T_s=kN\), its equation is
\[
 F=k_{ss}+\tfrac12k^3=-p-\omega q,\qquad p=X\cdot N,\quad q=X\cdot T .
\]
Here \(J\) is counterclockwise rotation by \(\pi/2\) and \(\omega\) is any signed rotation coefficient.

**Theorem.** The number of ordered pairs of distinct labels with the same position satisfies
\[
 \#\{(s,t)\in(\mathbb R/L\mathbb Z)^2:s\ne t,\ X(s)=X(t)\}
 \ \le\ 3\big[1+2^{24}L(1+L)^2\big]^2 .
\]
An image point with \(j\) distinct preimages contributes \(j(j-1)\). Tangential intersections are included. For unnormalized dilation coefficient \(a>0\), the length in the bound is \(a^{1/4}\) times the original primitive length. A parametrization following the same traversal several times has infinitely many coincident label pairs.

## Uniform geometric estimates

Write \(U=1+L,\ E=\tfrac12\int k^2ds,\ D=\int F^2ds,\ M=\max|k|\) and \(V=\max|k_s|\). Integrals are over one primitive traversal. The established closed-curve stress estimate is \(M^6\le 2^{24}ED\). The normalized profile identities are \(D=E\) and \(\int kF\,ds=L\). For the latter, integrate \(q_s=1+kp\) and \(p_s=-kq\). For the former, integration by parts in \(W_s=FN,\ W=k^2T/2+k_sN\) against \(X\) and \(JX\) gives \(\int Fp=-E,\ \int Fq=0\). Cauchy–Schwarz and \(E\le LM^2/2\) now give
\[
 L/\sqrt2\le E\le 2^{21}L^3,\qquad L>2^{-11},\qquad M\le 2^{11}U .
\]
The closed noncircular pitch inequality \(16\omega^2\le 2EL\) yields \(|\omega|\le2^9 U^2\). For a primitive circle the count is zero, so it suffices to consider noncircular profiles. Integrating \(|k_{ss}|\le |F|+M^3/2\) from a critical point of the periodic curvature gives
\[
 V\le\sqrt{LE}+LM^3/2\le 2^{33}U^4 .
\]
The two quantitative input inequalities are recorded in the project notes *Elastic Stress, Curvature Concentration, and the Remaining Dynamic Obstruction*, equation (1), and *Rotation Rate and the Curvature Variance of a Closed Similarity Profile*, equation (1). [Stress estimate](../../../LengthGrowth/StressCoercivity.txt) · [Pitch estimate](../../Pitch/PitchOscillationBound.txt)

The centred position also has an explicit bound \(R=\max|X|\le 2^{20}U^2\). At a point \(s_0\) of maximum radius put \(C=(I+\omega J)X(s_0)\) and \(e=C/|C|\). A maximum of \(X\cdot e\) has \(N=\pm e\). On the following arc of length \(d=2^{-13}U^{-1}< L\), the bound \(|N_s|\le M\) gives \(|N\cdot e|\ge1-Md\ge1/2\). Therefore
\[
 \tfrac12\sqrt d\,|C|\le\|C\cdot N\|_2
 \le\sqrt E+\sqrt{1+\omega^2}\,L^{3/2}.
\]
The right inequality uses \(N\cdot(I+\omega J)X=-F\) and \(|X-X(s_0)|\le L\). Since \(|C|=\sqrt{1+\omega^2}\,R\), the displayed bound follows from \(R\le 2d^{-1/2}(\sqrt E+L^{3/2})\). Here \(R>0\) by regularity.

## The graph equation and the size of its coefficients

Use any positively oriented orthonormal coordinate frame with origin at the similarity centre. A graph \((x,f(x))\) is oriented locally by increasing \(x\). Reversal of arclength changes the signs of \(k,F,p,q\) together and leaves \(\omega\) fixed, so every branch satisfies the same equation in this orientation. Put \(u=f',v=f'',z=f'''\), \(g=\sqrt{1+u^2}\). Then \(k=v/g^3,\ \partial_s=g^{-1}\partial_x,\ p=(f-xu)/g,\ q=(x+fu)/g\). Differentiating twice gives
\[
 f''''=G(x,f,u,v,z)
 =\frac{10u}{1+u^2}vz+
   \frac{5/2-15u^2}{(1+u^2)^2}v^3
  -(1+u^2)^2\,[f(1+\omega u)+x(\omega-u)] .
\]
On a graph with \(|dx/ds|\ge1/2\), we have \(g\le2,\ |u|\le2,\ |v|\le8M\le2^{14}U\), and
\[
 |z|=\left|g^4 k_s+\frac{3u v^2}{g^2}\right|
 \le16V+6(2^{14}U)^2\le 2^{38}U^4 .
\]
Also \(|x|,|f|\le R\). These separate bounds define a rectangular box containing the straight interpolation between the jets of any two such graphs at a common \(x\).

The four partial derivatives on this box satisfy
\[
 |G_f|\le2^{15}U^2,\quad |G_u|\le2^{57}U^5,\quad
 |G_v|\le2^{44}U^4,\quad |G_z|\le2^{19}U .
\]
Indeed, writing \(A(u)=10u/(1+u^2)\), \(B(u)=(5/2-15u^2)/(1+u^2)^2\), we have \(|A|\le20,\ |A'|\le10,\ |B|\le63,\ |B'|\le564\). Thus \(|G_v|\le20|z|+189v^2,\ |G_z|\le20|v|\) and \(|G_f|\le25(1+2|\omega|)\). For \(G_u\), the last term of the graph equation contributes at most \(145R(1+|\omega|)\), since \(|(1+u^2)^2|\le25\) and \(|4u(1+u^2)|\le40\). The remaining terms contribute at most \(10|vz|+564|v|^3\). Substituting the geometric bounds yields the four claimed powers of two.

## Three intersections on each pair of short charts

Choose \(\delta=2^{-24}U^{-2}\). Divide the parameter circle into \(m=\lceil L/\delta\rceil\) intervals of equal length, assigning each endpoint to just one interval. For each pair of distinct intervals, choose an unoriented \(x\)-axis bisecting the smaller angle between their two middle tangent lines. That angle is at most \(\pi/2\). Throughout either closed chart the tangent makes an unoriented angle at most \(\pi/4+M\delta<\pi/3\) with this common axis. Each chart projects injectively onto an interval in \(x\), with \(|dx/ds|\ge1/2\). A single chart is injective by the same argument using its middle tangent as axis.

The common projection interval has length at most \(\delta\). Let \(h=f_1-f_2\) there. If \(h\) has four distinct zeros, Rolle's theorem supplies zeros of each of \(h',h'',h'''\). On the interval between the first and last of the four zeros the fundamental theorem of calculus gives
\[
 \|h^{(j)}\|_\infty\le\delta^{4-j}\|h''''\|_\infty,\qquad 0\le j\le 3 .
\]
Subtract the two graph equations and integrate their first derivatives along the straight interpolation of jets. The resulting bound for \(\|h''''\|_\infty\) is that same norm times a factor at most
\[
 2^{15}U^2\delta^4+2^{57}U^5\delta^3+
 2^{44}U^4\delta^2+2^{19}U\delta
 \le 2^{-81}+2^{-15}+2^{-4}+2^{-5}<1 .
\]
Hence the two graph functions agree on a nonempty open interval. Along that common arc both increasing-\(x\) arclength parameters have differential \(g\,dx\). In the original traversal their labels must therefore agree up to \(s\mapsto s+c\) or \(s\mapsto c-s\). The position is real analytic on the whole periodic extension, by the polynomial ODE for \((X,T,k,k_s)\). Either identity on an open interval extends to all \(s\). In the first case \(c\) is a geometric period. Primitivity makes the two labels identical modulo \(L\), contradicting the disjoint chart interiors. In the second case differentiation at \(s=c/2\) gives \(X'(c/2)=0\), contradicting unit speed. There are consequently at most three distinct common positions for each pair of charts. An overlap reduced to a single projection coordinate contributes at most one.

Each ordered pair of intersecting chart interiors or assigned endpoints therefore gives at most three ordered pairs of distinct labels. Counting over the \(m(m-1)\) ordered chart pairs proves the theorem, since \(m\le 1+L/\delta\). The proof gives a bound for all coincidences, with no transversality assumption. If two distinct branches are tangent, their local analytic graph difference has vanishing order at most three, since agreement of their graph jets through third order gives identical solutions of the fourth-order graph equation by uniqueness.

## Formal verification

Lean verifies the fourth-order graph equation along an actual normalized support profile at every point with nonvertical tangent. For two graph functions the difference satisfies the derivative-chain hypothesis used in the local argument. The real-variable modules prove that four ordered, distinct zeros on a sufficiently short closed interval force the difference to vanish throughout that interval. They include variable coefficients, an explicit contraction estimate at the stated chart size, and finiteness and cardinality at most three for the zero set of a nonidentical difference under the displayed derivative bounds. [Graph equation](../../SolitonClassification/GraphProfileEquation.lean) · [Fourth-order disconjugacy](../../SolitonClassification/FourthOrderDisconjugacy.lean) · [Finite zero sets](../../SolitonClassification/FourthOrderZeroCount.lean) · [Quantitative chart theorem](../../SolitonClassification/QuantitativeCrossingChart.lean)

The estimates for the four partial derivatives of the graph equation, the choice of a common chart axis, the primitive-period coincidence argument, and the assembly into the global ordered-pair bound are written proofs in this note. [Project verification](CrossingVerification.json)
