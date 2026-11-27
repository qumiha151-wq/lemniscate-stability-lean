# Physical width and energy–length growth

Let \(X\) be a smooth closed planar free elastic flow, \(L\) its length, \(E=\frac12\int k^2\,ds\) its bending energy, and \(D=\int(k_{ss}+k^3/2)^2\,ds\) its dissipation. Time, curvature and width below are measured in the original plane. All statements allow arbitrary turning number, repeated traversals and self-intersections.

## Uniform straightening and width

Every trajectory has a finite constant \(C\) such that \(D(s+1)\le C[E(s)-E(s+1)]\) for \(s\ge1\). In particular \(D(t)\to0\), and
\[
\sup_u |k(t,u)|+\sup_u|k_s(t,u)|\longrightarrow0 .
\]
The proof bounds \(D\) on a positive tail and derives \(D'\le K D\) there from the actual force equation. Since \(E'=-D\), \(D+K E\) decreases. Comparing the end of a unit interval to a minimum-dissipation point on that interval gives the displayed inequality. The pointwise stress estimates then give both uniform limits, even when the limiting value of \(E\) is unknown. [Uniform straightening proof](../../LengthGrowth/ActualFlow/UniformStraightening.lean)

For any fixed half-width \(r>0\), every sufficiently late image escapes every strip of that half-width. The strip centre and direction may be chosen separately for each time. There is also a quantitative conclusion. For every \(0<s<t\), one time \(u\in[s,t]\) works simultaneously for all strips containing \(X(u)\). Each such strip of half-width \(r\) satisfies
\[
2(t-s)\ \le\ 2^{24}(8r)^6\big(E(s)^2-E(t)^2\big).
\]
Indeed, closing a regular curve inside such a strip forces \(8r\,|k|\ge1\) somewhere. At each material point \(|k|^6\le 2^{24}ED\). Select a minimum of \(ED\) on the time interval and integrate \(-(E^2)'=2ED\). As a consequence, for every \(A>0\) and every sufficiently late interval \([s,2s]\), there is some \(u\in[s,2s]\) for which **no strip of half-width \(A u^{1/6}\)** contains the curve. Bending energy is monotone and bounded below, so its squared drop on these intervals tends to zero. [Physical width proof](../../LengthGrowth/ActualFlow/ExpandingPhysicalWidth.lean)

## How fast the energy–length product can increase

Set \(U=EL\) and \(\eta=LU'/E^3\). For every positive time the sharp universal estimate
\[
\eta\le\tfrac12-\pi^2/U
\]
holds. A circle traversed once attains equality. To see the geometric origin of the deficit, set \(G=k_{ss}+k^3/2-Ek/(2L)\). The first variations give \(\frac12-\eta=L^2\int G^2\,ds/E^3\). For every translation \(z\in\mathbb C\) and angular coefficient \(\omega\in\mathbb R\), the identity
\[
\int G\,\langle N,(1+i\omega)X-z\rangle\,ds=-E/2
\]
bounds from below the product of the deficit and the squared normal support moment. The inequality persists after taking the infimum over \(z,\omega\). A centred Wirtinger inequality gives the coefficient \(\pi^2\). With \(R\) the least enclosing radius, the same calculation yields \(R^2\ge L/[2E(1-2a)]\) whenever \(a<1/2\) and \(\eta\ge a\). [Support identity](../../LengthGrowth/ActualFlow/SaturationSupport.lean) · [Physical growth inequality](../../LengthGrowth/ActualFlow/PhysicalSaturationGap.lean) · [Radius and circle equality](../../LengthGrowth/ActualFlow/SaturationRadius.lean)

The width result allows the direction of the thin strip to vary arbitrarily, and the times giving super-sixth-root width may depend on the threshold \(A\). The unrestricted fourth-root upper bound for the length of a single flow remains open. [Independent Lean project verification](Verification.json) · [Original open problems](https://arxiv.org/html/2404.12619v3#S1.SS2)
