# Collapse of the entire length-normalized trace on a positive energy plateau

Let \(X\) be one smooth closed immersed planar free elastic flow, \(E=\int k^2\,ds/2\), \(D=\int (k_{ss}+k^3/2)^2\,ds=-E'\), and \(L=\int ds\). For a fixed point \(O\), write \(R_O(t)=\max_u|X(t,u)-O|\) and \(\overline R_O(t)=\max_{1\le s\le t}R_O(s)\). We use ordinary physical time. For every such flow,
\[
 \int_2^\infty \frac{\overline R_O(t)^6}{t^3(\log t)^3}\,dt<\infty,\qquad
 \int_2^\infty
 \left(\frac{E(t)^2\overline R_O(t)}{L(t)}\right)^{2/3}
 \frac{dt}{t\log t}<\infty.                                           \tag{1}
\]
In particular, if the diameter is at least \(\varepsilon L(t)\) on a set of times with infinite \(dt/(t\log t)\) measure, then \(E(t)\to0\). For the diameter condition at every sufficiently large time, (1) and the monotonicity of \(E\) give \(E(t)=o((\log\log t)^{-3/4})\).

A positive limit \(E_\infty>0\) gives stronger estimates:
\[
 \int_2^\infty \left(\frac{t^{1/3}}{L(t)}\right)^{3/7}\frac{dt}{t}<\infty,\qquad
 \int_2^\infty
 \left(\frac{\overline R_O(t)}{L(t)}\right)^{2/5}
 \frac{dt}{t(\log t)^{1/5}}<\infty.                                  \tag{2}
\]
For each \(\varepsilon>0\), the times at which the normalized radius exceeds \(\varepsilon\) have finite measure for this second weight. In particular their ordinary logarithmic measure up to \(T\) is \(o((\log T)^{1/5})\). The first integral forces \(\limsup_{t\to\infty} L(t)/(t^{1/3}(\log t)^{7/3})=\infty\). Both conclusions concern a hypothesized positive energy plateau.

For every \(n\ge2\), choose any time \(\tau_n\in[1,2^n]\) maximizing \(E(s)L(s)\) on that interval. The whole-curve radii at these records satisfy
\[
 \sum_{n\ge2}\frac1{n^{1/5}}
     \left(\frac{R_O(\tau_n)}{L(\tau_n)}\right)^{2/5}<\infty
 \quad\text{if }E_\infty>0.                                            \tag{3}
\]
Consequently there are escaping records at which the full normalized images converge uniformly to a point, independently of parametrization. For each fixed tolerance the number of exceptional indices up to \(N\) is \(o(N^{1/5})\). The preceding [record bending theorem](BendingMassAtRecords.md) gives concentration of the *bending probability* at every escaping global record. The [tree-like limit theorem](TreeLikeRecordLimits.md) permits nonconstant tree-like limits at individual records. Equations (2) and (3) allow such limits on sufficiently sparse subsequences. They leave the unrestricted quarter-power length bound and the existence of a positive-energy plateau open.

## Physical exponential moment and finite time budget

On \(t\ge1\) let \(d(t)=(2^{24}E(t)D(t))^{1/3}\), \(B(t)=\int_1^t d(s)\,ds\). On every finite horizon \(T\ge1\),
\[
 \frac{B(T)^3}{T^2}+\int_1^T (B(t)/t)^3dt
       \le 2^{25}\bigl(E(1)^2-E(T)^2\bigr).                           \tag{4}
\]
In fact for \(y=B/t\), the derivative of the boundary term is \(3y^2d-2y^3\), and \(y^3-3y^2d+4d^3=(y-2d)^2(y+d)\ge0\). The energy law absorbs \(4d^3\). [Physical clock estimate](../../LengthGrowth/ActualFlow/RadiusMomentClock.lean)

The physical weighted-energy and point-detection theorems give, uniformly in the material label, \(a|X(s,u)|\le C-2\log a+256(a^4s+a^2B(s))\) for \(1\le s\) and \(0<a\le1\). At a late horizon \(t\) put \(h=\log t\) and \(v=\max(1,(t/h)^{1/4},(B(t)/h)^{1/2})\). The hypotheses \(h\ge1\), \(B(t)\le t^2\) hold eventually: Hölder gives \(B(t)\le C t^{2/3}\) since \(\int d^3<\infty\). Then \(1\le v\le t\). Taking \(a=1/v\) bounds both physical terms by \(h\) for all \(1\le s\le t\), and \(-\log a\le h\). Including the fixed translation \(O\) gives
\[
 \overline R_O(t)\le C_O\left[h+t^{1/4}h^{3/4}+\sqrt{B(t)h}\right]. \tag{5}
\]
[Physical estimate for every earlier image](../../LengthGrowth/ActualFlow/RadiusMomentEnvelope.lean) · [Exponential moment and local point detection](../SpatialLocalization/ExponentialLocalization.md)

Raise (5) to the sixth power and divide by \(t^3 h^3\). The first two terms give integrable multiples of \(h^3/t^3\) and \(h^{3/2}/t^{3/2}\). Equation (4) integrates the third. This proves the first part of (1). The physical dilation identity around \(O\) gives \(E(t)^2\le D(t)L(t)R_O(t)^2\le D(t)L(t)\overline R_O(t)^2\). Hölder with exponents 3 and \(3/2\), applied to the first part of (1) and \(\int E^2/(L\overline R_O^2)\le\int D<\infty\), proves the second. The radius is positive because each slice is an immersion. For the decay rate under persistent normalized diameter, use \(R_O\ge\operatorname{diam}(X)/2\) and integrate the resulting nonincreasing function \(E^{4/3}\) on the last half-interval of the variable \(\log\log t\).

## Localized bending and logarithmic time

Assume \(E_\infty>0\). The cut-off dilation test in the [bending concentration theorem](BendingMassAtRecords.md) supplies
\[
 D(t)\ge c/(L(t)H(t)^2),\qquad
 H(t)=1+\int_1^t(D^{2/3}+D^{3/4})\,ds+
                 \left(\int_1^t D^{1/2}\,ds\right)^{1/2}.            \tag{6}
\]
Starting at time one changes the comparison constant only. The [force persistence estimate](../ForcePersistence/ForceDissipationPersistence.md) makes \(D\) bounded on this half-line. Thus \(D^{3/4}\le C D^{2/3}\), and the last term of \(H\) is \(O(t^{1/4})\) by Cauchy–Schwarz. Set \(G(t)=\int_1^t D^{2/3}\,ds\). Then
\[
 \int_2^\infty \left(\frac{H(t)}{t^{1/3}}\right)^{3/2}\frac{dt}{t}<\infty. \tag{7}
\]
For clarity, the contribution of \(G\) is \(\int(G/t)^{3/2}dt\). Put \(z=G/t\) and \(d_1=D^{2/3}\). Differentiating \(G^{3/2}/\sqrt t\) gives \((3/2)\sqrt z\,d_1-z^{3/2}/2\). The inequality \((3/2)\sqrt z\,d_1\le z^{3/2}/4+5d_1^{3/2}\) follows by considering \(z\ge 6d_1\) and its complement. Consequently \(\tfrac14\int (G/t)^{3/2}\,dt\le5\int D\,dt\), and the boundary term subtracted at the upper endpoint is nonnegative. The other contributions to (7) decay at least as fast as \(t^{-1/8}\) against \(dt/t\).

With \(U=t^{1/3}/L\), \(V=H/t^{1/3}\), (6) says \(U/V^2\le C tD\). The latter is integrable against \(dt/t\). Multiply its \(3/7\) power by \((V^{3/2})^{4/7}\) and apply Hölder and (7). This proves the first part of (2). Against the same measure the first part of (1) means \(\overline R_O/(t^{1/3}\sqrt{\log t})\) has integrable sixth power. Multiply by \(U\) and use \(1/(2/5)=1/6+1/(3/7)\), using ordinary Hölder on the \(2/5\) power. This proves (2).

## Passing to record times

The estimates just proved for \(\overline R_O(t)\) in (1) and (2) remain valid with \(\overline R_O(2t)\) in the radius factors: the sixth-power estimate follows by the substitution \(s=2t\); the factors comparing the logarithms on \(t\ge2\) are bounded. Combine it again with the first part of (2). For \(t\in[2^{n-1},2^n]\), the positive plateau gives
\[
 L(\tau_n)=\frac{\max_{1\le s\le2^n} E(s)L(s)}{E(\tau_n)}
          \ge \frac{E_\infty}{E(1)}L(t),\qquad
 R_O(\tau_n)\le\overline R_O(2t).
\]
Integrating over each dyadic interval proves (3) since its \(dt/[t(\log t)^{1/5}]\) measure is comparable to \(n^{-1/5}\). For fixed tolerance, split any cumulative exceptional measure or count at a large fixed threshold. The remaining unweighted mass is at most the terminal inverse weight times an arbitrarily small weighted tail. This yields both stated little-o estimates. The running record levels must diverge by the first part of (2), so the selected records escape every compact time interval.

## Intersections with straight lines

These estimates force actual line crossings on a positive plateau. Fix any two orthogonal unit vectors. For at least one of them, denoted by \(v\), the projected variation \(V(v)=\int|v\cdot T|\,ds\) is at least \(L/2\), because the sum of the two integrands is at least one. For every unit \(w\) with \(|w-v|\le1/8\) one has \(V(w)\ge3L/8\). The one-dimensional area formula for the smooth periodic function \(w\cdot(X-O)\) gives \(V(w)=\int N_w(h)\,dh\), where \(N_w(h)\) counts preimages. Regular values have full measure and all relevant heights lie in an interval of length at most \(2R_O\). Some regular line therefore has at least \(L/(8R_O)\) transverse crossings. At that level the signs alternate cyclically, so at least \(L/(16R_O)\) crossings occur in each direction. Multiplicity here counts material labels, including different traversals of the same point.

In particular, suppose that on a set of times of infinite \(dt/[t(\log t)^{1/5}]\) measure the regular lines in each of two fixed orthogonal foliations have at most a common finite number of intersections. Then \(E_\infty=0\) by (2). Along the collapsing record subsequences of (3), one entire angular interval of possible line normals at each slice realizes unbounded crossing counts.

Lean verifies (4) directly from the forward material flow and the finite-horizon position estimate underlying (5). The integrations on the infinite half-line, the application of localized bending and the selection of record times are the written arguments above.
