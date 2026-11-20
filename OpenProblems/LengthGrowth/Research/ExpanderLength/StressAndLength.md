# Elastic stress and the length of closed expanders

For a smooth closed planar immersion, let $s$ denote arclength, $L$ its length, $T$ its unit tangent, $N=JT$ its unit normal and $k$ its signed curvature. Define $F=k_{ss}+k^3/2$, $E=\frac12\int k^2\,ds$, $D=\int F^2\,ds$, $W=(k^2/2)T+k_s N$ and $M=\max |W|$.

Every such immersion satisfies

$$
 M\le c\sqrt{LD},\qquad
 c=\frac{3}{2\pi}+\frac{1}{\sqrt{12}}<1. \tag{1}
$$

Suppose the curve is a pure homothetic expander with dilation coefficient one. At any curvature-zero point with marked derivative $b=k_s$, every positive full period $L$, including the primitive period, satisfies

$$
 EL\ge b^2/c^2,\qquad L^2\ge 2\pi |b|/c. \tag{2}
$$

The bounds hold for any turning number and any location of the marked point. Together with the unbounded centre-marker theorem, they give geometrically distinct primitive zero-turn flows with unbounded asymptotic fourth-root length coefficient. Their initial lengths can all be scaled to one. An upper estimate for that coefficient therefore requires more information than the initial length and turning number. The selected shooting family also admits finer large-marker asymptotics. [Unbounded centre-marker theorem](../../../SolitonClassification/SolitonClassification/UnboundedClosedExpanders.lean) · [Asymptotics for the shooting family](../../../SolitonClassification/Research/ReflectedScattering/InfinitelyManyZeroTurnExpanders.md)

## A stress identity on an arbitrary closed slice

The Frenet equations give $W_s=FN$ and $(kN)_s=k_sN-k^2T$. The average of the second derivative expression over a full period vanishes. Consequently

$$
 \left|\int W\,ds\right|=\frac32\left|\int k^2T\,ds\right|\le 3E.
$$

For any marked position $s$, integrate the derivative of $(u-L/2)W(s+u)$ from zero to $L$. The boundary difference is $LW(s)$. Since $\int_0^L(u-L/2)^2\,du=L^3/12$, Cauchy–Schwarz gives

$$
 L|W(s)|\le3E+\sqrt{L^3D/12}. \tag{3}
$$

Translate the position $X$ by its arclength centroid. Since $W_s=FN$ and $W\cdot T=k^2/2$, integration by parts gives $E=-\int F X\cdot N$. Cauchy–Schwarz and periodic mean-zero Wirtinger yield $E^2\le D\int|X|^2\le DL^3/(4\pi^2)$. Substitution in (3) proves (1). For an expander about $O$, $F=-(X-O)\cdot N$. The same integration by parts about $O$ gives $E=D$. Formula (2) follows from (1) and $E\le L^3/(4\pi^2)$. [Sharp virial inequality in Lean](../../LengthGrowth/ActualFlow/SharpVirial.lean)

In physical time, $L(t)=(1+4t)^{1/4}L$ for these normalized expanders, so their asymptotic coefficient is $4^{1/4}L$. A spatial dilation by $d>0$ sends $L(t)$ to $dL(t/d^4)$ and preserves the coefficient. A positive primitive period exists because the additive group of periods of a nonconstant continuous periodic immersion is closed and discrete. Applying (2) directly to that period removes dependence on covering multiplicity.

For every pure closed expander, its coefficient $C_\gamma=\lim_{t\to\infty}L(t)/t^{1/4}$ and the scale-invariant quantity $U=EL$ satisfy

$$
                        16\pi^2 U\le C_\gamma^4\le 8U^2.                 \tag{5}
$$

Indeed, $\int kF=L$ follows by integrating $(X\cdot T)_s=1+kX\cdot N$ about the expansion centre. Since $D=E$, Cauchy–Schwarz gives $L^2\le2E^2$. This proves the upper bound, and the preceding virial bound $E\le L^3/(4\pi^2)$ proves the lower one. A once-covered circle gives equality on both sides. Multiple circle covers retain equality on the upper side and can have arbitrarily large $U$. The selected primitive zero-turn family has $U\asymp b^2$ and $C_\gamma^4\asymp b^2$, so the power of $U$ in the lower bound also has the correct order at large $U$. These calculations distinguish fixing initial length alone (or energy alone) from bounding their product. Both $U$ and $C_\gamma$ survive a simultaneous geometric rescaling.

The same estimates (2) and (5) also hold for any rotating and dilating closed profile, if one exists, at dilation coefficient one and arbitrary angular coefficient $\omega$. Write $p=X\cdot N$, $q=X\cdot T$ about its similarity centre. The equation is $F=-p-\omega q$. Since $(W\cdot JX)_s=Fq+k_s$ and $p_s=-kq$, periodicity yields $\int Fq=\int kq=0$. The dilation identity again gives $D=-\int Fp=E$ and $\int kF=-\int kp=L$. Rotation preserves the physical dilation law for length. This extension uses no existence or classification assertion about rotating solutions.

There is also a diameter conclusion for profiles meeting their centre. The period-independent stress-window estimate gives $M\le C(B^{2/3}+RB)$ when $|X-O|\le R$ and $|F|\le B$. For a pure coefficient-one expander take $R=\max|X-O|$ and $B=R$. The radius bound $R\ge 2^{-1/4}$ absorbs $R^{2/3}$ into a constant times $R^2$. Since the centre lies on the curve, its diameter is at least $R$, hence is at least a universal constant times $\sqrt{|b|}$. [Radius and stress-window estimates](../../../SolitonClassification/Research/RadiusBounds/UniformRadiusGapAllPitches.md)

## Constraints on a single flow

Along any smooth forward free-elastic flow $E'=-D$. From (1), for $t_1<t_2$,

$$
 \int_{t_1}^{t_2}\frac{M(t)^2}{L(t)}\,dt
 \le c^2\big(E(t_1)-E(t_2)\big). \tag{4}
$$

For example, on disjoint time intervals $I_j$, suppose an approximate profile has stress at least $a b_j/d_j^2$ and length at most $A d_j\sqrt{b_j}$ throughout, for constants $a,A>0$. Here $d_j$ is its spatial scale and $b_j>0$ its target marker. Then

$$
 \sum_j \frac{|I_j|}{d_j^4}\frac{b_j^{3/2}}{d_j}
 \le \frac{A c^2}{a^2} E(0).
$$

Repeated approximations of prescribed relative duration therefore carry a summable dissipation cost. This condition still permits spatial scales to increase arbitrarily rapidly. Each exact expander separately obeys fourth-root growth. Uniqueness of forward evolution keeps an exactly attained expander on its own homothetic motion.

A diagonal limit of the exact initial profiles also faces a scale-invariant obstruction. Under any similarities and regular reparametrizations, their products $EL$ still diverge by (2). Regular $C^2$ convergence to a closed immersion would make $L$ and $E$ converge to finite limits. With unit length and constant speed the identity $\int_0^1|X_{uu}|^2\,du=2E$ even precludes boundedness in $W^{2,2}$. This limits compactness arguments that start with the exact expanders as initial data. It does not preclude a different smooth initial curve developing complicated shapes at later times.

There is a separate obstruction to placing infinitely many complete templates on disjoint portions of one smooth initial immersion. The tangent image of every regular closed plane curve contains antipodal directions. Otherwise that connected compact subset of the circle lies in an open semicircle, contradicting zero net displacement. An arc following the complete tangent field of a template with uniform angular error at most $\pi/4$ consequently contributes at least $\pi/2$ of absolute turning, whatever its scale. A smooth closed initial curve has finite total absolute curvature. This rules out the proposed spatial assembly on disjoint arcs at a single time. Whether one genuine flow can grow faster than fourth-root length at arbitrarily large times remains open.

## Formal verification

The [length module](../../LengthGrowth/ActualFlow/PointStress.lean) verifies (1), both inequalities in (2) for an actual homothetic position, and the finite-time dissipation bound for every integrable trace of measured stresses. Taking the continuous spatial maximum on a smooth time slab gives (4). The link from the separate expander existence theorem to the unbounded primitive growth coefficients, the diameter estimate, and the compactness and assembly arguments are mathematical deductions in this note. [Kernel verification](PointStressVerification.json)
