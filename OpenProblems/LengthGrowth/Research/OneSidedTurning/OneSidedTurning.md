# One-sided motion of inflection tangents and fourth-root length growth

Let a single smooth closed immersed curve evolve by the planar normal free elastic flow. Write $T=(\cos\theta,\sin\theta)$, $k=\theta_s$, $F=k_{ss}+k^3/2$, $E=\frac12\int k^2\,ds$, $L=\int ds$ and $D=\int F^2\,ds$. Derivatives indexed by $s$ use current arclength, while $\theta_t=-F_s$ holds on fixed material labels. Use the angle lift on the universal cover of the parameter circle. Its increment over one period is the fixed total signed turning $S$.

On each time slice introduce two compact sets and a nonnegative rate,
$$
 Z_{\max}=\{k=0,\ k_s\le0\},\qquad Z_{\min}=\{k=0,\ k_s\ge0\},\qquad
 P(t)=\left[\max_{Z_{\min}}F_s-\min_{Z_{\max}}F_s\right]_+.
$$
Set $P=0$ when either set is empty. Each true local angle maximum belongs to $Z_{\max}$ and each local minimum belongs to $Z_{\min}$. Vanishing higher derivatives and flat points are allowed. Since $F_s=k_{sss}$ at $k=0$, this rate can be read from the curvature jet at inflections.

**Theorem.** If $\int_T^\infty P(t)\,dt<\infty$ for some $T>0$, then this particular flow satisfies $L(t)=O((1+t)^{1/4})$. More precisely, write $m_\delta(t)$ for the largest number of interior-disjoint oriented arcs whose absolute net turning is at least $\delta>0$. For $t\ge a>0$ one has
$$
 m_\delta(t)\left(\delta-\int_a^t P(r)\,dr\right)\le \int |k(a)|\,ds. \tag{1}
$$
This one-sided estimate permits the angular oscillation to contract freely. The earlier two-sided criterion uses the full oscillation of $F_s$ on the zero set. [Earlier two-sided estimate](../CriticalInflectionDensity/InflectionAngularVelocity.md)

## Optimizing over disjoint arcs

For $n\ge1$ let $V_n^+(t)$ be the largest sum of net angle increases on at most $n$ oriented, interior-disjoint arcs in one traversal. Endpoints may coincide. A lift of the endpoint list can be written $u_1\le v_1\le\cdots\le u_n\le v_n\le u_1+1$, using material period one, and the objective is $\sum(\theta(t,v_i)-\theta(t,u_i))$. Take $u_1\in[0,1]$ to obtain a compact parameter space independent of time. The maximum exists. Replacing the increments by their negatives defines $V_n^-$. Taking complementary gaps yields $V_n^+-V_n^-=S$ since their signed increases sum to $S$. In particular when $S\ne0$ an entire-period arc must be allowed. A configuration with all its arcs collapsed and a configuration covering the entire circle are both included.

On a compact time interval the objective is uniformly Lipschitz in time. For any optimal endpoint list at a given time, delete zero-length arcs and merge consecutive arcs with zero gap, also across the cyclic seam. These operations preserve its objective at *all* times for this fixed endpoint list. If the reduced list is empty or the full circle the objective is constant in time. Otherwise every endpoint is surrounded by positive arc and gap lengths, so its position can be varied independently on the circle. Optimality makes each right endpoint a local angle maximum and each left endpoint a local minimum. Writing $j\le n$ for the remaining arcs, the time derivative of their objective at fixed endpoints is bounded above by $jP(t)$. This assertion uses the values at the time of optimization and does not differentiate any optimizing positions.

For clarity, take maximizers at $t+h$, extract a convergent subsequence as $h\downarrow0$, and use continuity to see that its limit maximizes at $t$. The difference $V_n^+(t+h)-V_n^+(t)$ is bounded above by the change of the objective at the maximizing endpoint list held fixed. Uniform continuity of its time derivative gives the same bound $nP(t)$ for the upper right derivative. Both zero sets have closed graphs on a compact time slab. Taking convergent subsequences of maximizing and minimizing labels shows $P$ is upper semicontinuous, including times when one set is empty. Thus $P$ is measurable and locally bounded. Integrating the derivative bound for the Lipschitz function $V_n^+$ gives
$$
 V_n^\pm(t)\le V_n^\pm(a)+n\int_a^t P(r)\,dr. \tag{2}
$$
The complement identity gives the negative version without an additional angular speed.

Split a maximizing $\delta$-excursion family into $n_+$ positive arcs and $n_-$ negative arcs. Apply (2) to each nonempty group. Their initial upper bounds are $\int k_+(a)\,ds$ and $\int k_-(a)\,ds$, respectively. This proves (1). If $P$ is integrable, choose $a$ large enough that $\int_a^\infty P<1/8$. Formula (1) bounds $m_{1/4}(t)$ uniformly thereafter. The arclength record theorem forces $m_{1/4}$ to be unbounded on arbitrarily late product records of any solution failing fourth-root growth. This proves the theorem. [Turning excursions and the genuine flow record estimate](../CriticalInflectionDensity/MacroscopicTurningAndQuarterGrowth.md)

## A fourth-order dissipation cost involving both kinds of inflection

At times when $P>0$, choose a pair attaining the two extrema in its definition. Let $\ell$ be the arclength of either connecting arc and put $R=\ell(L-\ell)/L$. Use the smallest such $R$ among extremizing pairs and put $R=0$ when $P=0$. Then $0\le R\le L/4$. The minimum exists by compactness and is measurable. One way to check measurability is to take the compact subsets with the zero-set constraints and $F_s(u)-F_s(v)\ge P(t)-1/j$: their graphs are Borel with compact sections, so their infima of the continuous resistance are Borel; the increasing minima converge to the exact minimum on $\{P>0\}$. The weaker replacement $R=L/4$ needs no choice of pairs.

Set
$$
 Y=\int F_{ss}^2\,ds,\qquad
 Y_+=\inf_{\lambda\ge0}\int(F_{ss}+\lambda k_{ss})^2\,ds. 
$$
This is an explicitly computable quadratic minimum, equal to $Y-[-\int F_{ss}k_{ss}]_+^2/\int k_{ss}^2$ when the denominator is positive and to $Y$ otherwise. The sign conditions on $k_s$ imply that the difference of $F_s+\lambda k_s$, from the maximum-label to the minimum-label, is at least $P$. On each complementary arc Cauchy–Schwarz bounds its squared difference by that arc's length times the integral of $(F_{ss}+\lambda k_{ss})^2$. Adding the two resulting lower bounds for the integral and minimizing over $\lambda\ge0$ proves
$$
             P^2\le R\,Y_+\le R\,Y. \tag{3}
$$
Consequently a directly measurable sufficient condition for fourth-root growth is $\int_T^\infty\sqrt{R Y_+}\,dt<\infty$.

There is an additional statement using the known weighted dissipation bound $\int_T^\infty D^{-2/3}Y\,dt<\infty$. Define $R_{\rm eff}=R\,Y_+/Y$ where $Y>0$, setting it to zero otherwise. If $\int_T^\infty R_{\rm eff}D^{2/3}\,dt<\infty$ the theorem applies by Cauchy–Schwarz. If a single flow fails fourth-root growth, there are consecutive, disjoint-interior time intervals $I_j$ starting after any fixed $T>0$ such that
$$
 \int_{I_j}P\,dt\ge 1/8,\qquad
 \sum_j\left(\int_{I_j}R_{\rm eff}D^{2/3}\,dt\right)^{-1}
       \le64\int_T^\infty D^{-2/3}Y\,dt <\infty. \tag{4}
$$
Indeed choose the next record so that $m_{1/4}$ exceeds $8\int |k|\,ds$ on the previous slice. Formula (1) forces the claimed angular cost. On each such interval (3) and Cauchy–Schwarz give $(\int P)^2\le(\int R_{\rm eff}D^{2/3})(\int D^{-2/3}Y)$. Summation proves (4). Each integral in the left-hand sum is strictly positive. The quantity in parentheses must grow without bound down this sequence, even though the total weighted fourth-order dissipation is finite. [Weighted dissipation along a single flow](../ForcePersistence/ForceDissipationPersistence.md)

## A strict distinction on actual flows

For fixed $A>1$ and any even positive integer $m$, set $k(s)=1+A\cos(ms)$ on the initial arclength circle $\mathbb R/(2\pi\mathbb Z)$. Integration gives $\theta(s+\pi)=\theta(s)+\pi$ and $T(s+\pi)=-T(s)$, so $X=\int T\,ds$ is a closed unit-speed immersion with this precise curvature. At every zero $k_s\ne0$ and $F_s=k_{sss}=-m^2k_s$. The material angular velocities $-F_s$ at all local angle maxima are negative and those at all minima are positive. Thus $P=0$ whereas the full inflection velocity oscillation equals $2m^3\sqrt{A^2-1}$. Compactness, smooth short-time evolution, and persistence of the finitely many simple zeros preserve the strict ordering on a positive time interval. The same inward motion can therefore have arbitrarily large two-sided angular cost density and zero one-sided cost density on genuine flow slices. In an exact rotating or dilating similarity solution all the inflections move at the same angular speed and $P=0$. [Global smooth existence from a closed immersion](https://arxiv.org/html/2404.12619v3#S1)

The long-time integrability of $P$ or of either sufficient right-hand side in (3)–(4) has not been shown for arbitrary data. The known examples creating many sign changes or many one-sign arcs cheaply are compatible with (1) because the earlier longer arcs can already have substantial net angular excursions. These one-sided conditions and weighted time-window costs are analytic deductions. [Inflection births](../FiniteSignChanges/InflectionBirths.md) · [Angular-lobe births](../CriticalInflectionDensity/AlternatingAngularBirths.md)

The one-sided rate itself can be arbitrarily large at fixed energy and length. In the preceding periodic construction replace $\cos x$ by $h(x)=\cos x+\frac19\cos(3x)$ and fix $A=6$. Write $c=\cos x$. Then $h=\frac23c+\frac49c^3$, $h'=-\sin x\,(\frac23+\frac43c^2)$, and $h'''=\sin x\,(-2+12c^2)$. At a zero of $1+Ah$ one has $|c|<1/4$, so $h',h'''$ have the same strict sign. There are both kinds of zero, and the two signs of $F_s=A m^3 h'''$ now give $P\ge c_0m^3$ for some $c_0>0$ independent of $m$. The initial length stays $2\pi$ and the energy $\pi[1+\frac{A^2}{2}(1+1/81)]$ is independent of the even integer $m$. Thus an energy-and-length bound at one time cannot by itself control the instantaneous outward inflection speed. This example asserts no lower bound for the time integral on a fixed positive time interval.


## Formal verification

The Lean modules verify the time derivative of the actual material turning integral, the compact comparison lemma, and the one-sided rate bound at every maximizing finite cyclic configuration, allowing endpoint collisions and full-circle arcs. The cyclic gain estimate is verified for a differentiable budget majorizing the instantaneous outward rate. The genuine normal-flow theorem proves the fourth-root length bound on a solution whose tangent-angle extrema admit a separating angular velocity and a differentiable budget with nonnegative derivative and tail increase at most 1/16. The measurable rate in (1), and the resistance and time-window estimates in (3)–(4), have written proofs here. Its integral corollary takes any continuous nonnegative upper bound on the outward difference of F_s over all pairs of curvature zeros with the indicated signs of k_s. Integrability on a time tail implies fourth-root length growth. It includes the curvature-jet sign test at angle extrema, empty inflection sets, and the choice of a separating velocity. The unrestricted fourth-root problem remains open. [Verification report](OneSidedVerification.json)

To pass from the particular measurable rate in (1) to this continuous-majorant formulation, choose a positive time inside an integrable tail and extend the nonnegative upper semicontinuous rate to the left by its value at that time. The resulting rate is integrable for Lebesgue measure restricted to the right tail. The Vitali–Carathéodory theorem gives a strictly larger lower semicontinuous extended-real function with integrable real part and finite values almost everywhere for this measure. Around each time, a real constant fits strictly between the two functions throughout a neighborhood. A locally finite continuous partition of unity on the line combines these constants into a continuous function between them, which is nonnegative and integrable on the tail. This approximation and the upper semicontinuity of the geometric rate are written deductions in this version. [Integrable-majorant theorem](../../LengthGrowth/ActualFlow/IntegrableInflectionGrowth.lean)
