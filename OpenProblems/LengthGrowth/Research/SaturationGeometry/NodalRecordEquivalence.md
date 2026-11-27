# An exact increasing-record criterion for fourth-root growth

For a smooth closed normal free elastic flow put $U=EL$ and fix any $T>0$. On each slice let $a=\sqrt{D/L}$ and define the signed curvature moment
\[
 b=\tfrac14\int |k|^3ds-\tfrac12\int \sigma F\,ds,
 \qquad \sigma=1 \text{ on } k\ge0,\quad \sigma=-1 \text{ on }k<0 .
\]
Let $G=2aL\max(0,b)$. The [three-deficit identity](NodalSlopeBudget.md) gives $U'\le G$. Its arclength integration argument identifies $b=\sum_{k(z)=0}|k_s(z)|$; that identification is written mathematics. The Lean theorem uses $b$ defined by the two actual integrals.

For $H\ge U(T)$ define the set $S_H$ of times $t\ge T$ with $U(t)>H$ and $U(u)\le U(t)$ for every $u\in[T,t]$. The following equivalence is now checked in [NodalRecords.lean](../../LengthGrowth/ActualFlow/NodalRecords.lean):
\[
 L(t)=O((1+t)^{1/4})\qquad\Longleftrightarrow\qquad
 \text{for some }H\ge U(T),\
 \int_{S_H}\mathbf1_{\{U'>0\}}G\,dt<\infty .
\]
The integrand vanishes even at a high record if its derivative is zero. The formal statement uses the nonnegative Lebesgue integral.

For the sufficient direction extend $U$ constantly to $t<T$. The high record set is measurable. Indeed, intersect the set $t\ge T,\ U(t)>H$ with the closed intersection, over $u\ge T$, of the sets $\{t:t\le u\}\cup\{t:U(u)\le U(t)\}$. On $S_H$ the function $U$ is nondecreasing in time. Its image contains every level $H<y\le U(t)$ for $t\ge T$: use the first time when $y$ is attained and continuity. The one-dimensional change-of-variables formula on a measurable monotone set gives
\[
 (U(t)-H)_+\le |U(S_H)|
 =\int_{S_H}\max(0,U')\,dt
 \le\int_{S_H}\mathbf1_{\{U'>0\}}G\,dt .
\]
The flow has bounded product on $[0,T]$ by continuity, and bounded product gives the [physical fourth-root length and energy bounds](../../LengthGrowth/ActualFlow/GrowthEquivalence.lean). Conversely a fourth-root upper bound on the given flow bounds its product. Choosing $H$ above that bound makes $S_H$ empty. This converse includes homothetic flows with nonzero inflection slopes. Finiteness for some threshold on every smooth closed flow remains open.
