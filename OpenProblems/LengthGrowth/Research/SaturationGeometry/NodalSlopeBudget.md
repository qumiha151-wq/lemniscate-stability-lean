# Length growth paid for by curvature slopes at inflections

On a smooth closed material free elastic flow use $E=\int k^2ds/2$, $D=\int F^2ds$, $F=k_{ss}+k^3/2$, $L=\int ds$. At each time define $m=\sqrt{2E/L}$, $a=\sqrt{D/L}$ and
\[
 B=\sum_{z:\,k(z)=0}|k_s(z)|
\]
over one parameter period without duplicating its endpoint. Multiple zeros contribute zero. Both $E$ and $D$ are positive: a closed regular curve cannot be straight and the dilation identity rules out a stationary one. Write $\sigma=1$ where $k\ge0$ and $-1$ elsewhere. Then the genuine physical flow satisfies the exact identity
\[
 \begin{split}
 (EL)'={}&2aLB
 -\frac{aL}{2}\int(|k|-m)^2(|k|+m/2)\,ds\\
 &-\frac L2\int(F-a\sigma)^2\,ds
 -\frac{Em}{2a}\int(F-a k/m)^2\,ds .                              \tag{1}
 \end{split}
\]
In particular $(EL)'\le2\sqrt{LD}\,B$. If $\int_T^\infty\sqrt{L D}\,B\,dt<\infty$ on some positive-time tail then $EL$ is bounded on the entire flow. The [actual-flow equivalence](../../LengthGrowth/ActualFlow/GrowthEquivalence.lean) implies $L(t)=O((1+t)^{1/4})$, and $E(t)=O((1+t)^{-1/4})$. The stronger condition $\int_T^\infty L B^2dt<\infty$ also suffices by Cauchy–Schwarz and $\int_T^\infty D\le E(T)$. A criterion retaining the three subtracted terms also follows by integrating the positive part of their combined right side.

For the signed integration, decompose $\{k\ne0\}$ into its open arcs. On each such arc, $\int\sigma k_{ss}=[\sigma k_s]_{\rm endpoints}$, and both endpoint contributions are nonpositive. Each simple zero contributes twice its absolute slope with a minus sign, and a zero with vanishing derivative contributes zero. Summing is justified by $\sum|\int_{\rm arc}\sigma k_{ss}|\le\int |k_{ss}|$. At nonisolated zeros $k_s=k_{ss}=0$ by Taylor's formula and sequences of nearby zeros; isolated zeros are a null set. A nonempty zero set can be used to cut the parameter circle; if there are no zeros the period integral of $k_{ss}$ vanishes. Thus $B$ is absolutely summable and
\[
 \int\sigma F\,ds=\frac12\int |k|^3ds-2B .
\]
In particular the choice of $\sigma$ on zeros preserves the formula and makes $\sigma^2=1$ everywhere.

The three differences in (1) can each be checked directly. Since $m^2L=\int k^2 ds$,
\[
 \int |k|^3-Lm^3=\int (|k|-m)^2(|k|+m/2) .
\]
Here and below unmarked spatial integrals are in arclength. Since $D=a^2L$,
\[
 aL-\int \sigma F=\frac1{2a}\int(F-a\sigma)^2,\qquad
 aLm-\int kF=\frac m{2a}\int(F-ak/m)^2 .
\]
Substitution in $U'=E\int kF-LD$ gives (1), including the factors of $m,a,L$.

## Smooth cutoffs and a canonical bound

For $b>0$ put $q=\sqrt{k^2+b^2}$, $u=k/q$ and $B_b=\int b^2k_s^2/q^3\,ds$. The periodic derivative of $uk_s$ is $b^2 k_s^2/q^3+uF-k^4/(2q)$. Hence $B_b=\int k^4/(2q)-uF$. Dominated convergence and the signed identity give $B_b\to 2B$ as $b\downarrow0$ on each individual slice, regardless of the number of inflections. The isolated zeros have zero measure and $F=0$ at the nonisolated zeros. This identity also gives time measurability of $B$ from the fixed choices $b=1/n$.

The estimate $0\le |k|-k^2/q\le b$ bounds the loss in replacing the absolute cubic moment by $k^4/q$. Thus on every actual slice,
\[
 Em\le B_b+bE+\sqrt{LD},\qquad
 (EL)'\le\sqrt{LD}(B_b+bE).
\]
The infimum of the latter bound over $b>0$ gives a nonnegative intrinsic upper rate; its time integral controls fourth-root growth. The infimum is at most $2\sqrt{LD}\,B$ by the pointwise limit. These estimates do not show the required time integral to be finite on every trajectory. For instance on a homothetically expanding profile with nonzero simple inflections the positive feeding term in (1) scales as a constant divided by time, while the subtracted terms cancel it exactly.

## A criterion using only increasing records

A weighted budget that covers every bounded-product flow can ignore time spent below a chosen product threshold and all times off the current record. More precisely let $U=EL$, fix $T>0$, choose $H\ge U(T)$, and let $R(t)=\max(H,\max_{T\le s\le t} U(s))$. Define
\[
 S_H=\{t>T:U(t)=R(t)>H,\ U'(t)>0\}.
\]
It is enough that $\int_{S_H}\sqrt{LD}\,B\,dt<\infty$. One may use the canonical nonnegative regularized upper rate in its place. In fact $R$ is locally Lipschitz since $U$ is smooth. At points with $U<R$, continuity makes $R$ locally constant. On a level set of a differentiable real function its derivative vanishes almost everywhere (at every nonisolated point where its derivative exists). Apply this to $R-H$ and to $R-U$. Thus $R'$ is zero almost everywhere where $R=H$, equals $U'$ almost everywhere where $U=R>H$, and is nonnegative. It follows that $R(t)-H=\int_{(T,t)\cap S_H} U'$; inequality (1) bounds this integral by twice the proposed budget. If the product is bounded, take $H$ above its supremum to get an empty budget. This proves an equivalence with existence of a finite threshold and finite record budget. It does not determine whether every unbounded-product scenario is impossible.

## Formal verification scope

[NodalSquare.lean](../../LengthGrowth/ActualFlow/NodalSquare.lean) checks the exact three-deficit identity in the signed-integral representation of $B$, its application to the true physical flow, and the fourth-root criterion for its nonnegative upper rate. [NodalSlopeRate.lean](../../LengthGrowth/ActualFlow/NodalSlopeRate.lean) checks the independent geometric integration by parts at every positive smoothing scale, the derivative estimate and the time-tail fourth-root criterion using the infimum over smoothing scales. The identification of the signed moment with the sum at all zeros, the small-scale limit, and the record-only criterion are written proofs.
