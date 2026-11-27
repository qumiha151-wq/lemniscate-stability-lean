# Initial acceleration of the energy–length product from a closed constrained elastica

Suppose a smooth closed free elastic flow starts from a length-constrained plane elastica. Write $F=k_{ss}+k^3/2$, $E=\int k^2ds/2$, $L=\int ds$, $U=EL$, $D=\int F^2ds$ and $c=E(0)/L(0)$. At the initial time $F=ck$: the constrained Euler equation has the form $F=c_0k$, and the dilation first variations of $E$ and $L$ identify $c_0=E/L$. Then
\[
 U'(0)=0,\qquad U''(0)=\tfrac{12}{5} L(0)c^3\int k_s^2\,ds.       \tag{1}
\]
In particular the noncircular closed Euler figure-eight starts a nonempty interval of strict energy–length records on the genuine free flow. The curvature of one traversal is proportional, up to a phase shift and a change of scale, to a Jacobi elliptic cosine with two simple zeros. [Miura and Yoshizawa, classification of closed planar elasticae](https://arxiv.org/abs/2203.08535)

For the computation let $c(t)=E(t)/L(t)$. The product variation is $U'=-L\int (F-c(t)k)F\,ds$, so at the initial constrained elastica only the derivative of the first factor inside the integral contributes to $U''$. In normal material coordinates, $k_t=-F_{ss}-k^2F$, $[\partial_t,\partial_s]=-kF\partial_s$, $E'=-D$ and $L'=\int kF$. At that slice these give
\[
  k_t=-c^2k-ck^3/2,\qquad c'=-4c^3,\qquad
  (F-c(t)k)_t=ck[(k^2-2c)^2-5k_s^2].
\]
For the last identity expand $F_t-c k_t=(k_t)_{ss}+(3k^2/2-c)k_t-(kF)_s k_s-2kF k_{ss}$ and insert $k_{ss}=ck-k^3/2$. Thus
\[
 U''=Lc^2\left(5\int k^2k_s^2-4\int k_{ss}^2\right)
     =Lc^2\left(4c\int k_s^2-\int k^2k_s^2\right),
\]
where the second step differentiates the elastica equation and integrates by parts. All integrals are in arclength over a period.

Use the average $\langle f\rangle=L^{-1}\int f$ and write $V=\langle k^4\rangle$, $S=\langle k_s^2\rangle$, $P=\langle k^2k_s^2\rangle$. The first integral $k_s^2=ck^2-k^4/4+H$ and $\langle k^2\rangle=2c$ imply $S=V/2-2c^2$ and $H=3V/4-4c^2$; the first identity also uses integration of $(kk_s)_s$. Integration of $(k^3k_s)_s$ gives $\langle k^6\rangle=2cV+6P$. Multiply the first integral by $k^2$ and average to obtain $P=cV-\langle k^6\rangle/4+2cH=(8c/5)S$. This proves (1).

There is a consequence for universal estimates of absolute gains. Let one fixed initial noncircular Euler figure-eight have energy $e>0$. For each integer $d$ run its $d$-fold traversal and dilate space by $de$, making the new initial energy exactly one while preserving turning number zero. At scaled time $t=(de)^4\tau$ the new product equals $d^2U(\tau)$, and its energy equals $E(\tau)/e$. For $\tau=d^{-1/2}$ the product rises by $(U''(0)/2+o(1))d$ on strict records, the energy expenditure is $O(d^{-1/2})$, and the elapsed physical time tends to infinity in those initial energy units. The record gain between $(de)^4d^{-1/2}$ and $2(de)^4d^{-1/2}$ has the same order. Since the two crossing zeros of the figure-eight curvature have nonzero slopes, the positive nodal charge on that later interval is of order $d^{3/2}$, by the scaling factor $d^2$ for its time integral. These are different smooth flows with growing initial $U$. They do not produce one trajectory with unbounded product. [IncreasingLemniscateRecords.md](IncreasingLemniscateRecords.md) gives a single primitive non-self-similar flow with infinite positive nodal charge and bounded increasing product.
