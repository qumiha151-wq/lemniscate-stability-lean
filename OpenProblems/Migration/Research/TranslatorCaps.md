# A quantitative obstruction to closing a translating strip with small caps

Orient the target direction by a unit vector $e$. Use $T,N=JT,k$ for the Frenet data, $F=k_{ss}+k^3/2$ and the geometric normal velocity $-FN$. The elastic energy is $E=\frac12\int k^2\,ds$. Put
\[
Q=\tfrac12 k^2T+k_sN,\qquad \sigma=Q\cdot e,\qquad n=N\cdot e.
\]
Direct differentiation gives $Q_s=FN$. Thus $\int Fn\,ds=0$ on every actual closed slice. The open-translator project already uses the corresponding monotonicity on a translating arc. The estimates below quantify the compensation that closing the arc forces onto the rest of the curve.

## Exact arcs and endpoint order

On a translator with speed $v>0$ in direction $e$, $F=-vn$. Consequently
\[
\sigma(a)-\sigma(b)=v\int_a^b n^2\,ds
\ge v\frac{|(X(b)-X(a))\cdot Je|^2}{b-a}.
\]
Here $|n|=|T\cdot Je|$, and the last estimate follows by integrating the tangent and applying Cauchy–Schwarz. A transverse span $R$ achieved in length at most $C R$ therefore costs a projected endpoint stress difference of at least $vR/C$. Bounding both endpoint curvature and its first arclength derivative independently of $R$ rules out such long arcs at fixed speed. A flat-to-flat exact translating cap has zero stress at both ends and can only be a straight segment parallel to $e$.

For any nonstraight connected translator, $\sigma$ is strictly decreasing in arclength. Indeed, equality on an interval forces $n\equiv0$ there. Its tangent is then constant, with $k=k_s=0$, and uniqueness for the smooth autonomous angle-curvature ODE gives a straight line everywhere. When $T=e$ the projected stress is $k^2/2\ge0$, and when $T=-e$ it is $-k^2/2\le0$. Thus an oriented translator cannot meet $T=-e$ and subsequently $T=e$. This argument is unchanged by reversing the arc parametrisation: $Q$ changes sign and the endpoints interchange, so the loss of projected stress remains positive.

For the specific certified example, $e=(1,0)$, $v=1$, $\theta(0)=\pi/2$, $k(0)=1$ and $k_s(0)=0$, hence $\sigma(0)=0$. On the positive half-line the tangent can never equal $e$, and the continuous lift stays in $(0,2\pi)$. On the negative half-line it never equals $-e$, and the lift stays in $(-\pi,\pi)$. The ODE is invariant under $\tilde\theta(s)=\pi-\theta(-s)$, $\tilde k(s)=k(-s)$, $\tilde k_s(s)=-k_s(-s)$. Uniqueness gives this reflection symmetry, but reflecting or reversing the arc cannot make its stress loss cancel with the loss on another piece moving at the same speed.

## Quantitative dissipation forced onto the caps

On one smooth closed slice partition the curve into a body $G$ and the remaining caps $H$. They can be any measurable arclength subsets. Define
\[
A=\int_G n^2\,ds,\qquad B=\int_H n^2\,ds.
\]
Suppose $A>0$ and the body follows the normal component of a target translation at speed $v>0$ with relative error $0\le\eta<1$, in the precise sense
\[
\int_G(F+vn)^2ds\le\eta^2v^2 A .
\]
Then $B>0$ and
\[
\int_H F^2ds \ge (1-\eta)^2v^2\frac{A^2}{B},
\qquad
D=\int_{G\cup H}F^2ds\ge(1-\eta)^2v^2 A(1+A/B).
\]
In fact $J=-\int_G Fn\,ds=vA-\int_G(F+vn)n\,ds\ge(1-\eta)vA>0$. The exact translation balance gives $\int_H Fn\,ds=J$. Cauchy–Schwarz on each part gives the two inequalities. In the normal material gauge the two caps together have integrated projected velocity $-J<0$. In particular they cannot both have nonnegative projected velocity at every point while the body satisfies this approximation. This sign statement concerns instantaneous normal-gauge velocity; the dissipation estimates themselves are geometric.

Apply the bound at each time of a genuine closed flow on $[0,\mathcal T]$. Suppose the body has a connected transverse span at least $R$ in arclength at most $C R$, and the caps have total arclength at most $\ell$, throughout that interval. Then $A\ge R/C$ and $B\le\ell$. With speed $v(t)>0$ and uniform relative error $\eta<1$, the exact energy identity implies
\[
E(0)-E(\mathcal T)\ge
(1-\eta)^2 \frac{R}{C}\left(1+\frac{R}{C\ell}\right)
\int_0^{\mathcal T}v(t)^2dt
\ge (1-\eta)^2 \frac{R}{C}\left(1+\frac{R}{C\ell}\right)
\frac{\left(\int_0^{\mathcal T}v(t)dt\right)^2}{\mathcal T}.
\]
In units with fixed target speed and a fixed positive time, a family with $E(0)=O(R)$ and $\ell=o(R)$ cannot satisfy these body and cap hypotheses as $R\to\infty$. This is an obstruction to the proposed inexpensive long-strip construction. A construction with large-energy or long caps, or a flow in which the body rapidly changes shape, escapes these particular estimates.

Full migration requires a strict separation of the entire images at two times. It allows opposite instantaneous velocities on the caps, which could exchange roles over time. To obtain migration by another gluing regime, one would need a finite-time closed-flow comparison that covers those caps and controls the most slowly advancing height point; the known complete open solution and its symmetry do not supply it.

## A long transverse translating arc already costs quadratic bending energy

This estimate is static and also applies to approximate translator arcs independently of the rest of the curve. Let $G$ be one connected arc of length $P$ with transverse endpoint displacement at least $\beta P$, $0<\beta\le1$. Suppose the relative normal-velocity approximation above holds with $\eta<1$. Set
\[
a=(1-\eta)\beta^2/2,\qquad b=a^2/[4(1+\eta)^2].
\]
When
\[
\sqrt{vP^3}\ge8\sqrt2\left(\frac{2}{b\sqrt a}
                   +\frac{1+\eta}{a^{3/2}\sqrt b}\right),
\]
the bending energy of the body alone satisfies
\[
 E_G=\tfrac12\int_G k^2\,ds\ \ge\ (ab/24)\,vP^2 .
\]

Indeed $A\ge\beta^2P$, while the approximation gives
$D_G=\int_G F^2ds\le(1+\eta)^2v^2P$. The flux difference across the arc is at least $(1-\eta)vA$, so $M=\max_G|Q|\ge avP>0$. From a maximum point choose the longer arclength side. On that side take a segment of length $l=\min(P/2,M^2/(4D_G))\ge bP$. The inequality $|Q(s)-Q(s_0)|\le\sqrt{D_G l}$ implies $|Q|\ge M/2$ throughout this segment. Its endpoints satisfy $|k|\le\sqrt{2M}$ and $|k_s|\le M$ since $|Q|^2=k_s^2+k^4/4$. Integration by parts on this very segment gives
\[
 \int |Q|^2 ds=[k k_s]+\tfrac34\int k^4ds-\int kFds,
\qquad
 \tfrac14M^2 l\le2\sqrt2 M^{3/2}+3ME_G+\sqrt{2MlD_G}.
\]
On dividing by $M^2 l$, the sum of the first and last right-hand terms is at most
\[
\frac{\sqrt2}{\sqrt{vP^3}}\left(\frac{2}{b\sqrt a}
               +\frac{1+\eta}{a^{3/2}\sqrt b}\right)\le\tfrac18.
\]
This gives $E_G\ge Ml/24\ge abvP^2/24$.

For an exact translator, $|Q_s|\le v$ permits the sharper segment length $l=\min(P/2,M/(2v))\ge\beta^2P/4$, while $M\ge v\beta^2P/2$. In the same integrated inequality the last error is bounded by $v\sqrt{2M}\,l$. Both error ratios vanish once $vP^3\to\infty$ at fixed $\beta$. Thus $E_G\ge v\beta^4 P^2/192$ for sufficiently large $vP^3$. In particular, a fixed-speed long transverse body cannot be cut from the known open solution, or approximated to fixed relative tolerance, while its bending energy grows only linearly in its arclength. Energy superlinear in arclength remains compatible with the broad open-immersion theorem.

## Verification

The independent Migration module `Migration.TranslatorCaps` checks the endpoint stress–chord inequality, the arc stress–energy integration identity, and the cap and total dissipation inequalities for arbitrary measurable pieces of a closed curve. Its material-coordinate theorem identifies the latter total with the negative physical time derivative of the bending energy of the same genuine normal flow. A finite-time corollary allows the chosen measurable body to change with time, while a fixed speed, error tolerance and uniform bounds $A\ge A_0>0, 0<B\le B_0$ give a constant lower rate of expenditure. The angular ordering argument, the variable-speed time integral, and the extraction of a quadratic static energy lower bound from a high-stress subarc are mathematical proofs in this note.

The open solution and its rigorous scope are documented in the separate OpenTranslators project. The underlying closed-flow question appears in [Miura–Wheeler](https://arxiv.org/abs/2404.12619). The migrating examples of [Kemmochi–Miura](https://arxiv.org/abs/2303.12516) use open curves with boundary conditions.
