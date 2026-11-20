# The sharp lower endpoint for finite quarter-power length growth

Let a smooth immersed closed plane curve evolve for all positive time by
the normal free elastic flow with signed normal velocity
$-(k_{ss}+k^3/2)$. Write $E=\frac12\int k^2\,ds$, $D=\int(k_{ss}+k^3/2)^2\,ds$
and $L=\int ds$. Suppose
$C=\limsup_{t\to\infty}L(t)/t^{1/4}<\infty$. Put
$C_0=(32\pi^4)^{1/4}$.

Then $C\ge C_0$ and

\[
\liminf_{t\to\infty}\frac{L(t)}{t^{1/4}}\ge\frac{32\pi^4}{C^3},
\qquad \limsup_{t\to\infty}E(t)L(t)\le\frac{C^4}{16\pi^2}.
\]

There is a universal $C_*>C_0$ for which $C<C_*$ implies that the rescaled flow converges smoothly, up to parametrisation, to a once-covered round circle, and $L(t)/t^{1/4}\to C_0$. Thus the interval $(C_0,C_*)$ contains no finite growth coefficient.

## The estimates

The input inequalities at any smooth time are $EL\ge2\pi^2$ and
$D/E^2\ge4\pi^2/L^3$. For the first, apply periodic mean-zero Wirtinger to the unit tangent. For the second, subtract the arclength centroid from the position to obtain $X$. The dilation first variation gives
$E=-\int (k_{ss}+k^3/2)\langle X,N\rangle\,ds$. Cauchy–Schwarz and periodic mean-zero Wirtinger give $E^2\le D\int|X|^2ds\le D L^3/(4\pi^2)$.

Take any $A>C$ with $A>0$. Eventually $L(t)\le A t^{1/4}$. Since $E'=-D$, integration from any such $T>0$ gives

\[
E(t)^{-1}\ge E(T)^{-1}+16\pi^2 A^{-3}(t^{1/4}-T^{1/4}).
\]

Consequently $\limsup t^{1/4}E(t)\le A^3/(16\pi^2)$. The pointwise lower bound on $EL$ implies $\liminf L/t^{1/4}\ge32\pi^4/A^3$. If $C=0$, this contradicts $L/t^{1/4}\to0$ for even one fixed $A>0$. Multiplying the upper bound on $t^{1/4}E$ by the eventual bound on $L/t^{1/4}$ and letting $A\downarrow C$ gives both displayed inequalities. In particular $C^4\ge32\pi^4$. If $C=C_0$, then $L/t^{1/4}\to C_0$ and $EL\to2\pi^2$.

## A universal interval of rigidity

Let $B_8=4\varpi^*\approx112.4396$ be the sharp lower bound on $L\int k^2\,ds$ for a closed immersed curve with a double point. In particular $B_8>4\pi^2$. This is the multiplicity-two case of [Miura, Theorem 1.1](https://arxiv.org/abs/2102.06597), also proved in the plane by [Müller and Rupp](https://arxiv.org/abs/2101.08509).

The growth coefficient also detects eventual embeddedness without a small-oscillation premise. If arbitrarily late slices have a double point, then $\limsup 2EL\ge B_8$, so $C^4\ge8\pi^2 B_8$. This conclusion always applies when the absolute turning number differs from one. Independently, Cauchy–Schwarz gives $2EL\ge(2\pi\omega)^2$ for every slice, so $C\ge C_0\sqrt{|\omega|}$.

Let $\varepsilon_1>0$ be the single-turn threshold in [Andrews and Wheeler, Theorem 1 and equation (1.4)](https://arxiv.org/html/2509.11129v2). Set

\[
\delta=\min\{\varepsilon_1,B_8-4\pi^2\},
\qquad C_*=[8\pi^2(4\pi^2+\delta)]^{1/4}.
\]

When $C<C_*$, the preceding estimate implies $2EL<4\pi^2+\delta$ at every sufficiently large time. Choose one such time. The curve is embedded since $2EL<B_8$. Its turning number has absolute value one by the turning-tangent theorem. Orient it positively. Then $K_{\mathrm{osc}}=L\int(k-2\pi/L)^2ds=2EL-4\pi^2<\varepsilon_1$. Dilate this time slice to length $2\pi$ and restart the flow. The cited theorem gives smooth convergence of the length-normalised flow to the once-covered round circle. Their unnormalised velocity is twice the one used here, so their unrescaled time for this restarted dilation by $a$ is $a^4(t-T)/2$. This fixed conversion preserves the geometric convergence. The normalised time covers an infinite interval: it is a positive constant times $\int_T^t L(u)^{-4}du$, which diverges under our finite upper envelope.

For clarity on the physical coefficient, normalise each slice to unit length. Use $\hat s=s/L$ and $\hat k=Lk$. Smooth convergence gives $\hat k\to2\pi$ and $\partial_{\hat s}\hat k\to0$ uniformly. The ordinary first variation and periodic integration by parts give $L'=\frac12\int k^4ds-\int k_s^2ds$, whence

\[
(L^4)'=4\bigg(\frac12\int_0^1\hat k^4d\hat s-
                       \int_0^1|\partial_{\hat s}\hat k|^2d\hat s\bigg)
      \longrightarrow 32\pi^4.
\]

Integration gives $L^4/t\to32\pi^4$. This proves the claimed gap and covers the endpoint $C=C_0$. Rigidity here is asymptotic; initially noncircular curves in the single-turn stability basin also attain this coefficient.

## Attainment by expanding circles

For $\gamma(t,u)=x_0+r(t)e^{iu}$, $N=-e^{iu}$ and $k=1/r$. Hence $r'=1/(2r^3)$ and $r(t)^4=r(0)^4+2t$. In particular $L=2\pi r$, $E=\pi/r$, $D=\pi/(2r^5)$. Both static inequalities are identities, and $L/t^{1/4}\to2\pi\,2^{1/4}=C_0$. A circle traversed $m$ times has coefficient $m C_0$.

The compactness and basin conclusions use the two cited mathematical theorems. The universal upper bound $C<\infty$ for arbitrary initial curves is a separate open question.
