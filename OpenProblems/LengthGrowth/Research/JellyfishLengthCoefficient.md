# Unbounded fourth-root length coefficients at turning number one

For every sufficiently large integer \(m\), let \(\gamma_m\) be the closed free-elastic expander obtained by reflecting an arc with seam angle \(\pi/m\). Write \(L_m(t)\) for its length under the normal velocity \(V=-(k_{ss}+k^3/2)\), and set \(C_m=\lim_{t\to\infty}L_m(t)/t^{1/4}\). Each curve has turning number one. There is an explicit positive constant \(K\) such that

\[
\lim_{m\to\infty}\frac{C_m}{\sqrt m}=K,\qquad
K=2\ell_0(3\pi/2)^{1/4},
\qquad \ell_0=4\int_0^1\frac{du}{\sqrt{1-u^4}}.
\]

Consequently no finite upper bound on the asymptotic coefficient can depend only on the turning number. This holds even if all initial lengths are fixed to the same value, since dilating an initial curve by \(d\) replaces its length at time \(t\) by \(dL(t/d^4)\). Whether each individual flow has some finite upper coefficient remains open.

## The time scale of the reflected-arc family

Use the arclength shooting branch \((\alpha(\varepsilon),\ell(\varepsilon))\), seam angle \(\theta(\varepsilon)\), and base curvature \(k_0\) in Andrews and Wheeler's construction. In their coordinates the centre is \(c=(-1/\varepsilon,0)\) and the unit normal is \(N=(-\cos\theta,-\sin\theta)\), where the angle in this formula is taken along the arc. Equation (3) on the arc gives \(k_{ss}+k^3/2=\alpha\varepsilon\langle\gamma-c,N\rangle\). The dilation parameter for the flow convention above is therefore \(a=-\alpha\varepsilon\). Write \(Y=\int_0^{\ell_0} k_0^2\,ds\) and \(H=\int_0^{\ell_0}k_0^4\,ds\). Both are positive. On the base arc \(\cos\theta_0=k_0^2\). The shooting derivatives at zero are \(\theta'(0)=Y\) and \(\alpha'(0)=-Y/(2H)\), with \(\theta(0)=\alpha(0)=0\). [Andrews and Wheeler, equations (3), (10), (28), and (42)](https://arxiv.org/html/2601.21227v1)

Choose the positive parameters \(\varepsilon_m\to0\) satisfying \(\theta(\varepsilon_m)=\pi/m\). The complete curve consists of \(2m\) congruent copies of the arc. Reflection and reversal of the parametrisation together preserve signed curvature, so each reflected arc contributes the same signed turning \(\pi/m\). The total turning is \(2\pi\). Its initial length is \(2m\ell(\varepsilon_m)\). [Andrews and Wheeler, Corollary 2.24 and Proposition 2.26](https://arxiv.org/html/2601.21227v1#S2.SS6)

If the dilation factor is \(r(0)=1\), curvature scaling gives \(r'=a/r^3\) and \(r^4=1+4at\). A tangential reparametrisation has no effect on length. In particular \(C_m^4=4a_m[2m\ell(\varepsilon_m)]^4\) where \(a_m=-\alpha(\varepsilon_m)\varepsilon_m>0\). The two shooting derivatives give \(m\varepsilon_m\to\pi/Y\) and \(-\alpha(\varepsilon_m)/\varepsilon_m\to Y/(2H)\). Hence

\[
\frac{C_m^4}{m^2}
=64\ell(\varepsilon_m)^4\,
 \frac{-\alpha(\varepsilon_m)}{\varepsilon_m}\,(m\varepsilon_m)^2
\longrightarrow \frac{32\pi^2\ell_0^4}{YH}.
\]

## Evaluation of the constant

The base curvature decreases from \(1\) to \(-1\) with \(k_0'=0\) at both endpoints. It obeys \(k_0''=-k_0^3/2\) and \(4(k_0')^2=1-k_0^4\). Integrating the second identity and integrating the first against \(k_0\) by parts gives \(H=\ell_0/3\). Changing variables from arclength to curvature gives the displayed formula for \(\ell_0\) and \(Y=4\int_0^1 u^2(1-u^4)^{-1/2}du\). With \(v=u^4\) these are the beta integrals \(B(1/4,1/2)\) and \(B(3/4,1/2)\). The beta–gamma identity and \(\Gamma(5/4)=\Gamma(1/4)/4\) give \(\ell_0Y=4\pi\). Substitution gives \(K^4=24\pi\ell_0^4\).

The Lean file in this project checks the homothetic length limit and the limit calculation from the two shooting derivatives and the seam relation. The existence and geometry of the arcs in this application use the cited construction. [Lean source](../LengthGrowth/ActualFlow/JellyfishGrowth.lean)
