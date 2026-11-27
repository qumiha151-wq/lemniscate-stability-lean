# Critical compactness of a single Hardy projection

Keep the notation and normalized arclength of OneSidedTangentSpectrum.md. Let \(P_\pm\) project onto strictly positive or negative Fourier indices. If the set of either one of \(P_\pm T(t)\) is relatively compact in the periodic Sobolev space \(H^{1/4}\) on a time tail, then the given free elastic flow satisfies the fourth-root length bound. Boundedness of either projected \(H^\alpha\) seminorm on a time tail suffices for every \(\alpha>1/4\).

Here is the stronger quantitative conclusion. Put \(X=U^{1/3}\), \(\omega_n=2\pi n\), and \(\rho=\sqrt2/128\). At every slice with \(U'\ge0\) and \(\pi|m|\le\rho X\), each sign separately satisfies
\[
 \sum_{\substack{\pm n>0\\ |\omega_n|>\rho X}}
        |\omega_n|^{1/2}|c_n|^2
 \ \ge\ \left(\frac{(2\rho)^7}{1024}\right)^{1/6}.
\]
The cutoff tends to infinity at every sequence of unbounded product records. This forbids even the critical precompactness of a single signed projection.

Indeed, the first moment in angular-frequency units on each sign is at least
\[
  \frac{\sqrt2}{32}X-\pi |m|=4\rho X-\pi|m|.
\]
The first moment of all modes with \(|\omega|\le\rho X\) is at most \(\rho X\), since \(\sum |c_n|^2=\int_0^1|T|^2=1\). Thus each surviving signed high tail has first moment \(D_1\ge 2\rho X\). For any subset of Fourier indices, Hölder gives \(D_1^7\le D_{1/2}^6 D_4\), because \(1=(6/7)(1/2)+(1/7)4\). The proved upper bound \(D_4\le1024X^7\) gives the displayed inequality. Uniform decay of the Fourier \(H^{1/4}\) tails is necessary for relative compactness and follows from approximation of a compact set by finitely many Fourier projections. For \(\alpha>1/4\), the same tail also gives the one-sided quantitative growth
\[
 \sum_{\pm n>0}|\omega_n|^{2\alpha}|c_n|^2
 \ge (\rho X)^{2\alpha-1/2}
       \left( (2\rho)^7/1024\right)^{1/6}.
\]
For \(1/4<\alpha\le1/2\), interpolation of \(D_1\) directly between \(D_{2\alpha}\) and \(D_4\) improves the right-hand growth to a positive constant times \(U^{(4\alpha-1)/3}\). The proof uses the turning-number conservation in the first-moment estimate. No condition on the other Hardy projection is imposed. Whether the critical compactness property holds for all individual flows remains open.

## A finite frequency band on each side

There is also an explicit upper endpoint for the escaping frequencies. Whenever \(\pi |m|\le X/128\), on both signs one has
\[
\sum_{\substack{\pm n>0\\ X/128<|2\pi n|\le64X^2}} |2\pi n|^{1/2}|c_n|^2\ \ge\ 3/2048.
\]
The whole signed first moment is at least \(3X/128\), since \(\sqrt2/32\ge4/128\). The frequencies at most \(X/128\) contribute at most \(X/128\), and the frequencies above \(64X^2\) contribute at most \((64X^2)^{-3}M_4\le X/256\). The first moment within the displayed band is consequently at least \(3X/256\). Since the square root of its top frequency is \(8X\), the critical moment on that same band is at least \(3/2048\).

## An equivalent criterion on a single flow

Let \(Q^\sigma_W(t)\) denote the squared homogeneous \(H^{1/4}\) tail above angular frequency \(W\) on side \(\sigma\). The fourth-root upper length bound is equivalent to each of the following conditions.

1. For every \(\varepsilon>0\), some \(W\ge1\) has \(Q_W^\sigma(t)<\varepsilon\) for both signs and all \(t\ge0\).
2. There are fixed \(W,A,t_0\) such that for every \(t>\max(0,t_0)\) with \(U(t)>A\), at least one sign has \(Q_W^\sigma(t)<3/2048\). The sign can depend on \(t\).

The reverse implication comes from the finite-band obstruction on arbitrarily late high records. For the forward implication the established energy-length characterization gives a uniform bound on \(U\), and Parseval gives \(M_2=2U\) at every time. On \(|\omega|>W\ge1\), the elementary estimate \(W\sqrt{|\omega|}\le|\omega|^2\) gives \(Q_W^\sigma(t)\le2U(t)/W\). Thus both positive and negative tails vanish uniformly. Uniform boundedness of the low modes, from the unit tangent normalization, makes this condition equivalent to relative compactness in the full periodic \(H^{1/4}\) space.
