# Arclength normalization of the geometric slice inequality

Let a smooth immersed closed curve have material parameter period \(p\), length \(L\), and bending energy \(E=\frac12\int k^2\,ds\). Its physical arclength coordinate is \(s\). Set
\[
P=\sqrt{2EL},\qquad a=L/P,\qquad u(x)=a\,k(ax).
\]
Curvature in this formula is evaluated on the actual unit-speed reparametrization. The normalized scalar function is smooth and has period \(P\). Its ordinary scalar force satisfies
\[
 v(x)=u''(x)+u(x)^3/2=a^3 F(ax),\qquad F=k_{ss}+k^3/2.
\]
With the mean taken over \([0,P]\), the general identity is
\[
 \langle u^i v^j\rangle=\frac{a^{i+3j}}{L}\int k^iF^j\,ds
 \quad(i,j\ge0).
\]
The geometric integrals use arclength density relative to the original material parameter. The proof composes the actual inverse arclength map with a linear dilation and transports its integral.

Write \(C=\int k^3\,ds\), \(S=\int k\,ds\), \(D=\int F^2\,ds\) and \(V=\int kF\,ds\). Applying the mixed moment identity gives
\[
 \langle u^2\rangle=1,\qquad
 \langle u\rangle=S/P,\qquad
 \langle u^3\rangle=LC/(2EP),
 \qquad
 \langle v^2\rangle-\tfrac12\langle uv\rangle
 =\frac{L^4(LD-EV)}{(2EL)^3}.
\]
Consequently the universal scalar periodic strict-gap inequality implies the material-coordinate statement `StrictHalfSliceGap ε`. The module `LengthGrowth.ActualFlow.CriticalRMSAdapter` proves this implication from the scalar theorem as an explicit hypothesis. The module `LengthGrowth.ActualFlow.CriticalRMSWindow` applies it to the periodic-window theorem; its remaining hypothesis is the deterministic one-window comparison for smooth scalar functions.

The integrated flow theorem supplies this deterministic comparison in `actual_window_comparison` and proves the material estimate in `static_gap`. [Integrated Lean theorems](../../LengthGrowth/ActualFlow/ExplicitCubicThreshold.lean)
