# Entry of the actual centre shots into the first transition layer

Start at \(X=0,\ k=0,\ k_s=b>0\), with unit tangent \((1,0)\), curvature normal pointing in the positive \(y\)-direction, and pure expansion coefficient one. Put \(\delta=1/b,\ x=\sqrt b\,s,\ \tau=\delta x,\ Z=X/\sqrt b,\ K=k/\sqrt b,\ V=k_s/b\). All positions and derivatives below belong to actual shots. Write \(W=(K^2/2)T+VN,\ A=|W|\). Then
\[
 Z_\tau=T,\qquad W_\tau=-pN,\qquad p=Z\cdot N,\quad q=Z\cdot T.
\]
The existing [fixed-time outer averaging proof](../ReflectedExpanders/LargeMarkerNecessaryBounds.md) yields \(Z=\gamma\tau e_y+O_B(\delta),\ W=(1-\tau^2/\tau_*^2)e_y+O_B(\delta)\) on every \([0,B]\) with \(B<\tau_*\), where \(\tau_*=\sqrt{3/\gamma}\). We extend that estimate to a layer where \(A\) is of order \(\delta^{2/3}\).

## A transverse quantity with zero mean drift

As long as \(A>0\), use \(e=W/A,\ \eta=Z\cdot e,\ \zeta=Z\cdot Je,\ K=\sqrt A\,U,\ V=Aw\), where \(U'=w,\ U''=-U^3/2,\ u=U^2/2,\ u^2+w^2=1\). Here \(\eta,\zeta\) are components of the actual \(Z\), without division by its norm. The phase, initially zero and lifted to the real line, and the moving frame satisfy
\[
 T=ue-wJe,\quad N=we+uJe,\quad p=w\eta+u\zeta,\quad q=u\eta-w\zeta,
\]
\[
 A_\tau=-pw,\qquad e_\tau=-(pu/A)Je,\qquad
 \phi_\tau=\sqrt A/\delta+Up/(2A).
\]
Put \(I=(W\wedge Z)/\sqrt A=\sqrt A\,\zeta\). Differentiating both factors in the determinant gives
\[
 I_\tau=A^{-1/2}[pq-Aw+\zeta pw/2].
\]
The bracket has zero mean over the oscillator phase. An explicit primitive at fixed \(A,e,Z\) is
\[
 P=\tfrac16 U^3(\eta^2-\zeta^2/2)-\tfrac12 Uw\eta\zeta-AU .
\]
Similarly the mean of \(A_\tau\) is \(-2\eta/3\), with primitive \(Q=-Uw\eta/3-U^3\zeta/6\) for \(A_\tau+2\eta/3\). Define
\[
 I_c=I-\delta P/A,\qquad A_c=A-\delta Q/\sqrt A .
\]
On \(0<A\le1,\ |Z|\le M\), all the functions \(P,Q\) and their partial derivatives in \(A,\eta,\zeta,\phi\) are uniformly bounded. The actual derivatives of \(\eta,\zeta\) are bounded by \(C_M/A\), since \(|Z_\tau|=1,\ |e_\tau|\le M/A\). Cancelling the leading phase derivative yields
\[
 |(I_c)_\tau|\le C_M\delta/A^2,\qquad
 |(A_c)_\tau+2\eta/3|\le C_M\delta/A^{3/2},\qquad
 |A_c/A-1|\le C_M\delta/A^{3/2}.                              \tag{1}
\]
These estimates are uniform down to the indicated amplitude.

## Reaching the layer before loss of positive radial alignment

Let \(z_*=\gamma\tau_*>0\), fix \(M>2z_*+2\), and choose \(\tau_0<\tau_*\) with fixed small \(a=1-\tau_0^2/\tau_*^2>0\). For sufficiently small \(\delta\),
\[
 A(\tau_0)=a+O_a(\delta),\quad Z(\tau_0)=\gamma\tau_0 e_y+O_a(\delta),
 \quad I_c(\tau_0)=O_a(\delta).
\]
Choose a fixed large \(L\), start at \(\tau_0\), and stop at the first \(A=L\delta^{2/3}\) or first loss of \(A<1,\ |Z|<M,\ \eta>z_*/4\). The initial conditions satisfy these strict bounds. By (1), choosing \(L\) sufficiently large gives \(A/2<A_c<2A\) and \((A_c)_\tau<-c\) before stopping, where \(c>0\) depends only on \(z_*\). In particular the elapsed time is at most \(C a\) and \(A\le C a\); take \(a\) small enough that \(A<1\) and \(3z_*/4<|Z|<M\) throughout, using \(|Z_\tau|=1\). Changing integration variable to the decreasing \(A_c\), (1) gives
\[
 |I|\le C_a\delta+C_M\delta/A,\qquad
 |\zeta|\le C_a\delta/\sqrt A+C_M\delta/A^{3/2}.                 \tag{2}
\]
Indeed \(\int d\tau/A^2\le C\int_{A_c(\tau)}^{A_c(\tau_0)}dy/y^2\le C'/A(\tau)\). Constants denoted \(C_M\) may also depend on the fixed positive \(z_*\), and are independent of \(L,a,\delta\). Bound (2) stays below \(z_*/4\) for \(|\zeta|\) when \(L\) is large and then \(\delta\) small. As \(\eta^2+\zeta^2=|Z|^2\) and initially \(\eta>0\), \(\eta>z_*/4\) cannot first fail. Hence the shot reaches \(A=L\delta^{2/3}\) in finite time. The hitting time lies between \(\tau_0\) and \(\tau_0+C a\). First take \(\delta\to0\) and then \(a\to0\); fixed-time averaging excludes such small \(A\) before any fixed \(B<\tau_*\). It follows that the layer time tends to \(\tau_*\), and \(Z\to z_* e_y\). All estimates also apply before this hitting.

## The incoming section in intrinsic coordinates

Let \(r=|Z|\) on this late incoming segment. In the canonical radius normalization the amplitude, radial stress, transverse datum and small parameter are
\[
 {\cal A}=\frac{A}{\delta^{2/3}r^{2/3}},\qquad
 {\cal H}={\cal A}\frac{\eta}{r},\qquad
 {\cal I}=\frac{I}{\delta^{1/3}r^{4/3}},\qquad
 \varepsilon=\delta^{2/3}r^{-4/3}.
\]
Indeed the physical vector stress is \(bW\) and the physical radius is \(\sqrt b\,r\). Thus \({\cal A}\) is the physical stress amplitude divided by the two-thirds power of the physical radius. The two normalized oscillator coordinates \(U,w\) and their phase are unchanged. Define the incoming section on the large-amplitude branch by
\[
 \widehat{\cal H}={\cal H}+\chi(\phi,\eta/r,\zeta/r)/\sqrt{\cal A}=H ,
\]
where \(\chi=Uw(\eta^2-\zeta^2)/3+U^3\eta\zeta/3\) when its last two arguments are unit-vector components.

For every sufficiently large fixed \(H\) the physical shot reaches this section on the incoming segment. To see this, apply (1) and (2) down to absolute amplitude \(L\delta^{2/3}\) with \(L=c_0 H\) and fixed \(c_0>0\) small enough that \({\cal A}<H/2\) there, using the uniform positive lower bound on \(r\). Earlier, the section variable started above \(2H\). Throughout this segment \(\eta/r>0\) is close to one when \(H\) is large, and \(\chi\) is bounded. At any crossing of \(H\) one therefore has \(H/2<{\cal A}<2H\). In this fixed compact amplitude band, express the radial and transverse frame relative to the true position. For inner arclength \(d\sigma=|X|^{1/3}ds\), if \(\theta\) is the tangent angle relative to the radial direction then
\[
 \kappa_\sigma=\nu-\varepsilon\kappa\cos\theta/3,\quad
 \nu_\sigma=-\kappa^3/2+\sin\theta-2\varepsilon\nu\cos\theta/3,\quad
 \theta_\sigma=\kappa-\varepsilon\sin\theta,\quad
 \varepsilon_\sigma=-4\varepsilon^2\cos\theta/3.
\]
Here \(\kappa=k/|X|^{1/3},\ \nu=k_s/|X|^{2/3}\). These regular equations converge uniformly on the band to the frozen system as \(\delta\to0\). In the frozen system \((\widehat{\cal H})_\sigma=-(1+(\eta/r)^2)/3+O({\cal A}^{-3/2})\) with an absolute remainder constant, by the [explicit frozen calculation](FrozenScattering.md). Consequently every actual crossing in this band has strictly negative derivative for small \(\delta\); in particular the late-segment crossing is unique and depends continuously on \(b\). At this crossing (2) gives
\[
 |{\cal I}|\le C_a\delta^{2/3}+C/H,\qquad
 \varepsilon\to0,                                                 \tag{3}
\]
with the second constant independent of \(H\). Thus \(\limsup_{b\to\infty}|{\cal I}|\le C/H\) for fixed sufficiently large \(H\); sending \(H\) to infinity gives zero uniformly in the lifted phase.

For the phase lift, on the late incoming segment
\(\phi_\tau\ge(\sqrt A/\delta)(1-C_M\delta/A^{3/2})>0\).
On \([0,\tau_0]\) fixed-time averaging keeps \(A\) bounded away from zero as \(\delta\to0\); the same phase formula shows that \(\phi(\tau_0)\ge c_a/\delta\) for small \(\delta\). Thus the chosen continuous lifted phase at the corrected section tends to positive infinity as \(b\to\infty\). This is a winding statement for a family of actual incoming data. The intersection with the seam family requires the two-coordinate matching argument.
