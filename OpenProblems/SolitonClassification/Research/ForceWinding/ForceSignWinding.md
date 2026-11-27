# Elastic force, turning number and intersections of a closed similarity profile

Let \(X:\mathbb R/L\mathbb Z\to\mathbb R^2\) be a smooth unit-speed free-elastic similarity profile with centre \(O\). Set the origin at \(O\), \(T=X'\), \(N=JT\), \(k=T'\cdot N\), and write the profile equation as
\[
 F=k''+\tfrac12 k^3=-aX\cdot N-bX\cdot T,\qquad a>0.
\]
Let \(m=(2\pi)^{-1}\int k\,ds\) be the signed turning number, counting the full parametrization.

**Every zero-turn profile has strictly positive and strictly negative elastic force. The same conclusion holds for every nonembedded profile of turning number \(+1\) or \(-1\).** In particular it applies to the certified winding-minus-one rotating immersion with two transverse double points. For all of these profiles, any two sufficiently close distinct logarithmic scales of their physical similarity motion have intersecting images. The statement compares whole curves at two different times.

Here is a stronger description when \(F\ge0\). Write \(h=\#X^{-1}(O)\), counting parameter labels in one period. Then \(m\ge1\), \(h<2m\), and each point other than \(O\) is taken at most \(m\) times. If \(b\ne0\), then \(h=0\). For \(m=1\) the curve is embedded. When \(h=0\), its images at all distinct logarithmic scales are disjoint, enclose \(O\), and form nested Jordan curves. When \(h=1\), the profile is a pure expander, its entire open arc away from \(O\) lies in the open half-plane on one side of the tangent at \(O\), and the intersection of any two different rescalings is precisely \(\{O\}\). Reversing orientation gives all statements for \(F\le0\), with \(-m\) in place of \(m\).

## The angular coordinate and centre passages

The support system has polynomial right-hand side in \(k,k',X\cdot N,X\cdot T\), so the profiles are real analytic. The force cannot vanish identically. Indeed \(W=(k^2/2)T+k'N\) satisfies \(W'=FN\), hence \((W\cdot X)'=F(X\cdot N)+k^2/2\). Its period integral would force \(k=0\), which is incompatible with a unit-speed closed immersion. Thus a force of constant weak sign has isolated zeros. The set \(X^{-1}(O)\) is finite because \(X\) is a compact immersion.

On an arc avoiding the centre, choose a polar argument \(\alpha\) of \(X=r e^{i\alpha}\). Write \(\beta=b/a\) and let \(\vartheta\) be a tangent-angle lift. The polar frame and the profile equation yield
\[
 X\cdot T=rr',\quad X\cdot N=-r^2\alpha',\quad
 \psi=\alpha-\beta\log r,\qquad \psi'=\frac{F}{a r^2}.
\]
For \(F\ge0\) the lift \(\psi\) is strictly increasing on every such arc. Moreover
\[
 \sin(\vartheta-\alpha)-\beta\cos(\vartheta-\alpha)=\frac{F}{ar}\ge0.
\]
It follows that \(\vartheta-\alpha-\arctan\beta\) has a continuous determination in \([0,\pi]\). This uses the ordinary continuous argument on the closed upper semicircle. For a profile avoiding \(O\) it returns to its original value after one period, and
\[
 \psi(s+L)-\psi(s)=\alpha(s+L)-\alpha(s)=2\pi m>0 .
\]
In this case the change of coordinates \(z\mapsto e^{-i\beta\log|z|}z\) on the punctured plane turns the profile into a radius function of the strictly increasing angle \(\psi\), taken modulo \(2\pi m\). The inverse coordinate map rotates by \(+\beta\log|z|\). Every specified ray in the new coordinates is met exactly \(m\) times, with multiplicity in the parameter. A particular noncentral point is met at most \(m\) times. In particular \(m=1\) gives an embedded Jordan curve of nonzero index about \(O\).

At a centre passage the differentiated support equation gives \(F'=-b\). Therefore a one-sign force and a centre passage require \(b=0\). We may take \(\psi=\alpha\) on each component of the complement of the centre. At a centre label \(s_0\), the outgoing direction of \(X(s)/|X(s)|\) tends to \(T(s_0)\), and the incoming direction tends to \(-T(s_0)\), by regularity. The upper-semicircle relative angle tends to \(0\) on the outgoing side and \(\pi\) on the incoming side. Thus one obtains an increasing lift of the position angle over the cut circle with a positive jump of exactly \(\pi\) at each centre passage, by choosing the lift \(\alpha=\vartheta-(\vartheta-\alpha)\) with the indicated relative angle. This gives the identity
\[
 2\pi m=h\pi+\int_{X\ne O}\frac{F}{a|X|^2}\,ds .
\]
The integrand is locally bounded up to a centre label because \(F=F'=0\) there and \(r/|s-s_0|\to1\). The last integral is strictly positive. The angle covers a total of \(2\pi m\) including its jumps, so at most \(m\) labels off the centre can represent any specified nonzero position. One may use half-open periods or translate the cut to a label with a different argument to avoid counting a period endpoint twice. For \(m=1\) at most one label maps to \(O\). If it occurs, the single open arc spans precisely \(\pi\) radians without attaining either endpoint angle. This proves the half-plane and embedding assertions.

Writing \(\tau=\log(\text{scale})\), the physical images of a profile are \(X_\tau=e^\tau R_{\beta\tau}X\). Its transformed angle \(\psi\) is invariant and its radius is multiplied by \(e^\tau\). In the embedded one-sign case, there is just one radius per attained angle. Two such images can therefore meet only at a common centre passage. If they avoid the centre, the nested domains are the inverse images of ordinary nested radial Jordan domains under the displayed change of coordinates, which extends homeomorphically by fixing \(O\).

## Intersections at nearby physical times under a sign change

At every parameter the infinitesimal displacement of \(X_\tau\) at \(\tau=0\) has normal component \((X+\beta JX)\cdot N=-F/a\). There is a single smooth periodic reparametrization \(\sigma_\tau(s)\) close to \(s\) putting this displacement in normal coordinates about the same parameter branch of \(X\). To construct it, solve
\[
 (X_\tau(\sigma_\tau(s))-X(s))\cdot T(s)=0,\qquad \sigma_0(s)=s .
\]
The derivative with respect to the unknown label is one at \(\tau=0\). Compactness provides a uniform neighbourhood of the diagonal, where local implicit solutions agree. This applies at self-intersections because the labels are kept in the neighbourhood of the diagonal. The resulting signed normal displacement \(d_\tau(s)\) satisfies \(\partial_\tau d_0(s)=-F(s)/a\); the derivative of the label contributes only a tangential term. At any two labels with opposite strict values of \(F\), the values of \(d_\tau\) have opposite signs for every sufficiently small nonzero \(\tau\). An intervening label has \(d_\tau=0\) and supplies a genuine intersection. The group law transfers the result to any pair of logarithmic scales with the same sufficiently small difference.

## A force test on every curvature lobe

For a noncircular profile, take two successive zeros of the analytic curvature and let \(\epsilon=\pm1\) be the sign of \(k\) between them. Both zeros have finite order since an identically straight profile cannot be closed. The stress \(W=(k^2/2)T+k'N\) has positive projection on \(T\) throughout the open lobe. Its polar argument there has derivative
\[
 \rho=\frac{\det(W,W')}{|W|^2}
      =\frac{k^2 F}{2((k')^2+k^4/4)} .
\]
The relative argument of \(W\) to \(T\) is \(\arctan(2k'/k^2)\). At the start of the lobe this angle tends to \(\epsilon\pi/2\); at the end it tends to \(-\epsilon\pi/2\). These limits follow by expanding \(k\) at a zero of any finite order. The identity \(k^2/((k')^2+k^4/4)=O((s-s_0)^2)\) near a multiple zero, and boundedness of \(F\), give integrability. Integration yields the exact identity
\[
 \int_{\rm lobe} k\,ds=\epsilon\pi+\int_{\rm lobe}\rho\,ds .
\]
Consequently if the unsigned turning of a lobe is less than \(\pi\), then \(F\) takes the sign opposite to \(k\) somewhere inside it. If the unsigned turning is greater than \(\pi\), then \(F\) takes the same sign as \(k\) somewhere. An unsigned turning equal to \(\pi\) forces both signs of \(F\) inside the lobe, since \(F\) cannot vanish throughout an open interval. Summing these identities gives \(2\pi m=\pi(n_+-n_-)+\int\rho\), with \(n_\pm\) the numbers of positive and negative lobes.

## Zero turning on arbitrary smooth closed elastic flows

The sign change at zero turning persists even without self-similarity or analyticity. On any smooth regular closed plane immersion, let \(W_\varepsilon=(k^2/2+\varepsilon)T+k'N\) for \(\varepsilon>0\). Its projection on \(T\) is strictly positive, so its direction turns by the same total angle \(2\pi m\) as \(T\). Differentiation gives \(W_\varepsilon'=(F+\varepsilon k)N\). Writing \(A_\varepsilon=k^2/2+\varepsilon\) gives a global identity without singular denominators,
\[
 2\pi m=\int \frac{A_\varepsilon(F+\varepsilon k)}
 {A_\varepsilon^2+(k')^2}\,ds .
\]
The absolute contribution of the \(\varepsilon k\) term to the integrand is at most \(\varepsilon |k|/(k^2/2+\varepsilon)\le\sqrt{\varepsilon/2}\). If \(F\ge0\), the remaining term is nonnegative. It is uniformly positive for small \(\varepsilon\) on a fixed compact subarc of positive length where \(F>0\) and \(k\ne0\). Such a subarc exists. The stress identity at the start of the proof excludes \(F\equiv0\), and \(k\equiv0\) on an open interval would give \(F=0\) there. Sending \(\varepsilon\) to zero proves \(m>0\). Reversing the orientation handles \(F\le0\).

Thus every smooth closed plane curve of turning number zero has elastic force of both strict signs. On a smooth regular free elastic flow such a slice meets every sufficiently close distinct time slice, including one-sided comparisons at an initial endpoint where the flow is smooth. The normal-coordinate argument above applies to physical time directly with normal velocity \(-F\). The small time interval may depend on the slice.

These necessary tests constrain the angular visits, force signs and time intersections of the actual profiles. The set of all sign-changing periodic orbits of the support equations is still unclassified.
