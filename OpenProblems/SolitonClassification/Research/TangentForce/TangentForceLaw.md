# A force prescribed by the oriented tangent selects the centered circle

Let \(X=(x,y)\) be a smooth closed immersed plane curve parametrized by arclength, with period \(L>0\). Write \(T=X_s\), \(N=JT\) for counterclockwise quarter-turn \(J\), \(k=\det(X_s,X_{ss})\), and \(F=k_{ss}+k^3/2\). Choose the origin at the center used in the normal similarity equation
\[
 F=-a\langle X,N\rangle-b\langle X,T\rangle .
\]
Assume that \(F=G(T)\) for some function on unit directions. No continuity, differentiability, or bound on \(G\) is required.

Then for constants \(c\ne0,\alpha\) and a nonzero integer \(n\),
\[
 c^4=2a,\qquad cL=2\pi n,\qquad
 X(s)=\frac1c\bigl(\sin(\alpha+cs),-\cos(\alpha+cs)\bigr).
\]
For prescribed \(a,b,G\), such a closed curve exists exactly when \(a>0\) and \(G\) is constant on the entire unit circle with value \(+(2a)^{3/4}/2\) or \(-(2a)^{3/4}/2\). Its radius is \((2a)^{-1/4}\), and the sign of the constant fixes the orientation. Every positive integer \(|n|\) occurs as a covering number. The rotation coefficient \(b\) is unrestricted because rotation about the center moves each point tangentially on the circle.

## Equal tangents and the projected chord

Set \(p=\langle X,N\rangle\), \(q=\langle X,T\rangle\). The Frenet equations give \(p'=-kq,\ q'=1+kp\). The dilation coefficient of a periodic support profile is strictly positive. For any continuous lift of the tangent angle, write \(T=(\cos\theta,\sin\theta)\) after a fixed rotation. Whenever \(\theta(l)=\theta(r)=h\), the endpoint frames agree. In this frame,
\[
 F(l)-F(r)=\langle X(r)-X(l),aN(l)+bT(l)\rangle
 =\int_l^r \bigl(a\sin(\theta(s)-h)+b\cos(\theta(s)-h)\bigr)\,ds.
\]
The hypothesis \(F=G(T)\) makes the left side zero.

Suppose \(k\) takes both signs. Then the angle has an upper excursion with endpoints at a common level \(h\), with \(0\le\theta-h<\pi/2\) on the intervening interval and \(\theta>h\) somewhere inside. To see this, choose a point with \(\theta'>0\) followed by a point with \(\theta'<0\), using periodicity of \(k\) to order the points. The angle attains a maximum strictly above both endpoint values. Take a level less than the maximum by less than \(\pi/2\), still above both endpoint values, and take the component of the strict superlevel set containing a maximizer. The same argument applied to \(-\theta\) gives a lower excursion. This argument permits degenerate extrema.

If \(b\ge0\), take the upper excursion. Both summands of the projected chord are nonnegative there. Its sine summand is positive on an open subinterval because \(a>0\). The integral is strictly positive. If \(b<0\), take the lower excursion. There \(-\pi/2<\theta-h\le0\), so the sine summand is nonpositive and \(b\cos(\theta-h)\) is strictly negative. Either sign contradicts the zero projected chord. Thus \(k\) has one weak sign.

## Recovering the actual position and the prescribed law

The one-sign curvature theorem for periodic support profiles now gives \(k=c\ne0,\ c^4=2a,\ p=-1/c,\ q=0\). Hence \(X=qT+pN=(T_y,-T_x)/c\). The Frenet equation \(T'=cJT\) gives \(T(s)=(\cos(\alpha+cs),\sin(\alpha+cs))\). Periodicity of the actual oriented tangent yields \(cL=2\pi n\). Since \(c\ne0\) and \(L>0\), also \(n\ne0\). The tangent attains every unit direction and \(F=c^3/2\), which proves the claimed restriction on \(G\). Direct substitution gives the converse.

The physical normal speed is \(-F\). Every noncircular closed similarity profile must therefore have two points with the same oriented unit tangent and different normal speeds. This statement applies to pure expanders and rotating expanders, including immersed curves with self-intersections and multiple coverings. It leaves open the classification of profiles whose force takes different values at equal tangents.

The Lean entry points in TangentLawGeometry.lean use force and curvature computed from position derivatives. The support and angle arguments are in TangentForceChord.lean, TangentFold.lean and TangentForceLaw.lean.
