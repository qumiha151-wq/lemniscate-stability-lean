# Curvature at a nearly straight radial section of an exterior similarity expander

Normalize the dilation rate of a planar free elastic similarity profile to one. Its pitch \(\omega\) can have either sign. Position is \(X\), the arclength frame is \(T,N=JT\), and \(k\) is signed curvature. Choose any positive radial critical point. Rotate and orient the curve so that \(X(0)=(d,0)\), \(T(0)=(0,1)\), \(d>0\). Write

\[
 A=d+|k(0)|+|k_s(0)|+|\omega|,\qquad
 c_*=\frac{\Gamma(1/4)}{2\Gamma(3/4)}=1.47933755\ldots .
\]

An exterior profile here means that its similarity centre lies strictly outside the convex hull of its entire image. The separating direction may depend on the profile.

**Theorem.** For every sequence of exterior closed profiles and radial sections with \(A_j\to0\),

\[
 \liminf_{j\to\infty}\frac{-k_j(0)-c_*d_j}{A_j}\ge0 .
 \tag{1}
\]

There are universal constants \(\kappa>0,\ A_0>0\) such that every such profile with \(0<A<A_0\) satisfies \(-k(0)\ge\kappa A\). In particular a separated small radial section must bend strictly toward increasing radial distance. These conclusions allow nonsymmetric profiles and require no bound on the ratio of rotation to initial distance.

Keeping both arclength directions of the linearized equation gives the stronger estimate

\[
 \liminf_{j\to\infty}
 \frac{-k_j(0)-c_*d_j-
       \dfrac{\Gamma(1/4)}{\sqrt2}
       \left|\dfrac{(k_j)_s(0)}{\sqrt\pi}-\dfrac{\omega_j}{2}\right|}{A_j}
 \ \ge0 .
 \tag{1a}
\]

There is additional rigidity at the boundary of (1). If the quotient in (1) tends to zero, then \(k_s(0)/A\to0,\ \omega/A\to0,\ d/A\to(1+c_*)^{-1}\). Thus approaching this particular curvature ratio requires both the angular coefficient and curvature slope to be of smaller order. The constant \(c_*\) is attained by an everywhere positive solution of the linearized equation. Existence of closed profiles attaining this limit has not been established.

## The actual equation and free separating direction

Put \(T=(-\sin\phi,\cos\phi)\), \(\phi(0)=0\), \(X=(x,y)\), \(v=k_s\). The exact arclength system is

\[
 x'=-\sin\phi,\quad y'=\cos\phi,\quad \phi'=k,\quad k'=v,\quad
 v'=-k^3/2+x\cos\phi+y\sin\phi+\omega(x\sin\phi-y\cos\phi),\quad \omega'=0.
 \tag{2}
\]

In particular the straight solution at the limiting initial data is \((x,y,\phi,k,v,\omega)=(0,s,0,0,0,0)\). For any sequence under consideration, extract a subsequence with

\[
 (d_j,k_j(0),v_j(0),\omega_j)/A_j\longrightarrow(D,K,V,B),
 \qquad D+|K|+|V|+|B|=1,\quad D\ge0 .
\]

On each fixed compact positive or negative time interval the smooth flow of (2) depends differentiably on its initial data in a neighborhood of the straight solution. This follows by local existence and differentiable dependence, using finitely many overlapping neighborhoods of the compact straight segment. Taylor expansion in the finite-dimensional data, followed by (2) for the arclength derivatives, gives \(x_j/A_j\to h\) in \(C^4_{\rm loc}\) and \(y_j=s+O(A_j^2)\) on compact intervals. More explicitly the first variation \(\varphi\) of \(\phi\) satisfies \(h'=-\varphi,\ \varphi'=\delta k,\ \delta k''=h+s\varphi-Bs\). Thus

\[
 h''''-s h'+h= Bs,\qquad
 (h,h',h'',h''')(0)=(D,0,-K,-V).
 \tag{3}
\]

For each exterior profile, choose a unit separator \(e_j=(u_j,w_j)\) with \(e_j\cdot X_j>0\) everywhere. Evaluation at zero gives \(u_j>0\). Evaluation at \(s=\pm1\), using \(x_j(\pm1)=O(A_j)\) and \(y_j(\pm1)=\pm1+O(A_j^2)\), gives \(|w_j|\le C A_j\). Hence \(u_j\to1\), and after extraction \(w_j/A_j\to l\). Passing to the limit on every compact interval yields

\[
                    h(s)+l s\ge0\qquad(s\in\mathbb R).
 \tag{4}
\]

The full-period hypothesis supplies both time directions, and its period can vary without affecting the argument. In particular (4) does not assume that the separating line is normal to the given radius. Taking the even part of (4) removes the unknown tilt and the odd forcing \(Bs\). This step uses parity of the *linear equation*, without imposing any geometric reflection symmetry on the actual curves.

## The even solution and the sign inequality

Define

\[
 H(s)=\int_0^\infty\frac{1-e^{-\xi^4/4}\cos(s\xi)}{\xi^2}\,d\xi.
\]

The integral is finite and strictly positive for all real \(s\). Differentiation under the integral near each fixed \(s\) gives \(H''=\int_0^\infty e^{-\xi^4/4}\cos(s\xi)\,d\xi\). Integrate the derivative of \((1-e^{-\xi^4/4}\cos(s\xi))/\xi\) to obtain \(H-sH'=-H''''\); both boundary terms vanish. In particular \(H(0)=\int_0^\infty \xi^2e^{-\xi^4/4}\,d\xi\). Substitution \(t=\xi^4/4\) now gives \(H''(0)/H(0)=c_*\). Also \(0<H(s)\le H(0)+C|s|\), by bounding the numerator by \(1-e^{-\xi^4/4}+1-\cos(s\xi)\) and scaling in the latter integral.

Let \(G\) solve the homogeneous equation in (3) with data \(G(0)=G'(0)=G'''(0)=0,\ G''(0)=1\). It is even. For \(s\ge0\), \(g=G''\) solves \(g'''=sg\), \(g(0)=1,\ g'(0)=g''(0)=0\). Up to any proposed first zero, successive integrations give \(g''\ge0,\ g'\ge0,\ g\ge1\). Hence \(G(s)\ge s^2/2\). Uniqueness of the linear initial-value problem gives the even part of (3) explicitly as

\[
                  h_{\rm even}=D H/H(0)+(-K-c_*D)G .
\]

If \(-K<c_*D\), the bound for \(H\) and the growth of \(G\) make this negative for sufficiently large \(s\), contradicting (4). This proves (1). If \(K=0\), then \(D=0\) and \(h_{\rm even}=0\). The function \(h(s)+ls\) is odd and nonnegative on the entire line and thus zero. Its derivative at zero gives \(l=0\), and (3) yields \(V=B=0\), contradicting normalization. The uniform \(\kappa,A_0\) follow by a sequential contradiction on the compact normalized data sphere.

## The slope and pitch contribution

Write \(g=h''\), so \(g'''=sg+B\). Its coefficients of degrees \(0,1,2,3\) are \(-K,-V,-D/2,B/6\), respectively. The remaining coefficients obey \(a_{m+4}=a_m/[(m+2)(m+3)(m+4)]\). For \(j=0,1,2,3\) let \(Y_j\) be the twice-integrated series starting with coefficient one at degree \(j\) in \(g\), and with zero constants of integration. Thus

\[
 Y_j(s)=\sum_{n\ge0}
 \frac{s^{4n+j+2}}{(4n+j+1)(4n+j+2)4^{3n}}
 \prod_{r=0}^2\frac{\Gamma(1+(j-r)/4)}
                       {\Gamma(n+1+(j-r)/4)} .
\]

The ratio test gives convergence at every \(s\). Uniqueness or substitution in (3) now yields \(h=D-KY_0-VY_1-DY_2/2+BY_3/6\). The \(Y_j\) have alternating parity, and all terms in each series are positive for \(s>0\). Their positive-direction ratios satisfy

\[
 \frac{Y_j(s)}{Y_0(s)}\longrightarrow C_j
 =4^{3j/4}\prod_{r=0}^2
 \frac{\Gamma(1+(j-r)/4)}{\Gamma(1-r/4)} .
\]

To see this without a special-function asymptotic for \(Y_j\), put \(N=s^{4/3}/4\). The ratio of adjacent terms (next over previous) in series \(j\) is

\[
 \frac{s^4(4n+j+1)}
 {(4n+j+3)(4n+j+4)(4n+j+5)(4n+j+6)}
 = (N/n)^3(1+O(1/n)).
\]

For fixed \(0<\delta<1/2\), the terms outside \([(1-\delta)N,(1+\delta)N]\) contribute a vanishing fraction of each series. Indeed between either endpoint and the corresponding endpoint of the narrower \(\delta/2\) interval the ratio toward the centre is uniformly greater than \(1+c_\delta\). Beyond the outer endpoints the tails are bounded by geometric series toward the centre, with any finite initial terms negligible compared to the intervening geometric growth. Within the outer interval Stirling's gamma ratio formula gives the ratio of the \(j\)-th summand to the zeroth summand at the same \(n\) as \(C_j(N/n)^{3j/4}(1+o(1))\), uniformly there. Bounding from above and below and then sending \(\delta\downarrow0\) proves the stated limits.

In particular \(C_1=\Gamma(1/4)/\sqrt{2\pi},\ C_2/2=c_*,\ C_3/6=\Gamma(1/4)/(2\sqrt2)\). Since \(Y_0(s)\ge s^2/2\), the affine tilt is negligible in comparison. Apply (4) at \(s\) and \(-s\), divide by \(Y_0(s)\), and let \(s\to+\infty\). The two inequalities give \(-K\ge c_*D+|C_1V-C_3B/6|\), proving (1a).

## Rigidity in the equality case

If \(-K=c_*D\), the even part is \(O(1+|s|)\). By (4), the odd part \(h_o\), after adding \(ls\), has absolute value bounded by that even part. Thus \(h_o=O(1+|s|)\). It satisfies the same inhomogeneous equation (3), with right side \(Bs\). On the positive half-line set \(u_R(x)=h_o(Rx)/R\). Extract a weak-star subsequential limit in \(L^\infty_{\rm loc}(0,\infty)\) as \(R\to\infty\). The uniform linear bound gives \(|u(x)|\le Cx\) almost everywhere on the whole half-line. The rescaled equation is \(R^{-4}u_R''''-xu_R'+u_R=Bx\). Testing with compactly supported smooth functions gives \(-xu'+u=Bx\), so \(u(x)/x=C_1-B\log x\). The global bound on \(u/x\) forces \(B=0\).

For zero forcing, the odd solution with \(h_o'(0)=0\) is determined by \(h_o'''(0)=-V\). The fundamental odd solution with third derivative one has second derivative \(g\) satisfying \(g'''=sg,\ (g,g',g'')(0)=(0,1,0)\). The same positivity argument gives \(g(s)\ge s\) and the odd solution grows at least as \(s^3/6\) for \(s\ge0\). The linear bound therefore forces \(V=0\). All normalized subsequential limits in the equality case consequently have \(D=(1+c_*)^{-1},\ K=-c_*D,\ V=B=0\), proving the stated full-sequence assertion.

## What the return condition adds

There is an explicit minimum travel time for *every* closed profile with a small straight-section jet. If \(0<A<1/2\) and

\[
 (1+t)^{2/3} A\exp\!\left(\tfrac32[(1+t)^{4/3}-1]\right)\le\tfrac12 ,
 \tag{5}
\]

then every geometric period \(P\) satisfies \(P>2t\) and \(\max |X|\ge t\cos(1/2)\). To verify this, set \(w=(1+|s|)^{1/3}\). On each side of zero, while \(|k|\le1\), the sum

\[
 U=|x|+w^{-1}|\phi|+w^{-2}|k|+w^{-3}|v|+|\omega|
\]

obeys \(dU/d|s|\le2wU\) almost everywhere. Indeed \(|y|\le|s|,\ |\omega|\le1\), and (2) gives \(|v'|\le |k|/2+2|x|+|s||\phi|+|s||\omega|\). The derivatives of the weights are nonpositive when \(|s|\) increases. Grönwall gives \(U\le A\exp(\frac32[(1+|s|)^{4/3}-1])\); (5) closes the bootstrap and bounds both \(|\phi|,|k|\) by \(1/2\) on \([-t,t]\). Consequently \(y'=\cos\phi\ge\cos(1/2)>0\) there. A full period cannot fit inside that interval. The radius estimate follows at \(t\). This yields at least order \((\log(1/A))^{3/4}\) growth of both period and maximum radius when \(A\to0\).

For pure expansion, combine the travel bound with the previously proved estimate \(R\le C\sqrt{S_{\max}}\), where \(S_{\max}=\max_s\sqrt{k^4/4+k_s^2}\). A sequence of these almost straight sections on closed pure profiles requires \(S_{\max}\ge c(\log(1/A))^{3/2}\) for small \(A\). The stress at the section itself is only \(O(A)\). [Global radius and stress estimate, part 1](../DegenerateHighStress.md)

The projection onto the actual separating direction cannot remain uniformly narrow in the jet units either. For *any* separating unit vectors \(e_j\) as above,
\[
 \frac{\max_s e_j\cdot X_j(s)}{A_j}\longrightarrow\infty .
\]
Otherwise (4) has a finite constant upper bound too. Its even part would be bounded on the full line. The representation of \(H\) yields \(H(s)\ge C|s|-H(0)\), using \(1-e^{-\xi^4/4}\cos(s\xi)\ge1-\cos(s\xi)-(1-e^{-\xi^4/4})\). Since both coefficients \(D\) and \(-K-c_*D\) of the even part are nonnegative and \(G(s)\ge s^2/2\), boundedness forces \(D=K=0\), already excluded. Since \(e_j\cdot X_j(0)\le d_j\le A_j\), the full projected width divided by \(A_j\) also diverges. This controls even a sequence of varying candidate separation axes.

In fact every separating unit direction \(e\) of a sufficiently small section satisfies the quantitative width bound

\[
  \max e\cdot X-\min e\cdot X\ \ge\ c A\bigl(\log(1/A)\bigr)^{3/4}
\]

with a universal \(c>0\). Here are the growing-interval error estimates. Set \(T=(\log(1/A))^{3/4}/8\), \(W=(1+T)^{1/3}\), \(L=\tfrac32[(1+T)^{4/3}-1]\), and \(Q=Ae^L\). For small \(A\), \(L\le\frac14\log(1/A)\) and (5) holds at \(T\). On \([-T,T]\) the preceding bootstrap gives \(|x|\le Q,\ |\phi|\le WQ,\ |k|\le W^2Q,\ |y-s|\le T W^2Q^2/2\). Let \(x_1,\phi_1,k_1,v_1\) solve the first variation with the actual, unnormalized initial jet. Its equations have \(x_1'=-\phi_1\) and \(v_1'=x_1+s\phi_1-\omega s\). The remainders when the actual variables are substituted into these two linear equations are bounded by \(C W^6Q^3\). For the last equation use

\[
 |v'-(x+s\phi-\omega s)|
 \le |k|^3/2+|x|\phi^2/2+|y-s||\phi|
 +|s||\phi|^3/6+|\omega|(|x||\phi|+|y-s|+|s|\phi^2/2).
\]

The middle two equations have zero remainder. Apply the same weighted Grönwall inequality to the difference of the four variables, initially zero. It gives \(\sup|x-x_1|\le C TW^6 A^3 e^{4L}=o(A)\), uniformly in the jet. Write \(e=(u,w_0)\). The fixed-interval argument above gives \(u\ge1/2,\ |w_0|\le CA\) uniformly. The even average of \(e\cdot X(\pm s)/u\) differs by \(o(A)\) from
\[
 F(s)=dH(s)/H(0)+bG(s),\qquad b=-k(0)-c_*d ,
\]
uniformly on this growing interval. Indeed the linear \(s\) contributions to the average of \(y\) cancel, and the remaining tilt error is bounded by \(C A T W^2 Q^2=o(A)\).

Put \(t=T/2\). Positivity at \(\pm T\) implies \(F(T)\ge-o(A)\). The positive series for \(G=Y_0\) starts at degree two, so \(G(t)/G(T)\le1/4\). Consequently the even average at \(t\) is at least \(d[H(t)-H(2t)/4]/H(0)-o(A)\). The Fourier integral gives \(|H(s)-C_0|s||\le H(0)\) with \(C_0=\int_0^\infty(1-\cos z)z^{-2}dz>0\), so this lower bound is at least \(c_1 d t-o(A)\) for large \(t\). If \(d\ge\kappa A/(2c_*)\), it controls the maximum by a positive multiple of \(At\). In the remaining case \(b\ge\kappa A/2\) by the uniform curvature theorem, and \(G(t)\ge t^2/2\) gives the same conclusion. Subtracting \(\min e\cdot X\le d\le A\) gives the asserted width.

These estimates exclude near-straight exterior returns on a bounded length or radius window and exclude initial directions violating (1), even with unbounded periods. Periodicity supplies no uniform upper bound on \(x_j/A_j\) on the full real line. A positive even solution \(H\) and the even solutions \(H+\epsilon G\) for \(\epsilon>0\) are consistent with (4). The limiting straight arm and the travel-time estimate therefore leave the distant nonlinear part of a possible closed exterior trajectory uncontrolled. This is a written analytic result. Existence or exclusion of exterior closed profiles beyond this range remains open.
