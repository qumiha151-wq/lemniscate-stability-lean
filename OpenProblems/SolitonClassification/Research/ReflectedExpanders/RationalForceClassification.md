# Closed similarity profiles with rational elastic force

**Theorem.** Let a smooth closed regular planar immersion be a similarity profile of the free elastic flow. Parameterize by arclength, write its signed curvature as \(k\), and put \(F=k_{ss}+k^3/2\). Suppose that on some nonempty open parameter interval \(F=G(k)\) for a real rational function \(G\) defined there. Up to Euclidean similarity, reparametrization and multiple covers, the only possibilities are the circle and Bernoulli's lemniscate. Both occur. For every noncircular example satisfying the hypothesis the angular coefficient is zero and \(F=5k^3/18\) everywhere.

**Continuation and removal of rotation.** Write \(G=N/D\) in lowest terms. With the similarity centre as origin and the normal given by positive quarter-turn of the unit tangent, the normal and tangential supports \(p,q\) satisfy
\[
 k_s=v,\qquad v_s=-k^3/2-ap-\omega q,\qquad
 p_s=-kq,\qquad q_s=1+kp .
\]
The dilation coefficient \(a\) is positive for closed regular profiles. The vector field is polynomial, so all four components and \(F\) are real analytic on the whole parameter line. The analytic identity \(D(k)F=N(k)\) extends from the interval to that line, across its endpoints and across every critical point of \(k\). No real number attained by \(k\) can be a zero of \(D\), since it would also be a zero of \(N\).

The one-sign curvature rigidity theorem gives positive and negative curvature values for every noncircular closed profile. One short derivation uses \(B=\int k^2\), \(C=\int k^3\), \(L=\int1\), and \(\rho=\sqrt{B/L}>0\). Periodic integration of the support equations gives \(\int F=C/2\), \(\int kF=aL\), and \(\int F^2=aB/2\). For the last identity the derivatives of \(vp+k^2q/2\) and \(vq-k^2p/2-k\) are \(Fp+k^2/2\) and \(Fq\), respectively. Cauchy–Schwarz twice gives \(|C|\le L\rho^3\). If \(k\ge0\), the integral of the nonnegative function \((k+\rho/2)(k-\rho)^2\) is \(C-L\rho^3\le0\), so \(k=\rho\). Reversing orientation handles \(k\le0\).

At any curvature zero differentiation gives \(G'(0)v=F_s=-\omega\), since \(F_s=k(aq-\omega p)-\omega\). If any zero has \(v=0\), then \(\omega=0\). Otherwise all zeros are simple. Periodicity and both curvature signs give an upward and a downward crossing, so the same formula again implies \(\omega=0\). Dilate by \(a^{1/4}\) to normalize the coefficient to one. A dilation by \(\lambda\) sends the force law to \(y\mapsto\lambda^{-3}G(\lambda y)\), preserving rationality. Now \(p=P(k)=-F\) for a rational \(P\).

**A rational identity.** Write \(x\) for the curvature variable. Define \(H\) on the curvature range by
\[
 H'(x)=-x^3-2P(x),\qquad H(k)=v^2 .
\]
An antiderivative gives the first identity and differentiation fixes a single additive constant for the second. On an open subinterval where \(kv\ne0\), put \(r(x)=P'(x)/x\). The equations \(p_s=-kq\) and \(q_s=1+kp\) give
\[
 q=-r(k)v,\qquad r'H+\tfrac12 rH'+1+xP=0.                    \tag{1}
\]
If \(r'\) is identically zero, \(P(x)=c_2x^2+c_0\), already a polynomial. Otherwise (1) expresses \(H=(-1-xP-rH'/2)/r'\) as a rational function on a smaller nonempty interval. Its rational derivative coincides identically with \(-x^3-2P\). Therefore (1) holds as an identity of complex rational functions.

Zero is in the curvature range and is a regular point of \(P\). At any other finite pole \(\zeta\), a simple pole of \(P\) is impossible because a rational derivative has zero residue. For a pole of order \(d\ge2\), let \(u=x-\zeta\) and \(P\sim C u^{-d}\). Then
\[
 H\sim \tfrac{2C}{d-1}u^{1-d},\quad
 r\sim-\tfrac{dC}{\zeta}u^{-d-1},\quad
 r'H+\tfrac12rH'\sim
 \tfrac{3d+1}{d-1}\tfrac{dC^2}{\zeta}u^{-2d-1}.
\]
The nonzero leading term cannot cancel \(1+xP\), whose pole has order \(d\). Thus \(P\) has no finite complex pole and is a real polynomial.

**Polynomial comparison.** If \(P\sim c x^d\) at infinity with \(d>3\), then \(H\sim-2c x^{d+1}/(d+1)\), \(r\sim dc x^{d-2}\). The leading term of \(r'H+rH'/2\) is \(-3d(d-1)c^2x^{2d-2}/(d+1)\), while \(1+xP\) has degree \(d+1<2d-2\). This excludes all degrees above three.

There is a simple sign-changing zero of \(k\). Indeed, if \(k_s=0\) at a sign-changing zero, its second derivative also vanishes, so \(p=0\) there. The pure support ODE then has the straight solution \(k=v=p=0,\ q=q_0+s-s_0\) through that state, contradicting periodicity by uniqueness. At a simple zero, \(P'(0)v=p_s=0\), hence \(P'(0)=0\). Write
\[
 P=c_3x^3+c_2x^2+c_0,\quad r=3c_3x+2c_2,\quad
 H=A-(1/4+c_3/2)x^4-(2c_2/3)x^3-2c_0x .
\]
The coefficients of (1), from \(x^4\) to \(1\), are
\[
 -c_3(5/4+9c_3/2),\quad -7c_3c_2,\quad -2c_2^2,\quad
 (1-9c_3)c_0,\quad 3c_3A-2c_2c_0+1 .
\]
The quadratic coefficient gives \(c_2=0\), and the constant coefficient now excludes \(c_3=0\), including every degree at most two and the case \(r'\equiv0\). The remaining equations give
\[
 c_3=-5/18,\qquad c_0=0,\qquad A=6/5 .
\]

**Identification of the profile.** The formulas imply \(q=5kv/6\) by continuation. At an upward curvature crossing the state is \((k,v,p,q)=(0,\sqrt{6/5},0,0)\). Bernoulli's lemniscate in Miura and Wheeler's normalization has \(k^3=-27p\) and \(a=15/2\), hence after normalization to \(a=1\) it has \(p=-5k^3/18\). At an upward crossing \(q=5kv/6=0\) and \(q_s=1=5v^2/6\), giving exactly the same state. Uniqueness of the polynomial support ODE identifies the two profiles globally. The Frenet reconstruction determines the plane curve after an initial rotation, and different closed parametrizations may traverse its primitive period more than once. Constant-curvature closed immersions are covers of circles and have constant force. The Bernoulli cubic persists under every spatial dilation. [Miura and Wheeler, §2.2.3](https://arxiv.org/html/2404.12619v3#S2.SS2.SSS3)
