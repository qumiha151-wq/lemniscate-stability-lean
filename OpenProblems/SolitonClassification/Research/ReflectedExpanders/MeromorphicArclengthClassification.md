# Closed similarity profiles with meromorphic arclength curvature

**Theorem.** Suppose the signed arclength curvature of a smooth closed regular free-elastic similarity profile agrees on a nonempty real interval with a single-valued meromorphic function on the complex plane. The profile is a circle or Bernoulli's lemniscate, up to similarity, reparametrization and multiple covers. Both occur. In particular the classification includes elliptic functions of every degree and every lattice. It imposes no order-of-growth bound.

## Complex differential equations for the curvature

Let \(a>0\) and \(\omega\in\mathbb R\) denote the dilation and angular coefficients. For arclength \(s\), signed curvature \(k\), normal support \(p\), and tangential support \(q\), the real profile equations give
\[
 F=k''+k^3/2=-ap-\omega q,\qquad h=aq-\omega p,\qquad
 F'=kh-\omega,\qquad h'=a-kF .
\]
The real profile is analytic by its polynomial support ODE. Away from a real pole of a proposed meromorphic extension, agreement continues by real analyticity. A first pole in either real direction would contradict the finite actual curvature there. A constant open arc yields a constant profile by analyticity. Henceforth assume \(k\) is nonconstant. Its meromorphic extension has the same real period \(L>0\) by the identity theorem.

Extend \(F\) by its differential formula and \(h=(F'+\omega)/k\) meromorphically. The two first-order equations hold on the whole complex plane as meromorphic identities. Eliminating \(h\) without division gives \(kF''-k'(F'+\omega)+k^3F-ak^2=0\), or
\[
 k k''''-k'k'''+\tfrac32 k^2(k')^2+\tfrac52 k^3k''
       +\tfrac12 k^6-ak^2-\omega k'=0.                       \tag{1}
\]

## Laurent calculation at every pole

Write \(z=s-s_*\). At a pole of order \(m>1\), the term \(k^6/2\) has order \(6m\), larger than both \(4m+2\) and \(2m+4\), the largest orders of all the other terms. Thus all poles are simple. For \(k=c/z+O(1)\), the coefficient of \(z^{-6}\) in (1) is
\[
 18c^2+\tfrac{13}{2}c^4+\tfrac12c^6
 =\tfrac12 c^2(c^2+4)(c^2+9).
\]

To exclude \(c=2i\), put \(U=F+ih,\ V=F-ih,\ C=-\omega+ia,\ D=-\omega-ia\). The exact equations are \(U'=-ikU+C,\ V'=ikV+D\). For \(k=2i/z+d+e z+f z^2+g z^3+\cdots\), a pole of \(U\) would have a negative leading exponent equal to \(2\), which is impossible. Thus \(U\) is holomorphic with \(U_0=0\), and comparison of its constant and linear coefficients gives \(U_1=-C,\ 0=-idU_1\). Since \(a>0\), \(U_1\ne0\) and \(d=0\).

The cubic pole of \(F\) cancels since \(2c+c^3/2=0\), and its quadratic pole coefficient is \(3c^2d/2=0\). As \(V=2F-U\), it has at most a simple pole, whereas its differential equation requires the exponent of any pole to be \(-2\). Hence \(V\) is holomorphic, \(V_0=0\), and \(V_1=D/3\). Since \(F=O(z)\), its \(z^{-1}\) coefficient \(-6e\) and its constant coefficient \(-4f\) both vanish. With \(d=e=f=0\), the linear coefficient of \(k''+k^3/2\) equals \((6+3c^2/2)g=0\). Yet the same coefficient of \((U+V)/2\) equals \((\omega-2ia)/3\ne0\). This excludes \(2i\). For \(-2i\) the roles of \(U,V\) and \(C,D\) are exchanged and the conflicting coefficient is \((\omega+2ia)/3\).

It remains to calculate three coefficients when \(c^2=-9\). Write \(k=c/z+\sum_{j\ge1}u_jz^{j-1}\). Once previous \(u_j\)'s vanish, the coefficient of \(u_j z^{j-6}\) in the first five terms of (1) is \(c I_c(j)\). With \(h_0=j-1\) and \((h_0)_m=h_0(h_0-1)\cdots(h_0-m+1)\), direct linearization gives
\[
 I_c(j)=(h_0)_4+24+(h_0)_3+6h_0+
      3c^2(1-h_0)+\tfrac52c^2\big((h_0)_2+6\big)+3c^4.
\]
The two lower-order terms of (1) first enter at \(z^{-2}\), corresponding to \(j=4\). For \(j=1,2,3\) and \(c^2=-9\), the displayed factors are respectively \(105,138,126\). Hence \(u_1=u_2=u_3=0\). At each pole,
\[
 k=c/z+O(z^3),\qquad E:=k''+\tfrac29k^3=O(z).
\]
In particular \(E\) extends to an entire function with a zero at each pole of \(k\). In the elliptic subcase \(E\) is also elliptic and therefore constant. A nonconstant elliptic \(k\) has a pole, forcing this constant to be zero.

## The entire function \(E\) for arbitrary meromorphic curvature

Write \(T(r,k)=m(r,k)+N(r,k)\) for the Nevanlinna characteristic, with \(N(r,k)\) the integrated pole count including multiplicities. The higher logarithmic derivative lemma gives, for \(L_j=k^{(j)}/k,\ j=1,2,3,4\),
\[
 m(r,L_j)=O(S(r)),\qquad S(r)=\log^+T(r,k)+\log r+1
\]
outside a common exceptional set of finite linear measure. This estimate applies at arbitrary order of growth. [Latreuch and Belaïdi, Lemma 14](https://onlinelibrary.wiley.com/doi/10.1155/2014/342974)

On the part of each integration circle where \(|k|\ge1\), division of (1) by \(k^4\) gives
\[
 \tfrac12 k^2=
 -\frac{L_4-L_1L_3-a}{k^2}-\tfrac32L_1^2-\tfrac52L_2
 +\frac{\omega L_1}{k^3}.
\]
Taking \(\log^+\) of absolute values there, bounding the sum by a constant times the product of powers of \(\max(1,|L_j|)\), and integrating gives \(m(r,k)=O(S(r))\). On the complementary arc \(\log^+|k|=0\). The usual sum and product bounds give \(m(r,E)\le4m(r,k)+m(r,L_2)+O(1)=O(S(r))\). Since \(E\) is entire, \(T(r,E)=m(r,E)\).

If \(E\not\equiv0\), every pole of \(k\) is simple and is a zero of \(E\), so
\[
 N(r,k)\le N(r,1/E)\le T(r,E)+O(1)=O(S(r))
\]
by the first main theorem. This also applies to a nonzero constant \(E\). Consequently \(T(r,k)=O(S(r))\). On the other hand, \(k(s_0+nL)=k(s_0)\) for every integer \(n\) and any real \(s_0\). The preimage count for this finite value in \(|s|\le r/2\) is bounded below by a positive multiple of \(r\); each such point away from the origin contributes at least \(\log2\) to the integrated count at radius \(r\). The first main theorem yields \(T(r,k)\ge c_0r\) for all large \(r\), where \(c_0>0\). Thus \(S(r)/T(r,k)\to0\), contradicting the preceding inequality along radii outside the exceptional set. We have proved \(E\equiv0\).

## Identification and converse

We have \(F=5k^3/18\). The real rational-force classification identifies the actual profile with Bernoulli's lemniscate and yields \(\omega=0\). At \(a=1\) it gives \(k'^2=6/5-k^4/9\). In particular, at a positive maximum \(s_0\), \(k(s_0)=A=(54/5)^{1/4}\) and \(k'(s_0)=0\). In Jacobi's modulus convention, uniqueness of \(k''=-2k^3/9\) gives
\[
 k(s)=A\,\mathrm{cn}\!\left(\tfrac{\sqrt2 A}{3}(s-s_0),\tfrac1{\sqrt2}\right).
\]
Indeed at this modulus \(\mathrm{cn}''=-\mathrm{cn}^3\), with initial data \(1,0\). This verifies a doubly periodic meromorphic continuation of the actual Bernoulli arclength curvature, preserved by real dilation, orientation change, and covers. Circle curvature is constant. [Rational-force classification](RationalForceClassification.md) · [NIST DLMF, equation 22.13.14](https://dlmf.nist.gov/22.13.E14) · [NIST DLMF, Jacobi elliptic functions](https://dlmf.nist.gov/22.2)

## Extension to finite algebraic branching

**Corollary.** The classification still holds if the curvature germ on one real open interval is algebraic over the field of single-valued meromorphic functions of complex arclength on \(\mathbb C\). In particular it includes algebraic functions of elliptic functions and of the complex exponential.

Take the monic irreducible polynomial of the germ over that field. The poles of its coefficients and the zeros of its nonidentically-zero discriminant form a discrete set. Outside this set, all roots are locally analytic and continuation permutes the finitely many roots. About any exceptional point \(s_*\), choose a small punctured disk containing no other exceptional point. Set \(z=s-s_*\). A suitable positive integer \(n\) kills the permutation about the puncture, making every continued branch single-valued and holomorphic on the punctured disk in \(w=z^{1/n}\). The elementary root bound for a monic polynomial gives \(|k|\le1+\max_j|a_j|\), where \(a_j\) are its coefficients. These are meromorphic at \(s_*\), hence the branch grows at most as a fixed power of \(1/|w|\). It has a convergent Laurent series in \(w\) with finite principal part. The curvature and stress equations persist by continuation on the sheets reached by the original germ.

At a finite branch value with bounded \(k\), the possibly meromorphic Puiseux series \(U,V\) above cannot have poles: a negative exponent \(-\alpha\) has derivative order \(\alpha+1\), but the right sides of their linear equations have order at most \(\alpha\). Thus \(F\) is bounded and so is \(k''=F-k^3/2\). The Puiseux series for \(k'\) likewise cannot have a pole since its derivative is bounded. Consequently \((k,k',F,h)\) has finite limits on the branch. It obeys a polynomial first-order system at its limiting value. In a uniformizer \(w=z^{1/n}\), the system reads \(y_w=nw^{n-1}f(y)\). The usual analytic solution in \(s\), pulled back by \(s=s_*+w^n\), has the same initial data and agrees by analytic ODE uniqueness in \(w\). Thus the curvature has an ordinary Taylor expansion there.

At an unbounded branch write \(k\sim cz^{-\alpha}\) with positive rational \(\alpha\). For \(\alpha<1\) the uniquely highest-order group in (1) is \(kk''''-k'k'''\), with nonzero coefficient \(3c^2\alpha(\alpha+1)(\alpha+2)\). For \(\alpha>1\) the highest-order term is \(k^6/2\). Hence \(\alpha=1\) and \(c^2=-4\) or \(-9\). In the displayed Laurent linearization the indicial polynomials factor as
\[
 I_{\pm2i}(j)=(j+1)(j-1)(j-4)(j-5),\qquad
 I_{\pm3i}(j)=(j+1)(j-6)(j^2-4j-15/2).
\]
The last two roots are \(2\pm\sqrt{23/2}\), both irrational. If the Puiseux expansion had any noninteger relative exponent, let \(j>0\) be the least such exponent with nonzero coefficient \(u_j\). At \(z^{j-6}\) every product of earlier integer-power terms has integer exponent. Terms involving \(u_j\) and any correction to the leading power have strictly higher order in \(z\). Thus the coefficient there is exactly \(cI_c(j)u_j\), which cannot vanish for a noninteger rational \(j\). This proves that each unbounded branch is meromorphic in \(z\) itself.

All branches accessible from the germ have trivial local monodromy around every finite exceptional point. Any closed continuation path lies in a disk meeting only finitely many exceptional points. Its homotopy class in the punctured disk is generated by conjugates of small loops about those points. All such loops fix the continued germ, so continuation is globally single-valued and the ordinary Laurent expansions fill the exceptional points. The theorem now applies.
