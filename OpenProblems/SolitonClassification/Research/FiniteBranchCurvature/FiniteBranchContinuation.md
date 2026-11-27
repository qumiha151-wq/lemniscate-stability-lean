# Removal of isolated finite monodromy for closed similarity profiles

Let \(k\) be the signed arclength curvature germ of a smooth closed free elastic similarity profile. Suppose it can be continued meromorphically along every path in \(\mathbb C\setminus\Sigma\) from its initial germ, for a closed locally finite set \(\Sigma\). For each \(s_0\in\Sigma\) and each branch transported into a sufficiently small punctured disk about \(s_0\), assume its orbit under one turn about \(s_0\) is finite. The orbit length may depend on the branch and on \(s_0\). Then the germ has a single-valued meromorphic continuation to all of \(\mathbb C\). The meromorphic curvature classification gives a circle or a Bernoulli lemniscate, including multiple covers.

The finite local monodromy hypothesis gives a representation \(s=s_0+w^m\) on each such orbit, with \(k=f(w)\) meromorphic in the punctured \(w\)-disk. It gives no growth estimate at \(w=0\). In particular poles of \(f\) could a priori accumulate there. The next three arguments deal with these possibilities.

## A bounded curvature branch needs only one rectifiable path

Suppose a branch is holomorphic along a rectifiable path approaching a point \(s_0\) of the complex time plane, and \(|k|\le M\) along that path. The branch then agrees on its tail with an ordinary holomorphic solution at \(s_0\). This local assertion does not require finite monodromy.

Set \(v=k'\), \(F=k''+k^3/2\), and let the support component \(h\) satisfy \(F'=kh-b\), \(h'=a-kF\). The complex variables \(U=F+ih,\ V=F-ih\) satisfy
\[
 U'=-ikU-b+ia,\qquad V'=ikV-b-ia .
\]
The support variables are obtained by continuing the full physical system. Equivalently, \(h=(F'+b)/k\) away from curvature zeros. At an interior regular point of \(k\), meromorphic poles of \(U,V\) are incompatible with these linear equations, so both extend there. The constant-curvature case is immediate.

Take an arclength parametrization \(\gamma:[0,L)\to\mathbb C\) of the path. Along it the absolute differential inequalities for \(U,V\) give bounds depending only on \(M,L,a,b\) and the starting state, by Grönwall. Hence \(F,h\) are bounded. Integrating \(v'=F-k^3/2\) bounds \(v\) as well. All four \(s\)-derivatives of \(Y=(k,v,F,h)\) given by the first-order system are now bounded along the path. The values of \(Y\) are Cauchy along its tail and have a finite limit \(Y_*\).

The polynomial vector field
\[
 Y'=\Phi(Y)=(v,F-k^3/2,kh-b,a-kF)
\]
has a holomorphic local solution \(Y_0\) with \(Y_0(s_0)=Y_*\). On a small tail both \(Y(\gamma(t))\) and \(Y_0(\gamma(t))\) lie in a fixed ball where \(\Phi\) is Lipschitz. Their difference at time \(t\) is at most the tail integral of a fixed constant times its absolute value. Taking the supremum on a tail of length less than the reciprocal of that constant makes the supremum zero. Holomorphic uniqueness through any point on that tail identifies the continued branch with \(Y_0\). This proves the bounded-branch assertion. [Ilyashenko and Yakovenko, *Lectures on Analytic Differential Equations*, Theorem 1.1](https://doi.org/10.1090/GSM/086)

## An accumulation of poles would itself fill the puncture

Translate \(s_0\) to zero, and choose \(R>0\) so the base punctured disk \(0<|s|<R\) has no other exceptional values. The ordinary-pole calculation for this equation gives the germ identity \(k(s_1+t)=-k(s_1-t)\) at each genuine pole \(s_1\) on an ordinary sheet. It uses the resonance calculation at the simple poles with principal coefficient \(\pm3i\) in complex arclength. The difference of a solution and its odd reflection must start at a resonance; the only positive integer resonance is 6, whose coefficient multiplies the odd power \(t^5\). The difference itself contains only even powers. The other pole types \(\pm2i\) are excluded by the stress equations and \(a>0\).

If \(f\) has a pole over \(s_1\) with \(0<|s_1|<R/3\), lift the two segments \((1-t)s_1\) and \((1+t)s_1\), \(0\le t<1\), starting on that sheet. Ordinary poles on the segments permit meromorphic continuation. Odd reflection at \(s_1\) continues along the paired segments by the identity theorem. The second segment ends at \(2s_1\ne0\), an ordinary value in this disk. Its lifted branch is meromorphic there. Reflect that final germ to obtain a single-valued meromorphic germ \(H(s)\) at zero. On a small open portion of the first lifted segment \(f(w)=H(w^m)\). Both sides are meromorphic throughout a small punctured \(w\)-disk. The identity theorem there gives the same equality on the whole punctured disk. This fills the puncture and rules out an accumulation of poles of that branch at its end.

## A uniform estimate on every pole-free disk

There is a constant \(C_{a,b}\) such that every holomorphic solution of the scalar equation in a disk \(B(z_0,d)\), \(0<d\le1\), satisfies \(|k(z_0)|\le C_{a,b}/d\). The constant is independent of the branch and of the center.

For \(0<d_0<d\), maximize \((d_0-|z-z_0|)|k(z)|\) on the closed disk of radius \(d_0\). Call its value \(A\). If \(A>0\), at a maximizing point put \(\delta=d_0-|z-z_0|>0\), \(K=|k(z)|=A/\delta\). Everywhere in the disk of radius \(\delta/2\) about this point one has \(|k|\le2K\). The Cauchy derivative estimates at the maximizing point are
\[
 |k^{(j)}|\le 2^{j+1}j!\, K\,\delta^{-j},\qquad 1\le j\le4.
\]
Multiply the scalar equation
\[
 k^6=-2(kk''''-k'k''')-3k^2(k')^2-5k^3k''+2ak^2+2bk'
\]
by \(\delta^6\) and take absolute values. Since \(\delta\le1\), the Cauchy bounds yield
\[
 A^6\le 2304 A^2+288 A^4+2|a| A^2+8|b| A .
\]
Indeed the constants for the four derivative estimates are \(4,16,96,768\). If \(A\ge1\), division by \(A^4\) gives \(A^2\le2592+2|a|+8|b|\). Thus \(d_0|k(z_0)|\le \max(1,\sqrt{2592+2|a|+8|b|})\); let \(d_0\) increase to \(d\).

Suppose now that an orbit over \(0<|s-s_0|<R\) has no poles, as one may assume after the preceding section. For \(0<|s-s_0|<\min(R/2,1)\), the simply connected disk \(B(s,|s-s_0|/2)\) lifts through every point of that orbit. The bound gives
\[
 |k(s)|\le\frac{2C_{a,b}}{|s-s_0|}.
\]
This estimate also holds for a pole-free orbit of infinite monodromy. For finite monodromy \(s-s_0=w^m\), it says directly that \(w^m f(w)\) is bounded. The removable singularity theorem therefore gives a convergent Laurent series for \(f\) with pole order at most \(m\).

## Descent of the resulting Puiseux series

A finite limit is handled by the bounded-branch argument. Otherwise write \(f\sim c(s-s_0)^{-\alpha}\) with \(\alpha>0\) rational. For \(\alpha>1\) the sextic term has the unique highest pole order. For \(0<\alpha<1\) the quadratic derivative terms have the unique highest order and nonzero combined leading coefficient. Hence \(\alpha=1\), with \(c^2=-4\) or \(-9\). For a first fractional power \(u_j(s-s_0)^{j-1}\) with rational noninteger \(j>0\), its coefficient in the scalar equation at power \(j-6\) is a nonzero constant times \(I_c(j)u_j\). Earlier terms contribute only integer powers to this coefficient. The indicial polynomials are
\[
 I_{\pm2i}(j)=(j+1)(j-1)(j-4)(j-5),\qquad
 I_{\pm3i}(j)=(j+1)(j-6)(j^2-4j-15/2).
\]
Neither has a noninteger rational zero. Thus the Laurent expansion in \(w\) uses only exponents divisible by \(m\). Its convergence gives a meromorphic function of \(s\). The detailed Laurent calculation appears in the [meromorphic arclength proof](https://github.com/qumiha151-wq/lemniscate-stability-lean/blob/c0f32c929f04d8bcc0f3b661c8ac4b4f630223a0/OpenProblems/SolitonClassification/Research/ReflectedExpanders/MeromorphicArclengthClassification.md).

Every local monodromy orbit over each exceptional value therefore fixes the transported germ. A closed continuation path lies in a disk meeting finitely many exceptional values. The punctured disk fundamental group is generated by conjugates of loops about those values, all of which fix the germ on the appropriate sheet. Continuation is globally single-valued, and the local fillings give a meromorphic function on \(\mathbb C\).

## Formal scope

The Lean theorem `ClosedSimilarity.RamifiedBounded.isolated_finite_branch_descends` proves the local removal step for every finite cover and arbitrary positive dilation and real rotation coefficient. Each ordinary chart can itself be meromorphic. The returned function is meromorphic in the original arclength variable and agrees with the lifted curvature on a whole punctured neighborhood. The chart hypotheses impose no bound on the curvature and allow poles inside the punctured cover. Lean represents meromorphic germs by complex-valued functions; normal form fixes their point values at ordinary poles.

The two local mechanisms have separate entries. `finite_principal_of_charts` proves the finite principal part on a cover carrying holomorphic ordinary charts, using `disk_curvature_bound`. The latter gives the explicit constant in the inverse-distance estimate above. `descends_of_nearby_pole` constructs the base meromorphic germ directly by odd reflection. `bounded_curvature_descends` also supplies a holomorphic base germ when just the curvature is bounded in a punctured cover and the four support equations hold there.

The single bounded rectifiable path criterion above and the passage from topological finite local monodromy to a covering coordinate are written arguments. The general case of infinite local monodromy is outside the scope of the finite-cover theorem.
