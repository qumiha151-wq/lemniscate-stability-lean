# An explicit universal gap for the cubic curvature moment

With the notation of the [static curvature estimate](StrictHalfThreshold.md),
the following constants give one admissible threshold for every smooth
closed planar free elastic flow. Define

$$
\begin{gathered}
 m=\frac{1}{1000\cdot161^3},\quad
 M_1=\frac{512}{m^2},\quad A_1=20M_1,\quad T=\frac{256\pi A_1}{m},\\
 K=2(A_1+1)^2+2,\qquad \sigma=\frac m{16}\exp(-KT),\\
 \epsilon=\min\left\{\frac18,\frac m{16},
                    \frac{m^2\sigma^2}{1024T^2}\right\},
 \qquad g_*=\frac12-\epsilon .
\end{gathered}
$$

For a periodic real function \(u\) write \(\langle f\rangle\) for the
average over its period. If \(\langle u^2\rangle=1\), set
\(v=u''+u^3/2,\ h=\langle u^3\rangle,\ s=\langle u\rangle,\)
and \(e=\langle v^2\rangle-\langle uv\rangle/2\). We prove

$$
 |s|\le\epsilon,\quad e\le\epsilon
 \quad\Longrightarrow\quad |h|\le \tfrac12-\epsilon .
$$

The constants are deliberately coarse. Their purpose is to give a
finite-window proof with a specified positive gap.

## Bounds for an exact orbit

For the equation \(z''=-z^3/2+z/4+1/4\), every solution is periodic or
the constant 1. The energy is \((z')^2/2+V(z)\), where
\(V(z)=z^4/8-z^2/8-z/4\). We use the turning values \(c-r,c+r\) and
\(d=c^2+(1-c)/(2c)\) of the linked oscillator proof. Here \(0<c<1\),
\(r>0\), and \(c(c^2+r^2-1/2)=1/2\). At \(z=c+r\cos\theta\), the
positive time element on a half period is
\(2\,d\theta/\sqrt{(z+c)^2+d}\). In both ranges \(c\le1/2\) and
\(c\ge1/2\) one has \(d\ge1/4\), so the full period is at most \(8\pi\).

If \(|z|\le A\) on the orbit, \(A\ge2\), its mean over a full period
satisfies

$$
 \mu\ge\frac1{1000(1+A)^3}.
$$

Indeed, let \(N,D\) be the integrals over \(0\le\theta\le\pi\) with
integrands \(z/\sqrt{(z+c)^2+d}\) and \(1/\sqrt{(z+c)^2+d}\)
respectively. Then \(D\le2\pi\) and \(\mu=N/D\).
For \(c\le1/2\), the paired-integral estimate gives
\(N>4\pi c/(385r)\). Now \(r\le A\) and
\(c\ge1/[2(A^2+1)]\). This gives
\(\mu\ge1/[385A(A^2+1)]\).
For \(c\ge1/2\), every pair at \(\theta,\pi-\theta\) has a nonnegative
sum. On \(|\theta-\pi/2|\le1/8\) we have \(r<2\), \(d\le3/2\),
\(z\ge1/4\), and \(\sqrt{(z+c)^2+d}<5\). Thus \(N\ge1/80\)
and \(\mu\ge1/(160\pi)\). The equilibrium has mean one.
Finally the average of any interval of length \(T\) on such an orbit
differs from \(\mu\) by at most \(16\pi A/T\). Complete periods cancel,
and the remaining interval has length at most \(8\pi\).

## Data bounded on one unit interval

Suppose the claimed estimate fails. Reverse \(u\) in sign if necessary
so \(h>1/2-\epsilon\). Write the residual as
\(w=u''+u^3/2-u/4-1/4\). Periodic integration gives

$$
 \langle w^2\rangle=e+(1-2h+s)/8\le 11\epsilon/8\le2\epsilon .
$$

If \(\int_x^{x+1}(u^2+w^2)\le M\) with \(M\ge1\), put
\(B=\max_{[x,x+1]}|u|\). There is a point with \(|u|\le2\sqrt M\) in
each of the two end quarters, so \(|u'|\le8\sqrt M\) somewhere between
them. Since

$$
 \int_x^{x+1}|u''|\le BM/2+5\sqrt M/4+1/4,
$$

we have \(\sup|u'|\le12MB\) if \(B\ge1\). On an interval of length
\(1/(24M)\) adjoining a point of maximum magnitude, \(|u|\ge B/2\);
choose the side which stays in the unit interval. Thus
\(B^2\le96M^2\). Including \(B<1\) gives
\(B\le10M\) and, using the derivative estimate once more,
\(\sup|u'|\le16M^2\).

Start an exact oscillator with initial position and velocity \(u(x),u'(x)\).
Its energy is at most \(1400M^4\). Since \(V(z)\ge z^4/16\) for
\(|z|\ge4\), this exact solution satisfies \(|z|\le20M\) for all times.

## Finite-window comparison

Average the base point \(x\) uniformly over one period of \(u\), with
all functions extended periodically to the line. Call \(x\) good if

$$
 \int_x^{x+1}(u^2+w^2)\le M_1,\qquad
 \int_x^{x+T}w^2\le\sigma^2/T .
$$

Periodic Fubini and Markov's inequality bound the fraction of bad
points by \(2/M_1+2\epsilon T^2/\sigma^2\le m^2/64\).
The set of points satisfying the first condition with \(8\) in place
of \(M_1\) has fraction at least \(3/4\). At least half of all points
are therefore good and satisfy this smaller bound.

At every good point the exact solution from the same data has amplitude
at most \(A_1\) and \(\int_x^{x+T}|w|\le\sigma\).
In the sum norm on position and velocity, the oscillator vector field
has Lipschitz constant at most \(K\) when position stays within
\([-A_1-1,A_1+1]\). Gronwall's inequality up to the first time the
position error reaches one gives a position error at most
\(\sigma e^{KT}=m/16<1\). Consequently the same bound holds throughout
the window. For those good points satisfying the smaller bound \(8\),
the exact orbit has amplitude at most 160 and period mean at least \(m\).
For all other good points its period mean is positive. Since
\(16\pi A_1/T=m/16\), the actual window mean is at least \(7m/8\) on
the smaller set and at least \(-m/8\) at the remaining good points.

The actual window mean \(B_T(x)=T^{-1}\int_x^{x+T}u\) satisfies
\(\langle B_T^2\rangle\le\langle u^2\rangle=1\) by Jensen and
periodicity. The bad points therefore contribute at least \(-m/8\)
to \(\langle B_T\rangle\). Combining the three bounds gives
\(\langle u\rangle=\langle B_T\rangle\ge m/4>\epsilon\), contradicting
the hypothesis. This proves the static estimate with the value displayed
above and, by the length-growth argument, the stated choice of \(g_*\).

The estimates and averaging argument in this note are mathematical
proofs. The project's oscillator modules verify the angular-integral
inequalities. Its dynamic-transfer module takes the static estimate as a
hypothesis and verifies the implications for the geometric flow.
