# Opposite transverse limits for two symmetric seams

Choose the frozen position to be \(e_y=(0,1)\) and absorb its magnitude by cubic scaling of the arclength variable. Write \(T=(\cos\theta,\sin\theta)\), \(N=JT\), \(p=e_y\cdot N=\cos\theta,\ q=e_y\cdot T=\sin\theta\). The differential system is
\[
 k'=v,\qquad v'=-k^3/2-p,\qquad p'=-kq,\qquad q'=kp .
\]
Every solution considered here satisfies \(p^2+q^2=1\). A symmetric seam has data \((k,0,1,0)\) at time zero. The profiles in this note are those of the frozen transition equation.

Put \(W=(k^2/2)T+vN,\ A=|W|,\ H=W\cdot e_y,\ B=W\wedge e_y\), using the determinant with \(e_x\wedge e_y=1\). Then \(W'=-pN,\ H'=-p^2,\ B'=pq,\ |W'|\le1\). Finite-time global existence follows from \(|k|\le\sqrt{2A},\ |v|\le A\). For a symmetric seam, \(k,p,B,A\) are even and \(v,q,H\) odd by uniqueness of the polynomial system. It is enough to study the outgoing end with \(h=-H\). Its transverse limit equals the transverse limit on the incoming end.

## Two explicit averaging formulas

Write \(e=W/A,\ \eta=e\cdot e_y=H/A,\ \zeta=Je\cdot e_y=B/A\) where \(A>0\). Let \(U\) be the oscillator \(U''=-U^3/2,\ U(0)=0,\ U'(0)=1\). On its unit energy oval use the phase \(\phi\) specified by \(k=\sqrt A\,U,\ v=Aw,\ w=U',\ u=U^2/2\). Hence \(w^2+u^2=1,\ T=ue-wJe,\ N=we+uJe,\ p=w\eta+u\zeta,\ q=u\eta-w\zeta\). Here \(U,w,u\) are evaluated at \(\phi\). Direct differentiation gives
\[
 A'=-pw,\quad e'=-(pu/A)Je,\quad
 \eta'=-pu\zeta/A,\quad\zeta'=pu\eta/A,\qquad
 \phi'=\sqrt A+Up/(2A).
\]
The phase formula follows from the equation for \(k'\) where \(w\ne0\), or from the equation for \(v'\) at its turning points. These formulas need no choice of a global lift.

For \(I=B/\sqrt A=\sqrt A\,\zeta\), put
\[
 \Psi=\tfrac16 U^3(\eta^2-\zeta^2/2)-\tfrac12 Uw\eta\zeta,\quad
 \chi=\tfrac13 Uw(\eta^2-\zeta^2)+\tfrac13 U^3\eta\zeta,
 \qquad J=I-\Psi/A,\quad \widehat h=h-\chi/\sqrt A.
\]
The identities \((Uw)_\phi=3w^2-2,\ (U^3)_\phi=6uw\) give
\[
 \Psi_\phi=pq+\tfrac12\zeta pw,\qquad
 \chi_\phi=p^2-(1+\eta^2)/3.
\]
Using these and the differential system above yields the exact remainder
\[
 A^2 J'=pU\left[-uw(\eta^2/3+\zeta^2/12)
                    +(u^2/2+3w^2/4)\eta\zeta\right].                 \tag{1}
\]
For example the expression before simplification is
\(p[-U\Psi_\phi/2+u(\zeta\Psi_\eta-\eta\Psi_\zeta)-w\Psi]\).

Here are explicit bounds, with rounded constants enlarged in every estimate. If \(\eta=\cos a,\ \zeta=\sin a\), the oscillatory part in \(2a\) of \(\Psi-U^3/24\) has amplitude \(|U|/4\), and \(\chi\) has amplitude \(|U|/3\). Thus \(|\Psi|,|\chi|\le\sqrt2/3<0.472,\ |\chi_a|\le2\sqrt2/3\), and \(|\chi_\phi|\le2/3\). In \(\widehat h'\), after subtracting \((1+\eta^2)/3\), the terms involving phase drift, direction drift and amplitude drift are bounded by
\[
 A^{-3/2}\big[(2/3)\sqrt2/2+2\sqrt2/3+\sqrt2/6\big]<1.66 A^{-3/2}.
\]
Since \(|uw|\le1/2,\ |\eta\zeta|\le1/2,\ |U|\le\sqrt2\), formula (1) yields
\[
 |J'|<0.77/A^2.
\]
If also \(|I|\le0.4,\ A\ge11\), then \(|\zeta|\le0.4/\sqrt{11}\), which improves this to \(|J'|<0.37/A^2\).

## Escape and sections

All the nonstraight symmetric seam data at time zero reach every sufficiently large outgoing radial level and the corresponding incoming levels by reflection. Indeed \(h(0)=0,\ h'(0)=1\) and \(h'=p^2\ge0\). Suppose \(h\) had a finite positive limit. If \(A\) were unbounded, then for an arbitrarily large \(M=A(t)\), one has \(A\ge M/2\) for the following \(M/2\) time units. On that interval \(\widehat h'>0.28\) once \(M\) is large, contradicting boundedness. If \(A\) is bounded, so are \(k,v,p,q\). The omega-limit set is compact and invariant, and \(h\) is constant on it. Every complete orbit in it satisfies \(p=0\), hence \(q=\pm1,\ k=v=0\), giving \(h=0\), again a contradiction. This proof allows any real initial seam curvature, including \(k=0\). The corrected incoming section is \(\widehat H=H+\chi/\sqrt A\); by symmetry it equals the outgoing \(\widehat h\) at reflected times since \(\chi\) changes sign. For large \(h\), \(\widehat h'\) is positive uniformly. All earlier states with bounded \(A\) must be excluded from the section definition near \(A=0\); use the crossing on the large-amplitude part of the orbit.

Along each escaping end \(J\) has a finite limit. For \(h\ge11\), \(\widehat h'>0.28\), \(A\ge h\ge\widehat h-0.143\), and \(\int A^{-2}ds<\infty\). Moreover \(I-J\to0\). These limits and the strict corrected-section crossings are defined on the entire seam-curvature interval \([-1/4,1]\). Crossing times for a sufficiently large fixed section are uniformly bounded on this compact interval, by continuous dependence, compactness and transversality. One can alternatively use a fixed ordinary large \(h=L\) as a preliminary entrance; its monotonicity and eventual escape give a uniform time bound by a finite cover.

## Two strict signs

At \(s=20\), for seam curvature \(-1/4\), verified real enclosures give \(h>13,\ -0.10<J<-0.09,\ |I|<0.25\). For seam curvature \(1\) they give \(h>12,\ J>0.8\). The signs of the two limits follow with room to spare using only \(h>11\) at this starting time. Let \(d=0.143\); then \(|\widehat h-h|<d\), including at later times.

For the negative input work until a hypothetical first \(|I|=0.4\). On this whole interval \(\eta^2\ge1-0.16/11,\ \widehat h'>0.61\), so
\[
 |J(s)-J(20)|\le\frac{0.37}{0.61(\widehat h(20)-d)}
 <\frac{0.37}{0.61\cdot10.7}<0.057 .
\]
Since \(|I-J|<0.472/11\), throughout this interval \(|I|<0.21\), ruling out the stopping event. Thus \(I_\infty<-0.033\). For the positive input the uniform bounds give
\[
 |J(s)-J(20)|\le \frac{0.77}{0.28\cdot10.7}<0.258,
 \qquad I_\infty>0.542.
\]
Consequently the curve of symmetric seams intersects every sufficiently large incoming corrected section in a continuous path whose endpoints have transverse data of strictly opposite sign, bounded away from zero uniformly as the level increases.

## Finite validated calculation

The two initial states are exact rationals. The [checker](frozen_seams.py) advances all four coordinates using Arb real balls at 512-bit precision. It takes 2,048 equal steps on \([0,20]\) using Taylor order 38. On each step with initial enclosure \(z\) and width \(r\), it checks \(h\sup_{z+[-r,r]}|f_i|<r_i\) coordinatewise. A first-exit argument puts the full true step inside that box. Taylor coefficients through degree 37 are evaluated on the starting enclosure; the degree-38 remainder is evaluated on the tube. The coefficient recurrences use the displayed polynomial ODE. Thus all endpoints enclose the unique true solution. Every strict terminal comparison used above is asserted in the checker. From this directory run the following with Python and python-flint 0.9.0.

~~~sh
python frozen_seams.py negative
python frozen_seams.py positive
~~~

The [negative certificate](negative_seam.json) gives \(h(20)=13.45058747349863028202097\ldots,\ J(20)=-0.09848108914527997945321050\ldots\). The [positive certificate](positive_seam.json) gives \(h(20)=12.33211778476564736766204\ldots,\ J(20)=0.9021025263281717045061802\ldots\).
