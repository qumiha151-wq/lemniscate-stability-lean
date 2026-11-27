# Outward initial rate at each sufficiently high prescribed energy level

Let \(m\in\mathbb Z\) and define \(K=L\int k^2\,ds-(2\pi m)^2\). For every prescribed \(K\) satisfying
\[
 Q=\sqrt{K/(4\pi^2 b)}\ \ge 2\cdot10^6(1+|m|),\qquad b=4097/2048,
\]
there is a **real-analytic closed unit-speed plane immersion** of length \(2\pi\), turning number \(m\), and exactly this value of \(K\), at which the initial derivative of \(K\) under the free elastic flow is strictly positive. This includes \(m=0\). Together with the high-turn construction in [LinearOptimality.md](LinearOptimality.md), this proves an existential linear bound valid for all integer turning numbers: there is a universal \(C>0\) such that an initial curve with outward derivative exists on every level \(K\ge C(1+|m|)\). The high-turn construction supplies smooth immersions at linear thresholds. The all-analytic construction proved below has the displayed quadratic threshold.

The conclusion concerns forward invariance of an initial energy sublevel. A curve crossing one specified level need not continue to grow across arbitrarily many levels on the same trajectory.

## A positive trigonometric rate

Write \(\langle g\rangle=(2\pi)^{-1}\int_0^{2\pi}g(x)dx\). Set
\[
 f(x)=2\cos x+\tfrac1{32}\cos 3x,\qquad
 \phi(x)=2\sin x+\tfrac1{96}\sin 3x,\qquad H=f''+f^3/2.
\]
Fourier multiplication gives
\[
 b=\langle f^2\rangle=4097/2048,\quad
 j=\langle fH\rangle=17801219/16777216,\quad
 d=\langle H^2\rangle=60523245573/68719476736,
\]
and \(bj/2-d=6204174335/34359738368>1/6\). For a real Fourier series written in complex exponentials, the nonzero positive-index coefficients of \(H\) at indices \(1,3,5,7,9\) are respectively \(2147/4096,\ 212995/524288,\ 195/8192,\ 3/8192,\ 1/524288\). Reflection gives the negative-index coefficients.

Take \(N\) to be a nearest integer to \(Q\). For \(0\le a\le3\), set
\[
 A^2=Q^2-a^2/(2b),\qquad
 \theta(s)=ms+a\sin s+(A/N)\phi(Ns),\quad
 X(s)=\int_0^s e^{i\theta(v)}dv .
\]
Use the positive square root. We have \(A\ge10^6(1+|m|)\), \(|N-A|\le1\), and \(N>1\). Orthogonality gives \(k=\theta'=m+a\cos s+A f(Ns)\), signed turn \(2\pi m\), and \((2\pi)^2(\langle k^2\rangle-m^2)=(2\pi)^2(a^2/2+A^2b)=K\).

Here is an explicit rate check uniform in \(a\). Write \(w=k/A\), \(h=(k''+k^3/2)/A^3\), and \(e=(1+|m|)/A\le10^{-6}\). Then \(\|w-f(N\cdot)\|_\infty\le3e\), \(\|w\|_\infty\le4\), \(\|f\|_\infty,\|f''\|_\infty\le3\), and \(\|H\|_\infty<17\). The second-derivative error is at most \(3|(N/A)^2-1|+3/A^3\le12e\), and the cubic error is at most \(24\cdot3e\). Hence \(\|h-H(N\cdot)\|_\infty\le84e\) and \(\|h\|_\infty\le18\). Consequently
\[
 |\langle w^2\rangle-b|\le21e,\qquad
 |\langle wh\rangle-j|\le306e,\qquad
 |\langle h^2\rangle-d|\le2940e .
\]
Using \(|\langle wh\rangle|\le72\) and \(b<3\), the total error in \(\langle w^2\rangle\langle wh\rangle/2-\langle h^2\rangle\) from \(bj/2-d\) is at most \(4155e<1/6\). This is the actual derivative of \(EL\) divided by \((2\pi)^2A^6\), where \(E=\tfrac12\int k^2ds\). The sign follows from \(L'=\int kF\,ds\), \(E'=-\int F^2ds\), \(F=k''+k^3/2\).

## Closure for every turning number

For \(m\ne0\), take \(a=0\). The tangent shifts by the factor \(e^{2\pi i m/N}\) under \(s\mapsto s+2\pi/N\). This is a nontrivial \(N\)-th root of unity since \(N>|m|\). Summation of the cell displacements gives exact position closure.

For \(m=0\), oddness of \(\theta\) makes the mean vertical tangent zero. The mean horizontal tangent is a continuous real function of \(a\). Define \(J(z)=\langle\cos(z\sin s)\rangle\) and \(M(c)=\langle\cos(c\phi(s))\rangle\). Oddness also makes the corresponding complex averages real. The cosine expansion and the elementary even moments of sine give \(J(z)=\sum_{k\ge0}(-z^2/4)^k/(k!)^2\). The alternating bounds give \(J(2)\ge2/9\) (through \(k=3\)) and \(J(3)\le-4199/16384<-1/4\) (through \(k=4\)). For \(c=A/N\), the Lipschitz bound for cosine yields
\[
 M(c)\ge J(2)-1/96-3/N>1/5.
\]
At \(a=0\), the horizontal mean is exactly \(M(c)>0\). For the other endpoint use the elementary averaging bound
\[
 \left|\left\langle e^{ia\sin s}e^{ic\phi(Ns)}\right\rangle-
          J(a)M(c)\right|\le 8\pi a/N .
\]
On each complete cell subtract the value of the slow factor at the left endpoint. The fast factor minus its own mean integrates to zero and has magnitude at most two, and the slow factor has Lipschitz constant at most \(a\). Thus at \(a=3\) the horizontal mean is at most \(-1/20+24\pi/N<0\). The intermediate value theorem supplies \(a\) with exact position closure. All spatial derivatives then match periodically and the speed is identically one. The smooth closed free elastic flow exists for these data by the classical global existence theorem recalled in [Miura and Wheeler, Introduction](https://arxiv.org/html/2404.12619v3#S1).

The algebra and the closure estimates above supplement the earlier fixed-turn sequence in [FixedTurningObstruction.txt](../../FixedTurningObstruction.txt). Here the excess is prescribed continuously, including at zero turning.
