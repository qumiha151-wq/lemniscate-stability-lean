# Exponential localization of a closed free elastic flow

Let \(X(u,t)\) be any smooth global closed immersed planar free elastic flow in the material normal gauge. For any fixed origin \(O\), write \(R_O(t)=\sup_u|X(u,t)-O|\). Then
\[
                   R_O(t)=o\!\left(t^{1/3}\sqrt{\log(2+t)}\right).
\]
In particular the entire image, the uniform displacement of all material labels, the smallest enclosing radius and the norm of the arclength centroid grow as \(o(t^{1/3+\varepsilon})\) for every \(\varepsilon>0\), including \(o(t^{2/5})\). The position estimate allows any turning number, multiplicity and self-intersections. It bounds the displacement between endpoints of the motion; the accumulated distance traveled by a label need not equal its endpoint displacement.

## A weighted local energy law

Use arclength \(s\), unit tangent \(T\), left normal \(N\), signed curvature \(k\), force \(F=k_{ss}+k^3/2\), bending energy \(E=\int k^2\,ds/2\), dissipation \(D=\int F^2\,ds\), and \(M(t)=\max_s|k|\). Translate coordinates to \(O=0\). For any unit vector \(v\) and any constant \(a>0\), set
\[
 h=v\cdot X,\qquad q=v\cdot T,\qquad n=v\cdot N,\qquad w=e^{ah},
 \qquad Q_a=\int w(k^2/2+a^2)\,ds .
\]
All spatial integrals count one full period with every traversal. We claim the uniform estimate
\[
             Q_a'(t)\le256(a^4+a^2 M(t)^2)Q_a(t).                    \tag{1}
\]

Indeed \(X_t=-FN,\ (ds)_t=kF\,ds,\ k_t=-F_{ss}-k^2F\). At a fixed material label the bending density obeys
\[
        \partial_t(k^2\,ds/2)=\big[-F^2+(k_sF-kF_s)_s\big]ds.
\]
Now \(h_t=-nF,\ h_s=q,\ h_{ss}=kn\). Differentiate \(Q_a\), and integrate the flux term in this identity twice using periodicity. The result is
\[
 Q_a'=\int w G\,ds,\qquad
 G=-F^2-F(a^2q^2k+\tfrac32 an k^2+2aqk_s)+a^2F(k-an).             \tag{2}
\]
For example the two flux integrations contribute \(-2w_s k_sF-w_{ss}kF\), and the time derivative of the bending weight contributes \(-an wF k^2/2\).

Put \(j=k_s\). The periodic derivative
\[
  8a^2(wkj)_s=8a^2w\big(aqkj+j^2+k(F-k^3/2)\big)
\]
integrates to zero. After subtracting that derivative from \(wG\) and dividing by \(w\), the terms linear in \(F\), alongside \(-F^2\), are
\[
        -F(a^2 q^2 k+\tfrac32 an k^2+7a^2 k+a^3n+2aqj).
\]
For the first four products use \(-Fx\le F^2/8+2x^2\). For the fifth use \(-2aqjF\le F^2/4+4a^2q^2j^2\). The remaining mixed term satisfies \(-8a^3qkj\le4a^2j^2+4a^4q^2k^2\). Since \(|q|,|n|\le1\), the negative term \(-8a^2j^2\) absorbs both positive \(j^2\) terms. The residual is bounded above by \(104a^4k^2+9a^2k^4+2a^6\), which is at most \(256(a^4+a^2k^2)(k^2/2+a^2)\). Multiplying by \(w\) and integrating proves (1).

## Recovering every spatial point from the moment

Write \(L\) for the length, and \(E_0,L_0,R_0\) for the initial energy, length and maximum distance from the origin. Fenchel and Cauchy–Schwarz give \(EL\ge2\pi^2\), and \(E'=-D\). Fix \(m=\min(1,2\pi^2/E_0)>0\); every slice has \(L\ge m\). From any specified point with arclength label \(s\), the next arc of length \(m\), continued periodically across the endpoint if necessary, obeys \(h(x)\ge h(s)-m\) because \(X\) has unit arclength speed. Therefore
\[
       m a^2 e^{a(h(s)-m)}\le Q_a(t).
\]
This holds even when every point of the curve lies in the same distant half-plane. The direction \(v\) in this estimate can be chosen separately for each terminal time and label. Its choice is held fixed throughout the time integration that leads to (1).

Let \(B(t)=\int_0^t M(r)^2dr\). The initial bound and (1) give
\[
   Q_a(t)\le (E_0+a^2L_0)\exp\!\big(aR_0+256[a^4t+a^2 B(t)]\big).
\]
Applying the preceding lower bound to a point attaining \(R_O(t)\), with \(v\) directed toward the point from the fixed origin, yields for \(0<a\le1\)
\[
  R_O(t)\le R_0+m+
     \frac{\log((E_0+a^2L_0)/(m a^2))+256[a^4t+a^2B(t)]}{a}.        \tag{3}
\]
The case \(R_O(t)=0\) is immediate.

## The time scale

The closed-curve stress inequality \(M^6\le2^{24}ED\) and the energy identity imply, for \(t\ge s\ge0\),
\[
   B(t)-B(s)\le C(t-s)^{2/3}
      \left(\int_s^t E(r)D(r)\,dr\right)^{1/3}
    = C(t-s)^{2/3}\left((E(s)^2-E(t)^2)/2\right)^{1/3}.
\]
Since \(E^2\) decreases to a finite limit, splitting at a fixed \(s\) and then taking \(s\to\infty\) proves \(B(t)=o(t^{2/3})\). [Actual material stress inequality](../../LengthGrowth/ActualFlow/ArclengthCoercivity.lean)

Take \(H=\log(2+t)\) and, for \(t\ge2\),
\[
       a=\min\{1,(H/t)^{1/4},(H/(1+B(t)))^{1/2}\}.
\]
Then \(a^4t\le H\), \(a^2 B(t)\le H\), and \(\log(1/a)\le C H\) because \(B(t)\le C(1+t)^{2/3}\). Here and below this \(C\) may depend on the initial curve. Formula (3) gives
\[
 R_O(t)\le C\big[1+H+t^{1/4}H^{3/4}+\sqrt{(1+B(t))H}\big]
              =o(t^{1/3}\sqrt H).
\]
The uniform endpoint displacement follows by the triangle inequality with the initial compact image. The centroid is a weighted average of points in the same disk; the smallest enclosing disk also has radius at most \(R_O(t)\). A long curve can accumulate length within this region. The unrestricted fourth-root upper bound for length remains open. [Miura and Wheeler, free elastic flow for closed planar curves](https://arxiv.org/abs/2404.12619)

## Verification scope

Lean verifies (1) from the actual position-defined normal elastic equation in any smooth material parametrization on an open time interval. The derivative in (1) is the derivative of the integral defining \(Q_a\). Its proof differentiates the position-dependent weight and the measure, computes both components of the spatial velocity derivative and integrates a periodic flux. Lean also verifies the lower bound \(ma^2e^{a(h(u)-m)}\le Q_a\) for every material label at each regular slice. The use of the energy identity and the stress theorem to estimate \(B\), the integration of (1) and the choice of \(a\) in (3) give the written proof of the stated infinite-time asymptotics. [Material differential inequality and point detection](../../LengthGrowth/ActualFlow/MaterialWeightedRate.lean) · [Material first variation](../../LengthGrowth/ActualFlow/WeightedEnergyVariation.lean) · [Weighted spatial estimate](../../LengthGrowth/ActualFlow/WeightedForceRate.lean) · [Geometric point detection](../../LengthGrowth/ActualFlow/ExponentialPosition.lean)
