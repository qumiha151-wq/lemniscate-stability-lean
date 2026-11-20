# Which dilation factors can occur between two slices?

Let \(X\) be a smooth regular closed planar free elastic flow on \(0\le t<\infty\), smooth up to its initial curve. A **return** is a pair of distinct times \(s<t\) such that the immersed curve at \(t\) equals the curve at \(s\) up to a direct plane similarity and a diffeomorphism of the parameter circle. This definition retains the number of traversals, including for self-intersecting curves. Either orientation of the parameter is allowed.

**Theorem.** Exactly one of three alternatives holds.

1. The flow has no return.
2. There exists a least return factor \(\lambda_*>1\), and the return factors are exactly its positive integer powers.
3. Every dilation factor greater than one is a return factor. There is a point \(c\), a physical time \(T_*<0\), and a real number \(b\) such that

   \[
   [X(t)]=[c+\rho(t)e^{i b\log\rho(t)}(X(0)-c)],\qquad
   \rho(t)=\big((t-T_*)/(-T_*)\big)^{1/4}.
   \]

The brackets allow a change of parameter. Every return, if any exists, has the same spatial centre and the same fixed time in its parabolic scaling. A single return forces positive finite upper and lower bounds on \(L(t)/(1+t)^{1/4}\). Consequently a counterexample to the fourth-root upper bound must have no return. In particular, two returns with an irrational ratio of their log dilation factors force continuous self-similarity with a single angular coefficient.

The second alternative does not supply an example of a discretely repeating flow. The third leaves open the unrestricted classification of the profiles themselves. For the free elastic flow and its original questions see [Miura and Wheeler, §1.2](https://arxiv.org/abs/2404.12619).

## Uniqueness on a common time interval

For two geometric flows agreeing at a positive terminal time, choose a fixed orientation for each parameter circle and match their terminal fractional-arclength coordinates. A reversal is permitted when choosing the orientation. The terminal positions, signed curvatures, tangents and lengths then agree. Take the two clocks \(d\tau=L_i^{-4}dt\) with the same value zero at this time, and choose the zero-mean tangential gauge in each. The clock may initially depend on the flow. The fields
\[
K_i=L_i k_i,\quad f_i=(K_i)_{xx}+K_i^3/2,\quad
v_i=\int_{\mathbb T}K_i f_i,\quad (w_i)_x=v_i-K_i f_i,\quad
\int_{\mathbb T}w_i=0
\]
satisfy \((K_i)_\tau=-(f_i)_{xx}+(K_iw_i)_x\). For \(z=K_1-K_2\) the difference \(K_1f_1-K_2f_2\) has \(L^2\) norm at most \(C\|z\|_{H^2}\) on compact smooth time intervals. Integration gives the same bound for \(|v_1-v_2|\); periodic Poincaré gives it for \(\|w_1-w_2\|_2\). Subtracting the expanded curvature equations now gives
\[
\|z_\tau+(1+\partial_x^4)z\|_2
 \le C(\|z\|_2^2+\|z_{xx}\|_2^2)^{1/2}.
\]
All coefficients are bounded on any compact smooth subinterval ending at the matching time. For clarity, with \(A=1+\partial_x^4\), \(g=z_\tau+Az\), \(Z=\|z\|_2^2\), the estimate reads \(\|g\|_2\le C\langle Az,z\rangle^{1/2}\). Hence \(Z'\le C^2 Z/2\). While \(Z>0\) put \(Q=\langle Az,z\rangle/Z\). Completing the square in

\[
 Q'=-2\|(A-Q)z\|_2^2/Z+2\langle(A-Q)z,g\rangle/Z
\]

gives \(Q'\le C^2Q/2\), while \((\log Z)'\ge-2Q-2C\sqrt Q\). Thus \(Q\) stays bounded forward until a putative finite first zero of \(Z\), which keeps \(\log Z\) bounded below. The forward and backward conclusions follow.

The remaining equations recover the actual immersed curves. They are
\[
(L_i)_\tau=v_iL_i,\qquad dt_i/d\tau=L_i^4,\qquad
(T_i)_\tau=(-\partial_x f_i+K_iw_i)JT_i,\qquad
(X_i)_\tau=L_i(-f_iJT_i+w_iT_i).
\]
With the common terminal data these give equality of lengths, of physical times, of tangents at each label and finally of positions. On every compact common physical interval the clocks are nonsingular; if one backward clock reached the chosen earlier physical endpoint first, equality of the recovered physical times forces the other to reach the same endpoint there. This proves geometric backward uniqueness on the original time domain. Forward uniqueness follows from the forward estimate by the same reconstruction. The initial endpoint is included by continuity for a solution smooth up to zero.

## One orbit recurrence

The energy \(E=\tfrac12\int k^2ds\) is positive and satisfies \(E'=-\int F^2ds<0\). Strictness follows from the closed-curve dilation virial \(\int F(X-c)\cdot N\,ds=-E\). Since \(E\) scales by \(\lambda^{-1}\), each match in forward time has \(\lambda_i>1\). Put \(a_i=\lambda_i^4\) and \(f_i(t)=a_i(t-s_i)+t_i\); here \(f_i\) is a time map. The curves \(X(t)\) and \(S_i^{-1}X(f_i(t))\) are both free elastic flows in \(t\). At \(t=s_i\) they agree modulo reparametrization. Two-sided uniqueness gives \([X(f_i(t))]=[S_iX(t)]\) wherever \(t\ge0\) and \(f_i(t)\ge0\). A zero initial matching time needs only forward uniqueness.

The unique time fixed point \(T_i=(a_i s_i-t_i)/(a_i-1)\) is strictly less than \(s_i\). If \(T_i\ge0\), applying the recurrence there gives \(E(T_i)=E(T_i)/\lambda_i\), which contradicts positivity. Thus \(T_i<0\); the recurrence applies at every \(t\ge0\). Its length component makes \(L(t)/(t-T_i)^{1/4}\) periodic in \(\log(t-T_i)\) with period \(\log a_i\) on its half-line. It is continuous, positive and bounded above and below on one fundamental interval. The ratios \((t-T_i)/(1+t)\) are also bounded above and away from zero, proving the two length bounds.

## All returns share their centres

The compositions \(f_1f_2\) and \(f_2f_1\) give energy \(E(t)/(\lambda_1\lambda_2)\) at both resulting times. Strict monotonicity forces the times to agree. The two affine time maps therefore have the same fixed point \(T_*\). The linear parts of the direct similarities commute in the plane, so \(S_1S_2(S_2S_1)^{-1}\) is a translation. The two compositions at the common time show that this translation preserves a nonempty compact curve image, hence is zero. Each expanding similarity has a unique fixed point, and commutation forces these points to be the same \(c\). This comparison also applies to two different choices of similarity for the very same pair of times.

## The closed group of return factors

Fix one return and the centres \(c,T_*\) just obtained. Write \(y=\tfrac14\log((t-T_*)/(-T_*))\) and let \(Y(y)\) be the class of \(e^{-y}(X(t)-c)\) in fractional-arclength parameters. The quotient identifies parameter rotations and reversals on the unit circle. Its distance is the infimum, over this compact parameter group, of uniform distances between representatives. It is a metric since the group acts by isometries and the infimum is attained. The trajectory is continuous, and multiplication by unit complex numbers acts continuously. Immersed constant-speed representatives of the same parametrized geometry differ by exactly such a parameter isometry.

For \(p=\log\lambda>0\) of the chosen return there is a unit complex number \(U\) such that \(Y(y+p)=UY(y)\) for \(y\ge0\). This extends the path consistently and continuously to all real \(y\): choose \(n\ge0\) with \(y+np\ge0\) and set \(Y(y)=U^{-n}Y(y+np)\).

Let \(G\) consist of all \((h,V)\in\mathbb R\times S^1\) satisfying \(Y(y+h)=VY(y)\) for every real \(y\). It is a closed subgroup by continuity. Its real projection \(P\) is closed because the other factor is compact. Each return gives a positive \(h=\log\lambda\) in \(P\). Indeed it shares the same centres, holds for all nonnegative times, and extends to negative \(y\) by the \(p\)-recurrence and commutation of rotations. Conversely every positive \(h\in P\) gives a return of factor \(e^h\) from every nonnegative physical time. The closed subgroup \(P\) contains \(p>0\). If its positive elements have positive infimum \(p_*\), then closedness gives a least positive element and division with remainder gives \(P=p_*\mathbb Z\). Otherwise \(P\) is dense and closed, hence \(P=\mathbb R\).

Suppose \(P=\mathbb R\) and let \(H=\{V:(0,V)\in G\}\). The allowed angular multipliers over \(h\) form one coset modulo \(H\). The resulting homomorphism \(\mathbb R\to S^1/H\) is continuous: along a convergent sequence of shifts, use compactness of angular representatives and closedness of \(G\) to identify every subsequential limit in the quotient. If \(H\) has finite order \(n\), raising to the \(n\)-th power identifies \(S^1/H\) with the circle. Every continuous homomorphism from the line to the circle is \(h\mapsto e^{i a h}\), by lifting through the exponential covering and using continuity and additivity of the lift starting at zero. Taking \(b=a/n\) proves the displayed formula.

The only other closed subgroup of the circle is the whole circle. In that case one can take \(b=0\). Each image is a centred circle: its continuous set of radii, if nonconstant, would generate an annulus of positive area, impossible for a smooth immersed loop. Regularity permits an integer covering of this circle. This proves the alternatives and includes all multiplicities.

The closed-group argument, the cyclic-or-full conclusion, all shifts from two incommensurate shifts, and commutation of clocks under an injective energy law are proved in [ReturnScales.lean](../../SolitonClassification/ReturnScales.lean). The passage from one matching pair of immersed curves to global recurrence, and the recovery of its fixed angular coefficient, are proved analytically above. The independent LengthGrowth project checks the scalar implication from a recurring length to the two-sided fourth-root bound.
