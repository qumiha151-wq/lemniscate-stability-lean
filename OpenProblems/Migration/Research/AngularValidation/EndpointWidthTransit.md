# Height range forces a positive cost at each migrating endpoint

Let a smooth regular closed free elastic flow move from \(h\le\lambda-g_0\) on a first time slice to \(h\ge\lambda+g_1\) on a second slice. Here \(h\) is any unit projection, \(x\) is the orthogonal coordinate, \(W_i=\max h_i-\min h_i\), \(A_i=\oint h_i\,dx_i\), and \(B_{\delta,i}=\oint\sqrt{x_s^2+\delta^2}\,ds\), where the spatial subscript denotes arclength differentiation. Let \(\Phi_\delta\) denote the actual time integral of the regularized projected-height evolution from the [two-time identity](../OrientedAreaTransit/OrientedAreaTransit.md). Then for each \(\delta>0\),
\[
 \Phi_\delta\ \ge\
 g_0B_{\delta,0}+g_1B_{\delta,1}
 +\max\{|A_0|,\delta W_0^2\}+\max\{|A_1|,\delta W_1^2\}.
\]
At either endpoint the level \(a=\lambda\pm g_i\) lies on one side of the curve. The closed function \((h-a)^2/2\) must travel from its minimum to maximum and return during one period. Its total variation is at least \(W_i^2\), since \(|h-a|\) ranges from some \(b\ge0\) to \(b+W_i\). The derivative of the primitive is \((h-a)h_s\), and \(|h_s|\le1\). Therefore \(\oint |h-a|\sqrt{x_s^2+\delta^2}\,ds\ge\delta W_i^2\). The same residual dominates \(|A_i|\). This proves the stated inequality. The Lean theorem works in the actual material parameter, and allows any ordered pair of labels in each endpoint bound. Selecting the highest and lowest labels in parameter order realizes \(W_i^2\).

The previously checked strip inequality \(E_iW_i\ge 2\) gives the direct lower bound \(\max\{|A_i|,4\delta/E_i^2\}\) per endpoint. The theorem obtains the extremal labels from the actual smooth periodic immersion and uses its position-defined bending energy. [Lean proof](../../Migration/EndpointEnergyTransit.lean)

One can combine the two terms in each maximum as
\[
             \sqrt{(1+\delta^2)|A_i|^2+\delta^2 W_i^4}
\]
by a separate written argument. The vector \((\sqrt{1+\delta^2}\,x_s,\delta |h_s|)\) has norm \(\sqrt{x_s^2+\delta^2}\) since \(x_s^2+h_s^2=1\). Integrate it against the positive measure \(|h-a|\,ds\). The absolute value of its first integrated coordinate is \(\sqrt{1+\delta^2}|A_i|\) because the whole slice is on one side and \(\oint dx=0\). Its second coordinate is at least \(\delta W_i^2\). The integral triangle inequality gives the claim.

The separate unit-speed estimate in [AngularEndpointMoment.lean](../../Migration/AngularEndpointMoment.lean) gives the lower bound \(2W_i/E_i-4/(3E_i^2)\ge8/(3E_i^2)\) for the residual even in the limit \(\delta\downarrow0\). It uses both sides of the farthest point and their shared curvature budget. The application of this spatial estimate to general material coordinates by arclength reparametrization is a written argument in [AngularExcursionBarrier.md](AngularExcursionBarrier.md). The max-form two-time estimate above is checked directly for arbitrary material coordinates in [EndpointWidthTransit.lean](../../Migration/EndpointWidthTransit.lean).
