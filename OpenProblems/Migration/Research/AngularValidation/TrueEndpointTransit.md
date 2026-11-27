# A uniform energy cost at both ends of a migrating closed flow

Fix a smooth regular closed planar free elastic flow, any unit height direction, and any positive smoothing parameter \(\delta\). Suppose the complete initial and final images obey \(h_0\le\lambda-g_0\) and \(h_1\ge\lambda+g_1\). With the regularized projected length \(B_{\delta,i}\), oriented area \(A_i\), and integrated force expression \(\Phi_\delta\) of the [two-time identity](../OrientedAreaTransit/OrientedAreaTransit.md), one has
\[
 \Phi_\delta\ \ge\ g_0 B_{\delta,0}+g_1 B_{\delta,1}
  +\max\{|A_0|,8/(3E_0^2)\}
  +\max\{|A_1|,8/(3E_1^2)\}.
\]
Here \(E_i=\tfrac12\oint k_i^2\,ds\). The lower bounds on the two endpoint contributions are uniform as \(\delta\) decreases and remain positive for zero gaps and zero signed areas. The theorem uses the original position-defined force and bending energy; it applies to arbitrary material labels and turning number. It gives a necessary condition for complete migration.

For a single endpoint above a line, choose a material label where height is largest. Its tangent is horizontal by differentiability, and the absolute projection of its unit normal in the vertical direction is one. Integrating positive speed constructs a global strictly increasing arclength coordinate on the lifted parameter line. Subtracting its positive linear trend gives a bounded periodic function, so it maps onto the whole real line. The smooth curve supplies the derivative of its inverse. Integrating curvature in the translated arclength coordinate gives an angle \(\theta\) with \(\theta(0)=0\). Differentiating the rotated tangent and normal projections with the Frenet equations proves \(|x_s|=|\cos\theta|\). Changing variables identifies angular energy, endpoint moment and physical bending energy over a full material period.

The two flanks at that extremal material label give the estimate \(2W/E-4/(3E^2)\) from the [spatial calculation](AngularExcursionBarrier.md), where \(W\) is the actual directional width. The required room on the period follows by traversing both material arcs between a lowest and a highest point, each of length at least \(W\). The closed-curve strip inequality gives \(EW\ge2\). Reflection yields the same result for the other half-plane. Combining the two endpoint moments with the material force identity proves the uniform bound above. The [smoothing-dependent estimate](EndpointWidthTransit.md) remains available at every positive parameter.

[Arclength construction](../../Migration/MaterialArclength.lean) · [Frenet transport and integral change of variables](../../Migration/MaterialAngleAtSupport.lean) · [Actual material endpoint moment](../../Migration/TrueEndpointMoment.lean) · [Two-time bound](../../Migration/TrueEndpointTransit.lean)
