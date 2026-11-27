# Exterior prescribed centres for exact expanding flows

Take the sequence of matched zero-turn pure expanders \(X_j\), with coefficient one, centre zero, maximum radius \(R_j\), root-mean-square force \(\sqrt{E_j/L_j}\asymp R_j\), and scaled profiles converging in Hausdorff distance after rotation to the segment \([-1,1]\times\{0\}\). The precise limits and reflection argument appear in [the optimal-centre proof](OptimalExteriorDefect.md).

For the unit vertical vector \(e\), \(w_j=\max|X_j\cdot e|>0\) and \(w_j/R_j\to0\). Central symmetry makes the height extrema exactly \(\pm w_j\). Put \(c_j=\sqrt{w_jR_j}\) and translate to \(Y_j=X_j+c_je\). Relative to the prescribed centre zero, the image lies in the height strip \([c_j-w_j,c_j+w_j]\). Its nominal double has lowest height \(2(c_j-w_j)\) and hence separation gap \(c_j-3w_j\). Its ratio to the initial width \(2w_j\) diverges.

The force \(F=k_{ss}+k^3/2\) is preserved by translation. Since \(F=-X_j\cdot N\),
\[
 F+Y_j\cdot N=c_j e\cdot N .
\]
The dilation virial gives \(\int F^2ds=E_j\), and the supremum dominates the root mean square. Thus
\[
 \frac{\|F+Y_j\cdot N\|_2}{\|F\|_2}\le
 \frac{c_j}{\sqrt{E_j/L_j}}\to0,\qquad
 \frac{\|F+Y_j\cdot N\|_\infty}{\|F\|_\infty}\le
 \frac{c_j}{\sqrt{E_j/L_j}}\to0 .
\]
The actual images are \(c_je+\rho(t)X_j\), where \(\rho(t)=(1+4t)^{1/4}\). Every image passes through \(c_je\). At \(\rho=2\) the candidate double differs from the true image by translation through \(c_je\). This distance is \(o(R_j)\) but its ratio to the transverse width diverges. At any \(\rho\ge1\) the residual of the instantaneous comparison with dilation about zero at rate \(\rho^{-4}\) is \(\rho^{-4}c_j(e\cdot N)\), and the true force is \(\rho^{-3}F\). The preceding relative bounds therefore improve by the factor \(1/\rho\).
