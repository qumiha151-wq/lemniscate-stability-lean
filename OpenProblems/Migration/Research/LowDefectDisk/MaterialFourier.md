# Fourier estimates for the actual arclength tangent

Take a material slice of a smooth closed regular plane curve with signed total curvature \(2\pi\). Write \(L\) for its length, \(c\) for its arclength centroid, and \(D=(L\int k^2\,ds-4\pi^2)/(4\pi^2)\). In fractional arclength \(x=s/L\), let \(T\) be the unit tangent, \(G=(2\pi/L)(X-c)\), and \(t_n\) the \(n\)-th Fourier coefficient of \(T\). Norms and integrals below use the interval of length one.

For the material immersion itself, Lean proves \(t_0=0\), \(\sum |t_n|^2=1\), \(\sum n|t_n|^2=1\), and \(\sum(n-1)^2|t_n|^2=D\). The proof obtains the arclength coordinate from the inverse cumulative length and uses the Frenet derivative of that tangent. [Material arclength identities](../../Migration/LowDefectMaterialModes.lean)

If \(D\le 0.14\), then \(1-|t_1|^2\le0.26D\) and \(|t_2|\le0.266D\). The quadratic bound on the second coefficient uses \(|T|=1\) and closure. [Second coefficient](../../Migration/LowDefectSecondHarmonic.lean)

For the same actual slice, \(\int_0^1|G+iT|^2 dx\le(0.75)^2D\). At nonzero frequencies the position coefficient is \(-it_n/n\). Its combination with the normal has squared coefficient \((1-1/n)^2 |t_n|^2\). The signed first moment and the exceptional second coefficient control the sum. Centering by the actual arclength centroid gives a zero constant position mode. [Normal-position correction](../../Migration/LowDefectMaterialCorrection.lean)

The uniform spatial remainder for the position and its use in the directional support and flux bounds are additional steps in the common-disk argument. [Physical disk proof](LowDefectPhysicalDisk.md)

