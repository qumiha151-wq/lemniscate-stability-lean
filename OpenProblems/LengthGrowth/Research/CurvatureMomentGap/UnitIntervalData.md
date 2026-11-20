# Local data and exact oscillator bounds

Let \(u\) be a smooth real function, and on \([x,x+1]\) let
\[
w=u''+u^3/2-u/4-1/4,\qquad
\int_x^{x+1}(u^2+w^2)\,ds\le M,\qquad M\ge1.
\]
The theorem `LengthGrowth.OscillatorLocal.unit_interval_data` proves that every point of this interval satisfies \(|u|\le10M\) and \(|u'|\le16M^2\). It applies to smooth functions on the whole line, including periodic extensions.

The proof chooses a minimum of \(u^2\) on each end quarter. Both selected values have magnitude at most \(2M\), and their separation is at least one half. A mean-value point between them has \(|u'|\le8M\). If \(B\) is the maximum of \(|u|\) on the unit interval, its defining maximum is attained. The residual identity gives the pointwise bound
\[
 |u''|\le (B/2+1/2)(u^2+w^2)+7/8 .
\]
Integration and the fundamental theorem of calculus therefore bound every \(|u'|\) by \(8M+(B/2+1/2)M+7/8\). When \(B\ge1\), this is at most \(12MB\). An interval of length \(1/(24M)\) containing a maximizer fits inside the unit interval. Throughout it \(|u|\ge B/2\). The integral hypothesis implies \(B^2\le96M^2\), which gives the claimed bounds.

For a smooth exact solution \(z''=-z^3/2+z/4+1/4\), define
\[
 E_z(t)=(z'(t))^2/2+(z(t)^4-z(t)^2-2z(t))/8 .
\]
The theorem `oscillatorEnergy_constant` differentiates this expression and proves conservation. The theorem `exact_orbit_from_unit_interval` combines conservation with the local estimate. If \(z(a)=u(x)\) and \(z'(a)=u'(x)\), then for all \(t\)
\[
 E_z(t)\le1400M^4,\qquad |z(t)|\le20M,\qquad |z'(t)|\le60M^2.
\]
The formal statement applies to any smooth exact solution on the real line with the indicated data. Its proof uses the existing quartic potential from the period-numerator module.
