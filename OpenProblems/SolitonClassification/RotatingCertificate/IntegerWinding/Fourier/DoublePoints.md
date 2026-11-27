# Exactly two ordinary double points on the primitive winding-one expander

The primitive rotating expander in [WholeOrbitFourier.md](WholeOrbitFourier.md) has exactly **two distinct self-intersection points**. Each has exactly two preimages and the two unit tangents are transverse. The double-point Gauss word, starting at the marked initial point, is **A B B A**. The statements concern the full smooth immersed curve.

Orient the curve so its initial tangent equals $1\in\mathbb C$. The support reconstruction is $X=(q+ip)e^{i\theta}$, with $\theta(\xi)=\lambda_*\int_0^\xi k(\eta)\,d\eta$ in the normalized label of the Fourier proof. Integrating the Fourier polynomial explicitly gives
\[
 \hat\theta(\xi)=\hat\lambda\left(\hat k_0\xi+
       \sum_{n\ne0}\hat k_n\frac{e^{in\xi}-1}{in}\right).
\]
Choose the signed representative $|\xi|\le\pi$. The certified global error $10^{-19}$ for $k,p,q$, the length error $|\pi\hat\lambda-l_*|<2\cdot10^{-30}$ and $l_*<31$, $|k|<9$ give $|\theta-\hat\theta|<10^{-16}$. These bounds enter every interval computation of position and tangent.

For a uniform grid of $M$ labels, a full cell has physical arclength at most $61/M$. Each projected coordinate of each point of the cell differs from its initial value by at most this amount, because the true curve is parametrized by arclength. If two distinct labels have circular arclength distance below $1/10$, they cannot have equal position: along the shorter arc the tangent differs in angle from the initial tangent by less than $9/10$, so the displacement has strictly positive projection along that initial tangent. This also handles the seam of the parametrization.

For each of the remaining unordered cell pairs, the two position squares must intersect if there is a crossing. The verifier registers each square in every square lattice bin that it meets, using outward-rounded integer endpoints. Any pair with overlapping squares appears in at least one common bin. Pairs whose coordinate centres are farther than $2(61/M)$ in either coordinate are discarded. With $M=32768$ there are 42 remaining pairs in two clusters. With $M=49152$ there are 45 in two clusters. Every retained pair is included in the next step.

In one cluster choose grid labels $i,j$ and an arclength radius $r$ large enough that the square of offsets $[-r,r]^2$ covers the entire cluster. For the true arclength curve define
\[
 F(u,v)=X(s_i+u)-X(s_j+v),\qquad
 J_0=[T(s_i),-T(s_j)],\qquad B=J_0^{-1}.
\]
The interval determinant excludes zero. Throughout the square, the induced maximum matrix norm satisfies $\|DF-J_0\|_\infty\le18r$ by $|k|\le9$. The verifier checks both $q=18r\|B\|_\infty<1$ and $\|B F(0,0)\|_\infty+qr<r$. Therefore $z\mapsto z-BF(z)$ maps the closed square into itself and contracts it. Its unique fixed point is the unique crossing in that square, and $DF$ is invertible there. All four single-label enclosures are pairwise disjoint even after allowing periodic wrapping. If both crossings had the same image, combining labels from different pairs would give additional roots. Thus both image points are ordinary double points.

On the finer mesh, A has labels near $10374/49152$ and $14742/49152$, and B near $11129/49152$ and $13569/49152$, as fractions of one traversal. The respective physical arclength box radii are below $0.0050$ and $0.0038$. The calculations use exact integer polynomial defects, the earlier validated shooting bounds, and rigorous interval tests. The continuum counting and fixed point arguments are written proofs. Run [the replay](replay.py) to verify the numerical certificates, including both grids.
