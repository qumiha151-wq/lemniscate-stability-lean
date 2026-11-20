# Prescribing the physical radius at a seam crossing

Consider the normalized support flow
\[
k'=v,\qquad v'=-k^3/2-p,\qquad p'=-kq,\qquad q'=d+kp.
\]
For seam curvature \(c\) use initial state \((c,0,1,0)\). For \(d>0\) set \(\lambda=d^{-1/4}\). If \(z_d\) is the normalized trajectory, the actual dilation-coefficient-one trajectory at physical arclength \(s\) is
\[
(\lambda k_d,\lambda^2v_d,\lambda^3p_d,\lambda^3q_d)(\lambda s).
\]
This follows by differentiating each of the four coordinates and applying uniqueness of the global support flow. The initial state satisfies both physical seam conditions \(v=q=0\).

Write \(r_d=\sqrt{p_d^2+q_d^2}\). At normalized time \(u\) the physical radius is \(\lambda^3r_d(u)\). Its inverse four-thirds power, the incoming parameter used to match two shots, is exactly \(d\,r_d(u)^{-4/3}\) when \(r_d(u)>0\).

For every pair of real times,
\[
                         |r_d(u)-r_d(v)|\le |d|\,|u-v|.
\]
Indeed \((r_d^2)'=2dq_d\). For each \(h>0\) the function \(\sqrt{h+r_d^2}\) has derivative bounded by \(|d|\), since \(|q_d|\le\sqrt{h+r_d^2}\). Apply the mean-value inequality and take \(h\downarrow0\). This proof includes passages through the physical origin. In particular \(1-|d|T\le r_d(u)\le1+|d|T\) for \(|u|\le T\), independently of \(c\).

Fix \(e>0\) with \(4eT\le1/2\) and any continuous selection of times \(u(d)\) on \([0,4e]\) with \(|u(d)|\le T\). Throughout this interval \(r_d(u(d))\) lies between \(1/2\) and \(2\). The continuous map \(d\mapsto d\,r_d(u(d))^{-4/3}\) starts at zero and reaches at least \(e\) at \(d=4e\). Thus some \(d\in(0,4e]\) realizes exactly the prescribed physical radius parameter. [Physical support conjugacy and global radius bound](../../SolitonClassification/PhysicalSeamScale.lean) · [Realization at a prescribed radius](../../SolitonClassification/SeamRadiusExistence.lean)

## A continuous selection across seam curvatures

Let \(c\) run through a compact set and suppose the crossing times \(u(c,d)\) are continuous jointly, bounded, and uniformly Lipschitz in \(d\) on a strip \(0\le d\le D\), where \(DT\le1/2\). The scale factor \(a(c,d)=r_d(u(c,d))^{-4/3}\) is uniformly Lipschitz in \(d\). To see this, first compare states at the same time using continuous dependence with a uniform Grönwall bound on the compact slab. The \(p,q\) components each have absolute value at most two, so \(p^2+q^2\) inherits a Lipschitz bound there. To change the evaluation time on one trajectory, use the radius speed bound and the Lipschitz constant of \(u\). Finally \(x^{-2/3}\) is Lipschitz on \([1/4,4]\).

Write \(K\) for the resulting scale-factor Lipschitz constant and \(m=1/4\) for a common lower bound for \(a\). Choose \(S>0\) with \(S\le D\) and \(SK\le m/2\). For \(0\le x\le y\le S\),
\[
y a(c,y)-x a(c,x)
=(y-x)a(c,y)+x(a(c,y)-a(c,x))
\ \ge\ (m/2)(y-x).
\]
It follows that for every \(0\le e\le Sm\) there is a unique \(d\in[0,S]\) satisfying \(d a(c,d)=e\). This choice is jointly continuous. Indeed if \(d_0\) solves the equation for \((c_0,e_0)\), then the solution for \((c,e)\) differs from \(d_0\) by at most \(2|e-d_0a(c,d_0)|/m\). This argument treats \(e=0\) as well as positive \(e\).

The actual crossing times of a particular section must satisfy the stated boundedness, continuity and Lipschitz hypotheses to use the family conclusion. Establishing these properties depends on the geometry of that section. These radius calculations alone do not close the centre shot to a periodic orbit.
