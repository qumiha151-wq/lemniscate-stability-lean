import SolitonClassification.ForceWindingInjective

noncomputable section
open Function
namespace ClosedSimilarity.ForceWinding

private theorem reflected_point (θ F H:ℝ→ℝ) (s:ℝ) :
    liftedPoint (fun t=> -θ t) (fun t=> -F t) H s =
    -(starRingEnd ℂ) (liftedPoint θ F H s) := by
  rw [liftedPoint_eq,liftedPoint_eq,Circle.coe_exp,Circle.coe_exp,Complex.exp_mul_I,Complex.exp_mul_I]
  apply Complex.ext <;>
    simp only [Complex.neg_re,Complex.neg_im,Complex.conj_re,Complex.conj_im,Complex.mul_re,
      Complex.mul_im,Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,rect_re,rect_im,
      Complex.cos_ofReal_re,Complex.cos_ofReal_im,Complex.sin_ofReal_re,Complex.sin_ofReal_im,
      Real.cos_neg,Real.sin_neg] <;> ring

theorem negative_turn_crossing {a b L:ℝ} {k θ F H:ℝ→ℝ} (ap:0<a) (lp:0<L) (rot:b≠0)
    (dθ:∀s,HasDerivAt θ (k s) s)
    (dF:∀s,HasDerivAt F (k s*H s-b) s) (dH:∀s,HasDerivAt H (a-k s*F s) s)
    (pf:Periodic F L) (ph:Periodic H L) (turn:∀s,θ (s+L)=θ s-2*Real.pi)
    {s t:ℝ} (st:s<t) (near:t<s+L) (co:liftedPoint θ F H s=liftedPoint θ F H t) :
    (∃u,F u<0) ∧ ∃v,0<F v := by
  constructor
  · by_contra! pos
    have q := positive_turn ap lp dθ dF dH pf ph (τ:= -(2*Real.pi))
      (fun u=>by rw [turn];ring) pos (avoids_centre_of_rotating rot dF pos)
    linarith only [q,Real.pi_pos]
  · by_contra! neg
    let Fn := fun s=> -F s
    let θn := fun s=> -θ s
    let kn := fun s=> -k s
    have dn (s:ℝ) : HasDerivAt Fn (kn s*H s-(-b)) s := by apply (dF s).neg.congr_deriv;dsimp [kn];ring
    have dh (s:ℝ) : HasDerivAt H (a-kn s*Fn s) s := by simpa only [kn,Fn,neg_mul_neg] using dH s
    have dt (s:ℝ) : HasDerivAt θn (kn s) s := (dθ s).neg
    have pp (s:ℝ) : 0≤Fn s := neg_nonneg.mpr (neg s)
    have tp (s:ℝ) : θn (s+L)=θn s+2*Real.pi := by dsimp [θn];rw [turn];ring
    have fp : Periodic Fn L := fun s=>by dsimp [Fn];rw [pf]
    apply one_turn_distinct ap dt dn dh fp ph tp pp (avoids_centre_of_rotating (neg_ne_zero.mpr rot) dn pp) st near
    rw [show liftedPoint θn Fn H s= -(starRingEnd ℂ) (liftedPoint θ F H s) from reflected_point θ F H s,
      show liftedPoint θn Fn H t= -(starRingEnd ℂ) (liftedPoint θ F H t) from reflected_point θ F H t,co]

/-- Force changes sign on a winding-minus-one rotating closed immersion having
a self intersection. The return equality is checked on the actual x,y curve. -/
theorem physical_crossing {a b L:ℝ} {k θ p q:ℝ→ℝ} (ap:0<a) (lp:0<L) (rot:b≠0)
    (dθ:∀s,HasDerivAt θ (k s) s)
    (dp:∀s,HasDerivAt p (-(k s)*q s) s) (dq:∀s,HasDerivAt q (1+k s*p s) s)
    (pp:Periodic p L) (pq:Periodic q L) (turn:∀s,θ (s+L)=θ s-2*Real.pi)
    {s t:ℝ} (st:s<t) (near:t<s+L)
    (ex:profileX p q θ s=profileX p q θ t) (ey:profileY p q θ s=profileY p q θ t) :
    (∃u, -a*p u-b*q u<0) ∧ ∃v,0< -a*p v-b*q v := by
  let F := fun s=> -a*p s-b*q s
  let H := fun s=>a*q s-b*p s
  have dF (u:ℝ) : HasDerivAt F (k u*H u-b) u := by
    apply (((dp u).const_mul (-a)).sub ((dq u).const_mul b)).congr_deriv;dsimp [H];ring
  have dH (u:ℝ) : HasDerivAt H (a-k u*F u) u := by
    apply (((dq u).const_mul a).sub ((dp u).const_mul b)).congr_deriv;dsimp [F];ring
  have pf : Periodic F L := fun u=>by dsimp [F];rw [pp,pq]
  have ph : Periodic H L := fun u=>by dsimp [H];rw [pp,pq]
  apply negative_turn_crossing ap lp rot dθ dF dH pf ph turn st near
  dsimp only [F,H];rw [liftedPoint_physical,liftedPoint_physical,ex,ey]

end ClosedSimilarity.ForceWinding
#print axioms ClosedSimilarity.ForceWinding.physical_crossing
