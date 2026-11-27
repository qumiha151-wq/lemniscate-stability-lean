import SolitonClassification.ForceWindingRegularized

noncomputable section
open Set Function Filter
open scoped Topology
namespace ClosedSimilarity.ForceWinding

/-- Weakly nonnegative force on periodic zero-turn curvature data necessarily
vanishes at every label, including all multiple or flat inflections. -/
theorem vanishes_of_one_sign {L:ℝ} {θ k v F:ℝ→ℝ} (lp:0<L) (pt:Periodic θ L)
    (pk:Periodic k L) (pv:Periodic v L) (dt:∀s,HasDerivAt θ (k s) s) (dk:∀s,HasDerivAt k (v s) s)
    (dv:∀s,HasDerivAt v (F s-(k s)^3/2) s) (cf:Continuous F) (pos:∀s,0≤F s) (s:ℝ) : F s=0 := by
  by_contra nz
  have fp : 0<F s := lt_of_le_of_ne (pos s) (Ne.symm nz)
  have hp : ∀ᶠ u in 𝓝 s,0<F u := cf.continuousAt (Ioi_mem_nhds fp)
  have flat : k=ᶠ[𝓝 s] (fun _=>0) := by
    filter_upwards [hp] with u hu
    by_contra ne
    exact hu.ne' (zero_at_regular lp pt pk pv dt dk dv pos ne)
  have flatv : v=ᶠ[𝓝 s] (fun _=>0) := by
    filter_upwards [flat.deriv] with u hu
    simpa only [(dk u).deriv,deriv_const] using hu
  have diff := flatv.deriv_eq
  rw [(dv s).deriv,flat.self_of_nhds,deriv_const] at diff
  exact nz (by linarith only [diff])

private theorem not_zero_on_closed_curve {L:ℝ} {p q k v F:ℝ→ℝ} (lp:0<L)
    (pk:Periodic k L) (pv:Periodic v L) (pp:Periodic p L) (pq:Periodic q L)
    (dk:∀s,HasDerivAt k (v s) s) (dv:∀s,HasDerivAt v (F s-(k s)^3/2) s)
    (dp:∀s,HasDerivAt p (-k s*q s) s) (dq:∀s,HasDerivAt q (1+k s*p s) s) :
    ¬(∀s,F s=0) := by
  intro zero
  let S := fun s=>k s^2/2*q s+v s*p s
  have ds (s:ℝ) : HasDerivAt S (k s^2/2) s := by
    apply ((((dk s).pow 2).div_const 2).mul (dq s) |>.add ((dv s).mul (dp s))).congr_deriv
    simp only [Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,zero];ring
  have per : Periodic S L := fun s=>by dsimp [S];rw [pk,pv,pp,pq]
  have mon : Monotone S := monotone_of_deriv_nonneg (fun s=>(ds s).differentiableAt)
    (fun s=>by rw [(ds s).deriv];positivity)

  have kz (s:ℝ) : k s=0 := by
    have r : S (s+L)=S s := per s
    have l : S (s-L)=S s := by simpa only [sub_eq_add_neg] using per.neg s
    have flat : S=ᶠ[𝓝 s] (fun _=>S s) := by
      filter_upwards [Ioo_mem_nhds (by linarith only [lp] : s-L<s) (by linarith only [lp] : s<s+L)] with y hy
      exact le_antisymm ((mon hy.2.le).trans_eq r) (l.symm.le.trans (mon hy.1.le))
    have u := flat.deriv_eq
    rw [(ds s).deriv,deriv_const] at u
    nlinarith only [u]
  have hm : StrictMono q := strictMono_of_hasDerivAt_pos dq (fun s=>by rw [kz];norm_num)
  exact (ne_of_lt (hm lp)) (by simpa using (pq 0).symm)

/-- On any smooth closed plane immersion of zero turning the physical elastic
force takes both strict signs. The supports are ordinary Frenet coordinates;
no similarity equation enters this result. -/
theorem zero_turn_curve_force_signs {L:ℝ} {θ p q k v F:ℝ→ℝ} (lp:0<L) (pt:Periodic θ L)
    (pk:Periodic k L) (pv:Periodic v L) (pp:Periodic p L) (pq:Periodic q L)
    (dt:∀s,HasDerivAt θ (k s) s) (dk:∀s,HasDerivAt k (v s) s)
    (dv:∀s,HasDerivAt v (F s-(k s)^3/2) s) (cf:Continuous F)
    (dp:∀s,HasDerivAt p (-k s*q s) s) (dq:∀s,HasDerivAt q (1+k s*p s) s) :
    (∃u,F u<0) ∧ ∃v,0<F v := by
  have nz := not_zero_on_closed_curve lp pk pv pp pq dk dv dp dq
  constructor
  · by_contra! pos
    exact nz (vanishes_of_one_sign lp pt pk pv dt dk dv cf pos)
  · by_contra! neg
    let θn := fun s=> -θ s
    let kn := fun s=> -k s
    let vn := fun s=> -v s
    let Fn := fun s=> -F s
    have dt' (s:ℝ) : HasDerivAt θn (kn s) s := (dt s).neg
    have dk' (s:ℝ) : HasDerivAt kn (vn s) s := (dk s).neg
    have dv' (s:ℝ) : HasDerivAt vn (Fn s-(kn s)^3/2) s := by
      apply (dv s).neg.congr_deriv;dsimp [Fn,kn];ring
    have tn : Periodic θn L := fun u=>by dsimp [θn];rw [pt]
    have knp : Periodic kn L := fun u=>by dsimp [kn];rw [pk]
    have vnp : Periodic vn L := fun u=>by dsimp [vn];rw [pv]
    have z := vanishes_of_one_sign lp tn knp vnp dt' dk' dv' cf.neg (fun s=>neg_nonneg.mpr (neg s))
    exact nz (fun s=>neg_eq_zero.mp (z s))

end ClosedSimilarity.ForceWinding
#print axioms ClosedSimilarity.ForceWinding.zero_turn_curve_force_signs
