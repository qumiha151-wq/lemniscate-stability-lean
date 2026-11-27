import LengthGrowth.ActualFlow.InitialTurnBound
import LengthGrowth.ActualFlow.TurningLabels
import LengthGrowth.ActualFlow.MaterialTurnContinuity

noncomputable section
open Set Function Finset Filter
namespace LengthGrowth.ActualFlow.ForwardImmersion
open TurningEnvelope

/-- A finite outward angular budget on one tail suffices for the actual
    fourth-root length estimate. The input bounds only the normal-force
    derivative at maxima and minima of the actual signed tangent-angle lift.
    Degenerate extrema and coincident endpoints are allowed. -/
theorem quarter_length_of_one_sided_inflection_budget (c : ForwardImmersion)
    (hf : c.IsNormalFEF) {a : ℝ} (ap : 0<a) (B rate ref : ℝ→ℝ)
    (cont : ContinuousOn B (Ici a)) (der : ∀ t>a, HasDerivAt B (rate t) t)
    (nonneg : ∀t>a,0≤rate t) (budget : ∀t≥a,B t-B a≤1/16)
    (hi : ∀t>a, ∀x, IsLocalMax (arcTurn (c.position t) 0) x →
      -arcDerivative (c.position t) (force (c.position t)) x ≤ ref t+rate t)
    (lo : ∀t>a, ∀x, IsLocalMin (arcTurn (c.position t) 0) x →
      ref t ≤ -arcDerivative (c.position t) (force (c.position t)) x) : c.HasQuarterLengthBound := by
  let θ := fun t => arcTurn (c.position t) 0
  let J := fun t => arcDerivative (c.position t) (force (c.position t))
  let V := fun t u => J t 0-J t u
  obtain ⟨A,Ap,initial⟩ := initial_gain_bound (c.regularPositionAt ap.le)
  have count {t : ℝ} (at' : a<t) (m : ℕ) (realized : (c.regularPositionAt (ap.trans at').le).HasTurningExcursions m) :
      (m:ℝ)≤16*A := by
    let p := c.regularPositionAt (ap.trans at').le
    obtain ⟨l,r,arcs,gaps,span,turn⟩ := p.material_labels_of_excursions realized
    have ct : ContinuousOn (fun q : ℝ×ℝ => θ q.1 q.2) (Icc a t ×ˢ univ) :=
      c.arcTurn_joint_continuous.mono fun _ h => ⟨ap.le.trans h.1.1,h.2⟩
    have dt (s : ℝ) (hs : s∈Ioc a t) (u : ℝ) :
        HasDerivAt (fun τ => θ τ u) (V s u) s :=
      c.interior.arcTurn_time_flux (c.interior_isNormalFEF hf) (ap.trans hs.1) 0 u
    have shifts (s : ℝ) (hs : s∈Icc a t) (h : ℝ) : Periodic (fun u => θ s (u+h)-θ s u) c.period :=
      (c.regularPositionAt (ap.le.trans hs.1)).arcTurn_periodic_increment h
    have vp (s : ℝ) (hs : s∈Ioc a t) : Periodic (V s) c.period := by
      intro u
      have eq (v : ℝ) := (c.interior.arcTurn_frameRate (c.interior_isNormalFEF hf) (ap.trans hs.1) v).1
      have per := c.interior.velocityGradientNormal_periodic (ap.trans hs.1) u
      change J s 0-J s (u+c.period)=J s 0-J s u
      linarith only [show -(J s (u+c.period))= -(J s u) from (eq _).symm.trans (per.trans (eq _))]
    have bcont := cont.mono (Icc_subset_Ici_self : Icc a t⊆Ici a)
    have H (e : Ends m) (he : Ordered c.period e) :
        gain (θ t) e≤A+(m:ℝ)*(B t-B a) :=
      cyclic_gain_barrier c.period_pos at'.le θ V B rate (fun s => J s 0+ref s)
        ct dt shifts vp bcont (fun s hs=>der s hs.1) (fun s hs=>nonneg s hs.1)
        (fun s hs x hx=>by dsimp [V,J]; linarith only [hi s hs.1 x hx])
        (fun s hs x hx=>by dsimp [V,J]; linarith only [lo s hs.1 x hx])
        (fun q hq=>le_trans (le_abs_self _) (initial m q hq)) e he
    have Hneg (e : Ends m) (he : Ordered c.period e) :
        gain (fun u => -θ t u) e≤A+(m:ℝ)*(B t-B a) := by
      apply cyclic_gain_barrier c.period_pos at'.le (fun s u=> -θ s u) (fun s u=> -V s u)
        B rate (fun s=> -(J s 0+ref s)-rate s) ct.neg (fun s hs u => (dt s hs u).neg)
        _ (fun s hs u => congrArg Neg.neg (vp s hs u)) bcont (fun s hs=>der s hs.1) (fun s hs=>nonneg s hs.1) _ _ _ e he
      · intro s hs h u
        dsimp only
        linarith only [shifts s hs h u]
      · intro s hs x hx
        have localMin : IsLocalMin (θ s) x := hx.mono fun y hy => by simpa using hy
        dsimp [V,J]
        linarith only [lo s hs.1 x localMin]
      · intro s hs x hx
        have localMax : IsLocalMax (θ s) x := hx.mono fun y hy => by simpa using hy
        dsimp [V,J]
        linarith only [hi s hs.1 x localMax]
      · intro q hq
        have negGain : gain (fun u=> -θ a u) q= -gain (θ a) q := by
          unfold gain; rw [←sum_neg_distrib]; apply sum_congr rfl; intro i _; ring
        rw [negGain]
        exact (neg_le_abs _).trans (initial m q hq)
    let rpos := fun i => if θ t (l i)≤θ t (r i) then r i else l i
    let rneg := fun i => if θ t (l i)≤θ t (r i) then l i else r i
    have ord (q : Fin m→ℝ) (sel : ∀i,q i=r i ∨ q i=l i) : Ordered c.period (l,q) := by
      have low (i) : l i≤q i := (sel i).elim (fun h => h ▸ arcs i) (fun h=>h.ge)
      have up (i) : q i≤r i := (sel i).elim (fun h=>h.le) (fun h=>h ▸ arcs i)
      exact ⟨low,fun i j h => (up i).trans (gaps i j h),fun i j => (up i).trans (span i j)⟩
    have one := H (l,rpos) (ord rpos fun i => by dsimp [rpos]; split <;> simp)
    have two := Hneg (l,rneg) (ord rneg fun i=>by dsimp [rneg]; split <;> simp)
    have both : gain (θ t) (l,rpos)+gain (fun u=> -θ t u) (l,rneg) =
        ∑i, |arcTurn p.position (l i) (r i)| := by
      unfold gain; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _
      rw [←p.arcTurn_between_primitives]
      change θ t (rpos i)-θ t (l i)+(-θ t (rneg i)- -θ t (l i))=|θ t (r i)-θ t (l i)|
      by_cases h : θ t (l i)≤θ t (r i)
      · simp [rpos,rneg,h,abs_of_nonneg (sub_nonneg.mpr h)]
      · simp [rpos,rneg,h,abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]; ring
    have floor := sum_le_sum (s:=Finset.univ) (fun i _ => turn i)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at floor
    linarith only [one,two,both,floor,mul_le_mul_of_nonneg_left (budget t at'.le) (Nat.cast_nonneg m)]
  by_contra fail
  let K := (16/(2^23):ℝ)^(1/6:ℝ)
  have kp : 0<K := Real.rpow_pos_of_pos (by norm_num) _
  have large : Filter.Tendsto (fun x : ℝ => K*x^(1/3:ℝ)) atTop atTop :=
    (tendsto_const_nhds (x:=K)).pos_mul_atTop kp (tendsto_rpow_atTop (by norm_num))
  obtain ⟨M,high⟩ := eventually_atTop.mp (large.eventually_gt_atTop (16*A))
  obtain ⟨t,ht,at',prod,_,m,arcs,lbound⟩ := c.turning_excursions_at_high_records hf fail a M
  exact (not_lt_of_ge (count at' m arcs)) ((high _ prod.le).trans_le lbound)

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_one_sided_inflection_budget
