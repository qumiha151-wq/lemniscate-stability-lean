import LengthGrowth.ActualFlow.CyclicTurnVariation
import LengthGrowth.ActualFlow.TurningEnvelope
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Set Filter Finset Function
open scoped Topology
namespace LengthGrowth.ActualFlow.TurningEnvelope

private theorem isClosed_setOf_forall {X : Type*} {ι : Sort*} [TopologicalSpace X]
    {f : ι → X → Prop} (h : ∀ i, IsClosed {x | f i x}) : IsClosed {x | ∀ i, f i x} := by
  rw [show {x | ∀ i, f i x} = ⋂ i, {x | f i x} by ext; simp]
  exact isClosed_iInter h

def boxed {n : ℕ} (P : ℝ) : Set (Ends n) :=
  {e | Ordered P e ∧ e ∈ (Icc (fun _ => 0) (fun _ => 2*P)) ×ˢ
                                (Icc (fun _ => 0) (fun _ => 2*P))}

theorem compact_boxed {n : ℕ} (P : ℝ) : IsCompact (boxed (n:=n) P) := by
  have closed : IsClosed {e : Ends n | Ordered P e} := by
    unfold Ordered
    apply IsClosed.inter
    · exact isClosed_setOf_forall fun i => isClosed_le ((continuous_apply i).comp continuous_fst)
        ((continuous_apply i).comp continuous_snd)
    · apply IsClosed.inter
      · apply isClosed_setOf_forall
        intro i
        apply isClosed_setOf_forall
        intro j
        apply isClosed_setOf_forall
        intro _
        exact isClosed_le ((continuous_apply i).comp continuous_snd) ((continuous_apply j).comp continuous_fst)
      · exact isClosed_setOf_forall fun i => isClosed_setOf_forall fun j =>
          isClosed_le ((continuous_apply i).comp continuous_snd)
            (((continuous_apply j).comp continuous_fst).add continuous_const)
  exact (isCompact_Icc.prod isCompact_Icc).inter_left closed

theorem boxed_representative {n : ℕ} {P : ℝ} (hp : 0<P) (e : Ends n) (he : Ordered P e)
    (θ : ℝ→ℝ) (per : ∀h, Periodic (fun x => θ (x+h)-θ x) P) :
    ∃ q : Ends n, q∈boxed P ∧ gain θ q=gain θ e := by
  cases n with
  | zero =>
    refine ⟨e,⟨he,?_,?_⟩,rfl⟩ <;> exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n =>
    let a := e.1 0
    let z := toIcoDiv hp 0 a
    let q : Ends (n+1) := (fun i => e.1 i-z • P,fun i => e.2 i-z • P)
    have tag : a-z • P∈Ico (0:ℝ) P := by
      rw [self_sub_toIcoDiv_zsmul]
      exact toIcoMod_mem_Ico' hp a
    have first (i : Fin (n+1)) : a≤e.1 i := by
      rcases eq_or_lt_of_le (Fin.zero_le i) with h|h
      · rw [←h]
      · exact (he.1 0).trans (he.2.1 0 i h)
    have lo (i : Fin (n+1)) := first i
    have hi (i : Fin (n+1)) : e.2 i≤a+P := he.2.2 i 0
    have eqg (i : Fin (n+1)) := (per (e.2 i-e.1 i)).sub_zsmul_eq (x:=e.1 i) z
    refine ⟨q,⟨⟨fun i => sub_le_sub_right (he.1 i) _,fun i j h => sub_le_sub_right (he.2.1 i j h) _,
      fun i j => by dsimp [q]; linarith only [he.2.2 i j]⟩,?_,?_⟩,?_⟩
    · exact ⟨fun i => by change 0≤e.1 i-z • P; linarith [tag.1,lo i],
          fun i => by change e.1 i-z • P≤2*P; linarith [tag.2,hi i,he.1 i]⟩
    · exact ⟨fun i => by change 0≤e.2 i-z • P; linarith [tag.1,lo i,he.1 i],
          fun i => by change e.2 i-z • P≤2*P; linarith [tag.2,hi i]⟩
    · apply sum_congr rfl
      intro i _
      change θ (e.2 i-z • P)-θ (e.1 i-z • P) = θ (e.2 i)-θ (e.1 i)
      simpa only [show e.1 i-z • P+(e.2 i-e.1 i)=e.2 i-z • P by ring,
          show e.1 i+(e.2 i-e.1 i)=e.2 i by ring] using eqg i

/-- An integral barrier for all cyclic arc gains. Only the outward spread
    of angular velocities at tangent-angle extrema enters the bound. -/
theorem cyclic_gain_barrier {n : ℕ} {P a b A : ℝ} (hp : 0<P) (ab : a≤b)
    (θ V : ℝ→ℝ→ℝ) (B B' c : ℝ→ℝ)
    (cθ : ContinuousOn (fun p : ℝ×ℝ => θ p.1 p.2) (Icc a b ×ˢ univ))
    (dθ : ∀t∈Ioc a b, ∀u, HasDerivAt (fun s => θ s u) (V t u) t)
    (per : ∀t∈Icc a b, ∀h, Periodic (fun x => θ t (x+h)-θ t x) P)
    (vp : ∀t∈Ioc a b, Periodic (V t) P)
    (cb : ContinuousOn B (Icc a b)) (db : ∀t∈Ioc a b, HasDerivAt B (B' t) t)
    (pos : ∀t∈Ioc a b, 0≤B' t)
    (hi : ∀t∈Ioc a b, ∀x, IsLocalMax (θ t) x → V t x≤c t+B' t)
    (lo : ∀t∈Ioc a b, ∀x, IsLocalMin (θ t) x → c t≤V t x)
    (init : ∀e : Ends n, Ordered P e → gain (θ a) e≤A) :
    ∀ e : Ends n, Ordered P e → gain (θ b) e≤A+(n:ℝ)*(B b-B a) := by
  intro e he
  obtain ⟨w,hw,eq⟩ := boxed_representative hp e he (θ b) (per b (right_mem_Icc.mpr ab))
  apply le_of_forall_pos_le_add
  intro ε ep
  let m := ε/(b-a+1)
  have mp : 0<m := div_pos ep (by linarith)
  let K := boxed (n:=n) P
  let f := fun q : ℝ×Ends n => gain (θ q.1) q.2-(n:ℝ)*(B q.1-B a)-m*(q.1-a)
  have cf : ContinuousOn f (Icc a b ×ˢ K) := by
    have clock : ContinuousOn (fun q : ℝ×Ends n => q.1) (Icc a b ×ˢ K) := continuous_fst.continuousOn
    have eval (g : Ends n→ℝ) (cg : Continuous g) : ContinuousOn
        (fun q : ℝ×Ends n => θ q.1 (g q.2)) (Icc a b ×ˢ K) :=
      cθ.comp (continuous_fst.prodMk (cg.comp continuous_snd)).continuousOn (fun _ h => ⟨h.1,mem_univ _⟩)
    have ang := continuousOn_finsetSum univ fun i _ =>
      (eval _ ((continuous_apply i).comp continuous_snd)).sub
        (eval _ ((continuous_apply i).comp continuous_fst))
    exact (ang.sub (continuousOn_const.mul ((cb.comp clock fun _ h=>h.1).sub continuousOn_const))).sub
      (continuousOn_const.mul (clock.sub continuousOn_const))
  have maxBound := compact_comparison (compact_boxed P) ab f cf
    (fun q hq => by simpa [f] using init q hq.1)
    (fun t ht q hq best => by
      have top (y : Ends n) (hy : Ordered P y) : gain (θ t) y≤gain (θ t) q := by
        obtain ⟨v,hv,hyv⟩ := boxed_representative hp y hy (θ t) (per t ⟨ht.1.le,ht.2⟩)
        have h := best v hv
        dsimp only [f] at h
        linarith
      have bound := maximizing_cyclic_rate hp q hq.1 (θ t) (V t) (per t ⟨ht.1.le,ht.2⟩)
        (vp t ht) (pos t ht) (hi t ht) (lo t ht) top
      have d := HasDerivAt.fun_sum (u:=univ) (fun i _ => (dθ t ht (q.2 i)).sub (dθ t ht (q.1 i)))
      exact ⟨_,by change gain (V t) q-(n:ℝ)*B' t-m*1<0; linarith,
        (d.sub (HasDerivAt.const_mul (n:ℝ) ((db t ht).sub_const (B a)))).sub
          (HasDerivAt.const_mul m ((hasDerivAt_id t).sub_const a))⟩)
    (b,w) ⟨right_mem_Icc.mpr ab,hw⟩
  change gain (θ b) w-(n:ℝ)*(B b-B a)-m*(b-a)≤A at maxBound
  have prod : m*(b-a+1)=ε := div_mul_cancel₀ _ (by linarith)
  linarith

end LengthGrowth.ActualFlow.TurningEnvelope
#print axioms LengthGrowth.ActualFlow.TurningEnvelope.cyclic_gain_barrier
