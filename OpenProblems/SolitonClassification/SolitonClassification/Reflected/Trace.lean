import SolitonClassification.Reflected.TaylorStep

namespace SolitonClassification.Reflected
open SolitonClassification.Rotating SolitonClassification.Rotating.UniversalMajorant
open Set

noncomputable abbrev Flow (t : ℝ) (a : State) := supportFlow 1 (by norm_num) t a

theorem flow_restart (a : State) (s t : ℝ) : Flow (s+t) a = Flow t (Flow s a) := by
  apply congrFun (supportFlow_unique 1 (by norm_num) (x:=fun t => Flow (s+t) a)
    (by simp) (fun t => ?_)) t
  simpa only [one_smul,Function.comp_def] using (supportFlow_derivative 1 (by norm_num) a (s+t)).scomp t
    ((hasDerivAt_id t).const_add s)

def BoxContains (b : Box) (a : State) : Prop := ∀i, (boxFn b i).Contains mesh (a i)

def boxSmall (b : Box) : Prop :=
  ∀ i : Fin 5, 100*(|(b[i.val]).center|+(b[i.val]).radius) ≤
    (if i.val=4 then 1 else 300)*(mesh:ℤ)

instance (b : Box) : Decidable (boxSmall b) := inferInstanceAs (Decidable (∀_i:Fin 5,_))

theorem boxSmall_sound {b : Box} {a : State} (hb : BoxContains b a) (hs : boxSmall b) :
    a ∈ innerTube := by
  have lim (i : Fin 5) (r : ℝ) (hr : ((if i.val=4 then 1 else 300:ℤ):ℝ)/100 ≤ r) :
      |a ⟨i.val,by omega⟩| ≤ r := by
    let z := b[i.val]
    have hp := hb ⟨i.val, by omega⟩
    change |a ⟨i.val,by omega⟩ - (((z.center:ℚ)/mesh:ℚ):ℝ)| ≤
      (((z.radius:ℚ)/mesh:ℚ):ℝ) at hp
    have h : (100:ℝ)*(|(z.center:ℝ)|+(z.radius:ℝ)) ≤
        ((if i.val=4 then 1 else 300:ℤ):ℝ)*(mesh:ℝ) := by exact_mod_cast hs i
    push_cast at hp
    have ht := abs_sub_le (a ⟨i.val,by omega⟩) ((z.center:ℝ)/mesh) 0
    simp only [sub_zero,abs_div] at ht
    by_cases hi : i.val=4 <;> norm_num [mesh,hi] at hr h hp ht ⊢ <;> linarith
  exact ⟨lim 0 _ (by norm_num),lim 1 _ (by norm_num),lim 2 _ (by norm_num),
    lim 3 _ (by norm_num),lim 4 _ (by norm_num)⟩

def traceStep : ℚ := 71277053833957/9250000000000000

theorem traceStep_spec : traceStep ∈ Icc 0 universalStepCap := by
  norm_num [traceStep,universalStepCap]

structure Segment (h : ℚ) (b c : Box) (duration : ℝ) : Prop where
  endpoint : ∀ a, BoxContains b a → BoxContains c (Flow duration a)
  tube : ∀ a, BoxContains b a → ∀t∈Icc 0 duration, Flow t a ∈ outerTube

theorem Segment.single {b c : Box} {h : ℚ} (hh : h ∈ Icc 0 universalStepCap)
    (hb : boxSmall b) (hc : advance h b = c) : Segment h b c (h:ℝ) := by
  constructor
  · intro a ha i
    rw [←hc]
    exact advance_sound ha (boxSmall_sound ha hb) hh i
  · intro a ha t ht
    apply supportFlow_short_mem_outerTube 1 (by norm_num) (boxSmall_sound ha hb) ht.1
    exact ht.2.trans ((by exact_mod_cast hh.2 : (h:ℝ)≤(universalStepCap:ℝ)).trans
      universalStepCap_le_local)

theorem Segment.join {h : ℚ} {b c d : Box} {s t : ℝ}
    (h1 : Segment h b c s) (h2 : Segment h c d t) : Segment h b d (s+t) := by
  constructor
  · intro a ha
    rw [flow_restart]
    exact h2.endpoint _ (h1.endpoint a ha)
  · intro a ha u hu
    by_cases hx : u≤s
    · exact h1.tube a ha u ⟨hu.1,hx⟩
    · have ht := h2.tube _ (h1.endpoint a ha) (u-s) ⟨by linarith,by linarith [hu.2]⟩
      simpa only [←flow_restart,add_sub_cancel_left,add_sub_cancel] using ht

end SolitonClassification.Reflected
#print axioms SolitonClassification.Reflected.Segment.single
#print axioms SolitonClassification.Reflected.Segment.join
