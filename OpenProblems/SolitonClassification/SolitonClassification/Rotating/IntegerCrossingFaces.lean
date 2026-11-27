import SolitonClassification.Rotating.IntegerCrossingArcs

namespace SolitonClassification.Rotating.IntegerTarget.CrossingCharts
noncomputable section
open Set
set_option maxHeartbeats 2500000
def idx (chart : Fin 2) (arm : Bool) (j : Fin 9) : Fin 36 :=
  ⟨18*chart.val+(if arm then 9 else 0)+j.val,by cases arm <;> simp <;> omega⟩
def firstIndex (k : Fin 2) (b : Bool) := (sample (idx k b 0)).index
def loc (k : Fin 2) (b : Bool) (j : Fin 9) := sample (idx k b j)
def coeffX (k : Fin 2) (v : Bool) : ℚ := if k=0 then (if v then 89/100 else 80/100) else (if v then -(28/100) else 83/100)
def coeffY (k : Fin 2) (v : Bool) : ℚ := if k=0 then (if v then -(45/100) else 61/100) else (if v then 96/100 else -(56/100))
def cutQ (k : Fin 2) (v : Bool) (i j : Fin 9) : ℚ :=
  coeffX k v*((loc k false i).x-(loc k true j).x)+coeffY k v*((loc k false i).y-(loc k true j).y)
def tolQ (k : Fin 2) (v : Bool) : ℚ := (|coeffX k v|+|coeffY k v|)*(1/125+2/800)
theorem record_order : ∀k b,∀j:Fin 9, (loc k b j).index=firstIndex k b+j.val := by decide +kernel
theorem numeric_signs : ∀k:Fin 2,∀j:Fin 9,
    cutQ k false 0 j < -tolQ k false ∧ tolQ k false<cutQ k false 8 j ∧
    cutQ k true j 0 < -tolQ k true ∧ tolQ k true<cutQ k true j 8 := by decide +kernel
theorem nonsingular : ∀k:Fin 2,coeffX k false*coeffY k true-coeffY k false*coeffX k true≠0 := by decide +kernel
theorem position_ranges : ∀k:Fin 2,∀j:Fin 9,
    (if k=0 then (603/100:ℚ) else 559/100)<(loc k false j).x ∧
    (loc k false j).x<(if k=0 then (611/100:ℚ) else 572/100) := by decide +kernel

def lo (k : Fin 2) (b : Bool) : ℝ := firstIndex k b
def dom (k : Fin 2) (b : Bool) := Icc (lo k b) (lo k b+8)
def projected (k : Fin 2) (v : Bool) (z w : ℝ × ℝ) : ℝ :=
  (coeffX k v:ℝ)*(z.1-w.1)+(coeffY k v:ℝ)*(z.2-w.2)

theorem dom_grid {k : Fin 2} {b : Bool} {x : ℝ} (hx : x∈dom k b) : x∈Icc 0 4000 := by
  have num : ∀k:Fin 2,∀b:Bool,firstIndex k b+8≤4000 := by decide +kernel
  have top : (firstIndex k b:ℝ)+8≤4000 := by exact_mod_cast num k b
  exact ⟨(Nat.cast_nonneg _).trans hx.1,hx.2.trans top⟩

theorem nearest {k : Fin 2} {b : Bool} {x : ℝ} (hx : x∈dom k b) :
    ∃j:Fin 9, |x-((loc k b j).index:ℝ)|≤1 := by
  have h := covered_cell 8 (by decide) (x-lo k b) (by linarith [hx.1]) (by norm_num; linarith [hx.2])
  obtain ⟨i,hi,t,ht,e⟩ := h
  let j : Fin 9 := ⟨i,by omega⟩
  refine ⟨j,?_⟩
  rw [record_order]
  push_cast
  change |x-((lo k b)+(i:ℝ))|≤1
  rw [show x-(lo k b+i)=t by linarith,abs_of_nonneg ht.1]
  exact ht.2

def close (v : ℝ × ℝ) (r : Sample) (e : ℝ) :=
  |v.1-(r.x:ℝ)|≤e ∧ |v.2-(r.y:ℝ)|≤e

theorem varying_close {c : Parameters} (hc : c∈cube) {k : Fin 2} {b : Bool} {x : ℝ} (hx : x∈dom k b) :
    ∃j:Fin 9, close (gridPosition c x) (loc k b j) (1/800+1/125) := by
  obtain ⟨j,hj⟩ := nearest hx
  let i:=idx k b j
  let a : ℝ := (sample i).index
  have sb := (basic i).1
  have ha : a∈Icc 0 4000 := ⟨Nat.cast_nonneg _,by dsimp only [a]; exact_mod_cast sb.le⟩
  have L := grid_lipschitz hc ha (dom_grid hx)
  have E := position_errors c hc i
  change |(gridPosition c a).1-((loc k b j).x:ℝ)|≤_ ∧ |(gridPosition c a).2-((loc k b j).y:ℝ)|≤_ at E
  have dist : h*|x-a|≤1/125 := (mul_le_mul_of_nonneg_left hj h_mem.1.le).trans (by simpa using h_mem.2.le)
  exact ⟨j,(abs_sub_le _ (gridPosition c a).1 _).trans (by linarith [L.1,E.1]),(abs_sub_le _ (gridPosition c a).2 _).trans (by linarith [L.2.1,E.2])⟩

theorem end_close {c : Parameters} (hc : c∈cube) (k : Fin 2) (b : Bool) (j : Fin 9) :
    close (gridPosition c (lo k b+(j.val:ℝ))) (loc k b j) (1/800) := by
  have H := position_errors c hc (idx k b j)
  have eq : (((sample (idx k b j)).index:ℕ):ℝ)=lo k b+(j.val:ℝ) := by
    change ((loc k b j).index:ℝ)=(firstIndex k b:ℝ)+(j.val:ℝ)
    exact_mod_cast record_order k b j
  change close (gridPosition c (((sample (idx k b j)).index:ℕ):ℝ)) (loc k b j) _ at H
  rwa [eq] at H

private theorem abs_delta {u v a b e f : ℝ} (h₁ : |u-a|≤e) (h₂ : |v-b|≤f) :
    |(u-v)-(a-b)|≤e+f := by
  rw [show (u-v)-(a-b)=(u-a)-(v-b) by ring]
  exact (abs_sub _ _).trans (add_le_add h₁ h₂)

theorem projection_error {k : Fin 2} {v : Bool} {a b : ℝ × ℝ} {i j : Fin 9} {e f : ℝ}
    (A : close a (loc k false i) e) (B : close b (loc k true j) f) (err : e+f≤1/125+2/800) :
    |projected k v a b-(cutQ k v i j:ℝ)|≤(tolQ k v:ℝ) := by
  have dx := (abs_delta A.1 B.1).trans err
  have dy := (abs_delta A.2 B.2).trans err
  unfold projected cutQ tolQ
  push_cast
  rw [show ∀a b c d e f:ℝ,a*b+c*d-(a*e+c*f)=a*(b-e)+c*(d-f) by intros;ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left dx (abs_nonneg _)) (mul_le_mul_of_nonneg_left dy (abs_nonneg _))

end
end SolitonClassification.Rotating.IntegerTarget.CrossingCharts
#print axioms SolitonClassification.Rotating.IntegerTarget.CrossingCharts.projection_error

