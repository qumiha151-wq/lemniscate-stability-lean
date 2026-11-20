import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Planar rectangle crossing by cancellation of the oriented 1–2 edges of a
    three-colour square grid. All comparisons on the four faces are strict. -/
noncomputable section
namespace SolitonClassification.Reflected.Rectangle
open Set Finset

private def indicator (a : Fin 3) : ℤ := if a = 2 then 1 else 0
private def edge (a b : Fin 3) : ℤ :=
  if a = 0 ∨ b = 0 then 0 else indicator b - indicator a

private theorem cell_rule : ∀ a b c d : Fin 3,
    (∃ k : Fin 3, a ≠ k ∧ b ≠ k ∧ c ≠ k ∧ d ≠ k) →
    edge a b + edge b c = edge a d + edge d c := by decide

private lemma edge_no_one : ∀ a b : Fin 3, a ≠ 1 → b ≠ 1 → edge a b = 0 := by decide
private lemma edge_no_two : ∀ a b : Fin 3, a ≠ 2 → b ≠ 2 → edge a b = 0 := by decide
private lemma telescope (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ range n, (f (i+1)-f i) = f n-f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; omega

private theorem grid_obstruction (n : ℕ) (C : ℕ → ℕ → Fin 3)
    (cell : ∀ i < n, ∀ j < n, ∃ k : Fin 3,
      C i j ≠ k ∧ C (i+1) j ≠ k ∧ C (i+1) (j+1) ≠ k ∧ C i (j+1) ≠ k)
    (left : ∀ j ≤ n, C 0 j = 0) (right : ∀ j ≤ n, C n j ≠ 0)
    (bottom : ∀ i ≤ n, C i 0 ≠ 2) (top : ∀ i ≤ n, C i n ≠ 1) : False := by
  let h := fun i j => edge (C i j) (C (i+1) j)
  let v := fun i j => edge (C i j) (C i (j+1))
  let row := fun j => ∑ i ∈ range n, h i j
  have strip (j : ℕ) (hj : j < n) : row (j+1)-row j = v n j - v 0 j := by
    change (∑ i ∈ range n, h i (j+1)) - (∑ i ∈ range n, h i j) = _
    rw [← sum_sub_distrib, ← telescope (fun i => v i j) n]
    apply sum_congr rfl
    intro i hi
    have eq := cell_rule _ _ _ _ (cell i (mem_range.mp hi) j hj)
    dsimp [v,h]
    omega
  have sides (j : ℕ) (hj : j < n) :
      row (j+1)-row j = indicator (C n (j+1))-indicator (C n j) := by
    rw [strip j hj]
    simp [v,edge,left j hj.le,right j hj.le,right (j+1) hj]
  have total := sum_congr (s₁ := range n) (s₂ := range n) rfl
    (fun j hj => sides j (mem_range.mp hj))
  rw [telescope, telescope (fun j => indicator (C n j))] at total
  have r0 : row 0 = 0 := sum_eq_zero fun i hi =>
    edge_no_two _ _ (bottom i (mem_range.mp hi).le) (bottom (i+1) (mem_range.mp hi))
  have rn : row n = 0 := sum_eq_zero fun i hi =>
    edge_no_one _ _ (top i (mem_range.mp hi).le) (top (i+1) (mem_range.mp hi))
  have cn : C n n = 2 := by
    have u := right n le_rfl
    have w := top n le_rfl
    omega
  simp [indicator,rn,r0,cn,bottom n le_rfl] at total

private def colour (p : ℝ × ℝ) : Fin 3 := if p.1 < 0 then 0 else if p.2 < 0 then 1 else 2

private lemma missing_colour (p : ℝ × ℝ) (hp : p ≠ 0) :
    ∃ r > 0, ∃ c : Fin 3, ∀ q, dist q p < r → colour q ≠ c := by
  have nearby {q : ℝ × ℝ} {r : ℝ} (h : dist q p < r) :
      |q.1-p.1| < r ∧ |q.2-p.2| < r := by
    simpa [Prod.dist_eq, Real.dist_eq] using h
  by_cases hx : p.1 < 0
  · refine ⟨-p.1,by linarith,2,fun q h => ?_⟩
    have := (abs_lt.mp (nearby h).1).2
    simp [colour,show q.1 < 0 by linarith]
  by_cases hp' : 0 < p.1
  · refine ⟨p.1,hp',0,fun q h => ?_⟩
    have := (abs_lt.mp (nearby h).1).1
    simp [colour,show ¬q.1 < 0 by linarith]
    split <;> decide
  have hy : p.2 ≠ 0 := by
    intro eq
    apply hp
    exact Prod.ext (by change p.1=0; linarith) eq
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · refine ⟨-p.2,by linarith,2,fun q h => ?_⟩
    have := (abs_lt.mp (nearby h).2).2
    simp [colour,show q.2 < 0 by linarith]
    split <;> decide
  · refine ⟨p.2,hpos,1,fun q h => ?_⟩
    have := (abs_lt.mp (nearby h).2).1
    simp [colour,show ¬q.2 < 0 by linarith]
    split <;> decide

def square : Set (ℝ × ℝ) := Icc (0,0) (1,1)

/-- Strict opposite signs on each pair of faces force a genuine simultaneous
    zero, without a uniqueness or coordinatewise monotonicity assumption. -/
theorem zero_in_square (F : ℝ × ℝ → ℝ × ℝ) (hc : ContinuousOn F square)
    (left : ∀ y ∈ Icc (0:ℝ) 1, (F (0,y)).1 < 0)
    (right : ∀ y ∈ Icc (0:ℝ) 1, 0 < (F (1,y)).1)
    (bottom : ∀ x ∈ Icc (0:ℝ) 1, (F (x,0)).2 < 0)
    (top : ∀ x ∈ Icc (0:ℝ) 1, 0 < (F (x,1)).2) :
    ∃ p ∈ square, F p = 0 := by
  classical
  by_contra! hn
  let S := {z : ℝ × ℝ // z ∈ square}
  have : CompactSpace S := isCompact_iff_compactSpace.mp (show IsCompact square from isCompact_Icc)
  let f : S → ℝ × ℝ := fun z => F z
  have hf : Continuous f := continuousOn_iff_continuous_domRestrict.mp hc
  let regions := fun c : Fin 3 => interior {z : S | colour (f z) ≠ c}
  have cover : (univ : Set S) ⊆ ⋃ c, regions c := by
    intro z _
    obtain ⟨r,hr,c,avoid⟩ := missing_colour (f z) (hn z z.property)
    apply mem_iUnion.mpr
    refine ⟨c,mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset (hf.continuousAt (Metric.ball_mem_nhds _ hr))
      (fun q hq => avoid (f q) hq)
  obtain ⟨δ,hδ,pick⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun c : Fin 3 => isOpen_interior (s := {z : S | colour (f z) ≠ c})) cover
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hδ
  let n := m+1
  have hn' : 0 < (n:ℝ) := by dsimp [n]; positivity
  let tick := fun i : ℕ => (min i n : ℕ) / (n:ℝ)
  have ht i : tick i ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hn'.le, ?_⟩
    exact (div_le_one hn').mpr (by exact_mod_cast min_le_right i n)
  let z (i j : ℕ) : S := ⟨(tick i,tick j), ⟨⟨(ht i).1,(ht j).1⟩,⟨(ht i).2,(ht j).2⟩⟩⟩
  have t0 : tick 0 = 0 := by simp [tick]
  have tn : tick n = 1 := by simp [tick,hn'.ne']
  have small (i : ℕ) (hi : i < n) : dist (tick (i+1)) (tick i) < δ := by
    have e : tick (i+1)-tick i = 1/(n:ℝ) := by
      simp only [tick,min_eq_left (Nat.succ_le_of_lt hi),min_eq_left hi.le,Nat.cast_succ,add_div]
      ring
    rw [Real.dist_eq,e,abs_of_pos (by positivity)]
    simpa [n] using hm
  let C := fun i j => colour (f (z i j))
  apply grid_obstruction n C
  · intro i hi j hj
    obtain ⟨c,hr⟩ := pick (z i j) (mem_univ _)
    have avoid (a b : ℕ) (hx : dist (tick a) (tick i) < δ)
        (hy : dist (tick b) (tick j) < δ) : C a b ≠ c := by
      apply interior_subset (s := {q : S | colour (f q) ≠ c})
      apply hr
      exact max_lt hx hy
    have same (a : ℕ) : dist (tick a) (tick a) < δ := by simpa using hδ
    exact ⟨c,avoid _ _ (same _) (same _), avoid _ _ (small _ hi) (same _),
      avoid _ _ (small _ hi) (small _ hj), avoid _ _ (same _) (small _ hj)⟩
  · intro j _
    simp [C,f,z,colour,t0,left _ (ht j)]
  · intro j _
    simp [C,f,z,colour,tn,not_lt_of_gt (right _ (ht j))]
    split <;> decide
  · intro i _
    simp [C,f,z,colour,t0,bottom _ (ht i)]
    split <;> decide
  · intro i _
    simp [C,f,z,colour,tn,not_lt_of_gt (top _ (ht i))]
    split <;> decide

def box (a b c d : ℝ) : Set (ℝ × ℝ) := Icc (a,c) (b,d)

theorem zero_in_box (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (F : ℝ × ℝ → ℝ × ℝ) (hf : ContinuousOn F (box a b c d))
    (left : ∀ y ∈ Icc c d, (F (a,y)).1 < 0)
    (right : ∀ y ∈ Icc c d, 0 < (F (b,y)).1)
    (bottom : ∀ x ∈ Icc a b, (F (x,c)).2 < 0)
    (top : ∀ x ∈ Icc a b, 0 < (F (x,d)).2) :
    ∃ p ∈ box a b c d, F p = 0 := by
  let lerp (l h t : ℝ) := l + (h-l)*t
  have within {l h t : ℝ} (hh : l ≤ h) (ht : t ∈ Icc (0:ℝ) 1) :
      lerp l h t ∈ Icc l h := by
    obtain ⟨ht0,ht1⟩ := ht
    dsimp [lerp]
    exact ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hh) ht0],
      by nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr ht1)]⟩
  let g (p : ℝ × ℝ) := (lerp a b p.1, lerp c d p.2)
  have maps : MapsTo g square (box a b c d) := by
    intro p hp
    obtain ⟨hx,hx'⟩ := within hab (show p.1 ∈ Icc (0:ℝ) 1 from ⟨hp.1.1,hp.2.1⟩)
    obtain ⟨hy,hy'⟩ := within hcd (show p.2 ∈ Icc (0:ℝ) 1 from ⟨hp.1.2,hp.2.2⟩)
    exact ⟨⟨hx,hy⟩,⟨hx',hy'⟩⟩
  have hg : Continuous g := by dsimp [g,lerp]; fun_prop
  obtain ⟨p,hp,eq⟩ := zero_in_square (F ∘ g) (hf.comp hg.continuousOn maps)
    (fun y hy => by simpa [g,lerp] using left _ (within hcd hy))
    (fun y hy => by simpa [g,lerp] using right _ (within hcd hy))
    (fun x hx => by simpa [g,lerp] using bottom _ (within hab hx))
    (fun x hx => by simpa [g,lerp] using top _ (within hab hx))
  exact ⟨g p,maps hp,eq⟩

/-- A continuously winding incoming phase meets a bounded lift of the seam
    phase at arbitrarily large markers, at exactly the same transverse datum.
    Continuity is only needed on finite rectangles in the admissible tail. -/
theorem unbounded_matching_markers
    (b₀ c d P M : ℝ) (hcd : c ≤ d) (hP : 0 < P)
    (phase impact : ℝ → ℝ) (seamPhase seamImpact : ℝ × ℝ → ℝ)
    (wind : ∀ B ≥ b₀, ∀ t : ℝ, ∃ B' ≥ B, t < phase B')
    (regular : ∀ B ≥ b₀, ∀ B' ≥ B,
      ContinuousOn (fun p : ℝ × ℝ =>
        (phase p.1 - seamPhase p, seamImpact p - impact p.1)) (box B B' c d))
    (bounded : ∀ b ≥ b₀, ∀ y ∈ Icc c d, |seamPhase (b,y)| ≤ M)
    (low : ∀ b ≥ b₀, seamImpact (b,c) < impact b)
    (high : ∀ b ≥ b₀, impact b < seamImpact (b,d)) :
    ∀ B ≥ b₀, ∃ b ≥ B, ∃ y ∈ Icc c d, ∃ n : ℕ,
      phase b = seamPhase (b,y) + n*P ∧ impact b = seamImpact (b,y) := by
  intro B hB
  obtain ⟨n,hn⟩ := exists_nat_gt ((phase B + M)/P)
  have first : phase B + M < n*P := (div_lt_iff₀ hP).mp hn
  obtain ⟨B',hB',last⟩ := wind B hB (M+n*P)
  let F (p : ℝ × ℝ) := (phase p.1 - seamPhase p - n*P, seamImpact p - impact p.1)
  have hc : ContinuousOn F (box B B' c d) := by
    have r := regular B hB B' hB'
    exact (r.fst.sub continuousOn_const).prodMk r.snd
  obtain ⟨p,hp,hz⟩ := zero_in_box B B' c d hB' hcd F hc
    (fun y hy => by
      have e := (abs_le.mp (bounded B hB y hy)).1
      dsimp [F]; linarith)
    (fun y hy => by
      have e := (abs_le.mp (bounded B' (hB.trans hB') y hy)).2
      dsimp [F]; linarith)
    (fun x hx => sub_neg.mpr (low x (hB.trans hx.1)))
    (fun x hx => sub_pos.mpr (high x (hB.trans hx.1)))
  have h₁ := congrArg Prod.fst hz
  have h₂ := congrArg Prod.snd hz
  change phase p.1 - seamPhase p - n*P = 0 at h₁
  change seamImpact p - impact p.1 = 0 at h₂
  exact ⟨p.1,hp.1.1,p.2,⟨hp.1.2,hp.2.2⟩,n,by linarith,by linarith⟩

end SolitonClassification.Reflected.Rectangle
#print axioms SolitonClassification.Reflected.Rectangle.zero_in_square
#print axioms SolitonClassification.Reflected.Rectangle.unbounded_matching_markers
