import SolitonClassification.Rotating.IntegerGlobalChordRule
import SolitonClassification.Rotating.IntegerGlobalChartLabels
namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
noncomputable section
open Set CrossingCharts GlobalCrossings

theorem pair_in_chart_of_checked_subdivision {b L : ℝ} (I : WindingOneImmersion b L)
    (nodes : NodeBounds I) (cap : ∀s,|I.k s|≤10) {H : ℝ} (per : L=H*h)
    (err : |H-8000|≤1/1000) (tree : Tree) (valid : check tree (-4001) 4001 (-4001) 4001=true)
    {x y : ℝ} (lo : -4001≤x) (lt : x<y) (hi : y≤4001) (span : (y-x)*h<L)
    (same : atGrid I x=atGrid I y) : InAChart x y := by
  apply check_sound lt.le _ tree (-4001) 4001 (-4001) 4001 valid
    (by norm_num [Inside];exact ⟨lo,lt.le.trans hi,lo.trans lt.le,hi⟩)
  constructor
  · intro a b c d cut inside
    have close : y-x≤32 ∨ 7970≤y-x := by
      rcases cut with low | high
      · have bound : (d:ℝ)-(a:ℝ)≤32 := by exact_mod_cast low
        exact Or.inl (by linarith [inside.1,inside.2.2.2])
      · have bound : (7970:ℝ)≤(c:ℝ)-(b:ℝ) := by exact_mod_cast high
        exact Or.inr (by linarith [inside.2.1,inside.2.2.1])
    rcases short_grid_aliases I cap h_mem.1 h_mem.2.le per err lo hi lt.le close same with eq|eq
    · exact (lt.ne eq).elim
    · exact (span.ne eq).elim
  · intro a b c d flag pass inside
    exact chart_of_box inside pass
  · intro a b c d i j axis pass inside
    exact (axis_distinct I nodes inside pass same).elim
  · intro a b c d i j m n u v pass inside
    exact (chord_distinct I nodes cap inside pass same).elim

/-- The interval [-T,T) contains each parameter class exactly once.
Within it the only coincident pairs are the ones provided by the two charts. -/
theorem two_pairs_of_subdivision {b T : ℝ} (I : WindingOneImmersion b (2*T))
    {c : Parameters} (hc : c∈cube) (nodes : NodeBounds I) (cap : ∀s,|I.k s|≤10)
    (half : |T/h-4000|≤1/2000)
    (agree : ∀v:ℝ, -(T/h)≤v → v≤T/h → atGrid I v=gridPosition c v)
    (tree : Tree) (valid : check tree (-4001) 4001 (-4001) 4001=true) :
    Nonempty (TwoCrossingPairs (fun s => (I.x s,I.y s)) T) := by
  have halves := abs_le.mp half
  have minT : (3000:ℝ)<T/h := by linarith [halves.1]
  have maxT : T/h<4001 := by linarith [halves.2]
  have Tpos : 0<T := by have := (lt_div_iff₀ h_mem.1).mp minT; nlinarith [h_mem.1]
  have physical (z:ℝ) : z/h*h=z := div_mul_cancel₀ z h_mem.1.ne'
  let data := fun k : Fin 2 => unique_transverse_chart hc k
  let p := fun k : Fin 2 => Classical.choose (data k).exists
  have chart (k : Fin 2) := Classical.choose_spec (data k).exists
  have inp (k : Fin 2) : 0<(p k).1 ∧ (p k).1<(p k).2 ∧ (p k).2<3000 :=
    chart_in_period (chart k).1 (chart k).2.1
  have map1 (k : Fin 2) : atGrid I (p k).1=gridPosition c (p k).1 :=
    agree _ (by linarith [(inp k).1]) (by linarith [(inp k).2.1,(inp k).2.2])
  have map2 (k : Fin 2) : atGrid I (p k).2=gridPosition c (p k).2 :=
    agree _ (by linarith [(inp k).1,(inp k).2.1]) (by linarith [(inp k).2.2])
  let q := fun k : Fin 2 => ((p k).1*h,(p k).2*h)
  refine ⟨⟨q,?_,?_,?_,?_⟩⟩
  · intro k
    have range := inp k
    exact ⟨by dsimp [q]; linarith [mul_pos range.1 h_mem.1],
      mul_lt_mul_of_pos_right range.2.1 h_mem.1,(lt_div_iff₀ h_mem.1).mp (range.2.2.trans minT)⟩
  · intro k
    exact (map1 k).trans ((chart k).2.2.1.trans (map2 k).symm)
  · change atGrid I (p 0).1 ≠ atGrid I (p 1).1
    rw [map1,map1]
    intro e
    have s := separate_locations hc 0 (chart 0).1
    have t := separate_locations hc 1 (chart 1).1
    norm_num at s t
    rw [e] at s
    linarith [s.1,t.2]
  · intro s t hs st ht eq
    let x := s/h
    let y := t/h
    have xy : x<y := (div_lt_div_iff_of_pos_right h_mem.1).mpr st
    have xl : -(T/h)≤x := by dsimp only [x]; rw [←neg_div]; exact (div_le_div_iff_of_pos_right h_mem.1).mpr hs
    have yr : y<T/h := (div_lt_div_iff_of_pos_right h_mem.1).mpr ht
    have ex : x*h=s := physical s
    have ey : y*h=t := physical t
    have same : atGrid I x=atGrid I y := by simpa [atGrid,ex,ey] using eq
    have per : 2*T=(2*(T/h))*h := by rw [mul_assoc,physical]
    have error : |2*(T/h)-8000|≤1/1000 := abs_le.mpr ⟨by linarith [halves.1],by linarith [halves.2]⟩
    have span : (y-x)*h<2*T := by rw [sub_mul,ex,ey];linarith
    obtain ⟨k,hx,hy⟩ := pair_in_chart_of_checked_subdivision I nodes cap per error tree valid
      (by linarith : -4001≤x) xy (yr.trans maxT).le span same
    have gridEq := (agree x xl (xy.trans yr).le).symm.trans (same.trans (agree y (xl.trans xy.le) yr.le))
    have indep (u) (hu : u∈dom k false) (v) (hv : v∈dom k true) :
        Real.sin (gridAngle c v-gridAngle c u)≠0 := abs_pos.mp (by linarith [crossing_angles_transverse hc hu hv])
    obtain ⟨xe,ye⟩ := unique_chart_parameters hc indep hx hy (chart k).1 (chart k).2.1 gridEq (chart k).2.2.1
    exact ⟨k,Prod.ext (by change s=(p k).1*h;rw [←xe,ex]) (by change t=(p k).2*h;rw [←ye,ey])⟩

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCount
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCount.two_pairs_of_subdivision

