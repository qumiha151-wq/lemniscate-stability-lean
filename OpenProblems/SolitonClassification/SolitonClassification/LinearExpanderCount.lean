import SolitonClassification.PhysicalMarkerCounts
import SolitonClassification.PhysicalMatchedMarker
import SolitonClassification.StrongCentreMarker

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set ReflectedArc

/-- At least N distinct geometric similarity classes have a positive
    normalized centre marker bounded linearly in N.  Geometric similarity
    allows arbitrary smooth reparametrization and forgets the named periods. -/
theorem linear_count_inequivalent_zero_turn_expanders :
    ∃ A C : ℝ, 0<A ∧ 0<C ∧ ∀ N : ℕ,
      ∃ b L : Fin N → ℝ, ∃ P : (i : Fin N) → ZeroTurnExpander (L i) (b i),
        (∀ i, 0<L i ∧ A≤b i ∧ b i≤A+C*((N:ℝ)+1) ∧ HasUniqueCentreMarker (P i)) ∧
        (∀ i j, i≠j → IsEmpty (GeometricSimilarity (P i) (P j))) := by
  obtain ⟨H,E,B,C,cp,b32,w,c,roots⟩ := exists_linearly_many_physical_matches
  have bp : 0<B := lt_of_lt_of_le (by norm_num) b32
  refine ⟨B,C,bp,cp,?_⟩
  intro N
  obtain ⟨β,z,n,inj,data⟩ := roots N
  have arcs (i : Fin N) : ∃ l>0, let y := solution 1 ![0,(β i:ℝ),0,0] l
      y 1=0 ∧ y 3=0 := matched_quarter c w (β i) (z i) (n i)
    (data i).2.1 (data i).2.2.1 (data i).2.2.2
  choose l lp seams using arcs
  have pos (i : Fin N) : 0<(β i:ℝ) := bp.trans_le (β i).property
  have realize (i : Fin N) : ∃ P : ZeroTurnExpander (4*l i) (β i:ℝ), HasUniqueCentreMarker P := by
    apply marked_of_quarter (z := solution 1 ![0,(β i:ℝ),0,0]) (lp i) (pos i)
    · exact continuous_iff_continuousAt.mpr fun r => (solution_derivative _ _ r).continuousAt
    · exact fun r _ => solution_derivative _ _ r
    · exact solution_zero _ _
    · exact (seams i).1
    · exact (seams i).2
  choose P marked using realize
  refine ⟨fun i => β i,fun i => 4*l i,P,fun i =>
    ⟨mul_pos (by norm_num) (lp i),(β i).property,(data i).1,marked i⟩,?_⟩
  intro i j diff
  exact ⟨fun S => diff (inj (Subtype.ext (S.marker_eq (pos i) (marked j))))⟩

/-- For all large thresholds B, at least floor(c B) pairwise inequivalent
    zero-turn shapes have a normalized centre curvature derivative in (0,B]. -/
theorem positive_lower_density_of_geometric_markers :
    ∃ c>0, ∃ B₀>0, ∀ B≥B₀,
      let N := ⌊c*B⌋₊
      ∃ b L : Fin N → ℝ, ∃ P : (i : Fin N) → ZeroTurnExpander (L i) (b i),
        (∀ i, 0<L i ∧ 0<b i ∧ b i≤B ∧ HasUniqueCentreMarker (P i)) ∧
        (∀ i j, i≠j → IsEmpty (GeometricSimilarity (P i) (P j))) := by
  obtain ⟨A,C,ap,cp,count⟩ := linear_count_inequivalent_zero_turn_expanders
  let c := 1/(2*C)
  have sc : 0<c := one_div_pos.mpr (by positivity)
  refine ⟨c,sc,2*(A+C),by positivity,?_⟩
  intro B hB
  let N := ⌊c*B⌋₊
  obtain ⟨b,L,P,ok,separate⟩ := count N
  refine ⟨b,L,P,fun i => ⟨(ok i).1,ap.trans_le (ok i).2.1,?_,(ok i).2.2.2⟩,separate⟩
  have hBp : 0≤B := (show 0≤2*(A+C) by positivity).trans hB
  have bound : (N:ℝ)≤c*B := Nat.floor_le (mul_nonneg sc.le hBp)
  have calcC : C*(c*B) = B/2 := by dsimp [c]; field_simp
  linarith [mul_le_mul_of_nonneg_left bound cp.le,(ok i).2.2.1]

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.linear_count_inequivalent_zero_turn_expanders
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.positive_lower_density_of_geometric_markers
