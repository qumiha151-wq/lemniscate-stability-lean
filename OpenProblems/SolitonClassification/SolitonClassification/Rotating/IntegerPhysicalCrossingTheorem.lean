import SolitonClassification.Rotating.IntegerRetainedPhysicalTrace
import SolitonClassification.Rotating.IntegerGlobalPairExclusion
import SolitonClassification.Rotating.IntegerGlobalPhysicalBounds
import SolitonClassification.Rotating.IntegerPhysicalDoublePoints

namespace SolitonClassification.Rotating.IntegerTarget.Physical
noncomputable section
open Set GlobalCount CrossingCharts NormalEvolution

/-- A single actual primitive rotating expander realizes the two transverse
double points. Ordered pairs in a half-open least period are exhaustive. -/
structure DoublePointEvolution (P : Seed) : Prop where
  evolution : PrimitiveEvolution P
  initial_pairs : ∃z : TwoCrossingPairs (fun s => (P.I.x s,P.I.y s)) (P.L/2),
    ∀k, 1/4 < |Real.sin (P.I.theta (z.pair k).2-P.I.theta (z.pair k).1)|
  slice_pairs : ∀t : ℝ, -1/4<t → ∃shift : ℝ, Nonempty (TwoCrossingPairs
    (fun s => (normalX P t (s+shift),normalY P t (s+shift))) (P.L/2))

theorem two_double_points_of_verified_subdivision (fullLedger : Tree) (fullLedger_valid : check fullLedger (-4001) 4001 (-4001) 4001=true) : ∃P : Seed, DoublePointEvolution P := by
  obtain ⟨c,hc,I,low,high,bl,bh,kp,kn,rot,least,disk,trace⟩ := exists_retained_immersion
  obtain ⟨half,nodes,cap,agree⟩ := bounds_of_physical_trace c hc I (fun s hs => ⟨(trace s hs).1,(trace s hs).2.1⟩)
  obtain ⟨z⟩ := two_pairs_of_subdivision I hc nodes cap half agree fullLedger fullLedger_valid
  let T := c 2
  let P : Seed := ⟨c 4,2*T,I,by dsimp [T]; linarith⟩
  have ev : PrimitiveEvolution P := by
    refine ⟨⟨low,high⟩,⟨bl,bh⟩,kp,kn,rot,least,?_,normalEvolution_is_pure_normal P,
      fun t _ => normal_length P t,fun t _ => physical_image_eq P t,?_⟩
    · exact fun s => ⟨normalX_initial P s,normalY_initial P s⟩
    · exact fun t _ => physical_disk_of_square P disk t
  have period : P.L/2=c 2 := by change 2*(c 2)/2=c 2;ring
  refine ⟨P,ev,?_,?_⟩
  · rw [period]
    refine ⟨z,?_⟩
    intro k
    let s := (z.pair k).1
    let t := (z.pair k).2
    obtain ⟨hs,st,ht⟩ := z.inside k
    change -(c 2)≤s at hs
    change s<t at st
    change t<c 2 at ht
    let x := s/h
    let y := t/h
    have ex : x*h=s := div_mul_cancel₀ _ h_mem.1.ne'
    have ey : y*h=t := div_mul_cancel₀ _ h_mem.1.ne'
    have eqn : atGrid I x=atGrid I y := by simpa [atGrid,ex,ey,s,t] using z.coincide k
    have xy : x<y := (div_lt_div_iff_of_pos_right h_mem.1).mpr st
    have X : -(c 2/h)≤x := by rw [←neg_div];exact (div_le_div_iff_of_pos_right h_mem.1).mpr hs
    have Y : y<c 2/h := (div_lt_div_iff_of_pos_right h_mem.1).mpr ht
    have H := abs_le.mp half
    have per : 2*c 2=2*(c 2/h)*h := by rw [mul_assoc,div_mul_cancel₀ _ h_mem.1.ne']
    have error : |2*(c 2/h)-8000|≤1/1000 := abs_le.mpr ⟨by linarith [H.1],by linarith [H.2]⟩
    have span : (y-x)*h<2*c 2 := by rw [sub_mul,ex,ey];linarith
    obtain ⟨j,hx,hy⟩ := pair_in_chart_of_checked_subdivision I nodes cap per error fullLedger fullLedger_valid
      (by linarith [H.2] : -4001≤x) xy (by linarith [H.2] : y≤4001) span eqn
    have ang1 : I.theta s=gridAngle c x := by
      unfold gridAngle
      rw [ex]
      exact (trace s ⟨hs,st.le.trans ht.le⟩).2.2
    have ang2 : I.theta t=gridAngle c y := by
      unfold gridAngle
      rw [ey]
      exact (trace t ⟨hs.trans st.le,ht.le⟩).2.2
    change 1/4 < |Real.sin (I.theta t-I.theta s)|
    rw [ang1,ang2]
    exact crossing_angles_transverse hc hx hy
  · intro t _
    rw [period]
    exact physical_two_double_points P rfl z t

end
end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.two_double_points_of_verified_subdivision

