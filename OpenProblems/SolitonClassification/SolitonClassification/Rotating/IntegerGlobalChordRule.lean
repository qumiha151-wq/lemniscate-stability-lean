import SolitonClassification.Rotating.IntegerGlobalArcBounds
import SolitonClassification.Rotating.IntegerGlobalSeparation

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
noncomputable section
open Set CrossingCharts GlobalCrossings
set_option maxHeartbeats 2000000

/-- The projected coordinate in the integer ledger's units of one millionth. -/
private def scaledProjection {b L : ℝ} (I : WindingOneImmersion b L) (u v : ℤ) (x : ℝ) :=
  (10:ℝ)^6*projection I (u:ℝ) (v:ℝ) (x*h)

private theorem projected_node {b L : ℝ} (I : WindingOneImmersion b L) (nodes : NodeBounds I)
    (u v : ℤ) {i : ℕ} (hi : i<1146) :
    |scaledProjection I u v (refPoint i).index-(linear u v (refPoint i):ℝ)|≤100*(|(u:ℝ)|+|(v:ℝ)|) := by
  let r:=refPoint i
  let X:=I.x ((r.index:ℝ)*h)
  let Y:=I.y ((r.index:ℝ)*h)
  have x := nodes i hi false
  have y := nodes i hi true
  change |X-(r.x:ℝ)/10^6|≤1/10000 at x
  change |Y-(r.y:ℝ)/10^6|≤1/10000 at y
  have xr := mul_le_mul_of_nonneg_left x (abs_nonneg (u:ℝ))
  have yr := mul_le_mul_of_nonneg_left y (abs_nonneg (v:ℝ))
  unfold scaledProjection projection linear
  push_cast
  change |(10:ℝ)^6*((u:ℝ)*X+(v:ℝ)*Y)-((u:ℝ)*(r.x:ℝ)+(v:ℝ)*(r.y:ℝ))|≤_
  rw [show (10:ℝ)^6*((u:ℝ)*X+(v:ℝ)*Y)-((u:ℝ)*(r.x:ℝ)+(v:ℝ)*(r.y:ℝ))=
    10^6*((u:ℝ)*(X-(r.x:ℝ)/10^6)+(v:ℝ)*(Y-(r.y:ℝ)/10^6)) by ring,abs_mul]
  have triangle := abs_add_le ((u:ℝ)*(X-(r.x:ℝ)/10^6)) ((v:ℝ)*(Y-(r.y:ℝ)/10^6))
  rw [abs_mul,abs_mul] at triangle
  norm_num
  linarith only [xr,yr,triangle]

private theorem ledger_enclosure {b L : ℝ} (I : WindingOneImmersion b L) (nodes : NodeBounds I)
    (cap : ∀s,|I.k s|≤10) (u v : ℤ) {i j : ℕ} (hi : i<1146) (hj : j<1146)
    {A B : ℤ} (a : (refPoint i).index=A) (b' : (refPoint j).index=B) (width : B=A+1)
    {x : ℝ} (ax : (A:ℝ)≤x) (xb : x≤(B:ℝ)) :
    (min (linear u v (refPoint i)) (linear u v (refPoint j)):ℝ)-700*(|(u:ℝ)|+|(v:ℝ)|)≤scaledProjection I u v x ∧
    scaledProjection I u v x≤(max (linear u v (refPoint i)) (linear u v (refPoint j)):ℝ)+700*(|(u:ℝ)|+|(v:ℝ)|) := by
  let w:=|(u:ℝ)|+|(v:ℝ)|
  let R:=fun n:ℕ => (linear u v (refPoint n):ℝ)
  let F:=scaledProjection I u v
  have M := projection_enclosure I (u:ℝ) (v:ℝ)
    (show x*h∈Icc ((A:ℝ)*h) ((B:ℝ)*h) from ⟨mul_le_mul_of_nonneg_right ax h_mem.1.le,mul_le_mul_of_nonneg_right xb h_mem.1.le⟩)
    (fun z _ => cap z)
  have dif : (B:ℝ)*h-(A:ℝ)*h=h := by rw [width];push_cast;ring
  rw [dif] at M
  have h2 := pow_le_pow_left₀ h_mem.1.le h_mem.2.le 2
  have mcap : 10^6*margin (u:ℝ) (v:ℝ) h ≤600*w := by
    change 10^6*(10*w*h^2/8)≤600*w
    have hn : 0≤w := add_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith only [mul_le_mul_of_nonneg_left h2 hn,hn]
  have hA := projected_node I nodes u v hi
  have hB := projected_node I nodes u v hj
  rw [a] at hA
  rw [b'] at hB
  change |F A-R i|≤100*w at hA
  change |F B-R j|≤100*w at hB
  have lo : min (R i) (R j)-100*w ≤ min (F A) (F B) := le_min
    (by linarith only [(abs_le.mp hA).1,min_le_left (R i) (R j)])
    (by linarith only [(abs_le.mp hB).1,min_le_right (R i) (R j)])
  have up : max (F A) (F B) ≤ max (R i) (R j)+100*w := max_le
    (by linarith only [(abs_le.mp hA).2,le_max_left (R i) (R j)])
    (by linarith only [(abs_le.mp hB).2,le_max_right (R i) (R j)])
  have scalePos : (0:ℝ)≤10^6 := by norm_num
  have Ml := mul_le_mul_of_nonneg_left M.1 scalePos
  have Mu := mul_le_mul_of_nonneg_left M.2 scalePos
  rw [mul_sub,mul_min_of_nonneg _ _ scalePos] at Ml
  rw [mul_add,mul_max_of_nonneg _ _ scalePos] at Mu
  change min (F A) (F B)-10^6*margin (u:ℝ) (v:ℝ) h≤F x at Ml
  change F x≤max (F A) (F B)+10^6*margin (u:ℝ) (v:ℝ) h at Mu
  change min (R i) (R j)-700*w≤F x ∧ F x≤max (R i) (R j)+700*w
  exact ⟨by linarith only [lo,Ml,mcap],by linarith only [up,Mu,mcap]⟩

theorem chord_distinct {b L : ℝ} (I : WindingOneImmersion b L) (nodes : NodeBounds I)
    (cap : ∀s,|I.k s|≤10) {x y : ℝ} {A B C D : ℤ} (bounds : Inside x y A B C D)
    {i j m n : ℕ} {u v : ℤ} (ok : ChordPass A B C D i j m n u v) : atGrid I x≠atGrid I y := by
  obtain ⟨hi,hj,hm,hn,ai,bj,cm,dn,w₁,w₂,sep⟩ := ok
  have X := ledger_enclosure I nodes cap u v hi hj ai bj w₁ bounds.1 bounds.2.1
  have Y := ledger_enclosure I nodes cap u v hm hn cm dn w₂ bounds.2.2.1 bounds.2.2.2
  intro eq
  have proj := congrArg (fun p : ℝ×ℝ => (10:ℝ)^6*((u:ℝ)*p.1+(v:ℝ)*p.2)) eq
  change scaledProjection I u v x=scaledProjection I u v y at proj
  rcases sep with left | right
  · have z := (Int.cast_lt (R:=ℝ)).mpr left
    push_cast at z X Y
    linarith only [z,X.2,Y.1,proj]
  · have z := (Int.cast_lt (R:=ℝ)).mpr right
    push_cast at z X Y
    linarith only [z,X.1,Y.2,proj]

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCount
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCount.chord_distinct
