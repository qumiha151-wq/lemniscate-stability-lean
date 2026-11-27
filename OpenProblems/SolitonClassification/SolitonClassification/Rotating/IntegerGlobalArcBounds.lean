import SolitonClassification.Rotating.IntegerGlobalLedger
import SolitonClassification.Rotating.IntegerGlobalGridGeometry

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
noncomputable section
open Set CrossingCharts GlobalCrossings

theorem step_bound : h≤7553/10^6 := by norm_num [h,DyadicReset.step,DyadicReset.Middle.hn,DyadicReset.Middle.hd]

def atGrid {b L : ℝ} (I : WindingOneImmersion b L) (x : ℝ) := (I.x (x*h),I.y (x*h))

def observed (r : RefPoint) (axis : Bool) : ℝ := (coord r axis:ℝ)/10^6
def component (p : ℝ×ℝ) (axis : Bool) : ℝ := if axis then p.2 else p.1

theorem coord_lipschitz {b L : ℝ} (I : WindingOneImmersion b L) (axis : Bool) (x y : ℝ) :
    |component (atGrid I x) axis-component (atGrid I y) axis|≤h*|x-y| := by
  have rates := unit_coordinate_motion I (y*h) (x*h)
  rw [←sub_mul,abs_mul,abs_of_pos h_mem.1,mul_comm |x-y| h] at rates
  cases axis
  · exact rates.1
  · exact rates.2

def NodeBounds {b L : ℝ} (I : WindingOneImmersion b L) := ∀i : ℕ, i<1146 → ∀axis : Bool,
  |component (atGrid I (refPoint i).index) axis-observed (refPoint i) axis|≤1/10000

theorem axis_distinct {b L : ℝ} (I : WindingOneImmersion b L) (nodes : NodeBounds I)
    {x y : ℝ} {A B C D : ℤ} (bounds : Inside x y A B C D) {i j : ℕ} {axis : Bool}
    (ok : AxisPass A B C D i j axis) : atGrid I x≠atGrid I y := by
  obtain ⟨hi,hj,sep⟩ := ok
  have radius {x : ℝ} {a b : ℤ} (ha : (a:ℝ)≤x) (hb : x≤(b:ℝ)) (n : ℕ) (hn : n<1146) :
      |component (atGrid I x) axis-observed (refPoint n) axis|≤(nodeRadius a b (refPoint n):ℝ)/10^6 := by
    let p := refPoint n
    let R := max |a-p.index| |b-p.index|
    have hA : |(a:ℝ)-(p.index:ℝ)|≤(R:ℝ) := by exact_mod_cast (le_max_left |a-p.index| |b-p.index|)
    have hB : |(b:ℝ)-(p.index:ℝ)|≤(R:ℝ) := by exact_mod_cast (le_max_right |a-p.index| |b-p.index|)
    have dist : |x-(p.index:ℝ)|≤(R:ℝ) := abs_le.mpr ⟨by linarith [(abs_le.mp hA).1],by linarith [(abs_le.mp hB).2]⟩
    have K := mul_le_mul step_bound dist (abs_nonneg _) (by norm_num : (0:ℝ)≤7553/10^6)
    have lip := coord_lipschitz I axis x p.index
    have obs := nodes n hn axis
    change |component (atGrid I p.index) axis-observed p axis|≤1/10000 at obs
    have eq : (nodeRadius a b p:ℝ)=100+7553*(R:ℝ) := by dsimp only [nodeRadius,R];push_cast;rfl
    change |component (atGrid I x) axis-observed p axis|≤(nodeRadius a b p:ℝ)/10^6
    rw [eq]
    linarith only [abs_sub_le (component (atGrid I x) axis) (component (atGrid I p.index) axis) (observed p axis),lip,K,obs]
  intro same
  have hx := radius bounds.1 bounds.2.1 i hi
  have hy := radius bounds.2.2.1 bounds.2.2.2 j hj
  rw [same] at hx
  have tri : |observed (refPoint i) axis-observed (refPoint j) axis| ≤
      (nodeRadius A B (refPoint i):ℝ)/10^6+(nodeRadius C D (refPoint j):ℝ)/10^6 :=
    (abs_sub_le _ (component (atGrid I y) axis) _).trans
      (add_le_add ((abs_sub_comm _ _).le.trans hx) hy)
  have bound : (((nodeRadius A B (refPoint i)):ℝ)+((nodeRadius C D (refPoint j)):ℝ)) <
       |((coord (refPoint i) axis:ℤ):ℝ)-((coord (refPoint j) axis:ℤ):ℝ)| := by exact_mod_cast sep
  simp only [observed,←sub_div,abs_div] at tri
  norm_num at tri
  linarith only [bound,tri]

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCount
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCount.axis_distinct

