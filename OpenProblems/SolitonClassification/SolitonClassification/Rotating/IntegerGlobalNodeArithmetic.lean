import SolitonClassification.Rotating.IntegerGlobalNodeChecks
import SolitonClassification.Rotating.IntegerGlobalNodeAngle

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
noncomputable section

def qG (x : ℤ) : ℚ := (x:ℚ)/G
def qD (x : ℤ) : ℚ := (x:ℚ)/D

private theorem rescale {a b : ℤ} (h : |a|≤b) (den : ℚ) (pos : 0<den) :
    |(a:ℚ)/den|≤(b:ℚ)/den := by
  rw [abs_div,abs_of_pos pos]
  apply div_le_div_of_nonneg_right _ pos.le
  exact_mod_cast h

macro "node_ring" : tactic => `(tactic|
  (push_cast <;> norm_num [qG,qD,H,D,G] <;> first | (congr 1 <;> ring) | ring))

def rational_phases (t : ℤ) (a : NodeAngles) (phase : |t|≤5*G)
    (start : startOK t a) (unit : ∀k : Fin 17,normsOK a k)
    (stages : ∀k : Fin 16,stageOK a k) :
    FineAngles (qG t) := by
  refine ⟨fun k=>qD (a.C k),fun k=>qD (a.S k),?_,?_,?_,?_,?_,?_,?_⟩
  · convert rescale phase (G:ℚ) (by norm_num [G]) using 1 <;> node_ring
  · convert rescale start.1 (2*(H:ℚ)^2*D) (by norm_num [H,G,D]) using 1 <;> node_ring
  · convert rescale start.2 (6*(H:ℚ)^3*D) (by norm_num [H,G,D]) using 1 <;> node_ring
  · intro k hk
    convert rescale (unit ⟨k,by omega⟩).1 (D:ℚ) (by norm_num [D]) using 1 <;> node_ring
  · intro k hk
    convert rescale (unit ⟨k,by omega⟩).2 (D:ℚ) (by norm_num [D]) using 1 <;> node_ring
  · intro k hk
    convert rescale (stages ⟨k,hk⟩).1 ((D:ℚ)^2) (by norm_num [D]) using 1 <;> node_ring
  · intro k hk
    convert rescale (stages ⟨k,hk⟩).2 ((D:ℚ)^2) (by norm_num [D]) using 1 <;> node_ring

theorem rational_coordinates (p q : ℤ) (a : NodeAngles) (r : RefPoint)
    (mag : |p|+|q|≤15*G) (h : coordinatesOK r p q a) :
    |qG p|+|qG q|≤15 ∧
    |qG q*qD (a.C 16)-qG p*qD (a.S 16)-(r.x:ℚ)/10^6|≤1/10^6 ∧
    |qG q*qD (a.S 16)+qG p*qD (a.C 16)-(r.y:ℚ)/10^6|≤1/10^6 := by
  constructor
  · have hm : |(p:ℚ)|+|(q:ℚ)|≤15*(G:ℚ) := by exact_mod_cast mag
    unfold qG
    rw [abs_div,abs_div,abs_of_pos (show (0:ℚ)<G by norm_num [G]),←add_div]
    exact (div_le_iff₀ (by norm_num [G])).mpr hm
  constructor
  · convert rescale h.1 ((10:ℚ)^6*G*D) (by norm_num [G,D]) using 1 <;> node_ring
  · convert rescale h.2 ((10:ℚ)^6*G*D) (by norm_num [G,D]) using 1 <;> node_ring

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCount
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCount.rational_coordinates
