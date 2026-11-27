import SolitonClassification.Rotating.IntegerGlobalNodeBlock00
import SolitonClassification.Rotating.IntegerGlobalNodeBlock01
import SolitonClassification.Rotating.IntegerGlobalNodeBlock02
import SolitonClassification.Rotating.IntegerGlobalNodeBlock03
import SolitonClassification.Rotating.IntegerGlobalNodeBlock04
import SolitonClassification.Rotating.IntegerGlobalNodeBlock05
import SolitonClassification.Rotating.IntegerGlobalNodeBlock06
import SolitonClassification.Rotating.IntegerGlobalNodeBlock07
import SolitonClassification.Rotating.IntegerGlobalNodeBlock08
import SolitonClassification.Rotating.IntegerGlobalNodeBlock09
import SolitonClassification.Rotating.IntegerGlobalNodeBlock10
import SolitonClassification.Rotating.IntegerGlobalNodeBlock11
import SolitonClassification.Rotating.IntegerGlobalNodeBlock12
import SolitonClassification.Rotating.IntegerGlobalNodeBlock13
import SolitonClassification.Rotating.IntegerGlobalNodeBlock14
import SolitonClassification.Rotating.IntegerGlobalNodeBlock15
import SolitonClassification.Rotating.IntegerGlobalNodeBlock16
import SolitonClassification.Rotating.IntegerGlobalNodeBlock17
import SolitonClassification.Rotating.IntegerGlobalNodePositions

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
open Set DyadicReset
noncomputable section
set_option maxHeartbeats 1800000

theorem every_reference_checked (i : ℕ) (hi : i<refTable.size) : ∃ a, nodeChecked (refPoint i) a := by
  rw [ref_count] at hi
  by_cases b0 : i<64
  · let j : Fin 64 := ⟨i-0,by omega⟩
    have eq : 0+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock00.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b1 : i<128
  · let j : Fin 64 := ⟨i-64,by omega⟩
    have eq : 64+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock01.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b2 : i<192
  · let j : Fin 64 := ⟨i-128,by omega⟩
    have eq : 128+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock02.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b3 : i<256
  · let j : Fin 64 := ⟨i-192,by omega⟩
    have eq : 192+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock03.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b4 : i<320
  · let j : Fin 64 := ⟨i-256,by omega⟩
    have eq : 256+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock04.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b5 : i<384
  · let j : Fin 64 := ⟨i-320,by omega⟩
    have eq : 320+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock05.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b6 : i<448
  · let j : Fin 64 := ⟨i-384,by omega⟩
    have eq : 384+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock06.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b7 : i<512
  · let j : Fin 64 := ⟨i-448,by omega⟩
    have eq : 448+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock07.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b8 : i<576
  · let j : Fin 64 := ⟨i-512,by omega⟩
    have eq : 512+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock08.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b9 : i<640
  · let j : Fin 64 := ⟨i-576,by omega⟩
    have eq : 576+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock09.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b10 : i<704
  · let j : Fin 64 := ⟨i-640,by omega⟩
    have eq : 640+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock10.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b11 : i<768
  · let j : Fin 64 := ⟨i-704,by omega⟩
    have eq : 704+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock11.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b12 : i<832
  · let j : Fin 64 := ⟨i-768,by omega⟩
    have eq : 768+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock12.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b13 : i<896
  · let j : Fin 64 := ⟨i-832,by omega⟩
    have eq : 832+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock13.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b14 : i<960
  · let j : Fin 64 := ⟨i-896,by omega⟩
    have eq : 896+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock14.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b15 : i<1024
  · let j : Fin 64 := ⟨i-960,by omega⟩
    have eq : 960+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock15.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b16 : i<1088
  · let j : Fin 64 := ⟨i-1024,by omega⟩
    have eq : 1024+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock16.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  by_cases b17 : i<1146
  · let j : Fin 58 := ⟨i-1088,by omega⟩
    have eq : 1088+j.val=i := by dsimp [j]; omega
    have checked := NodeBlock17.certified j
    rw [eq] at checked
    exact ⟨_,checked⟩
  omega

theorem reference_index_bound (i : ℕ) (hi : i<refTable.size) : |(refPoint i).index|≤3999 := by
  obtain ⟨a,h⟩ := every_reference_checked i hi
  have b : (refPoint i).index.natAbs<4000 := h.1
  rw [←Int.natCast_natAbs]
  exact_mod_cast (show (refPoint i).index.natAbs≤3999 by omega)

theorem reference_position_errors (c : Parameters) (hc : c∈cube) (i : ℕ) (hi : i<refTable.size) :
    let r := refPoint i
    let v := segmentPosition c ((r.index:ℝ)*step Middle.hn)
    |v.1-(r.x:ℝ)/10^6|≤1/10000 ∧ |v.2-(r.y:ℝ)/10^6|≤1/10000 := by
  obtain ⟨a,h⟩ := every_reference_checked i hi
  exact position_of_checked c hc _ a h

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCount
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCount.reference_position_errors
