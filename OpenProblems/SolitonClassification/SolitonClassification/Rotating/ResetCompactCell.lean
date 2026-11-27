import SolitonClassification.Rotating.ResetTapeTransport
namespace SolitonClassification.Rotating.DyadicReset

/-- Read signed coefficients recorded with their bit length. Leading
coefficient widths occupy one octet each, allowing the kernel to load a
complete polynomial from one numeral, including internal zero terms. -/
def unpackRow : ℕ→ℕ→List ℤ
  | 0,_=>[]
  | n+1,q=>if q=0 then [] else
    let k:=q%256
    let v:=(q>>>8)%2^k
    let a : ℤ := if v%2=0 then (v/2:ℕ) else -((v/2:ℕ):ℤ)-1
    a::unpackRow n (q>>>(8+k))
abbrev PackedCell := Array ℕ
def unpackCell (P : PackedCell) : Array (List ℤ) := P.map (unpackRow 53)
def packedData (P : PackedCell) : Data := fun i=>unpackRow 53 ((P[i]?).getD 0)
def checksAt (hn : ℤ) (P : PackedCell) (i : Nat) :=
  CellCheck.sufficient (defectTerm (packedData P) d hn Middle.hd i)
theorem signedOfAll {n : ℤ} {P : PackedCell} (ok : (List.range 31).all (checksAt n P)=true) : SignedCheck n (packedData P) := fun i=>List.all_eq_true.mp ok i (List.mem_range.mpr i.isLt)
def sampleStart (P : PackedCell) : Node := (unpackCell P).map (fun p=>p.head?.getD 0)
def sampleEnd (P : PackedCell) : Node := (unpackCell P).map List.sum

theorem packed_head (P : PackedCell) (i : ℕ) :
    ((packedData P i).head?.getD 0)=((sampleStart P)[i]?).getD 0 := by
  simp only [packedData,sampleStart,unpackCell,Array.getElem?_map]
  cases h : P[i]? <;> rfl
theorem packed_sum (P : PackedCell) (i : ℕ) :
    (packedData P i).sum=((sampleEnd P)[i]?).getD 0 := by
  simp only [packedData,sampleEnd,unpackCell,Array.getElem?_map]
  cases h : P[i]? <;> rfl
theorem packed_match {P Q : PackedCell} (h : sampleEnd P=sampleStart Q) (i : ℕ) :
    (packedData P i).sum=(packedData Q i).head?.getD 0 := by rw [packed_sum,h,packed_head]
end SolitonClassification.Rotating.DyadicReset
