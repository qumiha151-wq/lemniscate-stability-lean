import SolitonClassification.FrozenDyadicRow

/-! Compact literals for polynomial witnesses. All decoded coefficients are
subsequently verified by the row's polynomial defect and endpoint tests. -/
namespace ClosedSimilarity.FrozenStress.Endpoint

def joinBlocks : List ℕ → ℕ
  | [] => 0
  | a::xs => a+(joinBlocks xs <<< 2048)

def decodeCoefficients : ℕ → ℕ → List ℤ
  | 0,_ => []
  | n+1,packed =>
    let width := packed % 1024
    let tailBits := packed >>> 10
    let digit := tailBits % (1 <<< width)
    let magnitude := digit >>> 1
    let coefficient : ℤ := if digit % 2 = 0 then Int.ofNat magnitude else Int.negSucc magnitude
    coefficient :: decodeCoefficients n (tailBits >>> width)

def coefficients (n : ℕ) (blocks : List ℕ) : List ℤ := decodeCoefficients n (joinBlocks blocks)

end ClosedSimilarity.FrozenStress.Endpoint
