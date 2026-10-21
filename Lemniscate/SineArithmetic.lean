import Lemniscate.CoarseArithmetic

/-! Exact rational certificates for the sine-even sector: the first diagonal,
two low tail-block rows, and the complete coupling majorant. -/
namespace Lemniscate.CoarseArithmetic

def sineEntry (j k : ℕ) : Interval :=
  let n : ℚ := 2*(j:ℚ)
  let m : ℚ := 2*(k:ℚ)
  let nonconstant := mul ⟨rlo,rhi⟩
    (add (scale (hInterval (j-k+(k-j))) (45*n*m-(15/4:ℚ)*(n-m)^2))
      (scale (hInterval (j+k)) (45*n*m+(15/4:ℚ)*(n+m)^2)))
  if j = k then add nonconstant ⟨-4*rhi^2*n^4-42,-4*rlo^2*n^4-42⟩
  else nonconstant

def sineFiniteRow (j : ℕ) : ℚ :=
  (sineEntry j j).hi +
    sumTo 6 (fun k => if k+2 = j then 0 else absUpper (sineEntry j (k+2))) +
    C*((2*(j:ℚ))^2*tail1 qb (8-j)+2*(2*(j:ℚ))*tail2 qb (8-j)+tail3 qb (8-j))

def momentTail (p : ℕ) (z : ℚ) (L : ℕ) : ℚ :=
  moment p z - sumTo L (fun n => (n:ℚ)^p*z^n)

def sineCouplingTail : ℚ :=
  C^2*(momentTail 6 (qb^2) 3+8*momentTail 5 (qb^2) 3+
    24*momentTail 4 (qb^2) 3+32*momentTail 3 (qb^2) 3+16*momentTail 2 (qb^2) 3)

def sineCouplingBound : ℚ :=
  (absUpper (sineEntry 1 2))^2+(absUpper (sineEntry 1 3))^2+sineCouplingTail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sine_first_diagonal_certificate : (sineEntry 1 1).hi < -12 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sine_low_row_certificates :
    sineFiniteRow 2 < -120 ∧ sineFiniteRow 3 < -1560 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sine_coupling_certificate : sineCouplingBound < 3916 := by decide +kernel

set_option maxRecDepth 100000 in
theorem sine_diagonal_correction_certificate :
    480*rhi*H*moment 3 (qb^2) ≤ 42 := by decide +kernel

end Lemniscate.CoarseArithmetic
