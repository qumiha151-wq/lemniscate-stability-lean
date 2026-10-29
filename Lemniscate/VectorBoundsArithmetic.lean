import Lemniscate.VectorIntervalData
import Lemniscate.GeometricMomentTails

/-! Exact arithmetic for the current paper's finite vector and error bounds.
Their application to actual vectors uses the separate interval soundness proof. -/
namespace Lemniscate.CoarseArithmetic

def intervalL4 {N : ℕ} (v : Fin N → Interval) : ℚ :=
  ∑ j : Fin N, absUpper (v j) * ∑ k : Fin 5, (2*(j.val+1:ℕ):ℚ)^k.val

def rotationRescaleData : Interval :=
  add (reciprocalPositive rotationFiniteNormData) (point (-1))

def adjointRescaleData : Interval :=
  add (reciprocalPositive adjointFinitePairingData) (point (-1))

def rotationErrorUpper : ℚ :=
  (2*H/rotationNormData.lo)*(∑ k : Fin 5, 2^k.val*momentTail (k.val+2) qb 16)+
  absUpper rotationRescaleData*intervalL4 (fun j : Fin 15 => rotationCoefficientData (Fin.castAdd 3 j))

def adjointErrorUpper : ℚ :=
  (∑ j : Fin 3, absUpper (adjointCoefficientData (Fin.natAdd 15 j))*
    ∑ k : Fin 5, (2*(15+j.val+1:ℕ):ℚ)^k.val)+
  absUpper adjointRescaleData*intervalL4 (fun j : Fin 15 => adjointCoefficientData (Fin.castAdd 3 j))+
  27/10^14

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem vector_error_comparisons :
    rotationErrorUpper < 2/10^12 ∧ adjointErrorUpper < 6/10^12 ∧
    intervalL4 rotationFiniteData+rotationErrorUpper < 200 ∧
    intervalL4 adjointFiniteData+adjointErrorUpper < 200 ∧
    (∑ j : Fin 15, (absUpper (differenceFiniteData j))^2) < 1/400 ∧
    (∀ j : Fin 15, 1 ≤ j.val → absUpper (rotationFiniteData j) <
      (13/1000)*sqrtTwoData.lo*a^((j.val:ℤ)-2)) ∧
    (∀ j : Fin 15, 1 ≤ j.val → absUpper (differenceFiniteData j) <
      (7/1000)*sqrtTwoData.lo*a^((j.val:ℤ)-2)) := by decide +kernel

end Lemniscate.CoarseArithmetic
