import Lemniscate.EvenFactorDataEnergy
import Lemniscate.EvenFactorCertificate0
import Lemniscate.EvenFactorCertificate1
import Lemniscate.EvenFactorCertificate2
import Lemniscate.EvenFactorCertificate3
import Lemniscate.EvenFactorCertificate4
import Mathlib.Tactic.FinCases

/-! Apply all five kernel-checked factor certificates. Identification of the
actual Bernstein matrices with these intervals remains a separate premise. -/
namespace Lemniscate
open Complex Matrix CoarseArithmetic
open scoped ComplexConjugate

theorem even_factor_certificate (k : Fin 5) :
    (∀ i : Fin 31, 0 ≤ evenFactorDiagonal k i) ∧
      (∀ i : Fin 31, evenFactorRowBound k i ≤ 1) := by
  fin_cases k
  · exact even_factor_certificate_0
  · exact even_factor_certificate_1
  · exact even_factor_certificate_2
  · exact even_factor_certificate_3
  · exact even_factor_certificate_4

theorem even_factor_certified_energy (k : Fin 5) (B : Matrix (Fin 31) (Fin 31) ℝ)
    (hB : ∀ i j, B i j = B j i)
    (hI : ∀ i j, Contains (evenBernsteinInterval k i j) (B i j)) (v : Fin 31 → ℂ) :
    (∑ i, ∑ j, conj (v i)*(B i j:ℂ)*v j).re ≤
      ∑ i, (-1-(evenFactorPenalty i:ℝ))*‖v i‖^2 :=
  even_factor_data_energy k B hB hI (even_factor_certificate k).1
    (even_factor_certificate k).2 v

end Lemniscate
