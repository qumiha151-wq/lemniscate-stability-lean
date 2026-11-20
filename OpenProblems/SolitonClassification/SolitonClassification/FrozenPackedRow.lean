import SolitonClassification.FrozenDyadicRow
import SolitonClassification.FrozenPolynomialBounds
import SolitonClassification.FrozenPackedPolynomial

/-! Kronecker substitution accelerates the four exact integer defect checks. -/
namespace ClosedSimilarity.FrozenStress.Endpoint
open IntegerPoly

def halfRadix : ℕ := 2^1599
def radix : ℤ := 2*(halfRadix:ℤ)

def packedFormula (B : ℤ) : Formula → ℤ
  | .atom p => pack B p
  | .add x y => packedFormula B x+packedFormula B y
  | .mul x y => packedFormula B x*packedFormula B y
  | .smul c x => c*packedFormula B x

theorem packedFormula_eq (B : ℤ) (e : Formula) :
    packedFormula B e=pack B e.polynomial := by
  induction e with
  | atom p => rfl
  | add x y hx hy => simp only [packedFormula,Formula.polynomial,pack_plus,hx,hy]
  | mul x y hx hy => simp only [packedFormula,Formula.polynomial,pack_times,hx,hy]
  | smul c x hx => simp only [packedFormula,Formula.polynomial,pack_scale,hx]

def Accept (e : Formula) (target : ℕ) : Prop :=
  e.magnitude<halfRadix ∧ digitsSize halfRadix e.width (packedFormula radix e)*T ≤ target
instance (e : Formula) (target : ℕ) : Decidable (Accept e target) := by unfold Accept; infer_instance

theorem Accept.sound {e : Formula} {target : ℕ} (h : Accept e target) :
    size e.polynomial*T≤target := by
  have ht := h.2
  rw [packedFormula_eq,radix,digitsSize_pack e.polynomial e.width (e.bounds.1.trans_lt h.1) e.bounds.2] at ht
  exact ht

def kFormula (r : Row) : Formula := .add (.smul 32 (.atom (deriv r.k))) (.smul (-1) (.atom r.v))
def vFormula (r : Row) : Formula :=
  .add (.smul (2*(S:ℤ)^2) (.add (.smul 32 (.atom (deriv r.v))) (.atom r.p)))
    (.mul (.mul (.atom r.k) (.atom r.k)) (.atom r.k))
def pFormula (r : Row) : Formula :=
  .add (.smul (32*(S:ℤ)) (.atom (deriv r.p))) (.mul (.atom r.k) (.atom r.q))
def qFormula (r : Row) : Formula :=
  .add (.smul (32*(S:ℤ)) (.atom (deriv r.q))) (.smul (-1) (.mul (.atom r.k) (.atom r.p)))

def PackedGood (r : Row) : Prop := size r.k≤8*S ∧
  Accept (kFormula r) S ∧ Accept (vFormula r) (16*S^3) ∧
  Accept (pFormula r) (S^2) ∧ Accept (qFormula r) (S^2)
instance (r : Row) : Decidable (PackedGood r) := by unfold PackedGood; infer_instance

theorem packed_good_sound (r : Row) (hr : PackedGood r) : Good r :=
  ⟨hr.1,hr.2.1.sound,hr.2.2.1.sound,hr.2.2.2.1.sound,hr.2.2.2.2.sound⟩

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.packed_good_sound
