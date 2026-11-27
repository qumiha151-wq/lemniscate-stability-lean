import SolitonClassification.Rotating.IntegerGlobalReferences
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.IntegerTerminalRows

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
open DyadicReset

def positionNode : ℤ → Node
  | .ofNat j => GridPlus.atNode j
  | .negSucc j => GridMinus.atNode (j+1)

def lane (n : Node) (k : ℕ) : ℤ := n[k]?.getD 0
def G : ℤ := 2^240
def D : ℤ := 10^20
def H : ℤ := 65536*G

structure NodeAngles where
  values : Array (ℤ×ℤ)
  deriving Inhabited

def NodeAngles.get (a : NodeAngles) (k : ℕ) : ℤ×ℤ := a.values[k]?.getD (0,0)
def NodeAngles.C (a : NodeAngles) (k : ℕ) := (a.get k).1
def NodeAngles.S (a : NodeAngles) (k : ℕ) := (a.get k).2

def startOK (t : ℤ) (a : NodeAngles) : Prop :=
  |2*H^2*a.C 0-D*(2*H^2-t^2)| ≤ 2*H^2 ∧
  |6*H^3*a.S 0-D*(6*t*H^2-t^3)| ≤ 6*H^3
def normsOK (a : NodeAngles) (k : ℕ) : Prop := |a.C k|≤D ∧ |a.S k|≤D
def stageOK (a : NodeAngles) (k : ℕ) : Prop :=
  |D*a.C (k+1)-(a.C k^2-a.S k^2)|≤D ∧ |D*a.S (k+1)-2*a.S k*a.C k|≤D
def coordinatesOK (r : RefPoint) (p q : ℤ) (a : NodeAngles) : Prop :=
  |10^6*(q*a.C 16-p*a.S 16)-r.x*G*D|≤G*D ∧
  |10^6*(q*a.S 16+p*a.C 16)-r.y*G*D|≤G*D

def nodeChecked (r : RefPoint) (a : NodeAngles) : Prop :=
  let n := positionNode r.index
  r.index.natAbs<4000 ∧ |lane n 5|≤5*G ∧ |lane n 2|+|lane n 3|≤15*G ∧
    startOK (lane n 5) a ∧ (∀ k : Fin 17, normsOK a k) ∧
    (∀ k : Fin 16,stageOK a k) ∧ coordinatesOK r (lane n 2) (lane n 3) a

instance (r : RefPoint) (a : NodeAngles) : Decidable (nodeChecked r a) := by
  unfold nodeChecked startOK normsOK stageOK coordinatesOK
  infer_instance

end SolitonClassification.Rotating.IntegerTarget.GlobalCount
