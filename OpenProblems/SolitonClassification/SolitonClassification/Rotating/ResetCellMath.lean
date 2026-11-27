import SolitonClassification.Rotating.ResetExpression
import SolitonClassification.Rotating.Field
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace SolitonClassification.Rotating.DyadicReset
noncomputable section

private def weight (n : Nat) (l : List ℤ) :=
    (l.zipIdx n).map fun (c,j) => ((j+1 : Nat):ℤ)*c

private theorem weight_succ (n : Nat) (l : List ℤ) (t : ℝ) :
    eval t (weight (n+1) l)=eval t (weight n l)+eval t l := by
  induction l generalizing n with
  | nil => simp [weight,eval]
  | cons a l ih =>
    simp only [weight,List.zipIdx_cons,List.map_cons,eval,Int.cast_mul,Nat.cast_add,Nat.cast_one]
    change _+t*eval t (weight ((n+1)+1) l) = _+t*eval t (weight (n+1) l)+_
    rw [ih]; push_cast; ring

theorem eval_deriv (p : List ℤ) (t : ℝ) :
    HasDerivAt (fun x=>eval x p) (eval t (differential p)) t := by
  induction p with
  | nil => simpa [eval,differential] using hasDerivAt_const t (0:ℝ)
  | cons a p ih =>
    apply (((hasDerivAt_id t).mul ih).const_add (a:ℝ)).congr_deriv
    cases p with
    | nil => simp [differential,eval]
    | cons b q =>
      change 1*eval t (b::q)+t*eval t (weight 0 q)=eval t (weight 0 (b::q))
      change 1*((b:ℝ)+t*eval t q)+t*eval t (weight 0 q)=
        (((((0+1:Nat):ℤ)*b):ℤ):ℝ)+t*eval t (weight 1 q)
      rw [weight_succ 0 q t]
      norm_num; ring

abbrev Data := Nat → List ℤ
def path (p : Data) (d : ℤ) (t : ℝ) : State := fun i => eval t (p i)/(d:ℝ)
def velocity (p : Data) (d : ℤ) (t : ℝ) : State := fun i => eval t (differential (p i))/(d:ℝ)

def columnOf (d : ℤ) (x : Nat → ℝ) (j : Fin 5) : State :=
  fun i=>if i.val=4 then (if j.val=4 then 1 else 0) else x (6+5*j.val+(if i.val=5 then 4 else i.val))/d
def column (p : Data) (d : ℤ) (j : Fin 5) (t : ℝ) :=
  columnOf d (fun i=>eval t (p i)) j
def columnVelocity (p : Data) (d : ℤ) (j : Fin 5) (t : ℝ) : State :=
  fun i=>if i.val=4 then 0 else eval t (differential (p (6+5*j.val+(if i.val=5 then 4 else i.val))))/d

theorem path_deriv (p : Data) (d : ℤ) (t : ℝ) :
    HasDerivAt (path p d) (velocity p d t) t := by
  apply hasDerivAt_pi.mpr
  exact fun i => (eval_deriv (p i) t).div_const _

theorem column_deriv (p : Data) (d : ℤ) (j : Fin 5) (t : ℝ) :
    HasDerivAt (column p d j) (columnVelocity p d j t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  by_cases h : i.val=4
  · simp only [column,columnOf,columnVelocity,if_pos h]
    exact hasDerivAt_const t _
  · simp only [column,columnOf,columnVelocity,if_neg h]
    exact (eval_deriv _ t).div_const _

@[simp] theorem add_rv (a b : Term) (t : ℝ) : (a+b).realValue t=a.realValue t+b.realValue t := rfl
@[simp] theorem mul_rv (a b : Term) (t : ℝ) : (a*b).realValue t=a.realValue t*b.realValue t := rfl
@[simp] theorem neg_rv (a : Term) (t : ℝ) : (-a).realValue t= -a.realValue t := by
  change ((-1:ℤ):ℝ)*_= -_; push_cast; ring
@[simp] theorem sub_rv (a b : Term) (t : ℝ) : (a-b).realValue t=a.realValue t-b.realValue t := by
  change a.realValue t+((-1:ℤ):ℝ)*b.realValue t=_
  push_cast; ring

/-- The normalized integer polynomial is the actual geometric support
ODE residual, with differentiation in the local parameter z. -/
theorem state_identity (p : Data) {d hn hd : ℤ} (dp : (d:ℝ)≠0) (hp : (hd:ℝ)≠0)
    (t : ℝ) (i : Fin 6) : (defectTerm p d hn hd i).realValue t=
      (16*(hd:ℝ)*d^3)*(velocity p d t i-((hn:ℝ)/hd)*Rotating.field (path p d t) i) := by
  fin_cases i <;> norm_num [defectTerm,form,Term.realValue,velocity,Rotating.field,path,Matrix.cons_val_succ]
    <;> field_simp <;> ring

def slot (i : Fin 6) (j : Fin 5) : Nat :=
  6+5*j.val+(if i.val=5 then 4 else i.val)

/-- All nonconstant rows of every initial-data variation have the actual
Jacobian of the field on the reconstructed state path. -/
theorem column_identity (p : Data) {d hn hd : ℤ} (dp : (d:ℝ)≠0) (hp : (hd:ℝ)≠0)
    (t : ℝ) (j : Fin 5) (i : Fin 6) (var : i.val≠4) :
    (defectTerm p d hn hd (slot i j)).realValue t=(16*(hd:ℝ)*d^3)*
      (columnVelocity p d j t i-((hn:ℝ)/hd)*linear (path p d t) (column p d j t) i) := by
  fin_cases j <;> fin_cases i <;> norm_num [slot,defectTerm,form,Term.realValue,columnVelocity,
    linear,path,column,columnOf,Matrix.cons_val_succ] at * <;> field_simp <;> ring

end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.state_identity
#print axioms SolitonClassification.Rotating.DyadicReset.column_identity
