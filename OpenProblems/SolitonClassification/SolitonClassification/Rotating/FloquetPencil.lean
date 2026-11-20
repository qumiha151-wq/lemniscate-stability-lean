import SolitonClassification.Rotating.RationalBall
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Instances.Real.Lemmas

namespace SolitonClassification.Rotating.FloquetPencil
open Matrix Set
abbrev Four (R : Type*) := Matrix (Fin 4) (Fin 4) R

/-- Laplace expansion with explicit operations, usable for rational balls. -/
def detFour {R : Type*} (add mul : R → R → R) (neg : R → R) (A : Four R) : R :=
  let sub x y := add x (neg y)
  let minor (i j k : Fin 4) := add
    (sub (mul (A 1 i) (sub (mul (A 2 j) (A 3 k)) (mul (A 2 k) (A 3 j))))
         (mul (A 1 j) (sub (mul (A 2 i) (A 3 k)) (mul (A 2 k) (A 3 i)))))
    (mul (A 1 k) (sub (mul (A 2 i) (A 3 j)) (mul (A 2 j) (A 3 i))))
  add (sub (mul (A 0 0) (minor 1 2 3)) (mul (A 0 1) (minor 0 2 3)))
      (sub (mul (A 0 2) (minor 0 1 3)) (mul (A 0 3) (minor 0 1 2)))

theorem detFour_real (A : Four ℝ) : detFour (·+·) (·*·) Neg.neg A=A.det := by
  rw [Matrix.det_succ_row_zero]
  simp [detFour,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove]
  ring

theorem detFour_contains {B : Four RationalBall} {A : Four ℝ}
    (h : ∀ i j, (B i j).Contains (A i j)) :
    (detFour RationalBall.add RationalBall.mul RationalBall.neg B).Contains A.det := by
  rw [← detFour_real]
  unfold detFour
  repeat' first | apply RationalBall.contains_add | apply RationalBall.contains_neg
                | apply RationalBall.contains_mul | apply h

-- Canonical centres, rounded to nearest 10^(-12). The radius absorbs both
-- that rounding and the certified endpoint uncertainty for the true orbit.
def plus : Four ℚ := ![![(-10014986965827:ℚ)/10^12,(680810157396:ℚ)/10^12,(7022494622523:ℚ)/10^12,(1103375557742:ℚ)/10^12],
  ![(-79340629473163:ℚ)/10^12,(1740638931575:ℚ)/10^12,(77052871848596:ℚ)/10^12,(1022234997912:ℚ)/10^12],
  ![(-8109791078734:ℚ)/10^12,(1527233015461:ℚ)/10^12,(4841174202001:ℚ)/10^12,(3065428295519:ℚ)/10^12],
  ![(34798932531366:ℚ)/10^12,(-1566151775647:ℚ)/10^12,(-30287647110029:ℚ)/10^12,(-2165918269322:ℚ)/10^12]]

def minus : Four ℚ := ![![(46072632424977:ℚ)/10^12,(14413833960460:ℚ)/10^12,(1454115730376:ℚ)/10^12,(30104067880325:ℚ)/10^12],
  ![(289831118688511:ℚ)/10^12,(87421426737300:ℚ)/10^12,(7803377603931:ℚ)/10^12,(181972338449380:ℚ)/10^12],
  ![(8279133128439:ℚ)/10^12,(1617256411162:ℚ)/10^12,(-702076057953:ℚ)/10^12,(3257783228724:ℚ)/10^12],
  ![(-118887293949737:ℚ)/10^12,(-35754306897362:ℚ)/10^12,(-3371076319263:ℚ)/10^12,(-74367956353925:ℚ)/10^12]]

def ball (x : ℚ) : RationalBall := ⟨x,2/10^12⟩
def pencilBall (x : ℚ) (i j : Fin 4) := RationalBall.add (ball (plus i j))
    (RationalBall.neg (RationalBall.mul (RationalBall.point x) (ball (minus i j))))
def bound (x : ℚ) := detFour RationalBall.add RationalBall.mul RationalBall.neg (pencilBall x)
noncomputable def D (A B : Four ℝ) (x : ℝ) := (A - x • B).det

theorem bounds_real {A B : Four ℝ}
    (hA : ∀ i j, (ball (plus i j)).Contains (A i j))
    (hB : ∀ i j, (ball (minus i j)).Contains (B i j)) (x : ℚ) :
    (bound x).Contains (D A B x) := by
  apply detFour_contains
  intro i j
  simpa [pencilBall,sub_eq_add_neg] using RationalBall.contains_add (hA i j)
    (RationalBall.contains_neg (RationalBall.contains_mul (RationalBall.contains_point x) (hB i j)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem finite_bounds :
    (bound (-3)).radius < (bound (-3)).center ∧
    (bound (-2)).center < -(bound (-2)).radius ∧
    (bound (-1/100)).center < -(bound (-1/100)).radius ∧
    (bound (-1/1000)).radius < (bound (-1/1000)).center ∧
    (bound 100).center < -(bound 100).radius ∧
    (bound 110).radius < (bound 110).center := by decide +kernel

theorem signed_pencil {A B : Four ℝ}
    (hA : ∀ i j, (ball (plus i j)).Contains (A i j))
    (hB : ∀ i j, (ball (minus i j)).Contains (B i j)) :
    0 < D A B (-3) ∧ D A B (-2)<0 ∧ D A B (-1/100)<0 ∧
    0<D A B (-1/1000) ∧ D A B 100<0 ∧ 0<D A B 110 := by
  have pos (x : ℚ) (hx : (bound x).radius < (bound x).center) : 0<D A B x := by
    have hr := (abs_le.mp (bounds_real hA hB x)).1
    have := Rat.cast_lt (K:=ℝ) |>.mpr hx
    linarith
  have neg (x : ℚ) (hx : (bound x).center < -(bound x).radius) : D A B x<0 := by
    have hr := (abs_le.mp (bounds_real hA hB x)).2
    have hcast : ((bound x).center:ℝ) < -((bound x).radius:ℝ) := by exact_mod_cast hx
    linarith
  obtain ⟨a,b,c,d,e,f⟩ := finite_bounds
  exact ⟨by simpa using pos _ a,by simpa using neg _ b,by exact_mod_cast neg _ c,
    by exact_mod_cast pos _ d,by simpa using neg _ e,by simpa using pos _ f⟩

theorem three_real_multipliers {A B : Four ℝ}
    (hA : ∀ i j, (ball (plus i j)).Contains (A i j))
    (hB : ∀ i j, (ball (minus i j)).Contains (B i j)) :
    (∃ x ∈ Ioo (-3:ℝ) (-2), D A B x=0) ∧
    (∃ x ∈ Ioo (-1/100:ℝ) (-1/1000), D A B x=0) ∧
    (∃ x ∈ Ioo (100:ℝ) 110, D A B x=0) := by
  obtain ⟨a,b,c,d,e,f⟩ := signed_pencil hA hB
  have hc : Continuous (D A B) := by
    unfold D
    fun_prop
  exact ⟨intermediate_value_Ioo' (by norm_num) hc.continuousOn ⟨b,a⟩,
    intermediate_value_Ioo (by norm_num) hc.continuousOn ⟨c,d⟩,
    intermediate_value_Ioo (by norm_num) hc.continuousOn ⟨e,f⟩⟩

end SolitonClassification.Rotating.FloquetPencil

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating.FloquetPencil).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
          throwError "Unexpected axiom {a} in {n}"
      count := count+1
  logInfo m!"FLOQUET_PENCIL_AUDIT {count} declarations with standard axioms"
