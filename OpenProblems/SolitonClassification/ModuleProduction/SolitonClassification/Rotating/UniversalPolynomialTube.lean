module

public import SolitonClassification.Rotating.TrueLocalStateTail

@[expose] public section

/-! A coarse scalar excursion sharpens to coordinate-wise tube bounds.
Only the finite polynomial and its derivative are used; no real-flow tube
or solution-error premise enters this argument. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Polynomial
set_option Elab.async false
set_option maxHeartbeats 1000000

def expandedTube : Set State := {x | |x 0|≤1082/125 ∧ |x 1|≤4641/1000 ∧
  |x 2|≤3913/500 ∧ |x 3|≤3913/500 ∧ |x 4|≤263/500}

def expandedCoordinateSpeed : Fin 6 → ℝ := ![38,43,69,69,0,9]

theorem expandedTube_of_excursion {a x : State} (ha : a∈innerTube)
    (h : ‖x-a‖≤129/250) : x∈expandedTube := by
  have hb (i : Fin 6) : |x i|≤|a i|+129/250 := by
    have hi : |x i-a i|≤129/250 := (coordinate_bound (x-a) i).trans h
    have he:=abs_add_le (x i-a i) (a i)
    rw [sub_add_cancel] at he
    linarith
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  have hb0:=hb 0;have hb1:=hb 1;have hb2:=hb 2;have hb3:=hb 3;have hb4:=hb 4
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem expanded_field_coordinate_bound {x : State} (hx : x∈expandedTube) (i : Fin 6) :
    |field x i|≤expandedCoordinateSpeed i := by
  rcases hx with ⟨h0,h1,h2,h3,h4⟩
  fin_cases i
  · change |8*x 1|≤38
    rw [abs_mul];norm_num;linarith
  · change |-(x 0)^3/16-x 2/8-x 4*x 3/8|≤43
    calc
      _ ≤ |-(x 0)^3/16-x 2/8|+|x 4*x 3/8| := abs_sub _ _
      _ ≤ (|-(x 0)^3/16|+|x 2/8|)+|x 4*x 3/8| := by gcongr;apply abs_sub
      _ = |x 0|^3/16+|x 2|/8+|x 4| * |x 3|/8 := by simp [abs_div,abs_mul,abs_pow]
      _ ≤ (1082/125)^3/16+(3913/500)/8+(263/500)*(3913/500)/8 := by gcongr
      _ ≤ 43 := by norm_num
  · change |-x 0*x 3|≤69
    rw [abs_mul,abs_neg]
    calc
      _ ≤ (1082/125:ℝ)*(3913/500) := by gcongr
      _ ≤ 69 := by norm_num
  · change |1+x 0*x 2|≤69
    calc
      _ ≤ |(1:ℝ)|+|x 0*x 2| := abs_add_le _ _
      _ = 1+|x 0| * |x 2| := by simp [abs_mul]
      _ ≤ 1+(1082/125)*(3913/500) := by gcongr
      _ ≤ 69 := by norm_num
  · simp [field,expandedCoordinateSpeed]
  · change |x 0|≤9
    linarith

theorem polynomial_coordinate_displacement_of_coarse (P : StatePolynomial) {a : State}
    (ha : a∈innerTube) (hinit : polynomialPath P 0=a) {H : ℝ} (hH : 0≤H)
    (hexc : ∀t,|t|≤H → ‖polynomialPath P t-a‖≤129/250)
    (hres : ∀t,|t|≤H → ‖polynomialVelocity P t-field (polynomialPath P t)‖≤1)
    {t : ℝ} (ht : |t|≤H) (i : Fin 6) :
    |polynomialPath P t i-a i|≤(expandedCoordinateSpeed i+1)*|t| := by
  have hb (s : ℝ) (hs : s∈Icc (-H) H) : ‖(derivative (P i)).eval s‖≤expandedCoordinateSpeed i+1 := by
    have hs' : |s|≤H := abs_le.mpr hs
    have hfield:=expanded_field_coordinate_bound (expandedTube_of_excursion ha (hexc s hs')) i
    have hr : |polynomialVelocity P s i-field (polynomialPath P s) i|≤1 :=
      (coordinate_bound (polynomialVelocity P s-field (polynomialPath P s)) i).trans (hres s hs')
    have he:=abs_add_le (polynomialVelocity P s i-field (polynomialPath P s) i)
      (field (polynomialPath P s) i)
    rw [sub_add_cancel] at he
    change |polynomialVelocity P s i|≤_
    linarith
  have hm := (convex_Icc (-H) H).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _=>(P i).hasDerivAt s |>.hasDerivWithinAt) hb
    (x:=0) (y:=t) (by exact ⟨by linarith,hH⟩) (abs_le.mp ht)
  have hz : (P i).eval 0=a i := congrFun hinit i
  rw [hz] at hm
  simpa only [Real.norm_eq_abs,sub_zero,polynomialPath] using hm

theorem polynomial_tube_of_coarse_excursion (P : StatePolynomial) {a : State}
    (ha : a∈innerTube) (hinit : polynomialPath P 0=a) {H : ℝ} (hH : 0≤H) (hcap : H≤1/125)
    (hexc : ∀t,|t|≤H → ‖polynomialPath P t-a‖≤129/250)
    (hres : ∀t,|t|≤H → ‖polynomialVelocity P t-field (polynomialPath P t)‖≤1)
    {t : ℝ} (ht : |t|≤H) : polynomialPath P t∈outerTube := by
  have habs : |t|≤1/125 := ht.trans hcap
  have hb (i : Fin 6) : |polynomialPath P t i|≤|a i|+(expandedCoordinateSpeed i+1)*|t| := by
    have hd:=polynomial_coordinate_displacement_of_coarse P ha hinit hH hexc hres ht i
    have he:=abs_add_le (polynomialPath P t i-a i) (a i)
    rw [sub_add_cancel] at he
    linarith
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  have hb0:=hb 0;have hb1:=hb 1;have hb2:=hb 2;have hb3:=hb 3;have hb4:=hb 4
  norm_num [expandedCoordinateSpeed] at hb0 hb1 hb2 hb3 hb4
  change |polynomialPath P t 2|≤|a 2|+(69+1)*|t| at hb2
  change |polynomialPath P t 3|≤|a 3|+(69+1)*|t| at hb3
  change |polynomialPath P t 4|≤|a 4|+(0+1)*|t| at hb4
  norm_num at hb2 hb3 hb4
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem taylorPolynomial_tube_of_coarse_excursion {a : State} (ha : a∈innerTube) (N : ℕ)
    {H : ℝ} (hH : 0≤H) (hcap : H≤1/125)
    (hexc : ∀t,|t|≤H → ‖polynomialPath (taylorPolynomial a N) t-a‖≤129/250)
    (hres : ∀t,|t|≤H → ‖polynomialPath (taylorResidual a N) t‖≤1)
    {t : ℝ} (ht : |t|≤H) : polynomialPath (taylorPolynomial a N) t∈outerTube :=
  polynomial_tube_of_coarse_excursion _ ha (polynomialPath_taylor_zero a N) hH hcap hexc
    (fun s hs=>by simpa only [polynomial_residual_actual] using hres s hs) ht

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.taylorPolynomial_tube_of_coarse_excursion
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Universal polynomial tube audit passed for {count} declarations; standard axioms only."

end
