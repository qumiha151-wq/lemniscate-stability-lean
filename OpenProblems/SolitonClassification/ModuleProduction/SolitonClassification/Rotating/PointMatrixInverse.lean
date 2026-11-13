module

public import SolitonClassification.Rotating.ReferenceInversePerturbation

@[expose] public section

/-! A point matrix need not be close to identity. A proposed inverse is
validated through actual two-sided operator defects, and Neumann series
then identify and bound the genuine Ring.inverse. This is only a generic
bridge; no long-grid numerical inverse is asserted in this module. -/
namespace SolitonClassification.Rotating
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem flowEnd_unit_of_two_product_units (B C : FlowEnd)
    (hl : IsUnit (C*B)) (hr : IsUnit (B*C)) :
    IsUnit B ∧ Ring.inverse B=Ring.inverse (C*B)*C := by
  let L : FlowEnd := Ring.inverse (C*B)*C
  let R : FlowEnd := C*Ring.inverse (B*C)
  have hLB : L*B=1 := by
    dsimp [L]
    rw [mul_assoc]
    exact Ring.inverse_mul_cancel _ hl
  have hBR : B*R=1 := by
    dsimp [R]
    rw [←mul_assoc]
    exact Ring.mul_inverse_cancel _ hr
  have hLR : L=R := by
    calc
      L=L*1 := (mul_one _).symm
      _ = L*(B*R) := by rw [hBR]
      _ = (L*B)*R := (mul_assoc _ _ _).symm
      _ = R := by rw [hLB,one_mul]
  have hBL : B*L=1 := by rw [hLR,hBR]
  let u : Units FlowEnd := ⟨B,L,hBL,hLB⟩
  have hu : IsUnit B := ⟨u,rfl⟩
  refine ⟨hu,?_⟩
  change Ring.inverse B=L
  calc
    Ring.inverse B=(L*B)*Ring.inverse B := by rw [hLB,one_mul]
    _ = L*(B*Ring.inverse B) := mul_assoc _ _ _
    _ = L := by rw [Ring.mul_inverse_cancel _ hu,mul_one]

theorem flowEnd_inverse_of_two_defects (B C : FlowEnd) {q κ : ℝ}
    (hq : q<1) (_hκ : 0≤κ) (hC : ‖C‖≤κ)
    (hl : ‖C*B-1‖≤q) (hr : ‖B*C-1‖≤q) :
    IsUnit B ∧ ‖Ring.inverse B‖≤(1/(1-q))*κ := by
  have hleft:=flowEnd_inverse_bound_of_norm_sub_one_le (C*B) hl hq
  have hright:=flowEnd_inverse_bound_of_norm_sub_one_le (B*C) hr hq
  have hu:=flowEnd_unit_of_two_product_units B C hleft.1 hright.1
  refine ⟨hu.1,?_⟩
  rw [hu.2]
  exact (norm_mul_le _ _).trans
    (mul_le_mul hleft.2 hC (norm_nonneg C) (by positivity))

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.flowEnd_inverse_of_two_defects
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Two-sided point-matrix inverse certificate bridge audited."

end
