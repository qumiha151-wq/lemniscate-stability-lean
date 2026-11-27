import SolitonClassification.Rotating.ResetLift
import SolitonClassification.Rotating.ResetWholeInverse
import SolitonClassification.Rotating.MatrixColumnNorm
noncomputable section
open Set
namespace SolitonClassification.Rotating.DyadicReset
open CellCheck
set_option backward.isDefEq.respectTransparency false
def step (n : ℤ) : ℝ := (n:ℝ)/Middle.hd
def SignedCheck (n : ℤ) (p : Data) : Prop := ∀i : Fin 31,sufficient (defectTerm p d n Middle.hd i)=true
private theorem divide_signed {a v : ℝ} (pos : 0<(Middle.commonDen:ℝ))
    (ha : a=(Middle.commonDen:ℝ)*v) (bd : |a|≤(Middle.commonDen:ℝ)/10^64) : |v|≤eps := by
  rw [ha,abs_mul,abs_of_pos pos] at bd
  apply le_of_mul_le_mul_left (a:=(Middle.commonDen:ℝ)) _ pos
  simpa only [eps,div_eq_mul_inv,one_mul] using bd

theorem signed_state {n : ℤ} {p : Data} (C : SignedCheck n p) {t : ℝ} (ht : t∈Icc 0 1) :
    ‖velocity p Middle.den t-step n • Rotating.field (path p Middle.den t)‖≤eps := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num [eps])).mpr
  intro i
  rw [Real.norm_eq_abs]
  let ix : Fin 31 := ⟨i.val,by omega⟩
  apply divide_signed (a:=(defectTerm p Middle.den n Middle.hd i).realValue t)
    (by exact_mod_cast (by decide +kernel : 0<Middle.commonDen))
  · change _=(Middle.commonDen:ℝ)*(velocity p Middle.den t i-(step n)*Rotating.field (path p Middle.den t) i)
    rw [state_identity p (by norm_num [Middle.den]) (by norm_num [Middle.hd])]
    unfold Middle.commonDen step
    push_cast; ring
  · exact real_bound _ (C ix) (by rw [abs_of_nonneg ht.1]; exact ht.2)

theorem signed_variation {n : ℤ} {p : Data} (C : SignedCheck n p) {t : ℝ} (ht : t∈Icc 0 1) (j : Fin 5) :
    ‖columnVelocity p Middle.den j t-step n • linear (path p Middle.den t) (column p Middle.den j t)‖≤eps := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num [eps])).mpr
  intro i
  rw [Real.norm_eq_abs]
  by_cases hz : i.val=4
  · have hi : i=(4:Fin 6) := Fin.ext hz
    subst i
    change |(0:ℝ)-(step n)*0|≤eps
    norm_num [eps]
  · have sz : slot i j<31 := by unfold slot; split <;> omega
    let ix : Fin 31 := ⟨slot i j,sz⟩
    apply divide_signed (a:=(defectTerm p Middle.den n Middle.hd (slot i j)).realValue t)
      (by exact_mod_cast (by decide +kernel : 0<Middle.commonDen))
    · change _=(Middle.commonDen:ℝ)*(columnVelocity p Middle.den j t i-(step n)*(linear _ _) i)
      rw [column_identity p (by norm_num [Middle.den]) (by norm_num [Middle.hd]) t j i hz]
      unfold Middle.commonDen step
      push_cast; ring
    · exact real_bound _ (C ix) (by rw [abs_of_nonneg ht.1];exact ht.2)

theorem linear_wide {a : State} (ha : ∀i : Fin 6,i.val<5 → |a i|≤9) (u : State) :
    ‖linear a u‖≤20*‖u‖ := by
  have h0 := ha 0 (by decide)
  have h2 := ha 2 (by decide)
  have h3 := ha 3 (by decide)
  have h4 := ha 4 (by decide)
  have hn := norm_nonneg u
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · change |8*u 1|≤_
    rw [abs_mul]; norm_num
    linarith [coordinate_bound u 1]
  · change |-3*(a 0)^2*u 0/16-u 2/8-a 4*u 3/8-u 4*a 3/8|≤_
    calc
      _ ≤ |-3*(a 0)^2*u 0/16-u 2/8-a 4*u 3/8|+|u 4*a 3/8| := abs_sub _ _
      _ ≤ (|-3*(a 0)^2*u 0/16-u 2/8|+|a 4*u 3/8|)+|u 4*a 3/8| := by
        gcongr; apply abs_sub
      _ ≤ ((|-3*(a 0)^2*u 0/16|+|u 2/8|)+|a 4*u 3/8|)+|u 4*a 3/8| := by
        gcongr; apply abs_sub
      _ = 3*|a 0|^2*|u 0|/16+|u 2|/8+|a 4| * |u 3|/8+|u 4| * |a 3|/8 := by
        simp only [abs_div,abs_mul,abs_pow]; norm_num
      _ ≤ 3*9^2*‖u‖/16+‖u‖/8+9*‖u‖/8+‖u‖*9/8 := by
        gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith
  · change |-a 0*u 3-u 0*a 3|≤_
    calc
      _ ≤ |-a 0*u 3|+|u 0*a 3| := abs_sub _ _
      _ = |a 0| * |u 3|+|u 0| * |a 3| := by simp [abs_mul]
      _ ≤ 9*‖u‖+‖u‖*9 := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by linarith
  · change |a 0*u 2+u 0*a 2|≤_
    calc
      _ ≤ |a 0*u 2|+|u 0*a 2| := abs_add_le _ _
      _ = |a 0| * |u 2|+|u 0| * |a 2| := by simp [abs_mul]
      _ ≤ 9*‖u‖+‖u‖*9 := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by linarith
  · simp [linear]
  · change |u 0|≤_
    linarith [coordinate_bound u 0]

def fullColumn (p : Data) (j : Fin 6) (t : ℝ) : State :=
  if fr : j.val<5 then column p d ⟨j.val,fr⟩ t else coordinateBasis 5
def fullSlope (p : Data) (j : Fin 6) (t : ℝ) : State :=
  if fr : j.val<5 then columnVelocity p d ⟨j.val,fr⟩ t else 0
def matrixPath (p : Data) (t : ℝ) : FlowEnd := columnOperator (fun j=>fullColumn p j t)
def matrixSlope (p : Data) (t : ℝ) : FlowEnd := columnOperator (fun j=>fullSlope p j t)

theorem matrixPath_deriv (p : Data) (t : ℝ) : HasDerivAt (matrixPath p) (matrixSlope p t) t := by
  unfold matrixPath matrixSlope columnOperator
  apply HasDerivAt.fun_sum
  intro j hj
  let L := ContinuousLinearMap.smulRightL ℝ State State (ContinuousLinearMap.proj j)
  change HasDerivAt (fun s=>L (fullColumn p j s)) (L (fullSlope p j t)) t
  apply L.hasFDerivAt.comp_hasDerivAt t
  unfold fullColumn fullSlope
  split
  · apply column_deriv
  · exact hasDerivAt_const t _

theorem matrixPath_residual {n : ℤ} {p : Data} (C : SignedCheck n p) {t : ℝ} (ht : t∈unitCell) :
    ‖matrixSlope p t-(step n • fderiv ℝ field (path p d t))*matrixPath p t‖≤6*eps := by
  apply operator_difference_le_six_column_bound
  intro j
  change ‖matrixSlope p t (coordinateBasis j)-step n • fderiv ℝ field _ (matrixPath p t (coordinateBasis j))‖≤eps
  simp only [matrixSlope,matrixPath,columnOperator_basis,field_fderiv_apply]
  unfold fullSlope fullColumn
  split
  · exact signed_variation C ht _
  · have mat : linear (path p d t) (coordinateBasis 5)=0 := by
      ext i; fin_cases i <;> simp [coordinateBasis,linear]
    simp [mat,eps]

theorem matrixPath_join {p q : Data} (joins : ∀i,(p i).sum=(q i).head?.getD 0) :
    path p d 1=path q d 0 ∧ matrixPath p 1=matrixPath q 0 := by
  obtain ⟨sq,cols⟩ := adjacent_matching joins
  refine ⟨sq,congrArg columnOperator (funext fun j=>?_)⟩
  unfold fullColumn
  split
  · exact cols _
  · rfl

/-- The fields of the full transport certificate are derived from integer
polynomial checks and inequalities on the single rational left endpoint. -/
def polynomialMetric {n : ℤ} {p : Data} (C : SignedCheck n p) (sm : Small p)
    (hs : |step n|≤1/125) (u0 : IsUnit (matrixPath p 0)) (m0 : ‖matrixPath p 0‖≤2900)
    (i0 : ‖Ring.inverse (matrixPath p 0)‖≤3500) : MetricCell (step n) :=
  let inn := fun t (ht : t∈unitCell) => (lift_inner sm ht).1
  let a := fun t=>step n • fderiv ℝ field (path p d t)
  let bound : ∀t∈unitCell,‖a t‖≤4/25 := by
    intro t ht
    have hf : ‖fderiv ℝ field (path p d t)‖≤20 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro u; rw [field_fderiv_apply]
      exact linear_wide (inn t ht) u
    change ‖step n • fderiv ℝ field (path p d t)‖≤_
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hs hf (norm_nonneg _) (by norm_num)).trans (by norm_num)
  let inv := inverse_on_cell (M:=matrixPath p) (dM:=matrixSlope p) (A:=a)
    (fun t _=>(matrixPath_deriv p t).hasDerivWithinAt) bound (fun _ ht=>matrixPath_residual C ht) u0 m0 i0
  {Q := path p d
   dQ := velocity p d
   M := matrixPath p
   dM := matrixSlope p
   state_deriv := path_deriv p d
   variation_deriv := matrixPath_deriv p
   derivative_cont := (liftVelocity_cont p).fst
   inner := inn
   state_res := fun _ ht=>signed_state C ht
   var_res := fun _ ht=>matrixPath_residual C ht
   unit := fun t ht=>(inv t ht).1
   matrix_norm := fun t ht=>(inv t ht).2.1
   inverse_norm := fun t ht=>(inv t ht).2.2}

end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.polynomialMetric
