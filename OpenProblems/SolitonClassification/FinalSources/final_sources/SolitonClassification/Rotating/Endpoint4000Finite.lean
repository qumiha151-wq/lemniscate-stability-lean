module

public import SolitonClassification.Rotating.Endpoint4000Data
public import SolitonClassification.Rotating.CertifiedPi

@[expose] public section

/-! Finite endpoint arithmetic only. The arrays are proposed rational endpoints.
No actual flow, derivative, tube, or full-grid enclosure is asserted here.
The matrices below use row/column order, whereas the input full state matrices
use column/row order. The negative-time length derivative has a PLUS sign. -/
namespace SolitonClassification.Rotating.Endpoint4000Finite
open Finset Endpoint4000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

abbrev ParameterVector := Fin 5 → ℝ
abbrev RationalMatrix := Fin 5 → Fin 5 → ℚ

def rawB : RationalMatrix := ![![(-1354575747550081:ℚ)/200000000000000,(-48287126087566473:ℚ)/100000000000000000,(-4420429757657997:ℚ)/1250000000000000,(-11086982914477437:ℚ)/5000000000000000,(-8134302742349231:ℚ)/500000000000000],
  ![(4616945733935883:ℚ)/250000000000000,(542703482754787:ℚ)/400000000000000,(9608218131394837:ℚ)/1000000000000000,(385828308100901:ℚ)/62500000000000,(2272015471899441:ℚ)/50000000000000],
  ![(1858225252187359:ℚ)/100000000000000,(13398843881947247:ℚ)/10000000000000000,(4840411195692617:ℚ)/500000000000000,(6493740495460611:ℚ)/1000000000000000,(1111564318106791:ℚ)/25000000000000],
  ![(-17105543633940873:ℚ)/50000000000000000,(-3481311539701283:ℚ)/200000000000000000,(-1420431413594063:ℚ)/5000000000000000,(-10167045639481177:ℚ)/100000000000000000,(-6372867700755797:ℚ)/10000000000000000],
  ![(-8616656920378647:ℚ)/2000000000000000,(-15610924825490727:ℚ)/50000000000000000,(-2214798243673483:ℚ)/1000000000000000,(-6910855889989431:ℚ)/5000000000000000,(-2638901362855263:ℚ)/250000000000000]]

def rawJ : RationalMatrix := ![![(-5608761939320309:ℚ)/100000000000000,(1392094723141033:ℚ)/250000000000000,(-4169705776912349:ℚ)/500000000000000,(14525721441834383:ℚ)/500000000000000,(183833704071091:ℚ)/2500000000000],
  ![(-29533739852741137:ℚ)/10000000000000,(692494942454979:ℚ)/1250000000000,(-131985298993649:ℚ)/250000000000,(7250668519701451:ℚ)/5000000000000,(2312669281306801:ℚ)/500000000000],
  ![(-327778484155387:ℚ)/20000000000000,(2771625130146009:ℚ)/500000000000000,(-3963181014208199:ℚ)/1000000000000000,(481708931474671:ℚ)/2500000000000000,(3241651387920459:ℚ)/100000000000000],
  ![(1536862264800283:ℚ)/10000000000000,(-6729142697769113:ℚ)/250000000000000,(28411090298370247:ℚ)/1000000000000000,(-904104642346169:ℚ)/12500000000000,(-11434842942680413:ℚ)/50000000000000],
  ![(9356349710206749:ℚ)/100000000000000,(-1629769722386873:ℚ)/100000000000000,(100817634039741:ℚ)/6250000000000,(-4531983410367793:ℚ)/100000000000000,(-179717364594651:ℚ)/1250000000000]]

def phase : Fin 2 → ℚ :=
  ![(-2997696555817197 : ℚ)/50000000000000000,
    (-9982011451324311 : ℚ)/10000000000000000]

def rawField (x : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![8*x 1,-(x 0)^3/16-x 2/8-x 4*x 3/8,-x 0*x 3,1+x 0*x 2,0,x 0]

def projected (x : Fin 6 → ℚ) : Fin 5 → ℚ := ![x 0,8*x 1,x 2,x 3,x 5]

def rawValue : Fin 5 → ℚ :=
  projected (plusRaw-minusRaw)+![0,0,0,0,112*CertifiedPi.center/57]

noncomputable def value : ParameterVector := fun i => (rawValue i:ℝ)

noncomputable def endpointValue : ParameterVector :=
  ![plusState 0-minusState 0,8*(plusState 1-minusState 1),
    plusState 2-minusState 2,plusState 3-minusState 3,
    plusState 5-minusState 5+112*Real.pi/57]

def deltaColumn (j i : Fin 6) : ℚ :=
  (plusMatrix j i:ℚ)/mesh-(minusMatrix j i:ℚ)/mesh

def endpointColumns : Fin 5 → Fin 5 → ℚ :=
  ![projected (deltaColumn 0),projected (deltaColumn 2),
    projected (rawField plusRaw+rawField minusRaw),
    projected (fun i => phase 0/8*deltaColumn 1 i+phase 1*deltaColumn 3 i),
    projected (deltaColumn 4)]

def endpointJacobian : RationalMatrix := fun i j => endpointColumns j i

/-- Exact finite row-sum comparison; not an actual-flow derivative hypothesis. -/
theorem jacobian_rows_checked : ∀i : Fin 5,
    ∑j : Fin 5,|rawJ i j-endpointJacobian i j|≤6/10^6 := by
  decide +kernel

theorem preconditioned_rows_checked : ∀i : Fin 5,
    |∑j : Fin 5,rawB i j*rawValue j|≤1/10^30 := by
  decide +kernel

theorem state_rows_checked : ∀i : Fin 5,
    |plusRaw i.castSucc|≤(![814/100,4125/1000,731/100,731/100,1/100]:Fin 5→ℚ) i ∧
    |minusRaw i.castSucc|≤(![814/100,4125/1000,731/100,731/100,1/100]:Fin 5→ℚ) i := by
  decide +kernel

theorem value_difference : value-endpointValue=
    ![0,0,0,0,(112/57:ℝ)*((CertifiedPi.center:ℝ)-Real.pi)] := by
  ext i
  fin_cases i <;>
    simp [value,rawValue,projected,endpointValue,←plusState_cast,←minusState_cast]
  all_goals ring

theorem value_error : ‖value-endpointValue‖≤(1:ℝ)/10^30 := by
  rw [value_difference,pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · change ‖(0:ℝ)‖≤_; norm_num
  · change ‖(0:ℝ)‖≤_; norm_num
  · change ‖(0:ℝ)‖≤_; norm_num
  · change ‖(0:ℝ)‖≤_; norm_num
  · change |(112/57:ℝ)*((CertifiedPi.center:ℝ)-Real.pi)|≤_
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<112/57),abs_sub_comm]
    have h:=CertifiedPi.abs_pi_sub_center_lt
    have hnum : (112/57:ℝ)*(CertifiedPi.radius:ℝ)≤1/10^30 := by
      norm_num [CertifiedPi.radius]
    nlinarith

noncomputable def matrixOperator (M : RationalMatrix) : ParameterVector →L[ℝ] ParameterVector :=
  ContinuousLinearMap.pi fun i => ∑j : Fin 5,(M i j:ℝ) • ContinuousLinearMap.proj j

theorem matrixOperator_apply (M : RationalMatrix) (x : ParameterVector) (i : Fin 5) :
    matrixOperator M x i=∑j : Fin 5,(M i j:ℝ)*x j := by
  simp [matrixOperator]

theorem matrixOperator_sub (M N : RationalMatrix) :
    matrixOperator (M-N)=matrixOperator M-matrixOperator N := by
  ext x i
  simp [matrixOperator_apply,Finset.sum_sub_distrib,sub_mul]

theorem matrixOperator_norm_le (M : RationalMatrix) {C : ℚ} (hC : 0≤C)
    (hrow : ∀i : Fin 5,∑j : Fin 5,|M i j|≤C) : ‖matrixOperator M‖≤(C:ℝ) := by
  have hCr : (0:ℝ)≤(C:ℝ) := by exact_mod_cast hC
  apply ContinuousLinearMap.opNorm_le_bound _ hCr
  intro x
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hCr (norm_nonneg x))]
  intro i
  have hrowr : (∑j : Fin 5,|(M i j:ℝ)|)≤(C:ℝ) := by exact_mod_cast hrow i
  rw [Real.norm_eq_abs,matrixOperator_apply]
  calc
    _ ≤ ∑j : Fin 5,|(M i j:ℝ)*x j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑j : Fin 5,|(M i j:ℝ)| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
    _ = (∑j : Fin 5,|(M i j:ℝ)|)*‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (C:ℝ)*‖x‖ := mul_le_mul_of_nonneg_right hrowr (norm_nonneg x)

theorem jacobian_error : ‖matrixOperator rawJ-matrixOperator endpointJacobian‖≤(6:ℝ)/10^6 := by
  rw [←matrixOperator_sub]
  have h:=matrixOperator_norm_le (rawJ-endpointJacobian) (by norm_num)
    jacobian_rows_checked
  norm_num at h ⊢
  exact h

theorem preconditioned_value : ‖matrixOperator rawB value‖≤(1:ℝ)/10^30 := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs,matrixOperator_apply]
  change |∑j : Fin 5,(rawB i j:ℝ)*(rawValue j:ℝ)|≤_
  have h:=preconditioned_rows_checked i
  have hr := (Rat.cast_le (K:=ℝ)).mpr h
  simpa only [Rat.cast_abs,Rat.cast_sum,Rat.cast_mul,Rat.cast_div,
    Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] using hr

end SolitonClassification.Rotating.Endpoint4000Finite

#print axioms SolitonClassification.Rotating.Endpoint4000Finite.value_error
#print axioms SolitonClassification.Rotating.Endpoint4000Finite.jacobian_error
#print axioms SolitonClassification.Rotating.Endpoint4000Finite.preconditioned_value
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating.Endpoint4000Finite).isPrefixOf (privateToUserName name) then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Endpoint finite audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Endpoint finite audit: {count} declarations, standard three axioms only."
