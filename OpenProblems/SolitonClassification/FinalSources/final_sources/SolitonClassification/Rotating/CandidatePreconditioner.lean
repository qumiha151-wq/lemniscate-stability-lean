module

public import SolitonClassification.Rotating.ParameterMatrixNorm

@[expose] public section

/-! Fixed rational shooting matrices. B comes from the archived decimal
preconditioner; J is a fixed rational comparison matrix, not a certified
actual shooting derivative. Only the finite matrix inequalities below
are asserted. Actual derivative/endpoint comparisons remain obligations. -/
namespace SolitonClassification.Rotating.CandidatePreconditioner
noncomputable section
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

def rawB : ParameterMatrix :=
  ![![(-1354575747550081:ℚ)/200000000000000,(-48287126087566473:ℚ)/100000000000000000,(-4420429757657997:ℚ)/1250000000000000,(-11086982914477437:ℚ)/5000000000000000,(-8134302742349231:ℚ)/500000000000000],
  ![(4616945733935883:ℚ)/250000000000000,(542703482754787:ℚ)/400000000000000,(9608218131394837:ℚ)/1000000000000000,(385828308100901:ℚ)/62500000000000,(2272015471899441:ℚ)/50000000000000],
  ![(1858225252187359:ℚ)/100000000000000,(13398843881947247:ℚ)/10000000000000000,(4840411195692617:ℚ)/500000000000000,(6493740495460611:ℚ)/1000000000000000,(1111564318106791:ℚ)/25000000000000],
  ![(-17105543633940873:ℚ)/50000000000000000,(-3481311539701283:ℚ)/200000000000000000,(-1420431413594063:ℚ)/5000000000000000,(-10167045639481177:ℚ)/100000000000000000,(-6372867700755797:ℚ)/10000000000000000],
  ![(-8616656920378647:ℚ)/2000000000000000,(-15610924825490727:ℚ)/50000000000000000,(-2214798243673483:ℚ)/1000000000000000,(-6910855889989431:ℚ)/5000000000000000,(-2638901362855263:ℚ)/250000000000000]]

def rawJ : ParameterMatrix :=
  ![![(-5608761939320309:ℚ)/100000000000000,(1392094723141033:ℚ)/250000000000000,(-4169705776912349:ℚ)/500000000000000,(14525721441834383:ℚ)/500000000000000,(183833704071091:ℚ)/2500000000000],
  ![(-29533739852741137:ℚ)/10000000000000,(692494942454979:ℚ)/1250000000000,(-131985298993649:ℚ)/250000000000,(7250668519701451:ℚ)/5000000000000,(2312669281306801:ℚ)/500000000000],
  ![(-327778484155387:ℚ)/20000000000000,(2771625130146009:ℚ)/500000000000000,(-3963181014208199:ℚ)/1000000000000000,(481708931474671:ℚ)/2500000000000000,(3241651387920459:ℚ)/100000000000000],
  ![(1536862264800283:ℚ)/10000000000000,(-6729142697769113:ℚ)/250000000000000,(28411090298370247:ℚ)/1000000000000000,(-904104642346169:ℚ)/12500000000000,(-11434842942680413:ℚ)/50000000000000],
  ![(9356349710206749:ℚ)/100000000000000,(-1629769722386873:ℚ)/100000000000000,(100817634039741:ℚ)/6250000000000,(-4531983410367793:ℚ)/100000000000000,(-179717364594651:ℚ)/1250000000000]]

def B : Parameters →L[ℝ] Parameters := parameterMatrixOperator rawB
def J : Parameters →L[ℝ] Parameters := parameterMatrixOperator rawJ

theorem norm_rows_checked : ∀i : Fin 5,∑j : Fin 5,|rawB i j|≤82 := by
  decide +kernel

theorem defect_rows_checked : ∀i : Fin 5,
    ∑j : Fin 5,|parameterMatrixId i j-parameterMatrixMul rawB rawJ i j|≤1/10^10 := by
  decide +kernel

theorem actual_preconditioner_norm : ‖B‖≤82 := by
  exact_mod_cast parameterMatrixOperator_norm_le rawB (by norm_num) norm_rows_checked

theorem actual_preconditioner_defect :
    ‖ContinuousLinearMap.id ℝ Parameters-B.comp J‖≤(1:ℝ)/10^10 := by
  have h:=parameterMatrixOperator_defect_norm rawB rawJ (by norm_num) defect_rows_checked
  norm_num at h ⊢
  exact h

theorem actual_preconditioner_injective : Function.Injective B :=
  preconditioner_injective_of_defect B J (actual_preconditioner_defect.trans_lt (by norm_num))

end
end SolitonClassification.Rotating.CandidatePreconditioner

#print axioms SolitonClassification.Rotating.CandidatePreconditioner.actual_preconditioner_defect
#print axioms SolitonClassification.Rotating.CandidatePreconditioner.actual_preconditioner_injective
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Concrete rational shooting preconditioner audited: {count} declarations; standard axioms only."
