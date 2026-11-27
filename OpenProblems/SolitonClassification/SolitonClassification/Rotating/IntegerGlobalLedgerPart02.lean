import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_0_0_0_2_0_0 : Tree := (.square Tree.short (.first (.axis 32 37 false) (.second Tree.short (.axis 34 38 false))) Tree.short)
theorem fullLedger_0_0_0_0_2_0_0_valid : check fullLedger_0_0_0_0_2_0_0 (-3751) (-3689) (-3751) (-3689)=true := by
  decide +kernel

def fullLedger_0_0_0_0_2_0_1 : Tree := (.second (.first (.axis 33 41 false) (.first (.axis 36 41 true) (.second Tree.short (.axis 38 42 true)))) (.axis 35 45 true))
theorem fullLedger_0_0_0_0_2_0_1_valid : check fullLedger_0_0_0_0_2_0_1 (-3751) (-3689) (-3689) (-3626)=true := by
  decide +kernel

def fullLedger_0_0_0_0_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 40 44 true) Tree.short) (.axis 41 46 true)) Tree.short)
theorem fullLedger_0_0_0_0_2_0_2_valid : check fullLedger_0_0_0_0_2_0_2 (-3689) (-3626) (-3689) (-3626)=true := by
  decide +kernel

def fullLedger_0_0_0_0_2_0 : Tree := (.square fullLedger_0_0_0_0_2_0_0 fullLedger_0_0_0_0_2_0_1 fullLedger_0_0_0_0_2_0_2)
theorem fullLedger_0_0_0_0_2_0_valid : check fullLedger_0_0_0_0_2_0 (-3751) (-3626) (-3751) (-3626)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_2_0_0_valid,fullLedger_0_0_0_0_2_0_1_valid⟩,fullLedger_0_0_0_0_2_0_2_valid⟩⟩

def fullLedger_0_0_0_0_2_1_0 : Tree := (.second (.axis 35 51 false) (.axis 35 59 false))
theorem fullLedger_0_0_0_0_2_1_0_valid : check fullLedger_0_0_0_0_2_1_0 (-3751) (-3689) (-3626) (-3501)=true := by
  decide +kernel

def fullLedger_0_0_0_0_2_1_1 : Tree := (.second (.first (.second (.axis 41 49 false) (.axis 41 53 false)) (.second (.first (.axis 44 49 false) (.second Tree.short (.axis 46 50 false))) (.axis 45 53 true))) (.first (.axis 41 59 false) (.axis 45 59 false)))
theorem fullLedger_0_0_0_0_2_1_1_valid : check fullLedger_0_0_0_0_2_1_1 (-3689) (-3626) (-3626) (-3501)=true := by
  decide +kernel

def fullLedger_0_0_0_0_2_1 : Tree := (.first fullLedger_0_0_0_0_2_1_0 fullLedger_0_0_0_0_2_1_1)
theorem fullLedger_0_0_0_0_2_1_valid : check fullLedger_0_0_0_0_2_1 (-3751) (-3626) (-3626) (-3501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_2_1_0_valid,fullLedger_0_0_0_0_2_1_1_valid⟩

def fullLedger_0_0_0_0_2_2_0 : Tree := (.square Tree.short (.first (.axis 48 53 true) (.second Tree.short (.axis 50 54 true))) Tree.short)
theorem fullLedger_0_0_0_0_2_2_0_valid : check fullLedger_0_0_0_0_2_2_0 (-3626) (-3564) (-3626) (-3564)=true := by
  decide +kernel

def fullLedger_0_0_0_0_2_2_1 : Tree := (.second (.first (.axis 49 57 true) (.first (.axis 52 57 true) (.second Tree.short (.axis 54 58 false)))) (.first (.axis 49 61 false) (.axis 53 61 false)))
theorem fullLedger_0_0_0_0_2_2_1_valid : check fullLedger_0_0_0_0_2_2_1 (-3626) (-3564) (-3564) (-3501)=true := by
  decide +kernel

def fullLedger_0_0_0_0_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 56 60 false) Tree.short) (.axis 57 62 false)) Tree.short)
theorem fullLedger_0_0_0_0_2_2_2_valid : check fullLedger_0_0_0_0_2_2_2 (-3564) (-3501) (-3564) (-3501)=true := by
  decide +kernel

def fullLedger_0_0_0_0_2_2 : Tree := (.square fullLedger_0_0_0_0_2_2_0 fullLedger_0_0_0_0_2_2_1 fullLedger_0_0_0_0_2_2_2)
theorem fullLedger_0_0_0_0_2_2_valid : check fullLedger_0_0_0_0_2_2 (-3626) (-3501) (-3626) (-3501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_2_2_0_valid,fullLedger_0_0_0_0_2_2_1_valid⟩,fullLedger_0_0_0_0_2_2_2_valid⟩⟩

def fullLedger_0_0_0_0_2 : Tree := (.square fullLedger_0_0_0_0_2_0 fullLedger_0_0_0_0_2_1 fullLedger_0_0_0_0_2_2)
theorem fullLedger_0_0_0_0_2_valid : check fullLedger_0_0_0_0_2 (-3751) (-3501) (-3751) (-3501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_2_0_valid,fullLedger_0_0_0_0_2_1_valid⟩,fullLedger_0_0_0_0_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
