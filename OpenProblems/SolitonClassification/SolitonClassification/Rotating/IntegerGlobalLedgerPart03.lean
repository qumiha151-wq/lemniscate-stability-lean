import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_0_0_1_0 : Tree := (.second (.first (.axis 7 79 false) (.axis 23 79 false)) (.axis 15 111 false))
theorem fullLedger_0_0_0_1_0_valid : check fullLedger_0_0_0_1_0 (-4001) (-3751) (-3501) (-3001)=true := by
  decide +kernel

def fullLedger_0_0_0_1_1_0_0 : Tree := (.second (.first (.axis 35 71 false) (.axis 43 71 false)) (.axis 39 87 false))
theorem fullLedger_0_0_0_1_1_0_0_valid : check fullLedger_0_0_0_1_1_0_0 (-3751) (-3626) (-3501) (-3251)=true := by
  decide +kernel

def fullLedger_0_0_0_1_1_0_1_0_0 : Tree := (.second (.first (.axis 49 67 false) (.axis 53 67 false)) (.axis 51 75 false))
theorem fullLedger_0_0_0_1_1_0_1_0_0_valid : check fullLedger_0_0_0_1_1_0_1_0_0 (-3626) (-3564) (-3501) (-3376)=true := by
  decide +kernel

def fullLedger_0_0_0_1_1_0_1_0_1 : Tree := (.second (.first (.axis 57 67 true) (.second (.first (.axis 60 65 true) (.second Tree.short (.axis 62 66 true))) (.axis 61 69 true))) (.first (.axis 57 75 false) (.second (.axis 61 73 false) (.axis 61 77 false))))
theorem fullLedger_0_0_0_1_1_0_1_0_1_valid : check fullLedger_0_0_0_1_1_0_1_0_1 (-3564) (-3501) (-3501) (-3376)=true := by
  decide +kernel

def fullLedger_0_0_0_1_1_0_1_0 : Tree := (.first fullLedger_0_0_0_1_1_0_1_0_0 fullLedger_0_0_0_1_1_0_1_0_1)
theorem fullLedger_0_0_0_1_1_0_1_0_valid : check fullLedger_0_0_0_1_1_0_1_0 (-3626) (-3501) (-3501) (-3376)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_1_1_0_1_0_0_valid,fullLedger_0_0_0_1_1_0_1_0_1_valid⟩

def fullLedger_0_0_0_1_1_0_1_1 : Tree := (.first (.axis 51 87 false) (.second (.axis 59 83 false) (.axis 59 91 false)))
theorem fullLedger_0_0_0_1_1_0_1_1_valid : check fullLedger_0_0_0_1_1_0_1_1 (-3626) (-3501) (-3376) (-3251)=true := by
  decide +kernel

def fullLedger_0_0_0_1_1_0_1 : Tree := (.second fullLedger_0_0_0_1_1_0_1_0 fullLedger_0_0_0_1_1_0_1_1)
theorem fullLedger_0_0_0_1_1_0_1_valid : check fullLedger_0_0_0_1_1_0_1 (-3626) (-3501) (-3501) (-3251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_1_1_0_1_0_valid,fullLedger_0_0_0_1_1_0_1_1_valid⟩

def fullLedger_0_0_0_1_1_0 : Tree := (.first fullLedger_0_0_0_1_1_0_0 fullLedger_0_0_0_1_1_0_1)
theorem fullLedger_0_0_0_1_1_0_valid : check fullLedger_0_0_0_1_1_0 (-3751) (-3501) (-3501) (-3251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_1_1_0_0_valid,fullLedger_0_0_0_1_1_0_1_valid⟩

def fullLedger_0_0_0_1_1_1 : Tree := (.first (.axis 39 111 false) (.axis 55 111 false))
theorem fullLedger_0_0_0_1_1_1_valid : check fullLedger_0_0_0_1_1_1 (-3751) (-3501) (-3251) (-3001)=true := by
  decide +kernel

def fullLedger_0_0_0_1_1 : Tree := (.second fullLedger_0_0_0_1_1_0 fullLedger_0_0_0_1_1_1)
theorem fullLedger_0_0_0_1_1_valid : check fullLedger_0_0_0_1_1 (-3751) (-3501) (-3501) (-3001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_1_1_0_valid,fullLedger_0_0_0_1_1_1_valid⟩

def fullLedger_0_0_0_1 : Tree := (.first fullLedger_0_0_0_1_0 fullLedger_0_0_0_1_1)
theorem fullLedger_0_0_0_1_valid : check fullLedger_0_0_0_1 (-4001) (-3501) (-3501) (-3001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_1_0_valid,fullLedger_0_0_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
