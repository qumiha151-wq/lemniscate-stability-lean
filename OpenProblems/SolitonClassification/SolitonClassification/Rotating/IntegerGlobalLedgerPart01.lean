import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_0_0_0_1_0 : Tree := (.second (.first (.axis 3 39 false) (.axis 11 39 false)) (.axis 7 55 false))
theorem fullLedger_0_0_0_0_1_0_valid : check fullLedger_0_0_0_0_1_0 (-4001) (-3876) (-3751) (-3501)=true := by
  decide +kernel

def fullLedger_0_0_0_0_1_1_0_0 : Tree := (.second (.first (.axis 17 35 false) (.axis 21 35 false)) (.axis 19 43 false))
theorem fullLedger_0_0_0_0_1_1_0_0_valid : check fullLedger_0_0_0_0_1_1_0_0 (-3876) (-3814) (-3751) (-3626)=true := by
  decide +kernel

def fullLedger_0_0_0_0_1_1_0_1 : Tree := (.second (.first (.axis 25 35 true) (.second (.first (.axis 28 33 true) (.second Tree.short (.axis 30 34 true))) (.axis 29 37 true))) (.first (.axis 25 43 false) (.second (.axis 29 41 false) (.axis 29 45 false))))
theorem fullLedger_0_0_0_0_1_1_0_1_valid : check fullLedger_0_0_0_0_1_1_0_1 (-3814) (-3751) (-3751) (-3626)=true := by
  decide +kernel

def fullLedger_0_0_0_0_1_1_0 : Tree := (.first fullLedger_0_0_0_0_1_1_0_0 fullLedger_0_0_0_0_1_1_0_1)
theorem fullLedger_0_0_0_0_1_1_0_valid : check fullLedger_0_0_0_0_1_1_0 (-3876) (-3751) (-3751) (-3626)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_1_1_0_0_valid,fullLedger_0_0_0_0_1_1_0_1_valid⟩

def fullLedger_0_0_0_0_1_1_1 : Tree := (.first (.axis 19 55 false) (.second (.axis 27 51 false) (.axis 27 59 false)))
theorem fullLedger_0_0_0_0_1_1_1_valid : check fullLedger_0_0_0_0_1_1_1 (-3876) (-3751) (-3626) (-3501)=true := by
  decide +kernel

def fullLedger_0_0_0_0_1_1 : Tree := (.second fullLedger_0_0_0_0_1_1_0 fullLedger_0_0_0_0_1_1_1)
theorem fullLedger_0_0_0_0_1_1_valid : check fullLedger_0_0_0_0_1_1 (-3876) (-3751) (-3751) (-3501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_1_1_0_valid,fullLedger_0_0_0_0_1_1_1_valid⟩

def fullLedger_0_0_0_0_1 : Tree := (.first fullLedger_0_0_0_0_1_0 fullLedger_0_0_0_0_1_1)
theorem fullLedger_0_0_0_0_1_valid : check fullLedger_0_0_0_0_1 (-4001) (-3751) (-3751) (-3501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_1_0_valid,fullLedger_0_0_0_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
