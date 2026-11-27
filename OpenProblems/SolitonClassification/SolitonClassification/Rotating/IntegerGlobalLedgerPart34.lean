import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_0_0 : Tree := (.second (.axis 542 873 false) (.first (.axis 526 986 false) (.axis 558 986 false)))
theorem fullLedger_2_1_0_0_0_valid : check fullLedger_2_1_0_0_0 0 500 2000 3000=true := by
  decide +kernel

def fullLedger_2_1_0_0_1_0 : Tree := (.first (.axis 590 873 false) (.axis 622 873 false))
theorem fullLedger_2_1_0_0_1_0_valid : check fullLedger_2_1_0_0_1_0 500 1000 2000 2500=true := by
  decide +kernel

def fullLedger_2_1_0_0_1_1 : Tree := (.first (.second (.axis 590 970 false) (.axis 590 1002 false)) (.second (.axis 622 970 false) (.first (.axis 614 1002 true) (.second (.first (.axis 626 994 false) (.axis 634 994 false)) (.first (.axis 626 1010 false) (.axis 634 1010 true))))))
theorem fullLedger_2_1_0_0_1_1_valid : check fullLedger_2_1_0_0_1_1 500 1000 2500 3000=true := by
  decide +kernel

def fullLedger_2_1_0_0_1 : Tree := (.second fullLedger_2_1_0_0_1_0 fullLedger_2_1_0_0_1_1)
theorem fullLedger_2_1_0_0_1_valid : check fullLedger_2_1_0_0_1 500 1000 2000 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_0_1_0_valid,fullLedger_2_1_0_0_1_1_valid⟩

def fullLedger_2_1_0_0 : Tree := (.first fullLedger_2_1_0_0_0 fullLedger_2_1_0_0_1)
theorem fullLedger_2_1_0_0_valid : check fullLedger_2_1_0_0 0 1000 2000 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_0_0_valid,fullLedger_2_1_0_0_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
