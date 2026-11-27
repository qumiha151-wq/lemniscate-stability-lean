import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_0_1_0_0 : Tree := (.first (.second (.axis 646 951 false) (.axis 646 978 true)) (.second (.first (.axis 658 951 false) (.axis 666 951 false)) (.first (.second (.axis 658 974 false) (.axis 658 982 false)) (.axis 666 978 true))))
theorem fullLedger_2_1_0_1_0_1_0_0_valid : check fullLedger_2_1_0_1_0_1_0_0 1000 1250 2500 2750=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_0_1_0 : Tree := (.second (.axis 646 994 true) (.axis 646 1010 true))
theorem fullLedger_2_1_0_1_0_1_0_1_0_valid : check fullLedger_2_1_0_1_0_1_0_1_0 1000 1125 2750 3000=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_0_1_1 : Tree := (.second (.first (.second (.first (.second (.axis 656 988 false) (.axis 656 992 false)) (.axis 660 990 true)) (.axis 658 998 true)) (.axis 666 994 true)) (.first (.second (.axis 658 1006 true) (.second (.axis 658 1012 true) (.axis 658 1016 false))) (.axis 666 1010 true)))
theorem fullLedger_2_1_0_1_0_1_0_1_1_valid : check fullLedger_2_1_0_1_0_1_0_1_1 1125 1250 2750 3000=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_0_1 : Tree := (.first fullLedger_2_1_0_1_0_1_0_1_0 fullLedger_2_1_0_1_0_1_0_1_1)
theorem fullLedger_2_1_0_1_0_1_0_1_valid : check fullLedger_2_1_0_1_0_1_0_1 1000 1250 2750 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_0_1_0_valid,fullLedger_2_1_0_1_0_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_0 : Tree := (.second fullLedger_2_1_0_1_0_1_0_0 fullLedger_2_1_0_1_0_1_0_1)
theorem fullLedger_2_1_0_1_0_1_0_valid : check fullLedger_2_1_0_1_0_1_0 1000 1250 2500 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_0_0_valid,fullLedger_2_1_0_1_0_1_0_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
