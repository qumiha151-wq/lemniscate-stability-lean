import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_0_0_0 : Tree := (.second (.axis 654 848 false) (.axis 654 889 false))
theorem fullLedger_2_1_0_1_0_0_0_valid : check fullLedger_2_1_0_1_0_0_0 1000 1250 2000 2500=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_0_1_0 : Tree := (.first (.axis 678 848 false) (.axis 721 848 false))
theorem fullLedger_2_1_0_1_0_0_1_0_valid : check fullLedger_2_1_0_1_0_0_1_0 1250 1500 2000 2250=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_0_1_1 : Tree := (.first (.second (.axis 678 881 false) (.axis 678 915 false)) (.second (.first (.axis 700 881 false) (.second (.axis 725 877 false) (.axis 725 885 false))) (.first (.second (.axis 700 905 false) (.second (.axis 700 919 false) (.axis 700 927 false))) (.axis 725 915 true))))
theorem fullLedger_2_1_0_1_0_0_1_1_valid : check fullLedger_2_1_0_1_0_0_1_1 1250 1500 2250 2500=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_0_1 : Tree := (.second fullLedger_2_1_0_1_0_0_1_0 fullLedger_2_1_0_1_0_0_1_1)
theorem fullLedger_2_1_0_1_0_0_1_valid : check fullLedger_2_1_0_1_0_0_1 1250 1500 2000 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_0_1_0_valid,fullLedger_2_1_0_1_0_0_1_1_valid⟩

def fullLedger_2_1_0_1_0_0 : Tree := (.first fullLedger_2_1_0_1_0_0_0 fullLedger_2_1_0_1_0_0_1)
theorem fullLedger_2_1_0_1_0_0_valid : check fullLedger_2_1_0_1_0_0 1000 1500 2000 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_0_0_valid,fullLedger_2_1_0_1_0_0_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
