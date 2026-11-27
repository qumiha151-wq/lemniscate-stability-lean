import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_1_0_0_1_1_0_0 : Tree := (.second (.axis 755 877 true) (.second (.axis 755 883 true) (.first (.axis 751 887 false) (.axis 759 887 true))))
theorem fullLedger_2_1_0_1_1_0_0_1_1_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_0_0 1625 1687 2250 2375=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_0_1 : Tree := (.second (.axis 786 877 true) (.first (.second (.axis 782 883 true) (.axis 782 887 true)) (.second (.axis 788 883 false) (.first (.axis 787 887 false) (.axis 789 887 false)))))
theorem fullLedger_2_1_0_1_1_0_0_1_1_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_0_1 1687 1750 2250 2375=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_0 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_1_0_0 fullLedger_2_1_0_1_1_0_0_1_1_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_0 1625 1750 2250 2375=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_0_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
