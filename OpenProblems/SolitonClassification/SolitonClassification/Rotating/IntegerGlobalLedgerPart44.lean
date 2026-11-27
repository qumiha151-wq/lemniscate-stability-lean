import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_1_0_0_1_0_0_0 : Tree := (.second (.first (.axis 731 877 false) (.second (.axis 735 875 false) (.first (.axis 734 879 false) (.axis 736 879 false)))) (.axis 733 885 true))
theorem fullLedger_2_1_0_1_1_0_0_1_0_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_0_0_0 1500 1562 2250 2375=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_0_0_1 : Tree := (.second (.first (.second (.axis 739 875 false) (.first (.axis 738 879 false) (.axis 740 879 false))) (.axis 743 877 true)) (.first (.second (.axis 739 883 false) (.axis 739 887 false)) (.second (.axis 743 883 false) (.axis 743 887 false))))
theorem fullLedger_2_1_0_1_1_0_0_1_0_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_0_0_1 1562 1625 2250 2375=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_0_0 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_0_0_0 fullLedger_2_1_0_1_1_0_0_1_0_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_0_0 1500 1625 2250 2375=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_0_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_0_1 : Tree := (.first (.axis 733 915 true) (.second (.axis 741 905 true) (.first (.axis 739 923 true) (.second (.axis 743 919 true) (.first (.axis 742 927 true) (.second (.axis 745 925 true) (.first (.axis 744 928 false) (.axis 746 928 false))))))))
theorem fullLedger_2_1_0_1_1_0_0_1_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_0_1 1500 1625 2375 2500=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_0 : Tree := (.second fullLedger_2_1_0_1_1_0_0_1_0_0 fullLedger_2_1_0_1_1_0_0_1_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_0_valid : check fullLedger_2_1_0_1_1_0_0_1_0 1500 1625 2250 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_0_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
