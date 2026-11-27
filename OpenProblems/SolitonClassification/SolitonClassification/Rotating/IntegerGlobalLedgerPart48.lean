import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_1_1_0_0_0_0_0 : Tree := (.second (.first (.axis 731 933 true) (.second (.axis 735 931 true) (.axis 735 937 false))) (.axis 733 966 false))
theorem fullLedger_2_1_0_1_1_1_0_0_0_0_0_valid : check fullLedger_2_1_0_1_1_1_0_0_0_0_0 1500 1562 2500 2625=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_1_0_0_0_0_1 : Tree := (.second (.first (.second (.axis 739 931 false) (.axis 739 937 false)) (.second (.first (.axis 742 931 false) (.axis 745 931 false)) (.axis 743 937 false))) (.axis 741 966 false))
theorem fullLedger_2_1_0_1_1_1_0_0_0_0_1_valid : check fullLedger_2_1_0_1_1_1_0_0_0_0_1 1562 1625 2500 2625=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_1_0_0_0_0 : Tree := (.first fullLedger_2_1_0_1_1_1_0_0_0_0_0 fullLedger_2_1_0_1_1_1_0_0_0_0_1)
theorem fullLedger_2_1_0_1_1_1_0_0_0_0_valid : check fullLedger_2_1_0_1_1_1_0_0_0_0 1500 1625 2500 2625=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_1_0_0_0_0_0_valid,fullLedger_2_1_0_1_1_1_0_0_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_1_0_0_0_1 : Tree := (.axis 737 978 true)
theorem fullLedger_2_1_0_1_1_1_0_0_0_1_valid : check fullLedger_2_1_0_1_1_1_0_0_0_1 1500 1625 2625 2750=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_1_0_0_0 : Tree := (.second fullLedger_2_1_0_1_1_1_0_0_0_0 fullLedger_2_1_0_1_1_1_0_0_0_1)
theorem fullLedger_2_1_0_1_1_1_0_0_0_valid : check fullLedger_2_1_0_1_1_1_0_0_0 1500 1625 2500 2750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_1_0_0_0_0_valid,fullLedger_2_1_0_1_1_1_0_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_1_0_0_1 : Tree := (.second (.first (.second (.first (.axis 751 933 false) (.axis 759 933 false)) (.axis 755 966 false)) (.axis 786 951 false)) (.axis 769 978 false))
theorem fullLedger_2_1_0_1_1_1_0_0_1_valid : check fullLedger_2_1_0_1_1_1_0_0_1 1625 1750 2500 2750=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_1_0_0 : Tree := (.first fullLedger_2_1_0_1_1_1_0_0_0 fullLedger_2_1_0_1_1_1_0_0_1)
theorem fullLedger_2_1_0_1_1_1_0_0_valid : check fullLedger_2_1_0_1_1_1_0_0 1500 1750 2500 2750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_1_0_0_0_valid,fullLedger_2_1_0_1_1_1_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_1_0_1 : Tree := (.first (.second (.axis 737 994 false) (.axis 737 1010 false)) (.axis 769 1002 false))
theorem fullLedger_2_1_0_1_1_1_0_1_valid : check fullLedger_2_1_0_1_1_1_0_1 1500 1750 2750 3000=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_1_0 : Tree := (.second fullLedger_2_1_0_1_1_1_0_0 fullLedger_2_1_0_1_1_1_0_1)
theorem fullLedger_2_1_0_1_1_1_0_valid : check fullLedger_2_1_0_1_1_1_0 1500 1750 2500 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_1_0_0_valid,fullLedger_2_1_0_1_1_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_1_1 : Tree := (.second (.first (.second (.axis 804 951 false) (.axis 804 978 false)) (.axis 824 970 false)) (.axis 816 1002 false))
theorem fullLedger_2_1_0_1_1_1_1_valid : check fullLedger_2_1_0_1_1_1_1 1750 2000 2500 3000=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_1 : Tree := (.first fullLedger_2_1_0_1_1_1_0 fullLedger_2_1_0_1_1_1_1)
theorem fullLedger_2_1_0_1_1_1_valid : check fullLedger_2_1_0_1_1_1 1500 2000 2500 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_1_0_valid,fullLedger_2_1_0_1_1_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
