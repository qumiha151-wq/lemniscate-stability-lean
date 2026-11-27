import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_2_0_1_0 : Tree := (.second (.first (.axis 840 970 false) (.second (.axis 856 951 false) (.axis 856 978 false))) (.axis 848 1002 false))
theorem fullLedger_2_2_0_1_0_valid : check fullLedger_2_2_0_1_0 2000 2250 2500 3000=true := by
  decide +kernel

def fullLedger_2_2_0_1_1_0_0 : Tree := (.second (.first (.axis 877 951 false) (.axis 885 951 false)) (.axis 881 978 false))
theorem fullLedger_2_2_0_1_1_0_0_valid : check fullLedger_2_2_0_1_1_0_0 2250 2375 2500 2750=true := by
  decide +kernel

def fullLedger_2_2_0_1_1_0_1_0 : Tree := (.first (.axis 905 951 false) (.second (.first (.axis 919 933 true) (.second (.first (.axis 925 931 true) (.second Tree.short (.axis 928 932 false))) (.axis 927 937 false))) (.first (.axis 919 966 false) (.axis 927 966 false))))
theorem fullLedger_2_2_0_1_1_0_1_0_valid : check fullLedger_2_2_0_1_1_0_1_0 2375 2500 2500 2625=true := by
  decide +kernel

def fullLedger_2_2_0_1_1_0_1_1 : Tree := (.first (.axis 905 978 false) (.second (.axis 923 974 false) (.axis 923 982 false)))
theorem fullLedger_2_2_0_1_1_0_1_1_valid : check fullLedger_2_2_0_1_1_0_1_1 2375 2500 2625 2750=true := by
  decide +kernel

def fullLedger_2_2_0_1_1_0_1 : Tree := (.second fullLedger_2_2_0_1_1_0_1_0 fullLedger_2_2_0_1_1_0_1_1)
theorem fullLedger_2_2_0_1_1_0_1_valid : check fullLedger_2_2_0_1_1_0_1 2375 2500 2500 2750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_1_1_0_1_0_valid,fullLedger_2_2_0_1_1_0_1_1_valid⟩

def fullLedger_2_2_0_1_1_0 : Tree := (.first fullLedger_2_2_0_1_1_0_0 fullLedger_2_2_0_1_1_0_1)
theorem fullLedger_2_2_0_1_1_0_valid : check fullLedger_2_2_0_1_1_0 2250 2500 2500 2750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_1_1_0_0_valid,fullLedger_2_2_0_1_1_0_1_valid⟩

def fullLedger_2_2_0_1_1_1 : Tree := (.first (.axis 881 1002 false) (.second (.axis 915 994 false) (.axis 915 1010 false)))
theorem fullLedger_2_2_0_1_1_1_valid : check fullLedger_2_2_0_1_1_1 2250 2500 2750 3000=true := by
  decide +kernel

def fullLedger_2_2_0_1_1 : Tree := (.second fullLedger_2_2_0_1_1_0 fullLedger_2_2_0_1_1_1)
theorem fullLedger_2_2_0_1_1_valid : check fullLedger_2_2_0_1_1 2250 2500 2500 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_1_1_0_valid,fullLedger_2_2_0_1_1_1_valid⟩

def fullLedger_2_2_0_1 : Tree := (.first fullLedger_2_2_0_1_0 fullLedger_2_2_0_1_1)
theorem fullLedger_2_2_0_1_valid : check fullLedger_2_2_0_1 2000 2500 2500 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_1_0_valid,fullLedger_2_2_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
