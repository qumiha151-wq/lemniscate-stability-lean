import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_2_1_0_0 : Tree := (.first (.axis 848 1050 false) (.axis 889 1050 false))
theorem fullLedger_2_2_1_0_0_valid : check fullLedger_2_2_1_0_0 2000 2500 3000 3500=true := by
  decide +kernel

def fullLedger_2_2_1_0_1_0 : Tree := (.second (.first (.axis 951 1034 false) (.axis 978 1034 false)) (.axis 970 1066 false))
theorem fullLedger_2_2_1_0_1_0_valid : check fullLedger_2_2_1_0_1_0 2500 2750 3000 3500=true := by
  decide +kernel

def fullLedger_2_2_1_0_1_1_0_0 : Tree := (.second (.first (.axis 990 1026 true) (.second (.axis 998 1022 false) (.axis 998 1030 false))) (.axis 994 1042 false))
theorem fullLedger_2_2_1_0_1_1_0_0_valid : check fullLedger_2_2_1_0_1_1_0_0 2750 2875 3000 3250=true := by
  decide +kernel

def fullLedger_2_2_1_0_1_1_0_1_0_0 : Tree := (.second (.first (.axis 1004 1022 false) (.second (.axis 1008 1020 false) (.axis 1008 1024 false))) (.axis 1006 1030 false))
theorem fullLedger_2_2_1_0_1_1_0_1_0_0_valid : check fullLedger_2_2_1_0_1_1_0_1_0_0 2875 2937 3000 3125=true := by
  decide +kernel

def fullLedger_2_2_1_0_1_1_0_1_0_1 : Tree := (.second (.first (.second (.axis 1012 1020 false) (.axis 1012 1024 true)) (.second (.first (.axis 1015 1020 true) (.second Tree.short (.axis 1017 1021 true))) (.axis 1016 1024 true))) (.axis 1014 1030 true))
theorem fullLedger_2_2_1_0_1_1_0_1_0_1_valid : check fullLedger_2_2_1_0_1_1_0_1_0_1 2937 3000 3000 3125=true := by
  decide +kernel

def fullLedger_2_2_1_0_1_1_0_1_0 : Tree := (.first fullLedger_2_2_1_0_1_1_0_1_0_0 fullLedger_2_2_1_0_1_1_0_1_0_1)
theorem fullLedger_2_2_1_0_1_1_0_1_0_valid : check fullLedger_2_2_1_0_1_1_0_1_0 2875 3000 3000 3125=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_1_0_1_1_0_1_0_0_valid,fullLedger_2_2_1_0_1_1_0_1_0_1_valid⟩

def fullLedger_2_2_1_0_1_1_0_1_1 : Tree := (.first (.axis 1006 1042 false) (.axis 1014 1042 false))
theorem fullLedger_2_2_1_0_1_1_0_1_1_valid : check fullLedger_2_2_1_0_1_1_0_1_1 2875 3000 3125 3250=true := by
  decide +kernel

def fullLedger_2_2_1_0_1_1_0_1 : Tree := (.second fullLedger_2_2_1_0_1_1_0_1_0 fullLedger_2_2_1_0_1_1_0_1_1)
theorem fullLedger_2_2_1_0_1_1_0_1_valid : check fullLedger_2_2_1_0_1_1_0_1 2875 3000 3000 3250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_1_0_1_1_0_1_0_valid,fullLedger_2_2_1_0_1_1_0_1_1_valid⟩

def fullLedger_2_2_1_0_1_1_0 : Tree := (.first fullLedger_2_2_1_0_1_1_0_0 fullLedger_2_2_1_0_1_1_0_1)
theorem fullLedger_2_2_1_0_1_1_0_valid : check fullLedger_2_2_1_0_1_1_0 2750 3000 3000 3250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_1_0_1_1_0_0_valid,fullLedger_2_2_1_0_1_1_0_1_valid⟩

def fullLedger_2_2_1_0_1_1_1 : Tree := (.first (.axis 994 1066 false) (.axis 1010 1066 false))
theorem fullLedger_2_2_1_0_1_1_1_valid : check fullLedger_2_2_1_0_1_1_1 2750 3000 3250 3500=true := by
  decide +kernel

def fullLedger_2_2_1_0_1_1 : Tree := (.second fullLedger_2_2_1_0_1_1_0 fullLedger_2_2_1_0_1_1_1)
theorem fullLedger_2_2_1_0_1_1_valid : check fullLedger_2_2_1_0_1_1 2750 3000 3000 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_1_0_1_1_0_valid,fullLedger_2_2_1_0_1_1_1_valid⟩

def fullLedger_2_2_1_0_1 : Tree := (.first fullLedger_2_2_1_0_1_0 fullLedger_2_2_1_0_1_1)
theorem fullLedger_2_2_1_0_1_valid : check fullLedger_2_2_1_0_1 2500 3000 3000 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_1_0_1_0_valid,fullLedger_2_2_1_0_1_1_valid⟩

def fullLedger_2_2_1_0 : Tree := (.first fullLedger_2_2_1_0_0 fullLedger_2_2_1_0_1)
theorem fullLedger_2_2_1_0_valid : check fullLedger_2_2_1_0 2000 3000 3000 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_1_0_0_valid,fullLedger_2_2_1_0_1_valid⟩

def fullLedger_2_2_1_1 : Tree := (.first (.axis 873 1114 false) (.second (.axis 986 1098 false) (.axis 986 1130 false)))
theorem fullLedger_2_2_1_1_valid : check fullLedger_2_2_1_1 2000 3000 3500 4001=true := by
  decide +kernel

def fullLedger_2_2_1 : Tree := (.second fullLedger_2_2_1_0 fullLedger_2_2_1_1)
theorem fullLedger_2_2_1_valid : check fullLedger_2_2_1 2000 3000 3000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_1_0_valid,fullLedger_2_2_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
