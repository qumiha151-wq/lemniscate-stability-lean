import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_2_2_1_0_0 : Tree := (.first (.axis 1026 1098 false) (.second (.axis 1042 1090 false) (.axis 1042 1106 false)))
theorem fullLedger_2_2_2_1_0_0_valid : check fullLedger_2_2_2_1_0_0 3000 3250 3500 3750=true := by
  decide +kernel

def fullLedger_2_2_2_1_0_1_0 : Tree := (.second (.first (.axis 1054 1090 false) (.second (.axis 1062 1086 false) (.axis 1062 1094 false))) (.axis 1058 1106 false))
theorem fullLedger_2_2_2_1_0_1_0_valid : check fullLedger_2_2_2_1_0_1_0 3250 3375 3500 3750=true := by
  decide +kernel

def fullLedger_2_2_2_1_0_1_1_0_0 : Tree := (.second (.axis 1070 1086 false) (.axis 1070 1094 false))
theorem fullLedger_2_2_2_1_0_1_1_0_0_valid : check fullLedger_2_2_2_1_0_1_1_0_0 3375 3437 3500 3625=true := by
  decide +kernel

def fullLedger_2_2_2_1_0_1_1_0_1 : Tree := (.second (.first (.axis 1076 1086 true) (.second (.first (.axis 1079 1084 true) (.second Tree.short (.axis 1081 1085 false))) (.axis 1080 1088 false))) (.first (.axis 1076 1094 false) (.second (.axis 1080 1092 false) (.axis 1080 1096 false))))
theorem fullLedger_2_2_2_1_0_1_1_0_1_valid : check fullLedger_2_2_2_1_0_1_1_0_1 3437 3500 3500 3625=true := by
  decide +kernel

def fullLedger_2_2_2_1_0_1_1_0 : Tree := (.first fullLedger_2_2_2_1_0_1_1_0_0 fullLedger_2_2_2_1_0_1_1_0_1)
theorem fullLedger_2_2_2_1_0_1_1_0_valid : check fullLedger_2_2_2_1_0_1_1_0 3375 3500 3500 3625=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_1_0_1_1_0_0_valid,fullLedger_2_2_2_1_0_1_1_0_1_valid⟩

def fullLedger_2_2_2_1_0_1_1_1 : Tree := (.first (.axis 1070 1106 false) (.axis 1078 1106 false))
theorem fullLedger_2_2_2_1_0_1_1_1_valid : check fullLedger_2_2_2_1_0_1_1_1 3375 3500 3625 3750=true := by
  decide +kernel

def fullLedger_2_2_2_1_0_1_1 : Tree := (.second fullLedger_2_2_2_1_0_1_1_0 fullLedger_2_2_2_1_0_1_1_1)
theorem fullLedger_2_2_2_1_0_1_1_valid : check fullLedger_2_2_2_1_0_1_1 3375 3500 3500 3750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_1_0_1_1_0_valid,fullLedger_2_2_2_1_0_1_1_1_valid⟩

def fullLedger_2_2_2_1_0_1 : Tree := (.first fullLedger_2_2_2_1_0_1_0 fullLedger_2_2_2_1_0_1_1)
theorem fullLedger_2_2_2_1_0_1_valid : check fullLedger_2_2_2_1_0_1 3250 3500 3500 3750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_1_0_1_0_valid,fullLedger_2_2_2_1_0_1_1_valid⟩

def fullLedger_2_2_2_1_0 : Tree := (.first fullLedger_2_2_2_1_0_0 fullLedger_2_2_2_1_0_1)
theorem fullLedger_2_2_2_1_0_valid : check fullLedger_2_2_2_1_0 3000 3500 3500 3750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_1_0_0_valid,fullLedger_2_2_2_1_0_1_valid⟩

def fullLedger_2_2_2_1_1 : Tree := (.first (.axis 1034 1130 false) (.second (.first (.axis 1058 1122 false) (.axis 1074 1122 false)) (.axis 1066 1138 false)))
theorem fullLedger_2_2_2_1_1_valid : check fullLedger_2_2_2_1_1 3000 3500 3750 4001=true := by
  decide +kernel

def fullLedger_2_2_2_1 : Tree := (.second fullLedger_2_2_2_1_0 fullLedger_2_2_2_1_1)
theorem fullLedger_2_2_2_1_valid : check fullLedger_2_2_2_1 3000 3500 3500 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_1_0_valid,fullLedger_2_2_2_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
