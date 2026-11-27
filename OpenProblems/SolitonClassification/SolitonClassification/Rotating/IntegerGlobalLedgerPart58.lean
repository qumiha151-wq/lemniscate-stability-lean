import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_2_2_2_0_0_0 : Tree := (.square Tree.short (.first (.axis 1083 1088 false) (.second Tree.short (.axis 1085 1089 true))) Tree.short)
theorem fullLedger_2_2_2_2_0_0_0_valid : check fullLedger_2_2_2_2_0_0_0 3500 3562 3500 3562=true := by
  decide +kernel

def fullLedger_2_2_2_2_0_0_1 : Tree := (.second (.first (.axis 1084 1092 true) (.first (.axis 1087 1092 true) (.second Tree.short (.axis 1089 1093 true)))) (.axis 1086 1096 true))
theorem fullLedger_2_2_2_2_0_0_1_valid : check fullLedger_2_2_2_2_0_0_1 3500 3562 3562 3625=true := by
  decide +kernel

def fullLedger_2_2_2_2_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 1091 1095 true) Tree.short) (.first (.axis 1091 1097 false) (.axis 1093 1097 false))) Tree.short)
theorem fullLedger_2_2_2_2_0_0_2_valid : check fullLedger_2_2_2_2_0_0_2 3562 3625 3562 3625=true := by
  decide +kernel

def fullLedger_2_2_2_2_0_0 : Tree := (.square fullLedger_2_2_2_2_0_0_0 fullLedger_2_2_2_2_0_0_1 fullLedger_2_2_2_2_0_0_2)
theorem fullLedger_2_2_2_2_0_0_valid : check fullLedger_2_2_2_2_0_0 3500 3625 3500 3625=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_0_0_0_valid,fullLedger_2_2_2_2_0_0_1_valid⟩,fullLedger_2_2_2_2_0_0_2_valid⟩⟩

def fullLedger_2_2_2_2_0_1_0 : Tree := (.second (.first (.axis 1084 1102 false) (.second (.axis 1088 1100 false) (.axis 1088 1104 false))) (.axis 1086 1110 false))
theorem fullLedger_2_2_2_2_0_1_0_valid : check fullLedger_2_2_2_2_0_1_0 3500 3562 3625 3750=true := by
  decide +kernel

def fullLedger_2_2_2_2_0_1_1 : Tree := (.second (.first (.second (.axis 1092 1100 false) (.axis 1092 1104 false)) (.second (.first (.axis 1095 1100 false) (.second Tree.short (.axis 1097 1101 false))) (.axis 1096 1104 true))) (.axis 1094 1110 false))
theorem fullLedger_2_2_2_2_0_1_1_valid : check fullLedger_2_2_2_2_0_1_1 3562 3625 3625 3750=true := by
  decide +kernel

def fullLedger_2_2_2_2_0_1 : Tree := (.first fullLedger_2_2_2_2_0_1_0 fullLedger_2_2_2_2_0_1_1)
theorem fullLedger_2_2_2_2_0_1_valid : check fullLedger_2_2_2_2_0_1 3500 3625 3625 3750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_0_1_0_valid,fullLedger_2_2_2_2_0_1_1_valid⟩

def fullLedger_2_2_2_2_0_2_0 : Tree := (.square Tree.short (.first (.axis 1099 1104 true) (.second Tree.short (.axis 1101 1105 true))) Tree.short)
theorem fullLedger_2_2_2_2_0_2_0_valid : check fullLedger_2_2_2_2_0_2_0 3625 3687 3625 3687=true := by
  decide +kernel

def fullLedger_2_2_2_2_0_2_1 : Tree := (.second (.first (.axis 1100 1108 false) (.first (.axis 1103 1108 false) (.second Tree.short (.axis 1105 1109 false)))) (.first (.axis 1100 1112 false) (.axis 1104 1112 false)))
theorem fullLedger_2_2_2_2_0_2_1_valid : check fullLedger_2_2_2_2_0_2_1 3625 3687 3687 3750=true := by
  decide +kernel

def fullLedger_2_2_2_2_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 1107 1111 true) Tree.short) (.axis 1108 1113 true)) Tree.short)
theorem fullLedger_2_2_2_2_0_2_2_valid : check fullLedger_2_2_2_2_0_2_2 3687 3750 3687 3750=true := by
  decide +kernel

def fullLedger_2_2_2_2_0_2 : Tree := (.square fullLedger_2_2_2_2_0_2_0 fullLedger_2_2_2_2_0_2_1 fullLedger_2_2_2_2_0_2_2)
theorem fullLedger_2_2_2_2_0_2_valid : check fullLedger_2_2_2_2_0_2 3625 3750 3625 3750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_0_2_0_valid,fullLedger_2_2_2_2_0_2_1_valid⟩,fullLedger_2_2_2_2_0_2_2_valid⟩⟩

def fullLedger_2_2_2_2_0 : Tree := (.square fullLedger_2_2_2_2_0_0 fullLedger_2_2_2_2_0_1 fullLedger_2_2_2_2_0_2)
theorem fullLedger_2_2_2_2_0_valid : check fullLedger_2_2_2_2_0 3500 3750 3500 3750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_0_0_valid,fullLedger_2_2_2_2_0_1_valid⟩,fullLedger_2_2_2_2_0_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
