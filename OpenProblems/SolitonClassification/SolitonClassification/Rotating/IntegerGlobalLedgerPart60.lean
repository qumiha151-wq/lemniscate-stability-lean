import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_2_2_2_2_0_0 : Tree := (.square Tree.short (.first (.axis 1115 1120 false) (.second Tree.short (.axis 1117 1121 false))) Tree.short)
theorem fullLedger_2_2_2_2_2_0_0_valid : check fullLedger_2_2_2_2_2_0_0 3750 3812 3750 3812=true := by
  decide +kernel

def fullLedger_2_2_2_2_2_0_1 : Tree := (.second (.first (.axis 1116 1124 false) (.first (.axis 1119 1124 true) (.second Tree.short (.axis 1121 1125 true)))) (.axis 1118 1128 true))
theorem fullLedger_2_2_2_2_2_0_1_valid : check fullLedger_2_2_2_2_2_0_1 3750 3812 3812 3875=true := by
  decide +kernel

def fullLedger_2_2_2_2_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 1123 1127 true) Tree.short) (.axis 1124 1129 false)) Tree.short)
theorem fullLedger_2_2_2_2_2_0_2_valid : check fullLedger_2_2_2_2_2_0_2 3812 3875 3812 3875=true := by
  decide +kernel

def fullLedger_2_2_2_2_2_0 : Tree := (.square fullLedger_2_2_2_2_2_0_0 fullLedger_2_2_2_2_2_0_1 fullLedger_2_2_2_2_2_0_2)
theorem fullLedger_2_2_2_2_2_0_valid : check fullLedger_2_2_2_2_2_0 3750 3875 3750 3875=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_2_0_0_valid,fullLedger_2_2_2_2_2_0_1_valid⟩,fullLedger_2_2_2_2_2_0_2_valid⟩⟩

def fullLedger_2_2_2_2_2_1_0 : Tree := (.first (.second (.axis 1118 1132 false) (.axis 1118 1136 false)) (.first (.second (.axis 1124 1132 false) (.axis 1124 1136 false)) (.second (.first (.axis 1127 1132 false) (.second Tree.short (.axis 1129 1133 true))) (.axis 1128 1136 true))))
theorem fullLedger_2_2_2_2_2_1_0_valid : check fullLedger_2_2_2_2_2_1_0 3750 3875 3875 3938=true := by
  decide +kernel

def fullLedger_2_2_2_2_2_1_1 : Tree := (.first (.axis 1118 1142 false) (.first (.axis 1124 1142 false) (.axis 1128 1142 false)))
theorem fullLedger_2_2_2_2_2_1_1_valid : check fullLedger_2_2_2_2_2_1_1 3750 3875 3938 4001=true := by
  decide +kernel

def fullLedger_2_2_2_2_2_1 : Tree := (.second fullLedger_2_2_2_2_2_1_0 fullLedger_2_2_2_2_2_1_1)
theorem fullLedger_2_2_2_2_2_1_valid : check fullLedger_2_2_2_2_2_1 3750 3875 3875 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_2_1_0_valid,fullLedger_2_2_2_2_2_1_1_valid⟩

def fullLedger_2_2_2_2_2_2_0 : Tree := (.square Tree.short (.second (.first (.axis 1131 1135 true) Tree.short) (.axis 1132 1137 true)) Tree.short)
theorem fullLedger_2_2_2_2_2_2_0_valid : check fullLedger_2_2_2_2_2_2_0 3875 3938 3875 3938=true := by
  decide +kernel

def fullLedger_2_2_2_2_2_2_1 : Tree := (.first (.second (.axis 1132 1140 true) (.axis 1132 1144 false)) (.second (.first (.axis 1135 1140 true) (.second Tree.short (.axis 1137 1141 false))) (.axis 1136 1144 false)))
theorem fullLedger_2_2_2_2_2_2_1_valid : check fullLedger_2_2_2_2_2_2_1 3875 3938 3938 4001=true := by
  decide +kernel

def fullLedger_2_2_2_2_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 1139 1143 false) Tree.short) (.axis 1140 1145 true)) Tree.short)
theorem fullLedger_2_2_2_2_2_2_2_valid : check fullLedger_2_2_2_2_2_2_2 3938 4001 3938 4001=true := by
  decide +kernel

def fullLedger_2_2_2_2_2_2 : Tree := (.square fullLedger_2_2_2_2_2_2_0 fullLedger_2_2_2_2_2_2_1 fullLedger_2_2_2_2_2_2_2)
theorem fullLedger_2_2_2_2_2_2_valid : check fullLedger_2_2_2_2_2_2 3875 4001 3875 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_2_2_0_valid,fullLedger_2_2_2_2_2_2_1_valid⟩,fullLedger_2_2_2_2_2_2_2_valid⟩⟩

def fullLedger_2_2_2_2_2 : Tree := (.square fullLedger_2_2_2_2_2_0 fullLedger_2_2_2_2_2_1 fullLedger_2_2_2_2_2_2)
theorem fullLedger_2_2_2_2_2_valid : check fullLedger_2_2_2_2_2 3750 4001 3750 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_2_0_valid,fullLedger_2_2_2_2_2_1_valid⟩,fullLedger_2_2_2_2_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
