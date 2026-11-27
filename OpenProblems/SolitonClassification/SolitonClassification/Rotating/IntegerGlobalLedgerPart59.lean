import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_2_2_2_1_0_0 : Tree := (.first (.axis 1086 1122 false) (.axis 1094 1122 false))
theorem fullLedger_2_2_2_2_1_0_0_valid : check fullLedger_2_2_2_2_1_0_0 3500 3625 3750 3875=true := by
  decide +kernel

def fullLedger_2_2_2_2_1_0_1_0 : Tree := (.second (.first (.axis 1100 1118 false) (.axis 1104 1118 false)) (.axis 1102 1126 false))
theorem fullLedger_2_2_2_2_1_0_1_0_valid : check fullLedger_2_2_2_2_1_0_1_0 3625 3687 3750 3875=true := by
  decide +kernel

def fullLedger_2_2_2_2_1_0_1_1 : Tree := (.second (.first (.axis 1108 1118 true) (.second (.first (.axis 1111 1116 true) (.second Tree.short (.axis 1113 1117 true))) (.first (.axis 1111 1120 false) (.axis 1113 1120 false)))) (.first (.axis 1108 1126 false) (.second (.axis 1112 1124 false) (.axis 1112 1128 false))))
theorem fullLedger_2_2_2_2_1_0_1_1_valid : check fullLedger_2_2_2_2_1_0_1_1 3687 3750 3750 3875=true := by
  decide +kernel

def fullLedger_2_2_2_2_1_0_1 : Tree := (.first fullLedger_2_2_2_2_1_0_1_0 fullLedger_2_2_2_2_1_0_1_1)
theorem fullLedger_2_2_2_2_1_0_1_valid : check fullLedger_2_2_2_2_1_0_1 3625 3750 3750 3875=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_1_0_1_0_valid,fullLedger_2_2_2_2_1_0_1_1_valid⟩

def fullLedger_2_2_2_2_1_0 : Tree := (.first fullLedger_2_2_2_2_1_0_0 fullLedger_2_2_2_2_1_0_1)
theorem fullLedger_2_2_2_2_1_0_valid : check fullLedger_2_2_2_2_1_0 3500 3750 3750 3875=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_1_0_0_valid,fullLedger_2_2_2_2_1_0_1_valid⟩

def fullLedger_2_2_2_2_1_1 : Tree := (.first (.axis 1090 1138 false) (.second (.first (.axis 1102 1134 false) (.axis 1110 1134 false)) (.axis 1106 1142 false)))
theorem fullLedger_2_2_2_2_1_1_valid : check fullLedger_2_2_2_2_1_1 3500 3750 3875 4001=true := by
  decide +kernel

def fullLedger_2_2_2_2_1 : Tree := (.second fullLedger_2_2_2_2_1_0 fullLedger_2_2_2_2_1_1)
theorem fullLedger_2_2_2_2_1_valid : check fullLedger_2_2_2_2_1 3500 3750 3750 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_1_0_valid,fullLedger_2_2_2_2_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
