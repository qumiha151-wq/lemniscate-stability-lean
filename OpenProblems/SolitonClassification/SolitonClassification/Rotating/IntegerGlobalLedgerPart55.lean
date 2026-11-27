import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_2_2_0_1_0 : Tree := (.second (.first (.axis 1022 1058 false) (.second (.axis 1030 1054 false) (.axis 1030 1062 false))) (.axis 1026 1074 false))
theorem fullLedger_2_2_2_0_1_0_valid : check fullLedger_2_2_2_0_1_0 3000 3125 3250 3500=true := by
  decide +kernel

def fullLedger_2_2_2_0_1_1_0_0 : Tree := (.second (.axis 1038 1054 true) (.axis 1038 1062 false))
theorem fullLedger_2_2_2_0_1_1_0_0_valid : check fullLedger_2_2_2_0_1_1_0_0 3125 3187 3250 3375=true := by
  decide +kernel

def fullLedger_2_2_2_0_1_1_0_1 : Tree := (.second (.first (.second (.axis 1044 1052 true) (.axis 1044 1056 false)) (.second (.first (.second (.axis 1047 1051 true) (.axis 1047 1053 false)) (.second Tree.short (.axis 1049 1053 false))) (.axis 1048 1056 false))) (.axis 1046 1062 false))
theorem fullLedger_2_2_2_0_1_1_0_1_valid : check fullLedger_2_2_2_0_1_1_0_1 3187 3250 3250 3375=true := by
  decide +kernel

def fullLedger_2_2_2_0_1_1_0 : Tree := (.first fullLedger_2_2_2_0_1_1_0_0 fullLedger_2_2_2_0_1_1_0_1)
theorem fullLedger_2_2_2_0_1_1_0_valid : check fullLedger_2_2_2_0_1_1_0 3125 3250 3250 3375=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_1_1_0_0_valid,fullLedger_2_2_2_0_1_1_0_1_valid⟩

def fullLedger_2_2_2_0_1_1_1 : Tree := (.first (.axis 1038 1074 false) (.axis 1046 1074 false))
theorem fullLedger_2_2_2_0_1_1_1_valid : check fullLedger_2_2_2_0_1_1_1 3125 3250 3375 3500=true := by
  decide +kernel

def fullLedger_2_2_2_0_1_1 : Tree := (.second fullLedger_2_2_2_0_1_1_0 fullLedger_2_2_2_0_1_1_1)
theorem fullLedger_2_2_2_0_1_1_valid : check fullLedger_2_2_2_0_1_1 3125 3250 3250 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_1_1_0_valid,fullLedger_2_2_2_0_1_1_1_valid⟩

def fullLedger_2_2_2_0_1 : Tree := (.first fullLedger_2_2_2_0_1_0 fullLedger_2_2_2_0_1_1)
theorem fullLedger_2_2_2_0_1_valid : check fullLedger_2_2_2_0_1 3000 3250 3250 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_1_0_valid,fullLedger_2_2_2_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
