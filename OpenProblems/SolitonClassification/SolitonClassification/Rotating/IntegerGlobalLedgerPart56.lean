import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_2_2_0_2_0_0 : Tree := (.square Tree.short (.first (.axis 1051 1056 false) (.second Tree.short (.axis 1053 1057 true))) Tree.short)
theorem fullLedger_2_2_2_0_2_0_0_valid : check fullLedger_2_2_2_0_2_0_0 3250 3312 3250 3312=true := by
  decide +kernel

def fullLedger_2_2_2_0_2_0_1 : Tree := (.second (.first (.axis 1052 1060 true) (.first (.axis 1055 1060 true) (.second Tree.short (.axis 1057 1061 true)))) (.first (.axis 1052 1064 false) (.axis 1056 1064 false)))
theorem fullLedger_2_2_2_0_2_0_1_valid : check fullLedger_2_2_2_0_2_0_1 3250 3312 3312 3375=true := by
  decide +kernel

def fullLedger_2_2_2_0_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 1059 1063 false) Tree.short) (.axis 1060 1065 false)) Tree.short)
theorem fullLedger_2_2_2_0_2_0_2_valid : check fullLedger_2_2_2_0_2_0_2 3312 3375 3312 3375=true := by
  decide +kernel

def fullLedger_2_2_2_0_2_0 : Tree := (.square fullLedger_2_2_2_0_2_0_0 fullLedger_2_2_2_0_2_0_1 fullLedger_2_2_2_0_2_0_2)
theorem fullLedger_2_2_2_0_2_0_valid : check fullLedger_2_2_2_0_2_0 3250 3375 3250 3375=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_2_0_0_valid,fullLedger_2_2_2_0_2_0_1_valid⟩,fullLedger_2_2_2_0_2_0_2_valid⟩⟩

def fullLedger_2_2_2_0_2_1_0 : Tree := (.second (.first (.axis 1052 1070 false) (.second (.axis 1056 1068 false) (.axis 1056 1072 false))) (.axis 1054 1078 false))
theorem fullLedger_2_2_2_0_2_1_0_valid : check fullLedger_2_2_2_0_2_1_0 3250 3312 3375 3500=true := by
  decide +kernel

def fullLedger_2_2_2_0_2_1_1 : Tree := (.second (.first (.second (.first (.axis 1059 1068 false) (.axis 1061 1068 true)) (.axis 1060 1072 true)) (.second (.first (.axis 1063 1068 true) (.second Tree.short (.axis 1065 1069 true))) (.axis 1064 1072 true))) (.first (.axis 1060 1078 false) (.axis 1064 1078 true)))
theorem fullLedger_2_2_2_0_2_1_1_valid : check fullLedger_2_2_2_0_2_1_1 3312 3375 3375 3500=true := by
  decide +kernel

def fullLedger_2_2_2_0_2_1 : Tree := (.first fullLedger_2_2_2_0_2_1_0 fullLedger_2_2_2_0_2_1_1)
theorem fullLedger_2_2_2_0_2_1_valid : check fullLedger_2_2_2_0_2_1 3250 3375 3375 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_2_1_0_valid,fullLedger_2_2_2_0_2_1_1_valid⟩

def fullLedger_2_2_2_0_2_2_0 : Tree := (.square Tree.short (.first (.axis 1067 1072 true) (.second Tree.short (.axis 1069 1073 true))) Tree.short)
theorem fullLedger_2_2_2_0_2_2_0_valid : check fullLedger_2_2_2_0_2_2_0 3375 3437 3375 3437=true := by
  decide +kernel

def fullLedger_2_2_2_0_2_2_1 : Tree := (.second (.first (.axis 1068 1076 true) (.first (.axis 1071 1076 false) (.second Tree.short (.axis 1073 1077 false)))) (.first (.axis 1068 1080 false) (.axis 1072 1080 false)))
theorem fullLedger_2_2_2_0_2_2_1_valid : check fullLedger_2_2_2_0_2_2_1 3375 3437 3437 3500=true := by
  decide +kernel

def fullLedger_2_2_2_0_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 1075 1079 false) Tree.short) (.axis 1076 1081 true)) Tree.short)
theorem fullLedger_2_2_2_0_2_2_2_valid : check fullLedger_2_2_2_0_2_2_2 3437 3500 3437 3500=true := by
  decide +kernel

def fullLedger_2_2_2_0_2_2 : Tree := (.square fullLedger_2_2_2_0_2_2_0 fullLedger_2_2_2_0_2_2_1 fullLedger_2_2_2_0_2_2_2)
theorem fullLedger_2_2_2_0_2_2_valid : check fullLedger_2_2_2_0_2_2 3375 3500 3375 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_2_2_0_valid,fullLedger_2_2_2_0_2_2_1_valid⟩,fullLedger_2_2_2_0_2_2_2_valid⟩⟩

def fullLedger_2_2_2_0_2 : Tree := (.square fullLedger_2_2_2_0_2_0 fullLedger_2_2_2_0_2_1 fullLedger_2_2_2_0_2_2)
theorem fullLedger_2_2_2_0_2_valid : check fullLedger_2_2_2_0_2 3250 3500 3250 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_2_0_valid,fullLedger_2_2_2_0_2_1_valid⟩,fullLedger_2_2_2_0_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
