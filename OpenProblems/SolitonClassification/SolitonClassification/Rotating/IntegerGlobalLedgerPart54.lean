import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_2_2_0_0_0_0 : Tree := (.square Tree.short (.first (.axis 1019 1024 true) (.second Tree.short (.axis 1021 1025 true))) Tree.short)
theorem fullLedger_2_2_2_0_0_0_0_valid : check fullLedger_2_2_2_0_0_0_0 3000 3062 3000 3062=true := by
  decide +kernel

def fullLedger_2_2_2_0_0_0_1 : Tree := (.second (.first (.axis 1020 1028 true) (.first (.axis 1023 1028 true) (.second Tree.short (.axis 1025 1029 false)))) (.first (.axis 1020 1032 false) (.axis 1024 1032 false)))
theorem fullLedger_2_2_2_0_0_0_1_valid : check fullLedger_2_2_2_0_0_0_1 3000 3062 3062 3125=true := by
  decide +kernel

def fullLedger_2_2_2_0_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 1027 1031 false) Tree.short) (.axis 1028 1033 true)) Tree.short)
theorem fullLedger_2_2_2_0_0_0_2_valid : check fullLedger_2_2_2_0_0_0_2 3062 3125 3062 3125=true := by
  decide +kernel

def fullLedger_2_2_2_0_0_0 : Tree := (.square fullLedger_2_2_2_0_0_0_0 fullLedger_2_2_2_0_0_0_1 fullLedger_2_2_2_0_0_0_2)
theorem fullLedger_2_2_2_0_0_0_valid : check fullLedger_2_2_2_0_0_0 3000 3125 3000 3125=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_0_0_0_valid,fullLedger_2_2_2_0_0_0_1_valid⟩,fullLedger_2_2_2_0_0_0_2_valid⟩⟩

def fullLedger_2_2_2_0_0_1_0 : Tree := (.second (.axis 1022 1038 false) (.axis 1022 1046 false))
theorem fullLedger_2_2_2_0_0_1_0_valid : check fullLedger_2_2_2_0_0_1_0 3000 3062 3125 3250=true := by
  decide +kernel

def fullLedger_2_2_2_0_0_1_1 : Tree := (.second (.first (.axis 1028 1038 true) (.second (.first (.axis 1031 1036 true) (.second Tree.short (.axis 1033 1037 true))) (.axis 1032 1040 false))) (.first (.axis 1028 1046 false) (.second (.axis 1032 1044 false) (.axis 1032 1048 false))))
theorem fullLedger_2_2_2_0_0_1_1_valid : check fullLedger_2_2_2_0_0_1_1 3062 3125 3125 3250=true := by
  decide +kernel

def fullLedger_2_2_2_0_0_1 : Tree := (.first fullLedger_2_2_2_0_0_1_0 fullLedger_2_2_2_0_0_1_1)
theorem fullLedger_2_2_2_0_0_1_valid : check fullLedger_2_2_2_0_0_1 3000 3125 3125 3250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_0_1_0_valid,fullLedger_2_2_2_0_0_1_1_valid⟩

def fullLedger_2_2_2_0_0_2_0 : Tree := (.square Tree.short (.first (.axis 1035 1040 false) (.second Tree.short (.axis 1037 1041 false))) Tree.short)
theorem fullLedger_2_2_2_0_0_2_0_valid : check fullLedger_2_2_2_0_0_2_0 3125 3187 3125 3187=true := by
  decide +kernel

def fullLedger_2_2_2_0_0_2_1 : Tree := (.second (.first (.axis 1036 1044 false) (.first (.axis 1039 1044 true) (.second Tree.short (.axis 1041 1045 true)))) (.axis 1038 1048 true))
theorem fullLedger_2_2_2_0_0_2_1_valid : check fullLedger_2_2_2_0_0_2_1 3125 3187 3187 3250=true := by
  decide +kernel

def fullLedger_2_2_2_0_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 1043 1047 true) Tree.short) (.axis 1044 1049 true)) Tree.short)
theorem fullLedger_2_2_2_0_0_2_2_valid : check fullLedger_2_2_2_0_0_2_2 3187 3250 3187 3250=true := by
  decide +kernel

def fullLedger_2_2_2_0_0_2 : Tree := (.square fullLedger_2_2_2_0_0_2_0 fullLedger_2_2_2_0_0_2_1 fullLedger_2_2_2_0_0_2_2)
theorem fullLedger_2_2_2_0_0_2_valid : check fullLedger_2_2_2_0_0_2 3125 3250 3125 3250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_0_2_0_valid,fullLedger_2_2_2_0_0_2_1_valid⟩,fullLedger_2_2_2_0_0_2_2_valid⟩⟩

def fullLedger_2_2_2_0_0 : Tree := (.square fullLedger_2_2_2_0_0_0 fullLedger_2_2_2_0_0_1 fullLedger_2_2_2_0_0_2)
theorem fullLedger_2_2_2_0_0_valid : check fullLedger_2_2_2_0_0 3000 3250 3000 3250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_0_0_valid,fullLedger_2_2_2_0_0_1_valid⟩,fullLedger_2_2_2_0_0_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
