import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_1_0_0_0_0_0 : Tree := (.second (.first (.second (.axis 15 526 true) (.axis 15 558 true)) (.second (.axis 47 526 true) (.axis 47 558 false))) (.first (.second (.axis 15 590 false) (.axis 15 622 false)) (.axis 47 606 false)))
theorem fullLedger_1_0_0_0_0_0_valid : check fullLedger_1_0_0_0_0_0 (-4001) (-3501) 0 1000=true := by
  decide +kernel

def fullLedger_1_0_0_0_0_1 : Tree := (.second (.first (.second (.axis 79 526 false) (.axis 79 558 false)) (.axis 111 542 false)) (.axis 95 606 false))
theorem fullLedger_1_0_0_0_0_1_valid : check fullLedger_1_0_0_0_0_1 (-3501) (-3001) 0 1000=true := by
  decide +kernel

def fullLedger_1_0_0_0_0 : Tree := (.first fullLedger_1_0_0_0_0_0 fullLedger_1_0_0_0_0_1)
theorem fullLedger_1_0_0_0_0_valid : check fullLedger_1_0_0_0_0 (-4001) (-3001) 0 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_0_0_0_0_valid,fullLedger_1_0_0_0_0_1_valid⟩

def fullLedger_1_0_0_0_1 : Tree := (.first (.axis 31 729 false) (.axis 95 729 false))
theorem fullLedger_1_0_0_0_1_valid : check fullLedger_1_0_0_0_1 (-4001) (-3001) 1000 2000=true := by
  decide +kernel

def fullLedger_1_0_0_0 : Tree := (.second fullLedger_1_0_0_0_0 fullLedger_1_0_0_0_1)
theorem fullLedger_1_0_0_0_valid : check fullLedger_1_0_0_0 (-4001) (-3001) 0 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_0_0_0_valid,fullLedger_1_0_0_0_1_valid⟩

def fullLedger_1_0_0_1 : Tree := (.second (.first (.axis 159 574 false) (.axis 223 574 false)) (.axis 191 729 false))
theorem fullLedger_1_0_0_1_valid : check fullLedger_1_0_0_1 (-3001) (-2001) 0 2000=true := by
  decide +kernel

def fullLedger_1_0_0 : Tree := (.first fullLedger_1_0_0_0 fullLedger_1_0_0_1)
theorem fullLedger_1_0_0_valid : check fullLedger_1_0_0 (-4001) (-2001) 0 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_0_0_valid,fullLedger_1_0_0_1_valid⟩

def fullLedger_1_0_1_0 : Tree := (.first (.first (.axis 31 929 false) (.axis 95 929 false)) (.axis 191 929 false))
theorem fullLedger_1_0_1_0_valid : check fullLedger_1_0_1_0 (-4001) (-2001) 2000 3000=true := by
  decide +kernel

def fullLedger_1_0_1_1_0_0 : Tree := (.first (.first (.axis 15 1050 false) (.axis 47 1050 false)) (.axis 95 1050 false))
theorem fullLedger_1_0_1_1_0_0_valid : check fullLedger_1_0_1_1_0_0 (-4001) (-3001) 3000 3500=true := by
  decide +kernel

def fullLedger_1_0_1_1_0_1_0_0 : Tree := (.first (.first (.axis 7 1098 false) (.axis 23 1098 false)) (.axis 47 1098 false))
theorem fullLedger_1_0_1_1_0_1_0_0_valid : check fullLedger_1_0_1_1_0_1_0_0 (-4001) (-3501) 3500 3750=true := by
  decide +kernel

def fullLedger_1_0_1_1_0_1_0_1_0_0 : Tree := (.first (.first (.axis 3 1122 false) (.axis 11 1122 false)) (.axis 23 1122 false))
theorem fullLedger_1_0_1_1_0_1_0_1_0_0_valid : check fullLedger_1_0_1_1_0_1_0_1_0_0 (-4001) (-3751) 3750 3875=true := by
  decide +kernel

def fullLedger_1_0_1_1_0_1_0_1_0_1_0_0 : Tree := (.first (.second (.axis 3 1132 false) (.axis 3 1136 false)) (.axis 11 1134 false))
theorem fullLedger_1_0_1_1_0_1_0_1_0_1_0_0_valid : check fullLedger_1_0_1_1_0_1_0_1_0_1_0_0 (-4001) (-3876) 3875 3938=true := by
  decide +kernel

def fullLedger_1_0_1_1_0_1_0_1_0_1_0_1 : Tree := (.first (.second (.axis 3 1140 true) (.first (.second (.axis 1 1143 true) (.first Tree.short (.axis 2 1145 true))) (.axis 5 1144 false))) (.first (.second (.axis 9 1140 false) (.axis 9 1144 false)) (.axis 13 1142 false)))
theorem fullLedger_1_0_1_1_0_1_0_1_0_1_0_1_valid : check fullLedger_1_0_1_1_0_1_0_1_0_1_0_1 (-4001) (-3876) 3938 4001=true := by
  decide +kernel

def fullLedger_1_0_1_1_0_1_0_1_0_1_0 : Tree := (.second fullLedger_1_0_1_1_0_1_0_1_0_1_0_0 fullLedger_1_0_1_1_0_1_0_1_0_1_0_1)
theorem fullLedger_1_0_1_1_0_1_0_1_0_1_0_valid : check fullLedger_1_0_1_1_0_1_0_1_0_1_0 (-4001) (-3876) 3875 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_1_1_0_1_0_1_0_1_0_0_valid,fullLedger_1_0_1_1_0_1_0_1_0_1_0_1_valid⟩

def fullLedger_1_0_1_1_0_1_0_1_0_1_1 : Tree := (.second (.axis 23 1134 false) (.first (.axis 19 1142 false) (.axis 27 1142 false)))
theorem fullLedger_1_0_1_1_0_1_0_1_0_1_1_valid : check fullLedger_1_0_1_1_0_1_0_1_0_1_1 (-3876) (-3751) 3875 4001=true := by
  decide +kernel

def fullLedger_1_0_1_1_0_1_0_1_0_1 : Tree := (.first fullLedger_1_0_1_1_0_1_0_1_0_1_0 fullLedger_1_0_1_1_0_1_0_1_0_1_1)
theorem fullLedger_1_0_1_1_0_1_0_1_0_1_valid : check fullLedger_1_0_1_1_0_1_0_1_0_1 (-4001) (-3751) 3875 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_1_1_0_1_0_1_0_1_0_valid,fullLedger_1_0_1_1_0_1_0_1_0_1_1_valid⟩

def fullLedger_1_0_1_1_0_1_0_1_0 : Tree := (.second fullLedger_1_0_1_1_0_1_0_1_0_0 fullLedger_1_0_1_1_0_1_0_1_0_1)
theorem fullLedger_1_0_1_1_0_1_0_1_0_valid : check fullLedger_1_0_1_1_0_1_0_1_0 (-4001) (-3751) 3750 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_1_1_0_1_0_1_0_0_valid,fullLedger_1_0_1_1_0_1_0_1_0_1_valid⟩

def fullLedger_1_0_1_1_0_1_0_1_1 : Tree := (.second (.axis 47 1122 false) (.axis 47 1138 false))
theorem fullLedger_1_0_1_1_0_1_0_1_1_valid : check fullLedger_1_0_1_1_0_1_0_1_1 (-3751) (-3501) 3750 4001=true := by
  decide +kernel

def fullLedger_1_0_1_1_0_1_0_1 : Tree := (.first fullLedger_1_0_1_1_0_1_0_1_0 fullLedger_1_0_1_1_0_1_0_1_1)
theorem fullLedger_1_0_1_1_0_1_0_1_valid : check fullLedger_1_0_1_1_0_1_0_1 (-4001) (-3501) 3750 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_1_1_0_1_0_1_0_valid,fullLedger_1_0_1_1_0_1_0_1_1_valid⟩

def fullLedger_1_0_1_1_0_1_0 : Tree := (.second fullLedger_1_0_1_1_0_1_0_0 fullLedger_1_0_1_1_0_1_0_1)
theorem fullLedger_1_0_1_1_0_1_0_valid : check fullLedger_1_0_1_1_0_1_0 (-4001) (-3501) 3500 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_1_1_0_1_0_0_valid,fullLedger_1_0_1_1_0_1_0_1_valid⟩

def fullLedger_1_0_1_1_0_1_1 : Tree := (.second (.axis 95 1098 false) (.axis 95 1130 false))
theorem fullLedger_1_0_1_1_0_1_1_valid : check fullLedger_1_0_1_1_0_1_1 (-3501) (-3001) 3500 4001=true := by
  decide +kernel

def fullLedger_1_0_1_1_0_1 : Tree := (.first fullLedger_1_0_1_1_0_1_0 fullLedger_1_0_1_1_0_1_1)
theorem fullLedger_1_0_1_1_0_1_valid : check fullLedger_1_0_1_1_0_1 (-4001) (-3001) 3500 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_1_1_0_1_0_valid,fullLedger_1_0_1_1_0_1_1_valid⟩

def fullLedger_1_0_1_1_0 : Tree := (.second fullLedger_1_0_1_1_0_0 fullLedger_1_0_1_1_0_1)
theorem fullLedger_1_0_1_1_0_valid : check fullLedger_1_0_1_1_0 (-4001) (-3001) 3000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_1_1_0_0_valid,fullLedger_1_0_1_1_0_1_valid⟩

def fullLedger_1_0_1_1_1 : Tree := (.second (.axis 191 1050 false) (.axis 191 1114 false))
theorem fullLedger_1_0_1_1_1_valid : check fullLedger_1_0_1_1_1 (-3001) (-2001) 3000 4001=true := by
  decide +kernel

def fullLedger_1_0_1_1 : Tree := (.first fullLedger_1_0_1_1_0 fullLedger_1_0_1_1_1)
theorem fullLedger_1_0_1_1_valid : check fullLedger_1_0_1_1 (-4001) (-2001) 3000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_1_1_0_valid,fullLedger_1_0_1_1_1_valid⟩

def fullLedger_1_0_1 : Tree := (.second fullLedger_1_0_1_0 fullLedger_1_0_1_1)
theorem fullLedger_1_0_1_valid : check fullLedger_1_0_1 (-4001) (-2001) 2000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_1_0_valid,fullLedger_1_0_1_1_valid⟩

def fullLedger_1_0 : Tree := (.second fullLedger_1_0_0 fullLedger_1_0_1)
theorem fullLedger_1_0_valid : check fullLedger_1_0 (-4001) (-2001) 0 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_0_valid,fullLedger_1_0_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
