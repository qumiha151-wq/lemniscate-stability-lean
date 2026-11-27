import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_1_0_0_0 : Tree := (.first (.second (.axis 526 1034 false) (.first (.axis 518 1066 false) (.axis 534 1066 false))) (.second (.first (.axis 550 1034 false) (.axis 566 1034 false)) (.first (.second (.axis 550 1058 false) (.axis 550 1074 false)) (.axis 566 1066 true))))
theorem fullLedger_2_1_1_0_0_0_valid : check fullLedger_2_1_1_0_0_0 0 500 3000 3500=true := by
  decide +kernel

def fullLedger_2_1_1_0_0_1_0 : Tree := (.second (.first (.second (.axis 582 1026 false) (.first (.axis 578 1042 false) (.axis 586 1042 false))) (.second (.axis 598 1026 false) (.axis 598 1042 true))) (.first (.second (.axis 582 1058 true) (.axis 582 1074 true)) (.second (.axis 598 1058 true) (.axis 598 1074 true))))
theorem fullLedger_2_1_1_0_0_1_0_valid : check fullLedger_2_1_1_0_0_1_0 500 750 3000 3500=true := by
  decide +kernel

def fullLedger_2_1_1_0_0_1_1 : Tree := (.second (.first (.second (.axis 614 1026 true) (.axis 614 1042 true)) (.second (.axis 630 1026 true) (.first (.axis 626 1042 true) (.axis 634 1042 true)))) (.first (.axis 614 1066 true) (.second (.axis 630 1058 true) (.axis 630 1074 false))))
theorem fullLedger_2_1_1_0_0_1_1_valid : check fullLedger_2_1_1_0_0_1_1 750 1000 3000 3500=true := by
  decide +kernel

def fullLedger_2_1_1_0_0_1 : Tree := (.first fullLedger_2_1_1_0_0_1_0 fullLedger_2_1_1_0_0_1_1)
theorem fullLedger_2_1_1_0_0_1_valid : check fullLedger_2_1_1_0_0_1 500 1000 3000 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_1_0_0_1_0_valid,fullLedger_2_1_1_0_0_1_1_valid⟩

def fullLedger_2_1_1_0_0 : Tree := (.first fullLedger_2_1_1_0_0_0 fullLedger_2_1_1_0_0_1)
theorem fullLedger_2_1_1_0_0_valid : check fullLedger_2_1_1_0_0 0 1000 3000 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_1_0_0_0_valid,fullLedger_2_1_1_0_0_1_valid⟩

def fullLedger_2_1_1_0_1_0 : Tree := (.second (.first (.axis 526 1098 true) (.first (.axis 550 1098 true) (.axis 566 1098 true))) (.first (.second (.axis 526 1122 true) (.axis 526 1138 true)) (.second (.axis 558 1122 true) (.axis 558 1138 true))))
theorem fullLedger_2_1_1_0_1_0_valid : check fullLedger_2_1_1_0_1_0 0 500 3500 4001=true := by
  decide +kernel

def fullLedger_2_1_1_0_1_1 : Tree := (.second (.first (.axis 590 1098 true) (.first (.axis 614 1098 true) (.axis 630 1098 false))) (.first (.second (.axis 590 1122 true) (.axis 590 1138 false)) (.axis 622 1130 false)))
theorem fullLedger_2_1_1_0_1_1_valid : check fullLedger_2_1_1_0_1_1 500 1000 3500 4001=true := by
  decide +kernel

def fullLedger_2_1_1_0_1 : Tree := (.first fullLedger_2_1_1_0_1_0 fullLedger_2_1_1_0_1_1)
theorem fullLedger_2_1_1_0_1_valid : check fullLedger_2_1_1_0_1 0 1000 3500 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_1_0_1_0_valid,fullLedger_2_1_1_0_1_1_valid⟩

def fullLedger_2_1_1_0 : Tree := (.second fullLedger_2_1_1_0_0 fullLedger_2_1_1_0_1)
theorem fullLedger_2_1_1_0_valid : check fullLedger_2_1_1_0 0 1000 3000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_1_0_0_valid,fullLedger_2_1_1_0_1_valid⟩

def fullLedger_2_1_1_1_0_0_0 : Tree := (.second (.first (.second (.axis 646 1026 true) (.axis 646 1042 true)) (.second (.axis 662 1026 true) (.axis 662 1042 false))) (.first (.axis 646 1066 false) (.axis 662 1066 false)))
theorem fullLedger_2_1_1_1_0_0_0_valid : check fullLedger_2_1_1_1_0_0_0 1000 1250 3000 3500=true := by
  decide +kernel

def fullLedger_2_1_1_1_0_0_1 : Tree := (.second (.first (.second (.axis 678 1026 false) (.axis 678 1042 false)) (.axis 721 1034 false)) (.axis 686 1066 false))
theorem fullLedger_2_1_1_1_0_0_1_valid : check fullLedger_2_1_1_1_0_0_1 1250 1500 3000 3500=true := by
  decide +kernel

def fullLedger_2_1_1_1_0_0 : Tree := (.first fullLedger_2_1_1_1_0_0_0 fullLedger_2_1_1_1_0_0_1)
theorem fullLedger_2_1_1_1_0_0_valid : check fullLedger_2_1_1_1_0_0 1000 1500 3000 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_1_1_0_0_0_valid,fullLedger_2_1_1_1_0_0_1_valid⟩

def fullLedger_2_1_1_1_0_1 : Tree := (.first (.second (.axis 747 1034 false) (.axis 747 1066 false)) (.axis 816 1050 false))
theorem fullLedger_2_1_1_1_0_1_valid : check fullLedger_2_1_1_1_0_1 1500 2000 3000 3500=true := by
  decide +kernel

def fullLedger_2_1_1_1_0 : Tree := (.first fullLedger_2_1_1_1_0_0 fullLedger_2_1_1_1_0_1)
theorem fullLedger_2_1_1_1_0_valid : check fullLedger_2_1_1_1_0 1000 2000 3000 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_1_1_0_0_valid,fullLedger_2_1_1_1_0_1_valid⟩

def fullLedger_2_1_1_1_1 : Tree := (.first (.second (.first (.axis 654 1098 false) (.axis 686 1098 false)) (.axis 670 1130 false)) (.axis 790 1114 false))
theorem fullLedger_2_1_1_1_1_valid : check fullLedger_2_1_1_1_1 1000 2000 3500 4001=true := by
  decide +kernel

def fullLedger_2_1_1_1 : Tree := (.second fullLedger_2_1_1_1_0 fullLedger_2_1_1_1_1)
theorem fullLedger_2_1_1_1_valid : check fullLedger_2_1_1_1 1000 2000 3000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_1_1_0_valid,fullLedger_2_1_1_1_1_valid⟩

def fullLedger_2_1_1 : Tree := (.first fullLedger_2_1_1_0 fullLedger_2_1_1_1)
theorem fullLedger_2_1_1_valid : check fullLedger_2_1_1 0 2000 3000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_1_0_valid,fullLedger_2_1_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
