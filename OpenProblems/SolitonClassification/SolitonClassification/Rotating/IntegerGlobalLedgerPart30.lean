import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_0_1_0 : Tree := (.second (.first (.axis 526 670 false) (.axis 558 670 false)) (.axis 542 790 false))
theorem fullLedger_2_0_1_0_valid : check fullLedger_2_0_1_0 0 500 1000 2000=true := by
  decide +kernel

def fullLedger_2_0_1_1_0_0 : Tree := (.second (.first (.axis 582 654 false) (.axis 598 654 false)) (.axis 590 686 false))
theorem fullLedger_2_0_1_1_0_0_valid : check fullLedger_2_0_1_1_0_0 500 750 1000 1500=true := by
  decide +kernel

def fullLedger_2_0_1_1_0_1_0_0 : Tree := (.second (.axis 614 646 false) (.axis 614 662 false))
theorem fullLedger_2_0_1_1_0_1_0_0_valid : check fullLedger_2_0_1_1_0_1_0_0 750 875 1000 1250=true := by
  decide +kernel

def fullLedger_2_0_1_1_0_1_0_1_0_0 : Tree := (.second (.axis 626 642 false) (.axis 626 650 false))
theorem fullLedger_2_0_1_1_0_1_0_1_0_0_valid : check fullLedger_2_0_1_1_0_1_0_1_0_0 875 937 1000 1125=true := by
  decide +kernel

def fullLedger_2_0_1_1_0_1_0_1_0_1 : Tree := (.second (.first (.axis 632 642 true) (.second (.first (.axis 635 640 true) (.second Tree.short (.axis 637 641 true))) (.axis 636 644 false))) (.first (.axis 632 650 false) (.second (.axis 636 648 false) (.axis 636 652 false))))
theorem fullLedger_2_0_1_1_0_1_0_1_0_1_valid : check fullLedger_2_0_1_1_0_1_0_1_0_1 937 1000 1000 1125=true := by
  decide +kernel

def fullLedger_2_0_1_1_0_1_0_1_0 : Tree := (.first fullLedger_2_0_1_1_0_1_0_1_0_0 fullLedger_2_0_1_1_0_1_0_1_0_1)
theorem fullLedger_2_0_1_1_0_1_0_1_0_valid : check fullLedger_2_0_1_1_0_1_0_1_0 875 1000 1000 1125=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_1_1_0_1_0_1_0_0_valid,fullLedger_2_0_1_1_0_1_0_1_0_1_valid⟩

def fullLedger_2_0_1_1_0_1_0_1_1 : Tree := (.first (.axis 626 662 false) (.axis 634 662 false))
theorem fullLedger_2_0_1_1_0_1_0_1_1_valid : check fullLedger_2_0_1_1_0_1_0_1_1 875 1000 1125 1250=true := by
  decide +kernel

def fullLedger_2_0_1_1_0_1_0_1 : Tree := (.second fullLedger_2_0_1_1_0_1_0_1_0 fullLedger_2_0_1_1_0_1_0_1_1)
theorem fullLedger_2_0_1_1_0_1_0_1_valid : check fullLedger_2_0_1_1_0_1_0_1 875 1000 1000 1250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_1_1_0_1_0_1_0_valid,fullLedger_2_0_1_1_0_1_0_1_1_valid⟩

def fullLedger_2_0_1_1_0_1_0 : Tree := (.first fullLedger_2_0_1_1_0_1_0_0 fullLedger_2_0_1_1_0_1_0_1)
theorem fullLedger_2_0_1_1_0_1_0_valid : check fullLedger_2_0_1_1_0_1_0 750 1000 1000 1250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_1_1_0_1_0_0_valid,fullLedger_2_0_1_1_0_1_0_1_valid⟩

def fullLedger_2_0_1_1_0_1_1 : Tree := (.first (.axis 614 686 false) (.axis 630 686 false))
theorem fullLedger_2_0_1_1_0_1_1_valid : check fullLedger_2_0_1_1_0_1_1 750 1000 1250 1500=true := by
  decide +kernel

def fullLedger_2_0_1_1_0_1 : Tree := (.second fullLedger_2_0_1_1_0_1_0 fullLedger_2_0_1_1_0_1_1)
theorem fullLedger_2_0_1_1_0_1_valid : check fullLedger_2_0_1_1_0_1 750 1000 1000 1500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_1_1_0_1_0_valid,fullLedger_2_0_1_1_0_1_1_valid⟩

def fullLedger_2_0_1_1_0 : Tree := (.first fullLedger_2_0_1_1_0_0 fullLedger_2_0_1_1_0_1)
theorem fullLedger_2_0_1_1_0_valid : check fullLedger_2_0_1_1_0 500 1000 1000 1500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_1_1_0_0_valid,fullLedger_2_0_1_1_0_1_valid⟩

def fullLedger_2_0_1_1_1 : Tree := (.first (.axis 590 790 false) (.axis 622 790 false))
theorem fullLedger_2_0_1_1_1_valid : check fullLedger_2_0_1_1_1 500 1000 1500 2000=true := by
  decide +kernel

def fullLedger_2_0_1_1 : Tree := (.second fullLedger_2_0_1_1_0 fullLedger_2_0_1_1_1)
theorem fullLedger_2_0_1_1_valid : check fullLedger_2_0_1_1 500 1000 1000 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_1_1_0_valid,fullLedger_2_0_1_1_1_valid⟩

def fullLedger_2_0_1 : Tree := (.first fullLedger_2_0_1_0 fullLedger_2_0_1_1)
theorem fullLedger_2_0_1_valid : check fullLedger_2_0_1 0 1000 1000 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_1_0_valid,fullLedger_2_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
