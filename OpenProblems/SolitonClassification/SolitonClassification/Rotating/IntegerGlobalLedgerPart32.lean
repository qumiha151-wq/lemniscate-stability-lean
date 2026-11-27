import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_0_2_1_0 : Tree := (.second (.first (.axis 646 747 false) (.second (.axis 662 737 false) (.axis 662 769 false))) (.axis 654 816 false))
theorem fullLedger_2_0_2_1_0_valid : check fullLedger_2_0_2_1_0 1000 1250 1500 2000=true := by
  decide +kernel

def fullLedger_2_0_2_1_1_0_0 : Tree := (.second (.first (.axis 674 737 false) (.axis 682 737 false)) (.axis 678 769 false))
theorem fullLedger_2_0_2_1_1_0_0_valid : check fullLedger_2_0_2_1_1_0_0 1250 1375 1500 1750=true := by
  decide +kernel

def fullLedger_2_0_2_1_1_0_1_0 : Tree := (.first (.second (.axis 700 733 false) (.axis 700 741 false)) (.second (.first (.axis 723 733 false) (.second (.first (.axis 726 731 false) (.second Tree.short (.axis 728 732 false))) (.axis 727 735 false))) (.first (.axis 723 741 false) (.axis 727 741 true))))
theorem fullLedger_2_0_2_1_1_0_1_0_valid : check fullLedger_2_0_2_1_1_0_1_0 1375 1500 1500 1625=true := by
  decide +kernel

def fullLedger_2_0_2_1_1_0_1_1 : Tree := (.first (.axis 700 769 false) (.axis 725 769 false))
theorem fullLedger_2_0_2_1_1_0_1_1_valid : check fullLedger_2_0_2_1_1_0_1_1 1375 1500 1625 1750=true := by
  decide +kernel

def fullLedger_2_0_2_1_1_0_1 : Tree := (.second fullLedger_2_0_2_1_1_0_1_0 fullLedger_2_0_2_1_1_0_1_1)
theorem fullLedger_2_0_2_1_1_0_1_valid : check fullLedger_2_0_2_1_1_0_1 1375 1500 1500 1750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_1_1_0_1_0_valid,fullLedger_2_0_2_1_1_0_1_1_valid⟩

def fullLedger_2_0_2_1_1_0 : Tree := (.first fullLedger_2_0_2_1_1_0_0 fullLedger_2_0_2_1_1_0_1)
theorem fullLedger_2_0_2_1_1_0_valid : check fullLedger_2_0_2_1_1_0 1250 1500 1500 1750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_1_1_0_0_valid,fullLedger_2_0_2_1_1_0_1_valid⟩

def fullLedger_2_0_2_1_1_1 : Tree := (.first (.axis 678 816 false) (.axis 721 816 false))
theorem fullLedger_2_0_2_1_1_1_valid : check fullLedger_2_0_2_1_1_1 1250 1500 1750 2000=true := by
  decide +kernel

def fullLedger_2_0_2_1_1 : Tree := (.second fullLedger_2_0_2_1_1_0 fullLedger_2_0_2_1_1_1)
theorem fullLedger_2_0_2_1_1_valid : check fullLedger_2_0_2_1_1 1250 1500 1500 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_1_1_0_valid,fullLedger_2_0_2_1_1_1_valid⟩

def fullLedger_2_0_2_1 : Tree := (.first fullLedger_2_0_2_1_0 fullLedger_2_0_2_1_1)
theorem fullLedger_2_0_2_1_valid : check fullLedger_2_0_2_1 1000 1500 1500 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_1_0_valid,fullLedger_2_0_2_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
