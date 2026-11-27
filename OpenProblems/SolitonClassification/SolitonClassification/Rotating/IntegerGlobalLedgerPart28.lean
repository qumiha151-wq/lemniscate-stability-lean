import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_0_0_2_1_0 : Tree := (.second (.first (.axis 578 614 false) (.axis 586 614 false)) (.axis 582 630 false))
theorem fullLedger_2_0_0_2_1_0_valid : check fullLedger_2_0_0_2_1_0 500 625 750 1000=true := by
  decide +kernel

def fullLedger_2_0_0_2_1_1_0_0 : Tree := (.second (.first (.axis 592 610 false) (.second (.axis 596 608 false) (.axis 596 612 false))) (.axis 594 618 false))
theorem fullLedger_2_0_0_2_1_1_0_0_valid : check fullLedger_2_0_0_2_1_1_0_0 625 687 750 875=true := by
  decide +kernel

def fullLedger_2_0_0_2_1_1_0_1 : Tree := (.second (.first (.second (.axis 600 608 false) (.axis 600 612 false)) (.second (.first (.axis 603 608 false) (.second Tree.short (.axis 605 609 true))) (.axis 604 612 true))) (.axis 602 618 false))
theorem fullLedger_2_0_0_2_1_1_0_1_valid : check fullLedger_2_0_0_2_1_1_0_1 687 750 750 875=true := by
  decide +kernel

def fullLedger_2_0_0_2_1_1_0 : Tree := (.first fullLedger_2_0_0_2_1_1_0_0 fullLedger_2_0_0_2_1_1_0_1)
theorem fullLedger_2_0_0_2_1_1_0_valid : check fullLedger_2_0_0_2_1_1_0 625 750 750 875=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_1_1_0_0_valid,fullLedger_2_0_0_2_1_1_0_1_valid⟩

def fullLedger_2_0_0_2_1_1_1 : Tree := (.first (.axis 594 630 false) (.axis 602 630 false))
theorem fullLedger_2_0_0_2_1_1_1_valid : check fullLedger_2_0_0_2_1_1_1 625 750 875 1000=true := by
  decide +kernel

def fullLedger_2_0_0_2_1_1 : Tree := (.second fullLedger_2_0_0_2_1_1_0 fullLedger_2_0_0_2_1_1_1)
theorem fullLedger_2_0_0_2_1_1_valid : check fullLedger_2_0_0_2_1_1 625 750 750 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_1_1_0_valid,fullLedger_2_0_0_2_1_1_1_valid⟩

def fullLedger_2_0_0_2_1 : Tree := (.first fullLedger_2_0_0_2_1_0 fullLedger_2_0_0_2_1_1)
theorem fullLedger_2_0_0_2_1_valid : check fullLedger_2_0_0_2_1 500 750 750 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_1_0_valid,fullLedger_2_0_0_2_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
