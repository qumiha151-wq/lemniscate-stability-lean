import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_0_0_1_0 : Tree := (.second (.first (.axis 518 590 false) (.axis 534 590 false)) (.axis 526 622 false))
theorem fullLedger_2_0_0_1_0_valid : check fullLedger_2_0_0_1_0 0 250 500 1000=true := by
  decide +kernel

def fullLedger_2_0_0_1_1_0_0 : Tree := (.second (.first (.axis 546 582 false) (.axis 554 582 false)) (.axis 550 598 false))
theorem fullLedger_2_0_0_1_1_0_0_valid : check fullLedger_2_0_0_1_1_0_0 250 375 500 750=true := by
  decide +kernel

def fullLedger_2_0_0_1_1_0_1_0_0 : Tree := (.second (.first (.axis 560 578 false) (.axis 564 578 false)) (.axis 562 586 false))
theorem fullLedger_2_0_0_1_1_0_1_0_0_valid : check fullLedger_2_0_0_1_1_0_1_0_0 375 437 500 625=true := by
  decide +kernel

def fullLedger_2_0_0_1_1_0_1_0_1 : Tree := (.second (.first (.axis 568 578 true) (.second (.first (.axis 571 576 true) (.second Tree.short (.axis 573 577 true))) (.axis 572 580 true))) (.first (.axis 568 586 false) (.second (.axis 572 584 false) (.axis 572 588 false))))
theorem fullLedger_2_0_0_1_1_0_1_0_1_valid : check fullLedger_2_0_0_1_1_0_1_0_1 437 500 500 625=true := by
  decide +kernel

def fullLedger_2_0_0_1_1_0_1_0 : Tree := (.first fullLedger_2_0_0_1_1_0_1_0_0 fullLedger_2_0_0_1_1_0_1_0_1)
theorem fullLedger_2_0_0_1_1_0_1_0_valid : check fullLedger_2_0_0_1_1_0_1_0 375 500 500 625=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_1_1_0_1_0_0_valid,fullLedger_2_0_0_1_1_0_1_0_1_valid⟩

def fullLedger_2_0_0_1_1_0_1_1 : Tree := (.first (.axis 562 598 false) (.second (.axis 570 594 false) (.axis 570 602 false)))
theorem fullLedger_2_0_0_1_1_0_1_1_valid : check fullLedger_2_0_0_1_1_0_1_1 375 500 625 750=true := by
  decide +kernel

def fullLedger_2_0_0_1_1_0_1 : Tree := (.second fullLedger_2_0_0_1_1_0_1_0 fullLedger_2_0_0_1_1_0_1_1)
theorem fullLedger_2_0_0_1_1_0_1_valid : check fullLedger_2_0_0_1_1_0_1 375 500 500 750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_1_1_0_1_0_valid,fullLedger_2_0_0_1_1_0_1_1_valid⟩

def fullLedger_2_0_0_1_1_0 : Tree := (.first fullLedger_2_0_0_1_1_0_0 fullLedger_2_0_0_1_1_0_1)
theorem fullLedger_2_0_0_1_1_0_valid : check fullLedger_2_0_0_1_1_0 250 500 500 750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_1_1_0_0_valid,fullLedger_2_0_0_1_1_0_1_valid⟩

def fullLedger_2_0_0_1_1_1 : Tree := (.first (.axis 550 622 false) (.axis 566 622 false))
theorem fullLedger_2_0_0_1_1_1_valid : check fullLedger_2_0_0_1_1_1 250 500 750 1000=true := by
  decide +kernel

def fullLedger_2_0_0_1_1 : Tree := (.second fullLedger_2_0_0_1_1_0 fullLedger_2_0_0_1_1_1)
theorem fullLedger_2_0_0_1_1_valid : check fullLedger_2_0_0_1_1 250 500 500 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_1_1_0_valid,fullLedger_2_0_0_1_1_1_valid⟩

def fullLedger_2_0_0_1 : Tree := (.first fullLedger_2_0_0_1_0 fullLedger_2_0_0_1_1)
theorem fullLedger_2_0_0_1_valid : check fullLedger_2_0_0_1 0 500 500 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_1_0_valid,fullLedger_2_0_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
