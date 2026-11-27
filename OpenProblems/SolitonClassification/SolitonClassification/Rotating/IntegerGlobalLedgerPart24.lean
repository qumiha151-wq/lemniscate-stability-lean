import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_0_0_0_1_0 : Tree := (.second (.first (.axis 514 550 false) (.axis 522 550 false)) (.axis 518 566 false))
theorem fullLedger_2_0_0_0_1_0_valid : check fullLedger_2_0_0_0_1_0 0 125 250 500=true := by
  decide +kernel

def fullLedger_2_0_0_0_1_1_0_0 : Tree := (.second (.axis 530 546 false) (.axis 530 554 false))
theorem fullLedger_2_0_0_0_1_1_0_0_valid : check fullLedger_2_0_0_0_1_1_0_0 125 187 250 375=true := by
  decide +kernel

def fullLedger_2_0_0_0_1_1_0_1 : Tree := (.second (.first (.axis 536 546 true) (.second (.first (.axis 539 544 true) (.second Tree.short (.axis 541 545 false))) (.axis 540 548 false))) (.first (.axis 536 554 false) (.second (.axis 540 552 false) (.axis 540 556 false))))
theorem fullLedger_2_0_0_0_1_1_0_1_valid : check fullLedger_2_0_0_0_1_1_0_1 187 250 250 375=true := by
  decide +kernel

def fullLedger_2_0_0_0_1_1_0 : Tree := (.first fullLedger_2_0_0_0_1_1_0_0 fullLedger_2_0_0_0_1_1_0_1)
theorem fullLedger_2_0_0_0_1_1_0_valid : check fullLedger_2_0_0_0_1_1_0 125 250 250 375=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_1_1_0_0_valid,fullLedger_2_0_0_0_1_1_0_1_valid⟩

def fullLedger_2_0_0_0_1_1_1 : Tree := (.first (.axis 530 566 false) (.second (.axis 538 562 false) (.axis 538 570 false)))
theorem fullLedger_2_0_0_0_1_1_1_valid : check fullLedger_2_0_0_0_1_1_1 125 250 375 500=true := by
  decide +kernel

def fullLedger_2_0_0_0_1_1 : Tree := (.second fullLedger_2_0_0_0_1_1_0 fullLedger_2_0_0_0_1_1_1)
theorem fullLedger_2_0_0_0_1_1_valid : check fullLedger_2_0_0_0_1_1 125 250 250 500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_1_1_0_valid,fullLedger_2_0_0_0_1_1_1_valid⟩

def fullLedger_2_0_0_0_1 : Tree := (.first fullLedger_2_0_0_0_1_0 fullLedger_2_0_0_0_1_1)
theorem fullLedger_2_0_0_0_1_valid : check fullLedger_2_0_0_0_1 0 250 250 500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_1_0_valid,fullLedger_2_0_0_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
