import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_0_0_0_2_0_0 : Tree := (.square Tree.short (.first (.axis 543 548 false) (.second Tree.short (.axis 545 549 false))) Tree.short)
theorem fullLedger_2_0_0_0_2_0_0_valid : check fullLedger_2_0_0_0_2_0_0 250 312 250 312=true := by
  decide +kernel

def fullLedger_2_0_0_0_2_0_1 : Tree := (.second (.first (.axis 544 552 true) (.first (.axis 547 552 true) (.second Tree.short (.axis 549 553 true)))) (.axis 546 556 true))
theorem fullLedger_2_0_0_0_2_0_1_valid : check fullLedger_2_0_0_0_2_0_1 250 312 312 375=true := by
  decide +kernel

def fullLedger_2_0_0_0_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 551 555 true) Tree.short) (.axis 552 557 false)) Tree.short)
theorem fullLedger_2_0_0_0_2_0_2_valid : check fullLedger_2_0_0_0_2_0_2 312 375 312 375=true := by
  decide +kernel

def fullLedger_2_0_0_0_2_0 : Tree := (.square fullLedger_2_0_0_0_2_0_0 fullLedger_2_0_0_0_2_0_1 fullLedger_2_0_0_0_2_0_2)
theorem fullLedger_2_0_0_0_2_0_valid : check fullLedger_2_0_0_0_2_0 250 375 250 375=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_2_0_0_valid,fullLedger_2_0_0_0_2_0_1_valid⟩,fullLedger_2_0_0_0_2_0_2_valid⟩⟩

def fullLedger_2_0_0_0_2_1_0 : Tree := (.second (.first (.axis 544 562 false) (.second (.axis 548 560 false) (.axis 548 564 false))) (.axis 546 570 false))
theorem fullLedger_2_0_0_0_2_1_0_valid : check fullLedger_2_0_0_0_2_1_0 250 312 375 500=true := by
  decide +kernel

def fullLedger_2_0_0_0_2_1_1 : Tree := (.second (.first (.second (.axis 552 560 false) (.axis 552 564 false)) (.second (.first (.axis 555 560 false) (.second Tree.short (.axis 557 561 true))) (.axis 556 564 true))) (.axis 554 570 false))
theorem fullLedger_2_0_0_0_2_1_1_valid : check fullLedger_2_0_0_0_2_1_1 312 375 375 500=true := by
  decide +kernel

def fullLedger_2_0_0_0_2_1 : Tree := (.first fullLedger_2_0_0_0_2_1_0 fullLedger_2_0_0_0_2_1_1)
theorem fullLedger_2_0_0_0_2_1_valid : check fullLedger_2_0_0_0_2_1 250 375 375 500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_2_1_0_valid,fullLedger_2_0_0_0_2_1_1_valid⟩

def fullLedger_2_0_0_0_2_2_0 : Tree := (.square Tree.short (.first (.axis 559 564 true) (.second Tree.short (.axis 561 565 true))) Tree.short)
theorem fullLedger_2_0_0_0_2_2_0_valid : check fullLedger_2_0_0_0_2_2_0 375 437 375 437=true := by
  decide +kernel

def fullLedger_2_0_0_0_2_2_1 : Tree := (.second (.first (.axis 560 568 true) (.first (.axis 563 568 true) (.second Tree.short (.axis 565 569 false)))) (.first (.axis 560 572 false) (.axis 564 572 false)))
theorem fullLedger_2_0_0_0_2_2_1_valid : check fullLedger_2_0_0_0_2_2_1 375 437 437 500=true := by
  decide +kernel

def fullLedger_2_0_0_0_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 567 571 false) Tree.short) (.axis 568 573 true)) Tree.short)
theorem fullLedger_2_0_0_0_2_2_2_valid : check fullLedger_2_0_0_0_2_2_2 437 500 437 500=true := by
  decide +kernel

def fullLedger_2_0_0_0_2_2 : Tree := (.square fullLedger_2_0_0_0_2_2_0 fullLedger_2_0_0_0_2_2_1 fullLedger_2_0_0_0_2_2_2)
theorem fullLedger_2_0_0_0_2_2_valid : check fullLedger_2_0_0_0_2_2 375 500 375 500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_2_2_0_valid,fullLedger_2_0_0_0_2_2_1_valid⟩,fullLedger_2_0_0_0_2_2_2_valid⟩⟩

def fullLedger_2_0_0_0_2 : Tree := (.square fullLedger_2_0_0_0_2_0 fullLedger_2_0_0_0_2_1 fullLedger_2_0_0_0_2_2)
theorem fullLedger_2_0_0_0_2_valid : check fullLedger_2_0_0_0_2 250 500 250 500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_2_0_valid,fullLedger_2_0_0_0_2_1_valid⟩,fullLedger_2_0_0_0_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
