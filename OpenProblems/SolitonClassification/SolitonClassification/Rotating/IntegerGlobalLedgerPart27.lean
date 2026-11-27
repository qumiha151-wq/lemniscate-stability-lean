import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_0_0_2_0_0_0 : Tree := (.square Tree.short (.first (.axis 575 580 true) (.second Tree.short (.axis 577 581 false))) Tree.short)
theorem fullLedger_2_0_0_2_0_0_0_valid : check fullLedger_2_0_0_2_0_0_0 500 562 500 562=true := by
  decide +kernel

def fullLedger_2_0_0_2_0_0_1 : Tree := (.second (.first (.axis 576 584 false) (.first (.axis 579 584 false) (.second Tree.short (.axis 581 585 true)))) (.axis 578 588 true))
theorem fullLedger_2_0_0_2_0_0_1_valid : check fullLedger_2_0_0_2_0_0_1 500 562 562 625=true := by
  decide +kernel

def fullLedger_2_0_0_2_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 583 587 true) Tree.short) (.axis 584 589 true)) Tree.short)
theorem fullLedger_2_0_0_2_0_0_2_valid : check fullLedger_2_0_0_2_0_0_2 562 625 562 625=true := by
  decide +kernel

def fullLedger_2_0_0_2_0_0 : Tree := (.square fullLedger_2_0_0_2_0_0_0 fullLedger_2_0_0_2_0_0_1 fullLedger_2_0_0_2_0_0_2)
theorem fullLedger_2_0_0_2_0_0_valid : check fullLedger_2_0_0_2_0_0 500 625 500 625=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_0_0_0_valid,fullLedger_2_0_0_2_0_0_1_valid⟩,fullLedger_2_0_0_2_0_0_2_valid⟩⟩

def fullLedger_2_0_0_2_0_1_0 : Tree := (.second (.axis 578 594 false) (.axis 578 602 false))
theorem fullLedger_2_0_0_2_0_1_0_valid : check fullLedger_2_0_0_2_0_1_0 500 562 625 750=true := by
  decide +kernel

def fullLedger_2_0_0_2_0_1_1 : Tree := (.second (.first (.second (.axis 584 592 true) (.axis 584 596 false)) (.second (.first (.axis 587 592 false) (.second Tree.short (.axis 589 593 false))) (.axis 588 596 false))) (.first (.axis 584 602 false) (.axis 588 602 false)))
theorem fullLedger_2_0_0_2_0_1_1_valid : check fullLedger_2_0_0_2_0_1_1 562 625 625 750=true := by
  decide +kernel

def fullLedger_2_0_0_2_0_1 : Tree := (.first fullLedger_2_0_0_2_0_1_0 fullLedger_2_0_0_2_0_1_1)
theorem fullLedger_2_0_0_2_0_1_valid : check fullLedger_2_0_0_2_0_1 500 625 625 750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_0_1_0_valid,fullLedger_2_0_0_2_0_1_1_valid⟩

def fullLedger_2_0_0_2_0_2_0 : Tree := (.square Tree.short (.first (.axis 591 596 false) (.second Tree.short (.axis 593 597 true))) Tree.short)
theorem fullLedger_2_0_0_2_0_2_0_valid : check fullLedger_2_0_0_2_0_2_0 625 687 625 687=true := by
  decide +kernel

def fullLedger_2_0_0_2_0_2_1 : Tree := (.second (.first (.axis 592 600 true) (.first (.axis 595 600 true) (.second Tree.short (.axis 597 601 true)))) (.axis 594 604 true))
theorem fullLedger_2_0_0_2_0_2_1_valid : check fullLedger_2_0_0_2_0_2_1 625 687 687 750=true := by
  decide +kernel

def fullLedger_2_0_0_2_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 599 603 true) Tree.short) (.axis 600 605 false)) Tree.short)
theorem fullLedger_2_0_0_2_0_2_2_valid : check fullLedger_2_0_0_2_0_2_2 687 750 687 750=true := by
  decide +kernel

def fullLedger_2_0_0_2_0_2 : Tree := (.square fullLedger_2_0_0_2_0_2_0 fullLedger_2_0_0_2_0_2_1 fullLedger_2_0_0_2_0_2_2)
theorem fullLedger_2_0_0_2_0_2_valid : check fullLedger_2_0_0_2_0_2 625 750 625 750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_0_2_0_valid,fullLedger_2_0_0_2_0_2_1_valid⟩,fullLedger_2_0_0_2_0_2_2_valid⟩⟩

def fullLedger_2_0_0_2_0 : Tree := (.square fullLedger_2_0_0_2_0_0 fullLedger_2_0_0_2_0_1 fullLedger_2_0_0_2_0_2)
theorem fullLedger_2_0_0_2_0_valid : check fullLedger_2_0_0_2_0 500 750 500 750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_0_0_valid,fullLedger_2_0_0_2_0_1_valid⟩,fullLedger_2_0_0_2_0_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
