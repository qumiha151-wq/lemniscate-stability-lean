import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_0_0_2_2_0_0 : Tree := (.square Tree.short (.first (.axis 607 612 true) (.second Tree.short (.axis 609 613 true))) Tree.short)
theorem fullLedger_2_0_0_2_2_0_0_valid : check fullLedger_2_0_0_2_2_0_0 750 812 750 812=true := by
  decide +kernel

def fullLedger_2_0_0_2_2_0_1 : Tree := (.second (.first (.axis 608 616 true) (.first (.axis 611 616 true) (.second Tree.short (.axis 613 617 false)))) (.first (.axis 608 620 false) (.axis 612 620 false)))
theorem fullLedger_2_0_0_2_2_0_1_valid : check fullLedger_2_0_0_2_2_0_1 750 812 812 875=true := by
  decide +kernel

def fullLedger_2_0_0_2_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 615 619 false) Tree.short) (.axis 616 621 true)) Tree.short)
theorem fullLedger_2_0_0_2_2_0_2_valid : check fullLedger_2_0_0_2_2_0_2 812 875 812 875=true := by
  decide +kernel

def fullLedger_2_0_0_2_2_0 : Tree := (.square fullLedger_2_0_0_2_2_0_0 fullLedger_2_0_0_2_2_0_1 fullLedger_2_0_0_2_2_0_2)
theorem fullLedger_2_0_0_2_2_0_valid : check fullLedger_2_0_0_2_2_0 750 875 750 875=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_2_0_0_valid,fullLedger_2_0_0_2_2_0_1_valid⟩,fullLedger_2_0_0_2_2_0_2_valid⟩⟩

def fullLedger_2_0_0_2_2_1_0 : Tree := (.second (.first (.axis 608 626 false) (.second (.axis 612 624 false) (.axis 612 628 false))) (.axis 610 634 false))
theorem fullLedger_2_0_0_2_2_1_0_valid : check fullLedger_2_0_0_2_2_1_0 750 812 875 1000=true := by
  decide +kernel

def fullLedger_2_0_0_2_2_1_1 : Tree := (.second (.first (.axis 616 626 true) (.second (.first (.axis 619 624 true) (.second Tree.short (.axis 621 625 true))) (.axis 620 628 true))) (.first (.axis 616 634 false) (.second (.axis 620 632 false) (.axis 620 636 false))))
theorem fullLedger_2_0_0_2_2_1_1_valid : check fullLedger_2_0_0_2_2_1_1 812 875 875 1000=true := by
  decide +kernel

def fullLedger_2_0_0_2_2_1 : Tree := (.first fullLedger_2_0_0_2_2_1_0 fullLedger_2_0_0_2_2_1_1)
theorem fullLedger_2_0_0_2_2_1_valid : check fullLedger_2_0_0_2_2_1 750 875 875 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_2_1_0_valid,fullLedger_2_0_0_2_2_1_1_valid⟩

def fullLedger_2_0_0_2_2_2_0 : Tree := (.square Tree.short (.first (.axis 623 628 true) (.second Tree.short (.axis 625 629 false))) Tree.short)
theorem fullLedger_2_0_0_2_2_2_0_valid : check fullLedger_2_0_0_2_2_2_0 875 937 875 937=true := by
  decide +kernel

def fullLedger_2_0_0_2_2_2_1 : Tree := (.second (.first (.axis 624 632 false) (.first (.axis 627 632 false) (.second Tree.short (.axis 629 633 false)))) (.first (.axis 624 636 false) (.axis 628 636 false)))
theorem fullLedger_2_0_0_2_2_2_1_valid : check fullLedger_2_0_0_2_2_2_1 875 937 937 1000=true := by
  decide +kernel

def fullLedger_2_0_0_2_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 631 635 true) Tree.short) (.axis 632 637 true)) Tree.short)
theorem fullLedger_2_0_0_2_2_2_2_valid : check fullLedger_2_0_0_2_2_2_2 937 1000 937 1000=true := by
  decide +kernel

def fullLedger_2_0_0_2_2_2 : Tree := (.square fullLedger_2_0_0_2_2_2_0 fullLedger_2_0_0_2_2_2_1 fullLedger_2_0_0_2_2_2_2)
theorem fullLedger_2_0_0_2_2_2_valid : check fullLedger_2_0_0_2_2_2 875 1000 875 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_2_2_0_valid,fullLedger_2_0_0_2_2_2_1_valid⟩,fullLedger_2_0_0_2_2_2_2_valid⟩⟩

def fullLedger_2_0_0_2_2 : Tree := (.square fullLedger_2_0_0_2_2_0 fullLedger_2_0_0_2_2_1 fullLedger_2_0_0_2_2_2)
theorem fullLedger_2_0_0_2_2_valid : check fullLedger_2_0_0_2_2 750 1000 750 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_2_0_valid,fullLedger_2_0_0_2_2_1_valid⟩,fullLedger_2_0_0_2_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
