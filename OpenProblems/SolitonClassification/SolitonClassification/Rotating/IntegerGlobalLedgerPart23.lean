import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_0_0_0_0_0_0 : Tree := (.square Tree.short (.first (.axis 511 516 true) (.second Tree.short (.axis 513 517 true))) Tree.short)
theorem fullLedger_2_0_0_0_0_0_0_valid : check fullLedger_2_0_0_0_0_0_0 0 62 0 62=true := by
  decide +kernel

def fullLedger_2_0_0_0_0_0_1 : Tree := (.second (.first (.axis 512 520 true) (.first (.axis 515 520 true) (.second Tree.short (.axis 517 521 true)))) (.first (.axis 512 524 false) (.axis 516 524 false)))
theorem fullLedger_2_0_0_0_0_0_1_valid : check fullLedger_2_0_0_0_0_0_1 0 62 62 125=true := by
  decide +kernel

def fullLedger_2_0_0_0_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 519 523 false) Tree.short) (.axis 520 525 false)) Tree.short)
theorem fullLedger_2_0_0_0_0_0_2_valid : check fullLedger_2_0_0_0_0_0_2 62 125 62 125=true := by
  decide +kernel

def fullLedger_2_0_0_0_0_0 : Tree := (.square fullLedger_2_0_0_0_0_0_0 fullLedger_2_0_0_0_0_0_1 fullLedger_2_0_0_0_0_0_2)
theorem fullLedger_2_0_0_0_0_0_valid : check fullLedger_2_0_0_0_0_0 0 125 0 125=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_0_0_0_valid,fullLedger_2_0_0_0_0_0_1_valid⟩,fullLedger_2_0_0_0_0_0_2_valid⟩⟩

def fullLedger_2_0_0_0_0_1_0 : Tree := (.second (.first (.axis 512 530 false) (.second (.axis 516 528 false) (.axis 516 532 false))) (.axis 514 538 false))
theorem fullLedger_2_0_0_0_0_1_0_valid : check fullLedger_2_0_0_0_0_1_0 0 62 125 250=true := by
  decide +kernel

def fullLedger_2_0_0_0_0_1_1 : Tree := (.second (.first (.axis 520 530 true) (.second (.first (.axis 523 528 true) (.second Tree.short (.axis 525 529 true))) (.axis 524 532 true))) (.first (.axis 520 538 false) (.second (.axis 524 536 false) (.axis 524 540 false))))
theorem fullLedger_2_0_0_0_0_1_1_valid : check fullLedger_2_0_0_0_0_1_1 62 125 125 250=true := by
  decide +kernel

def fullLedger_2_0_0_0_0_1 : Tree := (.first fullLedger_2_0_0_0_0_1_0 fullLedger_2_0_0_0_0_1_1)
theorem fullLedger_2_0_0_0_0_1_valid : check fullLedger_2_0_0_0_0_1 0 125 125 250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_0_1_0_valid,fullLedger_2_0_0_0_0_1_1_valid⟩

def fullLedger_2_0_0_0_0_2_0 : Tree := (.square Tree.short (.first (.axis 527 532 true) (.second Tree.short (.axis 529 533 false))) Tree.short)
theorem fullLedger_2_0_0_0_0_2_0_valid : check fullLedger_2_0_0_0_0_2_0 125 187 125 187=true := by
  decide +kernel

def fullLedger_2_0_0_0_0_2_1 : Tree := (.second (.first (.axis 528 536 false) (.first (.axis 531 536 false) (.second Tree.short (.axis 533 537 false)))) (.first (.axis 528 540 false) (.axis 532 540 true)))
theorem fullLedger_2_0_0_0_0_2_1_valid : check fullLedger_2_0_0_0_0_2_1 125 187 187 250=true := by
  decide +kernel

def fullLedger_2_0_0_0_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 535 539 true) Tree.short) (.axis 536 541 true)) Tree.short)
theorem fullLedger_2_0_0_0_0_2_2_valid : check fullLedger_2_0_0_0_0_2_2 187 250 187 250=true := by
  decide +kernel

def fullLedger_2_0_0_0_0_2 : Tree := (.square fullLedger_2_0_0_0_0_2_0 fullLedger_2_0_0_0_0_2_1 fullLedger_2_0_0_0_0_2_2)
theorem fullLedger_2_0_0_0_0_2_valid : check fullLedger_2_0_0_0_0_2 125 250 125 250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_0_2_0_valid,fullLedger_2_0_0_0_0_2_1_valid⟩,fullLedger_2_0_0_0_0_2_2_valid⟩⟩

def fullLedger_2_0_0_0_0 : Tree := (.square fullLedger_2_0_0_0_0_0 fullLedger_2_0_0_0_0_1 fullLedger_2_0_0_0_0_2)
theorem fullLedger_2_0_0_0_0_valid : check fullLedger_2_0_0_0_0 0 250 0 250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_0_0_valid,fullLedger_2_0_0_0_0_1_valid⟩,fullLedger_2_0_0_0_0_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
