import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_2_2_2_2_0_0 : Tree := (.square Tree.short (.first (.axis 480 485 true) (.second Tree.short (.axis 482 486 true))) Tree.short)
theorem fullLedger_0_2_2_2_2_0_0_valid : check fullLedger_0_2_2_2_2_0_0 (-251) (-189) (-251) (-189)=true := by
  decide +kernel

def fullLedger_0_2_2_2_2_0_1 : Tree := (.second (.first (.axis 481 489 true) (.first (.axis 484 489 false) (.second Tree.short (.axis 486 490 false)))) (.first (.axis 481 493 false) (.axis 485 493 false)))
theorem fullLedger_0_2_2_2_2_0_1_valid : check fullLedger_0_2_2_2_2_0_1 (-251) (-189) (-189) (-126)=true := by
  decide +kernel

def fullLedger_0_2_2_2_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 488 492 false) Tree.short) (.axis 489 494 true)) Tree.short)
theorem fullLedger_0_2_2_2_2_0_2_valid : check fullLedger_0_2_2_2_2_0_2 (-189) (-126) (-189) (-126)=true := by
  decide +kernel

def fullLedger_0_2_2_2_2_0 : Tree := (.square fullLedger_0_2_2_2_2_0_0 fullLedger_0_2_2_2_2_0_1 fullLedger_0_2_2_2_2_0_2)
theorem fullLedger_0_2_2_2_2_0_valid : check fullLedger_0_2_2_2_2_0 (-251) (-126) (-251) (-126)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_2_0_0_valid,fullLedger_0_2_2_2_2_0_1_valid⟩,fullLedger_0_2_2_2_2_0_2_valid⟩⟩

def fullLedger_0_2_2_2_2_1_0 : Tree := (.first (.second (.first (.axis 481 497 false) (.axis 485 497 false)) (.axis 483 501 false)) (.first (.axis 489 499 true) (.second (.first (.axis 492 497 true) (.second Tree.short (.axis 494 498 true))) (.axis 493 501 true))))
theorem fullLedger_0_2_2_2_2_1_0_valid : check fullLedger_0_2_2_2_2_1_0 (-251) (-126) (-126) (-63)=true := by
  decide +kernel

def fullLedger_0_2_2_2_2_1_1 : Tree := (.first (.axis 483 507 false) (.first (.axis 489 507 false) (.second (.axis 493 505 false) (.axis 493 509 false))))
theorem fullLedger_0_2_2_2_2_1_1_valid : check fullLedger_0_2_2_2_2_1_1 (-251) (-126) (-63) 0=true := by
  decide +kernel

def fullLedger_0_2_2_2_2_1 : Tree := (.second fullLedger_0_2_2_2_2_1_0 fullLedger_0_2_2_2_2_1_1)
theorem fullLedger_0_2_2_2_2_1_valid : check fullLedger_0_2_2_2_2_1 (-251) (-126) (-126) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_2_1_0_valid,fullLedger_0_2_2_2_2_1_1_valid⟩

def fullLedger_0_2_2_2_2_2_0 : Tree := (.square Tree.short (.second (.first (.axis 496 500 false) Tree.short) (.axis 497 502 false)) Tree.short)
theorem fullLedger_0_2_2_2_2_2_0_valid : check fullLedger_0_2_2_2_2_2_0 (-126) (-63) (-126) (-63)=true := by
  decide +kernel

def fullLedger_0_2_2_2_2_2_1 : Tree := (.first (.second (.axis 497 505 false) (.axis 497 509 false)) (.second (.first (.axis 500 505 true) (.second Tree.short (.axis 502 506 true))) (.axis 501 509 true)))
theorem fullLedger_0_2_2_2_2_2_1_valid : check fullLedger_0_2_2_2_2_2_1 (-126) (-63) (-63) 0=true := by
  decide +kernel

def fullLedger_0_2_2_2_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 504 508 true) Tree.short) (.axis 505 510 true)) Tree.short)
theorem fullLedger_0_2_2_2_2_2_2_valid : check fullLedger_0_2_2_2_2_2_2 (-63) 0 (-63) 0=true := by
  decide +kernel

def fullLedger_0_2_2_2_2_2 : Tree := (.square fullLedger_0_2_2_2_2_2_0 fullLedger_0_2_2_2_2_2_1 fullLedger_0_2_2_2_2_2_2)
theorem fullLedger_0_2_2_2_2_2_valid : check fullLedger_0_2_2_2_2_2 (-126) 0 (-126) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_2_2_0_valid,fullLedger_0_2_2_2_2_2_1_valid⟩,fullLedger_0_2_2_2_2_2_2_valid⟩⟩

def fullLedger_0_2_2_2_2 : Tree := (.square fullLedger_0_2_2_2_2_0 fullLedger_0_2_2_2_2_1 fullLedger_0_2_2_2_2_2)
theorem fullLedger_0_2_2_2_2_valid : check fullLedger_0_2_2_2_2 (-251) 0 (-251) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_2_0_valid,fullLedger_0_2_2_2_2_1_valid⟩,fullLedger_0_2_2_2_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
