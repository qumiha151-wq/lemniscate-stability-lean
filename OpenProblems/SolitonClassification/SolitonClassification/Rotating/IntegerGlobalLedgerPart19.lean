import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_2_2_2_1_0_0 : Tree := (.first (.axis 451 487 false) (.second (.axis 459 483 false) (.axis 459 491 false)))
theorem fullLedger_0_2_2_2_1_0_0_valid : check fullLedger_0_2_2_2_1_0_0 (-501) (-376) (-251) (-126)=true := by
  decide +kernel

def fullLedger_0_2_2_2_1_0_1_0 : Tree := (.second (.first (.axis 465 483 false) (.second (.axis 469 481 false) (.axis 469 485 false))) (.axis 467 491 false))
theorem fullLedger_0_2_2_2_1_0_1_0_valid : check fullLedger_0_2_2_2_1_0_1_0 (-376) (-314) (-251) (-126)=true := by
  decide +kernel

def fullLedger_0_2_2_2_1_0_1_1 : Tree := (.second (.first (.second (.axis 473 481 false) (.axis 473 485 false)) (.second (.first (.axis 476 481 false) (.second Tree.short (.axis 478 482 true))) (.axis 477 485 true))) (.axis 475 491 false))
theorem fullLedger_0_2_2_2_1_0_1_1_valid : check fullLedger_0_2_2_2_1_0_1_1 (-314) (-251) (-251) (-126)=true := by
  decide +kernel

def fullLedger_0_2_2_2_1_0_1 : Tree := (.first fullLedger_0_2_2_2_1_0_1_0 fullLedger_0_2_2_2_1_0_1_1)
theorem fullLedger_0_2_2_2_1_0_1_valid : check fullLedger_0_2_2_2_1_0_1 (-376) (-251) (-251) (-126)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_1_0_1_0_valid,fullLedger_0_2_2_2_1_0_1_1_valid⟩

def fullLedger_0_2_2_2_1_0 : Tree := (.first fullLedger_0_2_2_2_1_0_0 fullLedger_0_2_2_2_1_0_1)
theorem fullLedger_0_2_2_2_1_0_valid : check fullLedger_0_2_2_2_1_0 (-501) (-251) (-251) (-126)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_1_0_0_valid,fullLedger_0_2_2_2_1_0_1_valid⟩

def fullLedger_0_2_2_2_1_1 : Tree := (.first (.axis 455 503 false) (.second (.axis 471 499 false) (.axis 471 507 false)))
theorem fullLedger_0_2_2_2_1_1_valid : check fullLedger_0_2_2_2_1_1 (-501) (-251) (-126) 0=true := by
  decide +kernel

def fullLedger_0_2_2_2_1 : Tree := (.second fullLedger_0_2_2_2_1_0 fullLedger_0_2_2_2_1_1)
theorem fullLedger_0_2_2_2_1_valid : check fullLedger_0_2_2_2_1 (-501) (-251) (-251) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_1_0_valid,fullLedger_0_2_2_2_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
