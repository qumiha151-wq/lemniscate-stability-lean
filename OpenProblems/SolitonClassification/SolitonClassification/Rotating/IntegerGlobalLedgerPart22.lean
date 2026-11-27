import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_1_1_0_0 : Tree := (.second (.first (.axis 287 574 false) (.axis 351 574 false)) (.axis 319 729 false))
theorem fullLedger_1_1_0_0_valid : check fullLedger_1_1_0_0 (-2001) (-1001) 0 2000=true := by
  decide +kernel

def fullLedger_1_1_0_1_0_0 : Tree := (.second (.first (.axis 399 542 false) (.axis 431 542 false)) (.axis 415 606 false))
theorem fullLedger_1_1_0_1_0_0_valid : check fullLedger_1_1_0_1_0_0 (-1001) (-501) 0 1000=true := by
  decide +kernel

def fullLedger_1_1_0_1_0_1_0_0 : Tree := (.second (.first (.axis 455 526 false) (.axis 471 526 false)) (.axis 463 558 false))
theorem fullLedger_1_1_0_1_0_1_0_0_valid : check fullLedger_1_1_0_1_0_1_0_0 (-501) (-251) 0 500=true := by
  decide +kernel

def fullLedger_1_1_0_1_0_1_0_1_0_0 : Tree := (.second (.first (.axis 483 518 false) (.second (.axis 491 514 false) (.axis 491 522 false))) (.axis 487 534 false))
theorem fullLedger_1_1_0_1_0_1_0_1_0_0_valid : check fullLedger_1_1_0_1_0_1_0_1_0_0 (-251) (-126) 0 250=true := by
  decide +kernel

def fullLedger_1_1_0_1_0_1_0_1_0_1_0 : Tree := (.first (.second (.axis 499 514 false) (.axis 499 522 false)) (.second (.first (.second (.axis 505 512 false) (.axis 505 516 false)) (.second (.first (.axis 508 512 false) (.second Tree.short (.axis 510 513 false))) (.axis 509 516 false))) (.axis 507 522 false)))
theorem fullLedger_1_1_0_1_0_1_0_1_0_1_0_valid : check fullLedger_1_1_0_1_0_1_0_1_0_1_0 (-126) 0 0 125=true := by
  decide +kernel

def fullLedger_1_1_0_1_0_1_0_1_0_1_1 : Tree := (.first (.axis 499 534 false) (.axis 507 534 false))
theorem fullLedger_1_1_0_1_0_1_0_1_0_1_1_valid : check fullLedger_1_1_0_1_0_1_0_1_0_1_1 (-126) 0 125 250=true := by
  decide +kernel

def fullLedger_1_1_0_1_0_1_0_1_0_1 : Tree := (.second fullLedger_1_1_0_1_0_1_0_1_0_1_0 fullLedger_1_1_0_1_0_1_0_1_0_1_1)
theorem fullLedger_1_1_0_1_0_1_0_1_0_1_valid : check fullLedger_1_1_0_1_0_1_0_1_0_1 (-126) 0 0 250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_0_1_0_1_0_1_0_1_0_valid,fullLedger_1_1_0_1_0_1_0_1_0_1_1_valid⟩

def fullLedger_1_1_0_1_0_1_0_1_0 : Tree := (.first fullLedger_1_1_0_1_0_1_0_1_0_0 fullLedger_1_1_0_1_0_1_0_1_0_1)
theorem fullLedger_1_1_0_1_0_1_0_1_0_valid : check fullLedger_1_1_0_1_0_1_0_1_0 (-251) 0 0 250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_0_1_0_1_0_1_0_0_valid,fullLedger_1_1_0_1_0_1_0_1_0_1_valid⟩

def fullLedger_1_1_0_1_0_1_0_1_1 : Tree := (.first (.axis 487 558 false) (.axis 503 558 false))
theorem fullLedger_1_1_0_1_0_1_0_1_1_valid : check fullLedger_1_1_0_1_0_1_0_1_1 (-251) 0 250 500=true := by
  decide +kernel

def fullLedger_1_1_0_1_0_1_0_1 : Tree := (.second fullLedger_1_1_0_1_0_1_0_1_0 fullLedger_1_1_0_1_0_1_0_1_1)
theorem fullLedger_1_1_0_1_0_1_0_1_valid : check fullLedger_1_1_0_1_0_1_0_1 (-251) 0 0 500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_0_1_0_1_0_1_0_valid,fullLedger_1_1_0_1_0_1_0_1_1_valid⟩

def fullLedger_1_1_0_1_0_1_0 : Tree := (.first fullLedger_1_1_0_1_0_1_0_0 fullLedger_1_1_0_1_0_1_0_1)
theorem fullLedger_1_1_0_1_0_1_0_valid : check fullLedger_1_1_0_1_0_1_0 (-501) 0 0 500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_0_1_0_1_0_0_valid,fullLedger_1_1_0_1_0_1_0_1_valid⟩

def fullLedger_1_1_0_1_0_1_1 : Tree := (.first (.axis 463 606 false) (.axis 495 606 false))
theorem fullLedger_1_1_0_1_0_1_1_valid : check fullLedger_1_1_0_1_0_1_1 (-501) 0 500 1000=true := by
  decide +kernel

def fullLedger_1_1_0_1_0_1 : Tree := (.second fullLedger_1_1_0_1_0_1_0 fullLedger_1_1_0_1_0_1_1)
theorem fullLedger_1_1_0_1_0_1_valid : check fullLedger_1_1_0_1_0_1 (-501) 0 0 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_0_1_0_1_0_valid,fullLedger_1_1_0_1_0_1_1_valid⟩

def fullLedger_1_1_0_1_0 : Tree := (.first fullLedger_1_1_0_1_0_0 fullLedger_1_1_0_1_0_1)
theorem fullLedger_1_1_0_1_0_valid : check fullLedger_1_1_0_1_0 (-1001) 0 0 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_0_1_0_0_valid,fullLedger_1_1_0_1_0_1_valid⟩

def fullLedger_1_1_0_1_1 : Tree := (.first (.axis 415 729 false) (.axis 479 729 false))
theorem fullLedger_1_1_0_1_1_valid : check fullLedger_1_1_0_1_1 (-1001) 0 1000 2000=true := by
  decide +kernel

def fullLedger_1_1_0_1 : Tree := (.second fullLedger_1_1_0_1_0 fullLedger_1_1_0_1_1)
theorem fullLedger_1_1_0_1_valid : check fullLedger_1_1_0_1 (-1001) 0 0 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_0_1_0_valid,fullLedger_1_1_0_1_1_valid⟩

def fullLedger_1_1_0 : Tree := (.first fullLedger_1_1_0_0 fullLedger_1_1_0_1)
theorem fullLedger_1_1_0_valid : check fullLedger_1_1_0 (-2001) 0 0 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_0_0_valid,fullLedger_1_1_0_1_valid⟩

def fullLedger_1_1_1_0 : Tree := (.second (.axis 319 929 false) (.second (.axis 319 1050 false) (.axis 319 1114 false)))
theorem fullLedger_1_1_1_0_valid : check fullLedger_1_1_1_0 (-2001) (-1001) 2000 4001=true := by
  decide +kernel

def fullLedger_1_1_1_1_0 : Tree := (.first (.axis 415 929 false) (.axis 479 929 false))
theorem fullLedger_1_1_1_1_0_valid : check fullLedger_1_1_1_1_0 (-1001) 0 2000 3000=true := by
  decide +kernel

def fullLedger_1_1_1_1_1_0 : Tree := (.second (.axis 415 1050 false) (.second (.axis 415 1098 false) (.axis 415 1130 false)))
theorem fullLedger_1_1_1_1_1_0_valid : check fullLedger_1_1_1_1_1_0 (-1001) (-501) 3000 4001=true := by
  decide +kernel

def fullLedger_1_1_1_1_1_1 : Tree := (.second (.first (.axis 463 1050 false) (.axis 495 1050 false)) (.first (.second (.axis 463 1098 false) (.axis 463 1130 false)) (.second (.axis 495 1098 false) (.first (.second (.axis 487 1122 false) (.axis 487 1138 false)) (.axis 503 1130 true)))))
theorem fullLedger_1_1_1_1_1_1_valid : check fullLedger_1_1_1_1_1_1 (-501) 0 3000 4001=true := by
  decide +kernel

def fullLedger_1_1_1_1_1 : Tree := (.first fullLedger_1_1_1_1_1_0 fullLedger_1_1_1_1_1_1)
theorem fullLedger_1_1_1_1_1_valid : check fullLedger_1_1_1_1_1 (-1001) 0 3000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_1_1_1_0_valid,fullLedger_1_1_1_1_1_1_valid⟩

def fullLedger_1_1_1_1 : Tree := (.second fullLedger_1_1_1_1_0 fullLedger_1_1_1_1_1)
theorem fullLedger_1_1_1_1_valid : check fullLedger_1_1_1_1 (-1001) 0 2000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_1_1_0_valid,fullLedger_1_1_1_1_1_valid⟩

def fullLedger_1_1_1 : Tree := (.first fullLedger_1_1_1_0 fullLedger_1_1_1_1)
theorem fullLedger_1_1_1_valid : check fullLedger_1_1_1 (-2001) 0 2000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_1_0_valid,fullLedger_1_1_1_1_valid⟩

def fullLedger_1_1 : Tree := (.second fullLedger_1_1_0 fullLedger_1_1_1)
theorem fullLedger_1_1_valid : check fullLedger_1_1 (-2001) 0 0 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_1_0_valid,fullLedger_1_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
