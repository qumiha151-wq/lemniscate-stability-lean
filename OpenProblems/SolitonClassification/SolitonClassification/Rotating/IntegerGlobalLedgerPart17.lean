import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_2_2_1_0_0 : Tree := (.first (.axis 391 463 false) (.second (.axis 407 455 false) (.axis 407 471 false)))
theorem fullLedger_0_2_2_1_0_0_valid : check fullLedger_0_2_2_1_0_0 (-1001) (-751) (-501) (-251)=true := by
  decide +kernel

def fullLedger_0_2_2_1_0_1_0 : Tree := (.second (.first (.axis 419 455 false) (.axis 427 455 false)) (.axis 423 471 false))
theorem fullLedger_0_2_2_1_0_1_0_valid : check fullLedger_0_2_2_1_0_1_0 (-751) (-626) (-501) (-251)=true := by
  decide +kernel

def fullLedger_0_2_2_1_0_1_1_0_0 : Tree := (.second (.first (.axis 433 451 false) (.axis 437 451 false)) (.axis 435 459 false))
theorem fullLedger_0_2_2_1_0_1_1_0_0_valid : check fullLedger_0_2_2_1_0_1_1_0_0 (-626) (-564) (-501) (-376)=true := by
  decide +kernel

def fullLedger_0_2_2_1_0_1_1_0_1 : Tree := (.second (.first (.axis 441 451 true) (.second (.first (.axis 444 449 true) (.second Tree.short (.axis 446 450 true))) (.axis 445 453 true))) (.first (.axis 441 459 false) (.second (.axis 445 457 false) (.axis 445 461 false))))
theorem fullLedger_0_2_2_1_0_1_1_0_1_valid : check fullLedger_0_2_2_1_0_1_1_0_1 (-564) (-501) (-501) (-376)=true := by
  decide +kernel

def fullLedger_0_2_2_1_0_1_1_0 : Tree := (.first fullLedger_0_2_2_1_0_1_1_0_0 fullLedger_0_2_2_1_0_1_1_0_1)
theorem fullLedger_0_2_2_1_0_1_1_0_valid : check fullLedger_0_2_2_1_0_1_1_0 (-626) (-501) (-501) (-376)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_1_0_1_1_0_0_valid,fullLedger_0_2_2_1_0_1_1_0_1_valid⟩

def fullLedger_0_2_2_1_0_1_1_1 : Tree := (.first (.axis 435 471 false) (.second (.axis 443 467 false) (.axis 443 475 false)))
theorem fullLedger_0_2_2_1_0_1_1_1_valid : check fullLedger_0_2_2_1_0_1_1_1 (-626) (-501) (-376) (-251)=true := by
  decide +kernel

def fullLedger_0_2_2_1_0_1_1 : Tree := (.second fullLedger_0_2_2_1_0_1_1_0 fullLedger_0_2_2_1_0_1_1_1)
theorem fullLedger_0_2_2_1_0_1_1_valid : check fullLedger_0_2_2_1_0_1_1 (-626) (-501) (-501) (-251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_1_0_1_1_0_valid,fullLedger_0_2_2_1_0_1_1_1_valid⟩

def fullLedger_0_2_2_1_0_1 : Tree := (.first fullLedger_0_2_2_1_0_1_0 fullLedger_0_2_2_1_0_1_1)
theorem fullLedger_0_2_2_1_0_1_valid : check fullLedger_0_2_2_1_0_1 (-751) (-501) (-501) (-251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_1_0_1_0_valid,fullLedger_0_2_2_1_0_1_1_valid⟩

def fullLedger_0_2_2_1_0 : Tree := (.first fullLedger_0_2_2_1_0_0 fullLedger_0_2_2_1_0_1)
theorem fullLedger_0_2_2_1_0_valid : check fullLedger_0_2_2_1_0 (-1001) (-501) (-501) (-251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_1_0_0_valid,fullLedger_0_2_2_1_0_1_valid⟩

def fullLedger_0_2_2_1_1 : Tree := (.first (.axis 399 495 false) (.second (.axis 431 487 false) (.axis 431 503 false)))
theorem fullLedger_0_2_2_1_1_valid : check fullLedger_0_2_2_1_1 (-1001) (-501) (-251) 0=true := by
  decide +kernel

def fullLedger_0_2_2_1 : Tree := (.second fullLedger_0_2_2_1_0 fullLedger_0_2_2_1_1)
theorem fullLedger_0_2_2_1_valid : check fullLedger_0_2_2_1 (-1001) (-501) (-501) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_1_0_valid,fullLedger_0_2_2_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
