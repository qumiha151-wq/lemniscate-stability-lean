import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_2_2_2_0_0_0 : Tree := (.square Tree.short (.first (.axis 448 453 true) (.second Tree.short (.axis 450 454 false))) Tree.short)
theorem fullLedger_0_2_2_2_0_0_0_valid : check fullLedger_0_2_2_2_0_0_0 (-501) (-439) (-501) (-439)=true := by
  decide +kernel

def fullLedger_0_2_2_2_0_0_1 : Tree := (.second (.first (.axis 449 457 false) (.first (.axis 452 457 false) (.second Tree.short (.axis 454 458 true)))) (.first (.axis 449 461 false) (.axis 453 461 true)))
theorem fullLedger_0_2_2_2_0_0_1_valid : check fullLedger_0_2_2_2_0_0_1 (-501) (-439) (-439) (-376)=true := by
  decide +kernel

def fullLedger_0_2_2_2_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 456 460 true) Tree.short) (.axis 457 462 true)) Tree.short)
theorem fullLedger_0_2_2_2_0_0_2_valid : check fullLedger_0_2_2_2_0_0_2 (-439) (-376) (-439) (-376)=true := by
  decide +kernel

def fullLedger_0_2_2_2_0_0 : Tree := (.square fullLedger_0_2_2_2_0_0_0 fullLedger_0_2_2_2_0_0_1 fullLedger_0_2_2_2_0_0_2)
theorem fullLedger_0_2_2_2_0_0_valid : check fullLedger_0_2_2_2_0_0 (-501) (-376) (-501) (-376)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_0_0_0_valid,fullLedger_0_2_2_2_0_0_1_valid⟩,fullLedger_0_2_2_2_0_0_2_valid⟩⟩

def fullLedger_0_2_2_2_0_1_0 : Tree := (.second (.axis 451 467 false) (.axis 451 475 false))
theorem fullLedger_0_2_2_2_0_1_0_valid : check fullLedger_0_2_2_2_0_1_0 (-501) (-439) (-376) (-251)=true := by
  decide +kernel

def fullLedger_0_2_2_2_0_1_1 : Tree := (.second (.first (.second (.axis 457 465 true) (.axis 457 469 false)) (.second (.first (.axis 460 465 true) (.second Tree.short (.axis 462 466 false))) (.axis 461 469 false))) (.first (.axis 457 475 false) (.axis 461 475 false)))
theorem fullLedger_0_2_2_2_0_1_1_valid : check fullLedger_0_2_2_2_0_1_1 (-439) (-376) (-376) (-251)=true := by
  decide +kernel

def fullLedger_0_2_2_2_0_1 : Tree := (.first fullLedger_0_2_2_2_0_1_0 fullLedger_0_2_2_2_0_1_1)
theorem fullLedger_0_2_2_2_0_1_valid : check fullLedger_0_2_2_2_0_1 (-501) (-376) (-376) (-251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_0_1_0_valid,fullLedger_0_2_2_2_0_1_1_valid⟩

def fullLedger_0_2_2_2_0_2_0 : Tree := (.square Tree.short (.first (.axis 464 469 false) (.second Tree.short (.axis 466 470 true))) Tree.short)
theorem fullLedger_0_2_2_2_0_2_0_valid : check fullLedger_0_2_2_2_0_2_0 (-376) (-314) (-376) (-314)=true := by
  decide +kernel

def fullLedger_0_2_2_2_0_2_1 : Tree := (.second (.first (.axis 465 473 true) (.first (.axis 468 473 true) (.second Tree.short (.axis 470 474 true)))) (.axis 467 477 true))
theorem fullLedger_0_2_2_2_0_2_1_valid : check fullLedger_0_2_2_2_0_2_1 (-376) (-314) (-314) (-251)=true := by
  decide +kernel

def fullLedger_0_2_2_2_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 472 476 true) Tree.short) (.axis 473 478 false)) Tree.short)
theorem fullLedger_0_2_2_2_0_2_2_valid : check fullLedger_0_2_2_2_0_2_2 (-314) (-251) (-314) (-251)=true := by
  decide +kernel

def fullLedger_0_2_2_2_0_2 : Tree := (.square fullLedger_0_2_2_2_0_2_0 fullLedger_0_2_2_2_0_2_1 fullLedger_0_2_2_2_0_2_2)
theorem fullLedger_0_2_2_2_0_2_valid : check fullLedger_0_2_2_2_0_2 (-376) (-251) (-376) (-251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_0_2_0_valid,fullLedger_0_2_2_2_0_2_1_valid⟩,fullLedger_0_2_2_2_0_2_2_valid⟩⟩

def fullLedger_0_2_2_2_0 : Tree := (.square fullLedger_0_2_2_2_0_0 fullLedger_0_2_2_2_0_1 fullLedger_0_2_2_2_0_2)
theorem fullLedger_0_2_2_2_0_valid : check fullLedger_0_2_2_2_0 (-501) (-251) (-501) (-251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_0_0_valid,fullLedger_0_2_2_2_0_1_valid⟩,fullLedger_0_2_2_2_0_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
