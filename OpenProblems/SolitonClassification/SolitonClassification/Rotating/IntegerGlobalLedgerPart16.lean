import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_2_2_0_2_0_0 : Tree := (.square Tree.short (.first (.axis 416 421 false) (.second Tree.short (.axis 418 422 true))) Tree.short)
theorem fullLedger_0_2_2_0_2_0_0_valid : check fullLedger_0_2_2_0_2_0_0 (-751) (-689) (-751) (-689)=true := by
  decide +kernel

def fullLedger_0_2_2_0_2_0_1 : Tree := (.second (.first (.axis 417 425 true) (.first (.axis 420 425 true) (.second Tree.short (.axis 422 426 true)))) (.axis 419 429 true))
theorem fullLedger_0_2_2_0_2_0_1_valid : check fullLedger_0_2_2_0_2_0_1 (-751) (-689) (-689) (-626)=true := by
  decide +kernel

def fullLedger_0_2_2_0_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 424 428 true) Tree.short) (.axis 425 430 false)) Tree.short)
theorem fullLedger_0_2_2_0_2_0_2_valid : check fullLedger_0_2_2_0_2_0_2 (-689) (-626) (-689) (-626)=true := by
  decide +kernel

def fullLedger_0_2_2_0_2_0 : Tree := (.square fullLedger_0_2_2_0_2_0_0 fullLedger_0_2_2_0_2_0_1 fullLedger_0_2_2_0_2_0_2)
theorem fullLedger_0_2_2_0_2_0_valid : check fullLedger_0_2_2_0_2_0 (-751) (-626) (-751) (-626)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_2_0_0_valid,fullLedger_0_2_2_0_2_0_1_valid⟩,fullLedger_0_2_2_0_2_0_2_valid⟩⟩

def fullLedger_0_2_2_0_2_1_0 : Tree := (.second (.first (.axis 417 435 false) (.second (.axis 421 433 false) (.axis 421 437 false))) (.axis 419 443 false))
theorem fullLedger_0_2_2_0_2_1_0_valid : check fullLedger_0_2_2_0_2_1_0 (-751) (-689) (-626) (-501)=true := by
  decide +kernel

def fullLedger_0_2_2_0_2_1_1 : Tree := (.second (.first (.second (.axis 425 433 false) (.axis 425 437 false)) (.second (.first (.axis 428 433 false) (.second Tree.short (.axis 430 434 true))) (.axis 429 437 true))) (.axis 427 443 false))
theorem fullLedger_0_2_2_0_2_1_1_valid : check fullLedger_0_2_2_0_2_1_1 (-689) (-626) (-626) (-501)=true := by
  decide +kernel

def fullLedger_0_2_2_0_2_1 : Tree := (.first fullLedger_0_2_2_0_2_1_0 fullLedger_0_2_2_0_2_1_1)
theorem fullLedger_0_2_2_0_2_1_valid : check fullLedger_0_2_2_0_2_1 (-751) (-626) (-626) (-501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_2_1_0_valid,fullLedger_0_2_2_0_2_1_1_valid⟩

def fullLedger_0_2_2_0_2_2_0 : Tree := (.square Tree.short (.first (.axis 432 437 true) (.second Tree.short (.axis 434 438 true))) Tree.short)
theorem fullLedger_0_2_2_0_2_2_0_valid : check fullLedger_0_2_2_0_2_2_0 (-626) (-564) (-626) (-564)=true := by
  decide +kernel

def fullLedger_0_2_2_0_2_2_1 : Tree := (.second (.first (.axis 433 441 true) (.first (.axis 436 441 true) (.second Tree.short (.axis 438 442 false)))) (.first (.axis 433 445 false) (.axis 437 445 false)))
theorem fullLedger_0_2_2_0_2_2_1_valid : check fullLedger_0_2_2_0_2_2_1 (-626) (-564) (-564) (-501)=true := by
  decide +kernel

def fullLedger_0_2_2_0_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 440 444 false) Tree.short) (.axis 441 446 true)) Tree.short)
theorem fullLedger_0_2_2_0_2_2_2_valid : check fullLedger_0_2_2_0_2_2_2 (-564) (-501) (-564) (-501)=true := by
  decide +kernel

def fullLedger_0_2_2_0_2_2 : Tree := (.square fullLedger_0_2_2_0_2_2_0 fullLedger_0_2_2_0_2_2_1 fullLedger_0_2_2_0_2_2_2)
theorem fullLedger_0_2_2_0_2_2_valid : check fullLedger_0_2_2_0_2_2 (-626) (-501) (-626) (-501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_2_2_0_valid,fullLedger_0_2_2_0_2_2_1_valid⟩,fullLedger_0_2_2_0_2_2_2_valid⟩⟩

def fullLedger_0_2_2_0_2 : Tree := (.square fullLedger_0_2_2_0_2_0 fullLedger_0_2_2_0_2_1 fullLedger_0_2_2_0_2_2)
theorem fullLedger_0_2_2_0_2_valid : check fullLedger_0_2_2_0_2 (-751) (-501) (-751) (-501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_2_0_valid,fullLedger_0_2_2_0_2_1_valid⟩,fullLedger_0_2_2_0_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
