import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_2_2_0_1_0 : Tree := (.second (.first (.axis 387 423 false) (.second (.axis 395 419 false) (.axis 395 427 false))) (.axis 391 439 false))
theorem fullLedger_0_2_2_0_1_0_valid : check fullLedger_0_2_2_0_1_0 (-1001) (-876) (-751) (-501)=true := by
  decide +kernel

def fullLedger_0_2_2_0_1_1_0_0 : Tree := (.second (.axis 403 419 false) (.axis 403 427 false))
theorem fullLedger_0_2_2_0_1_1_0_0_valid : check fullLedger_0_2_2_0_1_1_0_0 (-876) (-814) (-751) (-626)=true := by
  decide +kernel

def fullLedger_0_2_2_0_1_1_0_1 : Tree := (.second (.first (.second (.axis 409 417 true) (.axis 409 421 false)) (.second (.first (.axis 412 417 false) (.second Tree.short (.axis 414 418 false))) (.axis 413 421 false))) (.first (.axis 409 427 false) (.axis 413 427 false)))
theorem fullLedger_0_2_2_0_1_1_0_1_valid : check fullLedger_0_2_2_0_1_1_0_1 (-814) (-751) (-751) (-626)=true := by
  decide +kernel

def fullLedger_0_2_2_0_1_1_0 : Tree := (.first fullLedger_0_2_2_0_1_1_0_0 fullLedger_0_2_2_0_1_1_0_1)
theorem fullLedger_0_2_2_0_1_1_0_valid : check fullLedger_0_2_2_0_1_1_0 (-876) (-751) (-751) (-626)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_1_1_0_0_valid,fullLedger_0_2_2_0_1_1_0_1_valid⟩

def fullLedger_0_2_2_0_1_1_1 : Tree := (.first (.axis 403 439 false) (.axis 411 439 false))
theorem fullLedger_0_2_2_0_1_1_1_valid : check fullLedger_0_2_2_0_1_1_1 (-876) (-751) (-626) (-501)=true := by
  decide +kernel

def fullLedger_0_2_2_0_1_1 : Tree := (.second fullLedger_0_2_2_0_1_1_0 fullLedger_0_2_2_0_1_1_1)
theorem fullLedger_0_2_2_0_1_1_valid : check fullLedger_0_2_2_0_1_1 (-876) (-751) (-751) (-501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_1_1_0_valid,fullLedger_0_2_2_0_1_1_1_valid⟩

def fullLedger_0_2_2_0_1 : Tree := (.first fullLedger_0_2_2_0_1_0 fullLedger_0_2_2_0_1_1)
theorem fullLedger_0_2_2_0_1_valid : check fullLedger_0_2_2_0_1 (-1001) (-751) (-751) (-501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_1_0_valid,fullLedger_0_2_2_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
