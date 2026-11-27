import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_2_2_0_0_0_0 : Tree := (.square Tree.short (.first (.axis 384 389 true) (.second Tree.short (.axis 386 390 false))) Tree.short)
theorem fullLedger_0_2_2_0_0_0_0_valid : check fullLedger_0_2_2_0_0_0_0 (-1001) (-939) (-1001) (-939)=true := by
  decide +kernel

def fullLedger_0_2_2_0_0_0_1 : Tree := (.second (.first (.axis 385 393 false) (.first (.axis 388 393 false) (.second Tree.short (.axis 390 394 false)))) (.first (.axis 385 397 false) (.axis 389 397 false)))
theorem fullLedger_0_2_2_0_0_0_1_valid : check fullLedger_0_2_2_0_0_0_1 (-1001) (-939) (-939) (-876)=true := by
  decide +kernel

def fullLedger_0_2_2_0_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 392 396 true) Tree.short) (.axis 393 398 true)) Tree.short)
theorem fullLedger_0_2_2_0_0_0_2_valid : check fullLedger_0_2_2_0_0_0_2 (-939) (-876) (-939) (-876)=true := by
  decide +kernel

def fullLedger_0_2_2_0_0_0 : Tree := (.square fullLedger_0_2_2_0_0_0_0 fullLedger_0_2_2_0_0_0_1 fullLedger_0_2_2_0_0_0_2)
theorem fullLedger_0_2_2_0_0_0_valid : check fullLedger_0_2_2_0_0_0 (-1001) (-876) (-1001) (-876)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_0_0_0_valid,fullLedger_0_2_2_0_0_0_1_valid⟩,fullLedger_0_2_2_0_0_0_2_valid⟩⟩

def fullLedger_0_2_2_0_0_1_0 : Tree := (.second (.axis 387 403 true) (.axis 387 411 false))
theorem fullLedger_0_2_2_0_0_1_0_valid : check fullLedger_0_2_2_0_0_1_0 (-1001) (-939) (-876) (-751)=true := by
  decide +kernel

def fullLedger_0_2_2_0_0_1_1 : Tree := (.second (.first (.axis 393 403 true) (.second (.first (.axis 396 401 true) (.second Tree.short (.axis 398 402 true))) (.axis 397 405 true))) (.first (.axis 393 411 false) (.second (.axis 397 409 false) (.axis 397 413 false))))
theorem fullLedger_0_2_2_0_0_1_1_valid : check fullLedger_0_2_2_0_0_1_1 (-939) (-876) (-876) (-751)=true := by
  decide +kernel

def fullLedger_0_2_2_0_0_1 : Tree := (.first fullLedger_0_2_2_0_0_1_0 fullLedger_0_2_2_0_0_1_1)
theorem fullLedger_0_2_2_0_0_1_valid : check fullLedger_0_2_2_0_0_1 (-1001) (-876) (-876) (-751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_0_1_0_valid,fullLedger_0_2_2_0_0_1_1_valid⟩

def fullLedger_0_2_2_0_0_2_0 : Tree := (.square Tree.short (.first (.axis 400 405 false) (.second Tree.short (.axis 402 406 false))) Tree.short)
theorem fullLedger_0_2_2_0_0_2_0_valid : check fullLedger_0_2_2_0_0_2_0 (-876) (-814) (-876) (-814)=true := by
  decide +kernel

def fullLedger_0_2_2_0_0_2_1 : Tree := (.second (.first (.axis 401 409 false) (.first (.axis 404 409 true) (.second Tree.short (.axis 406 410 true)))) (.axis 403 413 true))
theorem fullLedger_0_2_2_0_0_2_1_valid : check fullLedger_0_2_2_0_0_2_1 (-876) (-814) (-814) (-751)=true := by
  decide +kernel

def fullLedger_0_2_2_0_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 408 412 true) Tree.short) (.axis 409 414 true)) Tree.short)
theorem fullLedger_0_2_2_0_0_2_2_valid : check fullLedger_0_2_2_0_0_2_2 (-814) (-751) (-814) (-751)=true := by
  decide +kernel

def fullLedger_0_2_2_0_0_2 : Tree := (.square fullLedger_0_2_2_0_0_2_0 fullLedger_0_2_2_0_0_2_1 fullLedger_0_2_2_0_0_2_2)
theorem fullLedger_0_2_2_0_0_2_valid : check fullLedger_0_2_2_0_0_2 (-876) (-751) (-876) (-751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_0_2_0_valid,fullLedger_0_2_2_0_0_2_1_valid⟩,fullLedger_0_2_2_0_0_2_2_valid⟩⟩

def fullLedger_0_2_2_0_0 : Tree := (.square fullLedger_0_2_2_0_0_0 fullLedger_0_2_2_0_0_1 fullLedger_0_2_2_0_0_2)
theorem fullLedger_0_2_2_0_0_valid : check fullLedger_0_2_2_0_0 (-1001) (-751) (-1001) (-751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_0_0_valid,fullLedger_0_2_2_0_0_1_valid⟩,fullLedger_0_2_2_0_0_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
