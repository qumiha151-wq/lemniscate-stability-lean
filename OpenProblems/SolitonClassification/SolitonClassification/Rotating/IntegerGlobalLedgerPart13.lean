import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_2_1_0_0 : Tree := (.first (.axis 271 415 false) (.axis 303 415 false))
theorem fullLedger_0_2_1_0_0_valid : check fullLedger_0_2_1_0_0 (-2001) (-1501) (-1001) (-501)=true := by
  decide +kernel

def fullLedger_0_2_1_0_1_0 : Tree := (.second (.first (.axis 327 399 false) (.axis 343 399 false)) (.axis 335 431 false))
theorem fullLedger_0_2_1_0_1_0_valid : check fullLedger_0_2_1_0_1_0 (-1501) (-1251) (-1001) (-501)=true := by
  decide +kernel

def fullLedger_0_2_1_0_1_1_0_0 : Tree := (.second (.first (.axis 355 391 false) (.axis 363 391 false)) (.axis 359 407 false))
theorem fullLedger_0_2_1_0_1_1_0_0_valid : check fullLedger_0_2_1_0_1_1_0_0 (-1251) (-1126) (-1001) (-751)=true := by
  decide +kernel

def fullLedger_0_2_1_0_1_1_0_1_0_0 : Tree := (.second (.first (.axis 369 387 false) (.axis 373 387 false)) (.axis 371 395 false))
theorem fullLedger_0_2_1_0_1_1_0_1_0_0_valid : check fullLedger_0_2_1_0_1_1_0_1_0_0 (-1126) (-1064) (-1001) (-876)=true := by
  decide +kernel

def fullLedger_0_2_1_0_1_1_0_1_0_1 : Tree := (.second (.first (.axis 377 387 true) (.second (.first (.axis 380 385 true) (.second Tree.short (.axis 382 386 true))) (.axis 381 389 true))) (.first (.axis 377 395 false) (.axis 381 395 false)))
theorem fullLedger_0_2_1_0_1_1_0_1_0_1_valid : check fullLedger_0_2_1_0_1_1_0_1_0_1 (-1064) (-1001) (-1001) (-876)=true := by
  decide +kernel

def fullLedger_0_2_1_0_1_1_0_1_0 : Tree := (.first fullLedger_0_2_1_0_1_1_0_1_0_0 fullLedger_0_2_1_0_1_1_0_1_0_1)
theorem fullLedger_0_2_1_0_1_1_0_1_0_valid : check fullLedger_0_2_1_0_1_1_0_1_0 (-1126) (-1001) (-1001) (-876)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_1_0_1_1_0_1_0_0_valid,fullLedger_0_2_1_0_1_1_0_1_0_1_valid⟩

def fullLedger_0_2_1_0_1_1_0_1_1 : Tree := (.axis 375 407 false)
theorem fullLedger_0_2_1_0_1_1_0_1_1_valid : check fullLedger_0_2_1_0_1_1_0_1_1 (-1126) (-1001) (-876) (-751)=true := by
  decide +kernel

def fullLedger_0_2_1_0_1_1_0_1 : Tree := (.second fullLedger_0_2_1_0_1_1_0_1_0 fullLedger_0_2_1_0_1_1_0_1_1)
theorem fullLedger_0_2_1_0_1_1_0_1_valid : check fullLedger_0_2_1_0_1_1_0_1 (-1126) (-1001) (-1001) (-751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_1_0_1_1_0_1_0_valid,fullLedger_0_2_1_0_1_1_0_1_1_valid⟩

def fullLedger_0_2_1_0_1_1_0 : Tree := (.first fullLedger_0_2_1_0_1_1_0_0 fullLedger_0_2_1_0_1_1_0_1)
theorem fullLedger_0_2_1_0_1_1_0_valid : check fullLedger_0_2_1_0_1_1_0 (-1251) (-1001) (-1001) (-751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_1_0_1_1_0_0_valid,fullLedger_0_2_1_0_1_1_0_1_valid⟩

def fullLedger_0_2_1_0_1_1_1 : Tree := (.first (.axis 359 431 false) (.axis 375 431 false))
theorem fullLedger_0_2_1_0_1_1_1_valid : check fullLedger_0_2_1_0_1_1_1 (-1251) (-1001) (-751) (-501)=true := by
  decide +kernel

def fullLedger_0_2_1_0_1_1 : Tree := (.second fullLedger_0_2_1_0_1_1_0 fullLedger_0_2_1_0_1_1_1)
theorem fullLedger_0_2_1_0_1_1_valid : check fullLedger_0_2_1_0_1_1 (-1251) (-1001) (-1001) (-501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_1_0_1_1_0_valid,fullLedger_0_2_1_0_1_1_1_valid⟩

def fullLedger_0_2_1_0_1 : Tree := (.first fullLedger_0_2_1_0_1_0 fullLedger_0_2_1_0_1_1)
theorem fullLedger_0_2_1_0_1_valid : check fullLedger_0_2_1_0_1 (-1501) (-1001) (-1001) (-501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_1_0_1_0_valid,fullLedger_0_2_1_0_1_1_valid⟩

def fullLedger_0_2_1_0 : Tree := (.first fullLedger_0_2_1_0_0 fullLedger_0_2_1_0_1)
theorem fullLedger_0_2_1_0_valid : check fullLedger_0_2_1_0 (-2001) (-1001) (-1001) (-501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_1_0_0_valid,fullLedger_0_2_1_0_1_valid⟩

def fullLedger_0_2_1_1 : Tree := (.first (.axis 287 479 false) (.second (.axis 351 463 false) (.axis 351 495 false)))
theorem fullLedger_0_2_1_1_valid : check fullLedger_0_2_1_1 (-2001) (-1001) (-501) 0=true := by
  decide +kernel

def fullLedger_0_2_1 : Tree := (.second fullLedger_0_2_1_0 fullLedger_0_2_1_1)
theorem fullLedger_0_2_1_valid : check fullLedger_0_2_1 (-2001) (-1001) (-1001) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_1_0_valid,fullLedger_0_2_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
