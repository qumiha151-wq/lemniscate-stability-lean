import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_2_0_1_0 : Tree := (.second (.first (.axis 263 335 false) (.second (.axis 279 327 false) (.axis 279 343 false))) (.axis 271 367 false))
theorem fullLedger_0_2_0_1_0_valid : check fullLedger_0_2_0_1_0 (-2001) (-1751) (-1501) (-1001)=true := by
  decide +kernel

def fullLedger_0_2_0_1_1_0_0 : Tree := (.second (.first (.axis 291 327 false) (.axis 299 327 false)) (.axis 295 343 false))
theorem fullLedger_0_2_0_1_1_0_0_valid : check fullLedger_0_2_0_1_1_0_0 (-1751) (-1626) (-1501) (-1251)=true := by
  decide +kernel

def fullLedger_0_2_0_1_1_0_1_0 : Tree := (.first (.axis 307 327 true) (.second (.first (.axis 313 323 true) (.second (.first (.axis 316 321 true) (.second Tree.short (.axis 318 322 true))) (.axis 317 325 true))) (.axis 315 331 true)))
theorem fullLedger_0_2_0_1_1_0_1_0_valid : check fullLedger_0_2_0_1_1_0_1_0 (-1626) (-1501) (-1501) (-1376)=true := by
  decide +kernel

def fullLedger_0_2_0_1_1_0_1_1 : Tree := (.first (.axis 307 343 false) (.second (.axis 315 339 false) (.axis 315 347 false)))
theorem fullLedger_0_2_0_1_1_0_1_1_valid : check fullLedger_0_2_0_1_1_0_1_1 (-1626) (-1501) (-1376) (-1251)=true := by
  decide +kernel

def fullLedger_0_2_0_1_1_0_1 : Tree := (.second fullLedger_0_2_0_1_1_0_1_0 fullLedger_0_2_0_1_1_0_1_1)
theorem fullLedger_0_2_0_1_1_0_1_valid : check fullLedger_0_2_0_1_1_0_1 (-1626) (-1501) (-1501) (-1251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_1_1_0_1_0_valid,fullLedger_0_2_0_1_1_0_1_1_valid⟩

def fullLedger_0_2_0_1_1_0 : Tree := (.first fullLedger_0_2_0_1_1_0_0 fullLedger_0_2_0_1_1_0_1)
theorem fullLedger_0_2_0_1_1_0_valid : check fullLedger_0_2_0_1_1_0 (-1751) (-1501) (-1501) (-1251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_1_1_0_0_valid,fullLedger_0_2_0_1_1_0_1_valid⟩

def fullLedger_0_2_0_1_1_1 : Tree := (.axis 303 367 false)
theorem fullLedger_0_2_0_1_1_1_valid : check fullLedger_0_2_0_1_1_1 (-1751) (-1501) (-1251) (-1001)=true := by
  decide +kernel

def fullLedger_0_2_0_1_1 : Tree := (.second fullLedger_0_2_0_1_1_0 fullLedger_0_2_0_1_1_1)
theorem fullLedger_0_2_0_1_1_valid : check fullLedger_0_2_0_1_1 (-1751) (-1501) (-1501) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_1_1_0_valid,fullLedger_0_2_0_1_1_1_valid⟩

def fullLedger_0_2_0_1 : Tree := (.first fullLedger_0_2_0_1_0 fullLedger_0_2_0_1_1)
theorem fullLedger_0_2_0_1_valid : check fullLedger_0_2_0_1 (-2001) (-1501) (-1501) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_1_0_valid,fullLedger_0_2_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
