import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_1_0_0_0 : Tree := (.second (.axis 31 287 false) (.first (.axis 15 351 false) (.axis 47 351 false)))
theorem fullLedger_0_1_0_0_0_valid : check fullLedger_0_1_0_0_0 (-4001) (-3501) (-2001) (-1001)=true := by
  decide +kernel

def fullLedger_0_1_0_0_1 : Tree := (.second (.first (.axis 79 287 false) (.axis 111 287 false)) (.first (.second (.axis 79 335 false) (.axis 79 367 false)) (.second (.axis 111 335 false) (.first (.axis 103 367 true) (.axis 119 367 true)))))
theorem fullLedger_0_1_0_0_1_valid : check fullLedger_0_1_0_0_1 (-3501) (-3001) (-2001) (-1001)=true := by
  decide +kernel

def fullLedger_0_1_0_0 : Tree := (.first fullLedger_0_1_0_0_0 fullLedger_0_1_0_0_1)
theorem fullLedger_0_1_0_0_valid : check fullLedger_0_1_0_0 (-4001) (-3001) (-2001) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_0_0_0_valid,fullLedger_0_1_0_0_1_valid⟩

def fullLedger_0_1_0_1_0 : Tree := (.second (.first (.second (.axis 143 271 false) (.axis 143 303 false)) (.second (.axis 175 271 false) (.axis 175 303 true))) (.first (.second (.first (.axis 135 335 true) (.axis 151 335 true)) (.axis 143 367 true)) (.second (.axis 175 335 true) (.axis 175 367 true))))
theorem fullLedger_0_1_0_1_0_valid : check fullLedger_0_1_0_1_0 (-3001) (-2501) (-2001) (-1001)=true := by
  decide +kernel

def fullLedger_0_1_0_1_1_0_0 : Tree := (.second (.first (.second (.axis 199 263 false) (.first (.axis 195 279 false) (.axis 203 279 false))) (.second (.axis 215 263 false) (.axis 215 279 true))) (.axis 207 303 true))
theorem fullLedger_0_1_0_1_1_0_0_valid : check fullLedger_0_1_0_1_1_0_0 (-2501) (-2251) (-2001) (-1501)=true := by
  decide +kernel

def fullLedger_0_1_0_1_1_0_1_0_0 : Tree := (.second (.first (.axis 227 263 false) (.second (.axis 235 259 false) (.axis 235 267 false))) (.first (.second (.axis 227 275 false) (.axis 227 283 true)) (.second (.first (.second (.axis 233 273 false) (.axis 233 277 true)) (.axis 237 275 true)) (.axis 235 283 true))))
theorem fullLedger_0_1_0_1_1_0_1_0_0_valid : check fullLedger_0_1_0_1_1_0_1_0_0 (-2251) (-2126) (-2001) (-1751)=true := by
  decide +kernel

def fullLedger_0_1_0_1_1_0_1_0_1 : Tree := (.second (.first (.second (.axis 243 259 false) (.axis 243 267 true)) (.second (.first (.axis 249 259 true) (.second (.first (.axis 252 257 true) (.second Tree.short (.axis 254 258 true))) (.axis 253 261 true))) (.axis 251 267 true))) (.axis 247 279 true))
theorem fullLedger_0_1_0_1_1_0_1_0_1_valid : check fullLedger_0_1_0_1_1_0_1_0_1 (-2126) (-2001) (-2001) (-1751)=true := by
  decide +kernel

def fullLedger_0_1_0_1_1_0_1_0 : Tree := (.first fullLedger_0_1_0_1_1_0_1_0_0 fullLedger_0_1_0_1_1_0_1_0_1)
theorem fullLedger_0_1_0_1_1_0_1_0_valid : check fullLedger_0_1_0_1_1_0_1_0 (-2251) (-2001) (-2001) (-1751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_0_1_1_0_1_0_0_valid,fullLedger_0_1_0_1_1_0_1_0_1_valid⟩

def fullLedger_0_1_0_1_1_0_1_1 : Tree := (.axis 239 303 true)
theorem fullLedger_0_1_0_1_1_0_1_1_valid : check fullLedger_0_1_0_1_1_0_1_1 (-2251) (-2001) (-1751) (-1501)=true := by
  decide +kernel

def fullLedger_0_1_0_1_1_0_1 : Tree := (.second fullLedger_0_1_0_1_1_0_1_0 fullLedger_0_1_0_1_1_0_1_1)
theorem fullLedger_0_1_0_1_1_0_1_valid : check fullLedger_0_1_0_1_1_0_1 (-2251) (-2001) (-2001) (-1501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_0_1_1_0_1_0_valid,fullLedger_0_1_0_1_1_0_1_1_valid⟩

def fullLedger_0_1_0_1_1_0 : Tree := (.first fullLedger_0_1_0_1_1_0_0 fullLedger_0_1_0_1_1_0_1)
theorem fullLedger_0_1_0_1_1_0_valid : check fullLedger_0_1_0_1_1_0 (-2501) (-2001) (-2001) (-1501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_0_1_1_0_0_valid,fullLedger_0_1_0_1_1_0_1_valid⟩

def fullLedger_0_1_0_1_1_1 : Tree := (.first (.second (.axis 207 335 true) (.axis 207 367 true)) (.second (.first (.second (.axis 231 327 true) (.axis 231 343 false)) (.axis 247 335 false)) (.axis 239 367 false)))
theorem fullLedger_0_1_0_1_1_1_valid : check fullLedger_0_1_0_1_1_1 (-2501) (-2001) (-1501) (-1001)=true := by
  decide +kernel

def fullLedger_0_1_0_1_1 : Tree := (.second fullLedger_0_1_0_1_1_0 fullLedger_0_1_0_1_1_1)
theorem fullLedger_0_1_0_1_1_valid : check fullLedger_0_1_0_1_1 (-2501) (-2001) (-2001) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_0_1_1_0_valid,fullLedger_0_1_0_1_1_1_valid⟩

def fullLedger_0_1_0_1 : Tree := (.first fullLedger_0_1_0_1_0 fullLedger_0_1_0_1_1)
theorem fullLedger_0_1_0_1_valid : check fullLedger_0_1_0_1 (-3001) (-2001) (-2001) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_0_1_0_valid,fullLedger_0_1_0_1_1_valid⟩

def fullLedger_0_1_0 : Tree := (.first fullLedger_0_1_0_0 fullLedger_0_1_0_1)
theorem fullLedger_0_1_0_valid : check fullLedger_0_1_0 (-4001) (-2001) (-2001) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_0_0_valid,fullLedger_0_1_0_1_valid⟩

def fullLedger_0_1_1_0_0 : Tree := (.first (.first (.second (.axis 15 399 false) (.axis 15 431 false)) (.second (.axis 47 399 false) (.axis 47 431 true))) (.first (.second (.axis 79 399 true) (.axis 79 431 true)) (.second (.axis 111 399 true) (.axis 111 431 true))))
theorem fullLedger_0_1_1_0_0_valid : check fullLedger_0_1_1_0_0 (-4001) (-3001) (-1001) (-501)=true := by
  decide +kernel

def fullLedger_0_1_1_0_1_0 : Tree := (.second (.first (.axis 15 463 true) (.first (.axis 39 463 true) (.axis 55 463 true))) (.first (.axis 15 495 true) (.second (.axis 47 487 true) (.axis 47 503 true))))
theorem fullLedger_0_1_1_0_1_0_valid : check fullLedger_0_1_1_0_1_0 (-4001) (-3501) (-501) 0=true := by
  decide +kernel

def fullLedger_0_1_1_0_1_1 : Tree := (.second (.first (.axis 79 463 true) (.first (.axis 103 463 true) (.axis 119 463 false))) (.first (.axis 79 495 true) (.axis 111 495 false)))
theorem fullLedger_0_1_1_0_1_1_valid : check fullLedger_0_1_1_0_1_1 (-3501) (-3001) (-501) 0=true := by
  decide +kernel

def fullLedger_0_1_1_0_1 : Tree := (.first fullLedger_0_1_1_0_1_0 fullLedger_0_1_1_0_1_1)
theorem fullLedger_0_1_1_0_1_valid : check fullLedger_0_1_1_0_1 (-4001) (-3001) (-501) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_1_0_1_0_valid,fullLedger_0_1_1_0_1_1_valid⟩

def fullLedger_0_1_1_0 : Tree := (.second fullLedger_0_1_1_0_0 fullLedger_0_1_1_0_1)
theorem fullLedger_0_1_1_0_valid : check fullLedger_0_1_1_0 (-4001) (-3001) (-1001) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_1_0_0_valid,fullLedger_0_1_1_0_1_valid⟩

def fullLedger_0_1_1_1_0 : Tree := (.first (.first (.second (.axis 143 399 true) (.axis 143 431 true)) (.second (.axis 175 399 true) (.axis 175 431 false))) (.first (.second (.axis 207 399 false) (.axis 207 431 false)) (.axis 239 415 false)))
theorem fullLedger_0_1_1_1_0_valid : check fullLedger_0_1_1_1_0 (-3001) (-2001) (-1001) (-501)=true := by
  decide +kernel

def fullLedger_0_1_1_1_1 : Tree := (.first (.second (.first (.axis 143 463 false) (.axis 175 463 false)) (.axis 159 495 false)) (.axis 223 479 false))
theorem fullLedger_0_1_1_1_1_valid : check fullLedger_0_1_1_1_1 (-3001) (-2001) (-501) 0=true := by
  decide +kernel

def fullLedger_0_1_1_1 : Tree := (.second fullLedger_0_1_1_1_0 fullLedger_0_1_1_1_1)
theorem fullLedger_0_1_1_1_valid : check fullLedger_0_1_1_1 (-3001) (-2001) (-1001) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_1_1_0_valid,fullLedger_0_1_1_1_1_valid⟩

def fullLedger_0_1_1 : Tree := (.first fullLedger_0_1_1_0 fullLedger_0_1_1_1)
theorem fullLedger_0_1_1_valid : check fullLedger_0_1_1 (-4001) (-2001) (-1001) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_1_0_valid,fullLedger_0_1_1_1_valid⟩

def fullLedger_0_1 : Tree := (.second fullLedger_0_1_0 fullLedger_0_1_1)
theorem fullLedger_0_1_valid : check fullLedger_0_1 (-4001) (-2001) (-2001) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_1_0_valid,fullLedger_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
