import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_2_0_2_0_0_0 : Tree := (.square Tree.short (.first (.axis 320 325 true) (.second Tree.short (.axis 322 326 true))) Tree.short)
theorem fullLedger_0_2_0_2_0_0_0_valid : check fullLedger_0_2_0_2_0_0_0 (-1501) (-1439) (-1501) (-1439)=true := by
  decide +kernel

def fullLedger_0_2_0_2_0_0_1 : Tree := (.second (.first (.axis 321 329 false) (.first (.axis 324 329 false) (.second Tree.short (.axis 326 330 false)))) (.axis 323 333 false))
theorem fullLedger_0_2_0_2_0_0_1_valid : check fullLedger_0_2_0_2_0_0_1 (-1501) (-1439) (-1439) (-1376)=true := by
  decide +kernel

def fullLedger_0_2_0_2_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 328 332 false) Tree.short) (.axis 329 334 false)) Tree.short)
theorem fullLedger_0_2_0_2_0_0_2_valid : check fullLedger_0_2_0_2_0_0_2 (-1439) (-1376) (-1439) (-1376)=true := by
  decide +kernel

def fullLedger_0_2_0_2_0_0 : Tree := (.square fullLedger_0_2_0_2_0_0_0 fullLedger_0_2_0_2_0_0_1 fullLedger_0_2_0_2_0_0_2)
theorem fullLedger_0_2_0_2_0_0_valid : check fullLedger_0_2_0_2_0_0 (-1501) (-1376) (-1501) (-1376)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_2_0_0_0_valid,fullLedger_0_2_0_2_0_0_1_valid⟩,fullLedger_0_2_0_2_0_0_2_valid⟩⟩

def fullLedger_0_2_0_2_0_1 : Tree := (.first (.second (.axis 323 339 false) (.axis 323 347 false)) (.second (.first (.axis 329 339 true) (.second (.first (.axis 332 337 true) (.second Tree.short (.axis 334 338 true))) (.axis 333 341 true))) (.axis 331 347 true)))
theorem fullLedger_0_2_0_2_0_1_valid : check fullLedger_0_2_0_2_0_1 (-1501) (-1376) (-1376) (-1251)=true := by
  decide +kernel

def fullLedger_0_2_0_2_0_2_0 : Tree := (.square Tree.short (.first (.axis 336 341 true) (.second Tree.short (.axis 338 342 true))) Tree.short)
theorem fullLedger_0_2_0_2_0_2_0_valid : check fullLedger_0_2_0_2_0_2_0 (-1376) (-1314) (-1376) (-1314)=true := by
  decide +kernel

def fullLedger_0_2_0_2_0_2_1 : Tree := (.second (.first (.axis 337 345 true) (.first (.axis 340 345 true) (.second Tree.short (.axis 342 346 false)))) (.first (.axis 337 349 false) (.axis 341 349 false)))
theorem fullLedger_0_2_0_2_0_2_1_valid : check fullLedger_0_2_0_2_0_2_1 (-1376) (-1314) (-1314) (-1251)=true := by
  decide +kernel

def fullLedger_0_2_0_2_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 344 348 false) Tree.short) (.axis 345 350 false)) Tree.short)
theorem fullLedger_0_2_0_2_0_2_2_valid : check fullLedger_0_2_0_2_0_2_2 (-1314) (-1251) (-1314) (-1251)=true := by
  decide +kernel

def fullLedger_0_2_0_2_0_2 : Tree := (.square fullLedger_0_2_0_2_0_2_0 fullLedger_0_2_0_2_0_2_1 fullLedger_0_2_0_2_0_2_2)
theorem fullLedger_0_2_0_2_0_2_valid : check fullLedger_0_2_0_2_0_2 (-1376) (-1251) (-1376) (-1251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_2_0_2_0_valid,fullLedger_0_2_0_2_0_2_1_valid⟩,fullLedger_0_2_0_2_0_2_2_valid⟩⟩

def fullLedger_0_2_0_2_0 : Tree := (.square fullLedger_0_2_0_2_0_0 fullLedger_0_2_0_2_0_1 fullLedger_0_2_0_2_0_2)
theorem fullLedger_0_2_0_2_0_valid : check fullLedger_0_2_0_2_0 (-1501) (-1251) (-1501) (-1251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_2_0_0_valid,fullLedger_0_2_0_2_0_1_valid⟩,fullLedger_0_2_0_2_0_2_valid⟩⟩

def fullLedger_0_2_0_2_1_0 : Tree := (.second (.first (.axis 323 359 false) (.second (.axis 331 355 false) (.axis 331 363 false))) (.axis 327 375 false))
theorem fullLedger_0_2_0_2_1_0_valid : check fullLedger_0_2_0_2_1_0 (-1501) (-1376) (-1251) (-1001)=true := by
  decide +kernel

def fullLedger_0_2_0_2_1_1_0 : Tree := (.first (.second (.first (.axis 337 355 false) (.axis 341 355 false)) (.axis 339 363 false)) (.second (.first (.axis 345 355 true) (.second (.first (.axis 348 353 true) (.second Tree.short (.axis 350 354 true))) (.axis 349 357 true))) (.axis 347 363 true)))
theorem fullLedger_0_2_0_2_1_1_0_valid : check fullLedger_0_2_0_2_1_1_0 (-1376) (-1251) (-1251) (-1126)=true := by
  decide +kernel

def fullLedger_0_2_0_2_1_1_1 : Tree := (.first (.axis 339 375 false) (.second (.axis 347 371 false) (.axis 347 379 false)))
theorem fullLedger_0_2_0_2_1_1_1_valid : check fullLedger_0_2_0_2_1_1_1 (-1376) (-1251) (-1126) (-1001)=true := by
  decide +kernel

def fullLedger_0_2_0_2_1_1 : Tree := (.second fullLedger_0_2_0_2_1_1_0 fullLedger_0_2_0_2_1_1_1)
theorem fullLedger_0_2_0_2_1_1_valid : check fullLedger_0_2_0_2_1_1 (-1376) (-1251) (-1251) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_2_1_1_0_valid,fullLedger_0_2_0_2_1_1_1_valid⟩

def fullLedger_0_2_0_2_1 : Tree := (.first fullLedger_0_2_0_2_1_0 fullLedger_0_2_0_2_1_1)
theorem fullLedger_0_2_0_2_1_valid : check fullLedger_0_2_0_2_1 (-1501) (-1251) (-1251) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_2_1_0_valid,fullLedger_0_2_0_2_1_1_valid⟩

def fullLedger_0_2_0_2_2_0_0 : Tree := (.square Tree.short (.first (.axis 352 357 true) (.second Tree.short (.axis 354 358 true))) Tree.short)
theorem fullLedger_0_2_0_2_2_0_0_valid : check fullLedger_0_2_0_2_2_0_0 (-1251) (-1189) (-1251) (-1189)=true := by
  decide +kernel

def fullLedger_0_2_0_2_2_0_1 : Tree := (.second (.first (.axis 353 361 true) (.first (.axis 356 361 true) (.second Tree.short (.axis 358 362 false)))) (.axis 355 365 false))
theorem fullLedger_0_2_0_2_2_0_1_valid : check fullLedger_0_2_0_2_2_0_1 (-1251) (-1189) (-1189) (-1126)=true := by
  decide +kernel

def fullLedger_0_2_0_2_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 360 364 false) Tree.short) (.axis 361 366 false)) Tree.short)
theorem fullLedger_0_2_0_2_2_0_2_valid : check fullLedger_0_2_0_2_2_0_2 (-1189) (-1126) (-1189) (-1126)=true := by
  decide +kernel

def fullLedger_0_2_0_2_2_0 : Tree := (.square fullLedger_0_2_0_2_2_0_0 fullLedger_0_2_0_2_2_0_1 fullLedger_0_2_0_2_2_0_2)
theorem fullLedger_0_2_0_2_2_0_valid : check fullLedger_0_2_0_2_2_0 (-1251) (-1126) (-1251) (-1126)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_2_2_0_0_valid,fullLedger_0_2_0_2_2_0_1_valid⟩,fullLedger_0_2_0_2_2_0_2_valid⟩⟩

def fullLedger_0_2_0_2_2_1 : Tree := (.first (.second (.first (.axis 353 371 false) (.axis 357 371 false)) (.axis 355 379 false)) (.second (.first (.axis 361 371 true) (.second (.first (.axis 364 369 true) (.second Tree.short (.axis 366 370 true))) (.axis 365 373 true))) (.axis 363 379 true)))
theorem fullLedger_0_2_0_2_2_1_valid : check fullLedger_0_2_0_2_2_1 (-1251) (-1126) (-1126) (-1001)=true := by
  decide +kernel

def fullLedger_0_2_0_2_2_2_0 : Tree := (.square Tree.short (.first (.axis 368 373 true) (.second Tree.short (.axis 370 374 true))) Tree.short)
theorem fullLedger_0_2_0_2_2_2_0_valid : check fullLedger_0_2_0_2_2_2_0 (-1126) (-1064) (-1126) (-1064)=true := by
  decide +kernel

def fullLedger_0_2_0_2_2_2_1 : Tree := (.second (.first (.axis 369 377 true) (.first (.axis 372 377 false) (.second Tree.short (.axis 374 378 false)))) (.axis 371 381 false))
theorem fullLedger_0_2_0_2_2_2_1_valid : check fullLedger_0_2_0_2_2_2_1 (-1126) (-1064) (-1064) (-1001)=true := by
  decide +kernel

def fullLedger_0_2_0_2_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 376 380 false) Tree.short) (.axis 377 382 true)) Tree.short)
theorem fullLedger_0_2_0_2_2_2_2_valid : check fullLedger_0_2_0_2_2_2_2 (-1064) (-1001) (-1064) (-1001)=true := by
  decide +kernel

def fullLedger_0_2_0_2_2_2 : Tree := (.square fullLedger_0_2_0_2_2_2_0 fullLedger_0_2_0_2_2_2_1 fullLedger_0_2_0_2_2_2_2)
theorem fullLedger_0_2_0_2_2_2_valid : check fullLedger_0_2_0_2_2_2 (-1126) (-1001) (-1126) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_2_2_2_0_valid,fullLedger_0_2_0_2_2_2_1_valid⟩,fullLedger_0_2_0_2_2_2_2_valid⟩⟩

def fullLedger_0_2_0_2_2 : Tree := (.square fullLedger_0_2_0_2_2_0 fullLedger_0_2_0_2_2_1 fullLedger_0_2_0_2_2_2)
theorem fullLedger_0_2_0_2_2_valid : check fullLedger_0_2_0_2_2 (-1251) (-1001) (-1251) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_2_2_0_valid,fullLedger_0_2_0_2_2_1_valid⟩,fullLedger_0_2_0_2_2_2_valid⟩⟩

def fullLedger_0_2_0_2 : Tree := (.square fullLedger_0_2_0_2_0 fullLedger_0_2_0_2_1 fullLedger_0_2_0_2_2)
theorem fullLedger_0_2_0_2_valid : check fullLedger_0_2_0_2 (-1501) (-1001) (-1501) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_2_0_valid,fullLedger_0_2_0_2_1_valid⟩,fullLedger_0_2_0_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
