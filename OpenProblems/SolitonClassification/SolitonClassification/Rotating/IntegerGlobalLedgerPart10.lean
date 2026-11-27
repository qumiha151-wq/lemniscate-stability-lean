import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_2_0_0_0_0_0 : Tree := (.square Tree.short (.first (.axis 256 261 true) (.second Tree.short (.axis 258 262 true))) Tree.short)
theorem fullLedger_0_2_0_0_0_0_0_valid : check fullLedger_0_2_0_0_0_0_0 (-2001) (-1939) (-2001) (-1939)=true := by
  decide +kernel

def fullLedger_0_2_0_0_0_0_1 : Tree := (.second (.first (.axis 257 265 true) (.first (.axis 260 265 true) (.second Tree.short (.axis 262 266 false)))) (.axis 259 269 false))
theorem fullLedger_0_2_0_0_0_0_1_valid : check fullLedger_0_2_0_0_0_0_1 (-2001) (-1939) (-1939) (-1876)=true := by
  decide +kernel

def fullLedger_0_2_0_0_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 264 268 false) Tree.short) (.axis 265 270 false)) Tree.short)
theorem fullLedger_0_2_0_0_0_0_2_valid : check fullLedger_0_2_0_0_0_0_2 (-1939) (-1876) (-1939) (-1876)=true := by
  decide +kernel

def fullLedger_0_2_0_0_0_0 : Tree := (.square fullLedger_0_2_0_0_0_0_0 fullLedger_0_2_0_0_0_0_1 fullLedger_0_2_0_0_0_0_2)
theorem fullLedger_0_2_0_0_0_0_valid : check fullLedger_0_2_0_0_0_0 (-2001) (-1876) (-2001) (-1876)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_0_0_0_0_valid,fullLedger_0_2_0_0_0_0_1_valid⟩,fullLedger_0_2_0_0_0_0_2_valid⟩⟩

def fullLedger_0_2_0_0_0_1 : Tree := (.first (.axis 259 279 false) (.second (.first (.axis 265 275 false) (.second (.first (.axis 268 273 false) (.second Tree.short (.axis 270 274 false))) (.axis 269 277 false))) (.axis 267 283 false)))
theorem fullLedger_0_2_0_0_0_1_valid : check fullLedger_0_2_0_0_0_1 (-2001) (-1876) (-1876) (-1751)=true := by
  decide +kernel

def fullLedger_0_2_0_0_0_2_0 : Tree := (.square Tree.short (.first (.axis 272 277 false) (.second Tree.short (.axis 274 278 false))) Tree.short)
theorem fullLedger_0_2_0_0_0_2_0_valid : check fullLedger_0_2_0_0_0_2_0 (-1876) (-1814) (-1876) (-1814)=true := by
  decide +kernel

def fullLedger_0_2_0_0_0_2_1 : Tree := (.second (.first (.axis 273 281 false) (.first (.axis 276 281 false) (.second Tree.short (.axis 278 282 false)))) (.axis 275 285 false))
theorem fullLedger_0_2_0_0_0_2_1_valid : check fullLedger_0_2_0_0_0_2_1 (-1876) (-1814) (-1814) (-1751)=true := by
  decide +kernel

def fullLedger_0_2_0_0_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 280 284 false) Tree.short) (.axis 281 286 true)) Tree.short)
theorem fullLedger_0_2_0_0_0_2_2_valid : check fullLedger_0_2_0_0_0_2_2 (-1814) (-1751) (-1814) (-1751)=true := by
  decide +kernel

def fullLedger_0_2_0_0_0_2 : Tree := (.square fullLedger_0_2_0_0_0_2_0 fullLedger_0_2_0_0_0_2_1 fullLedger_0_2_0_0_0_2_2)
theorem fullLedger_0_2_0_0_0_2_valid : check fullLedger_0_2_0_0_0_2 (-1876) (-1751) (-1876) (-1751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_0_0_2_0_valid,fullLedger_0_2_0_0_0_2_1_valid⟩,fullLedger_0_2_0_0_0_2_2_valid⟩⟩

def fullLedger_0_2_0_0_0 : Tree := (.square fullLedger_0_2_0_0_0_0 fullLedger_0_2_0_0_0_1 fullLedger_0_2_0_0_0_2)
theorem fullLedger_0_2_0_0_0_valid : check fullLedger_0_2_0_0_0 (-2001) (-1751) (-2001) (-1751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_0_0_0_valid,fullLedger_0_2_0_0_0_1_valid⟩,fullLedger_0_2_0_0_0_2_valid⟩⟩

def fullLedger_0_2_0_0_1 : Tree := (.first (.axis 263 303 true) (.second (.first (.axis 275 295 true) (.second (.first (.axis 281 291 true) (.second (.first (.axis 284 289 true) (.second Tree.short (.axis 286 290 true))) (.axis 285 293 true))) (.axis 283 299 true))) (.axis 279 311 true)))
theorem fullLedger_0_2_0_0_1_valid : check fullLedger_0_2_0_0_1 (-2001) (-1751) (-1751) (-1501)=true := by
  decide +kernel

def fullLedger_0_2_0_0_2_0_0 : Tree := (.square Tree.short (.first (.axis 288 293 true) (.second Tree.short (.axis 290 294 true))) Tree.short)
theorem fullLedger_0_2_0_0_2_0_0_valid : check fullLedger_0_2_0_0_2_0_0 (-1751) (-1689) (-1751) (-1689)=true := by
  decide +kernel

def fullLedger_0_2_0_0_2_0_1 : Tree := (.second (.first (.axis 289 297 true) (.first (.axis 292 297 true) (.second Tree.short (.axis 294 298 true)))) (.axis 291 301 true))
theorem fullLedger_0_2_0_0_2_0_1_valid : check fullLedger_0_2_0_0_2_0_1 (-1751) (-1689) (-1689) (-1626)=true := by
  decide +kernel

def fullLedger_0_2_0_0_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 296 300 true) Tree.short) (.axis 297 302 true)) Tree.short)
theorem fullLedger_0_2_0_0_2_0_2_valid : check fullLedger_0_2_0_0_2_0_2 (-1689) (-1626) (-1689) (-1626)=true := by
  decide +kernel

def fullLedger_0_2_0_0_2_0 : Tree := (.square fullLedger_0_2_0_0_2_0_0 fullLedger_0_2_0_0_2_0_1 fullLedger_0_2_0_0_2_0_2)
theorem fullLedger_0_2_0_0_2_0_valid : check fullLedger_0_2_0_0_2_0 (-1751) (-1626) (-1751) (-1626)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_0_2_0_0_valid,fullLedger_0_2_0_0_2_0_1_valid⟩,fullLedger_0_2_0_0_2_0_2_valid⟩⟩

def fullLedger_0_2_0_0_2_1 : Tree := (.first (.axis 291 311 true) (.second (.first (.axis 297 307 true) (.second (.first (.axis 300 305 true) (.second Tree.short (.axis 302 306 false))) (.axis 301 309 false))) (.axis 299 315 false)))
theorem fullLedger_0_2_0_0_2_1_valid : check fullLedger_0_2_0_0_2_1 (-1751) (-1626) (-1626) (-1501)=true := by
  decide +kernel

def fullLedger_0_2_0_0_2_2_0 : Tree := (.square Tree.short (.first (.axis 304 309 false) (.second Tree.short (.axis 306 310 false))) Tree.short)
theorem fullLedger_0_2_0_0_2_2_0_valid : check fullLedger_0_2_0_0_2_2_0 (-1626) (-1564) (-1626) (-1564)=true := by
  decide +kernel

def fullLedger_0_2_0_0_2_2_1 : Tree := (.second (.first (.axis 305 313 false) (.first (.axis 308 313 false) (.second Tree.short (.axis 310 314 false)))) (.axis 307 317 false))
theorem fullLedger_0_2_0_0_2_2_1_valid : check fullLedger_0_2_0_0_2_2_1 (-1626) (-1564) (-1564) (-1501)=true := by
  decide +kernel

def fullLedger_0_2_0_0_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 312 316 true) Tree.short) (.axis 313 318 true)) Tree.short)
theorem fullLedger_0_2_0_0_2_2_2_valid : check fullLedger_0_2_0_0_2_2_2 (-1564) (-1501) (-1564) (-1501)=true := by
  decide +kernel

def fullLedger_0_2_0_0_2_2 : Tree := (.square fullLedger_0_2_0_0_2_2_0 fullLedger_0_2_0_0_2_2_1 fullLedger_0_2_0_0_2_2_2)
theorem fullLedger_0_2_0_0_2_2_valid : check fullLedger_0_2_0_0_2_2 (-1626) (-1501) (-1626) (-1501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_0_2_2_0_valid,fullLedger_0_2_0_0_2_2_1_valid⟩,fullLedger_0_2_0_0_2_2_2_valid⟩⟩

def fullLedger_0_2_0_0_2 : Tree := (.square fullLedger_0_2_0_0_2_0 fullLedger_0_2_0_0_2_1 fullLedger_0_2_0_0_2_2)
theorem fullLedger_0_2_0_0_2_valid : check fullLedger_0_2_0_0_2 (-1751) (-1501) (-1751) (-1501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_0_2_0_valid,fullLedger_0_2_0_0_2_1_valid⟩,fullLedger_0_2_0_0_2_2_valid⟩⟩

def fullLedger_0_2_0_0 : Tree := (.square fullLedger_0_2_0_0_0 fullLedger_0_2_0_0_1 fullLedger_0_2_0_0_2)
theorem fullLedger_0_2_0_0_valid : check fullLedger_0_2_0_0 (-2001) (-1501) (-2001) (-1501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_0_0_valid,fullLedger_0_2_0_0_1_valid⟩,fullLedger_0_2_0_0_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
