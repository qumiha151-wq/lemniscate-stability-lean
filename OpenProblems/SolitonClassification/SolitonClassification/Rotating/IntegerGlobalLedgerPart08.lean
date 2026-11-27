import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_0_2_2_0_0_0 : Tree := (.square Tree.short (.first (.axis 192 197 false) (.second Tree.short (.axis 194 198 false))) Tree.short)
theorem fullLedger_0_0_2_2_0_0_0_valid : check fullLedger_0_0_2_2_0_0_0 (-2501) (-2439) (-2501) (-2439)=true := by
  decide +kernel

def fullLedger_0_0_2_2_0_0_1 : Tree := (.second (.first (.axis 193 201 false) (.first (.axis 196 201 true) (.second Tree.short (.axis 198 202 true)))) (.axis 195 205 true))
theorem fullLedger_0_0_2_2_0_0_1_valid : check fullLedger_0_0_2_2_0_0_1 (-2501) (-2439) (-2439) (-2376)=true := by
  decide +kernel

def fullLedger_0_0_2_2_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 200 204 true) Tree.short) (.axis 201 206 true)) Tree.short)
theorem fullLedger_0_0_2_2_0_0_2_valid : check fullLedger_0_0_2_2_0_0_2 (-2439) (-2376) (-2439) (-2376)=true := by
  decide +kernel

def fullLedger_0_0_2_2_0_0 : Tree := (.square fullLedger_0_0_2_2_0_0_0 fullLedger_0_0_2_2_0_0_1 fullLedger_0_0_2_2_0_0_2)
theorem fullLedger_0_0_2_2_0_0_valid : check fullLedger_0_0_2_2_0_0 (-2501) (-2376) (-2501) (-2376)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_2_0_0_0_valid,fullLedger_0_0_2_2_0_0_1_valid⟩,fullLedger_0_0_2_2_0_0_2_valid⟩⟩

def fullLedger_0_0_2_2_0_1 : Tree := (.first (.second (.axis 195 211 false) (.axis 195 219 false)) (.second (.first (.axis 201 211 true) (.second (.first (.axis 204 209 false) (.second Tree.short (.axis 206 210 false))) (.axis 205 213 false))) (.first (.axis 201 219 false) (.axis 205 219 false))))
theorem fullLedger_0_0_2_2_0_1_valid : check fullLedger_0_0_2_2_0_1 (-2501) (-2376) (-2376) (-2251)=true := by
  decide +kernel

def fullLedger_0_0_2_2_0_2_0 : Tree := (.square Tree.short (.first (.axis 208 213 false) (.second Tree.short (.axis 210 214 false))) Tree.short)
theorem fullLedger_0_0_2_2_0_2_0_valid : check fullLedger_0_0_2_2_0_2_0 (-2376) (-2314) (-2376) (-2314)=true := by
  decide +kernel

def fullLedger_0_0_2_2_0_2_1 : Tree := (.second (.first (.axis 209 217 false) (.first (.axis 212 217 true) (.second Tree.short (.axis 214 218 true)))) (.axis 211 221 true))
theorem fullLedger_0_0_2_2_0_2_1_valid : check fullLedger_0_0_2_2_0_2_1 (-2376) (-2314) (-2314) (-2251)=true := by
  decide +kernel

def fullLedger_0_0_2_2_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 216 220 true) Tree.short) (.axis 217 222 true)) Tree.short)
theorem fullLedger_0_0_2_2_0_2_2_valid : check fullLedger_0_0_2_2_0_2_2 (-2314) (-2251) (-2314) (-2251)=true := by
  decide +kernel

def fullLedger_0_0_2_2_0_2 : Tree := (.square fullLedger_0_0_2_2_0_2_0 fullLedger_0_0_2_2_0_2_1 fullLedger_0_0_2_2_0_2_2)
theorem fullLedger_0_0_2_2_0_2_valid : check fullLedger_0_0_2_2_0_2 (-2376) (-2251) (-2376) (-2251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_2_0_2_0_valid,fullLedger_0_0_2_2_0_2_1_valid⟩,fullLedger_0_0_2_2_0_2_2_valid⟩⟩

def fullLedger_0_0_2_2_0 : Tree := (.square fullLedger_0_0_2_2_0_0 fullLedger_0_0_2_2_0_1 fullLedger_0_0_2_2_0_2)
theorem fullLedger_0_0_2_2_0_valid : check fullLedger_0_0_2_2_0 (-2501) (-2251) (-2501) (-2251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_2_0_0_valid,fullLedger_0_0_2_2_0_1_valid⟩,fullLedger_0_0_2_2_0_2_valid⟩⟩

def fullLedger_0_0_2_2_1_0 : Tree := (.second (.first (.axis 195 231 false) (.second (.axis 203 227 true) (.axis 203 235 false))) (.axis 199 247 false))
theorem fullLedger_0_0_2_2_1_0_valid : check fullLedger_0_0_2_2_1_0 (-2501) (-2376) (-2251) (-2001)=true := by
  decide +kernel

def fullLedger_0_0_2_2_1_1_0 : Tree := (.first (.axis 211 231 true) (.second (.first (.axis 217 227 true) (.second (.first (.axis 220 225 true) (.second Tree.short (.axis 222 226 true))) (.axis 221 229 true))) (.first (.axis 217 235 false) (.axis 221 235 false))))
theorem fullLedger_0_0_2_2_1_1_0_valid : check fullLedger_0_0_2_2_1_1_0 (-2376) (-2251) (-2251) (-2126)=true := by
  decide +kernel

def fullLedger_0_0_2_2_1_1_1 : Tree := (.first (.axis 211 247 false) (.axis 219 247 false))
theorem fullLedger_0_0_2_2_1_1_1_valid : check fullLedger_0_0_2_2_1_1_1 (-2376) (-2251) (-2126) (-2001)=true := by
  decide +kernel

def fullLedger_0_0_2_2_1_1 : Tree := (.second fullLedger_0_0_2_2_1_1_0 fullLedger_0_0_2_2_1_1_1)
theorem fullLedger_0_0_2_2_1_1_valid : check fullLedger_0_0_2_2_1_1 (-2376) (-2251) (-2251) (-2001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_2_1_1_0_valid,fullLedger_0_0_2_2_1_1_1_valid⟩

def fullLedger_0_0_2_2_1 : Tree := (.first fullLedger_0_0_2_2_1_0 fullLedger_0_0_2_2_1_1)
theorem fullLedger_0_0_2_2_1_valid : check fullLedger_0_0_2_2_1 (-2501) (-2251) (-2251) (-2001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_2_1_0_valid,fullLedger_0_0_2_2_1_1_valid⟩

def fullLedger_0_0_2_2_2_0_0 : Tree := (.square Tree.short (.first (.axis 224 229 true) (.second Tree.short (.axis 226 230 false))) Tree.short)
theorem fullLedger_0_0_2_2_2_0_0_valid : check fullLedger_0_0_2_2_2_0_0 (-2251) (-2189) (-2251) (-2189)=true := by
  decide +kernel

def fullLedger_0_0_2_2_2_0_1 : Tree := (.second (.first (.axis 225 233 false) (.first (.axis 228 233 false) (.second Tree.short (.axis 230 234 false)))) (.axis 227 237 false))
theorem fullLedger_0_0_2_2_2_0_1_valid : check fullLedger_0_0_2_2_2_0_1 (-2251) (-2189) (-2189) (-2126)=true := by
  decide +kernel

def fullLedger_0_0_2_2_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 232 236 false) Tree.short) (.axis 233 238 true)) Tree.short)
theorem fullLedger_0_0_2_2_2_0_2_valid : check fullLedger_0_0_2_2_2_0_2 (-2189) (-2126) (-2189) (-2126)=true := by
  decide +kernel

def fullLedger_0_0_2_2_2_0 : Tree := (.square fullLedger_0_0_2_2_2_0_0 fullLedger_0_0_2_2_2_0_1 fullLedger_0_0_2_2_2_0_2)
theorem fullLedger_0_0_2_2_2_0_valid : check fullLedger_0_0_2_2_2_0 (-2251) (-2126) (-2251) (-2126)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_2_2_0_0_valid,fullLedger_0_0_2_2_2_0_1_valid⟩,fullLedger_0_0_2_2_2_0_2_valid⟩⟩

def fullLedger_0_0_2_2_2_1 : Tree := (.first (.axis 227 247 false) (.second (.first (.axis 233 243 true) (.second (.first (.axis 236 241 true) (.second Tree.short (.axis 238 242 true))) (.axis 237 245 true))) (.axis 235 251 false)))
theorem fullLedger_0_0_2_2_2_1_valid : check fullLedger_0_0_2_2_2_1 (-2251) (-2126) (-2126) (-2001)=true := by
  decide +kernel

def fullLedger_0_0_2_2_2_2_0 : Tree := (.square Tree.short (.first (.axis 240 245 true) (.second Tree.short (.axis 242 246 false))) Tree.short)
theorem fullLedger_0_0_2_2_2_2_0_valid : check fullLedger_0_0_2_2_2_2_0 (-2126) (-2064) (-2126) (-2064)=true := by
  decide +kernel

def fullLedger_0_0_2_2_2_2_1 : Tree := (.second (.first (.axis 241 249 false) (.first (.axis 244 249 false) (.second Tree.short (.axis 246 250 false)))) (.axis 243 253 false))
theorem fullLedger_0_0_2_2_2_2_1_valid : check fullLedger_0_0_2_2_2_2_1 (-2126) (-2064) (-2064) (-2001)=true := by
  decide +kernel

def fullLedger_0_0_2_2_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 248 252 false) Tree.short) (.axis 249 254 false)) Tree.short)
theorem fullLedger_0_0_2_2_2_2_2_valid : check fullLedger_0_0_2_2_2_2_2 (-2064) (-2001) (-2064) (-2001)=true := by
  decide +kernel

def fullLedger_0_0_2_2_2_2 : Tree := (.square fullLedger_0_0_2_2_2_2_0 fullLedger_0_0_2_2_2_2_1 fullLedger_0_0_2_2_2_2_2)
theorem fullLedger_0_0_2_2_2_2_valid : check fullLedger_0_0_2_2_2_2 (-2126) (-2001) (-2126) (-2001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_2_2_2_0_valid,fullLedger_0_0_2_2_2_2_1_valid⟩,fullLedger_0_0_2_2_2_2_2_valid⟩⟩

def fullLedger_0_0_2_2_2 : Tree := (.square fullLedger_0_0_2_2_2_0 fullLedger_0_0_2_2_2_1 fullLedger_0_0_2_2_2_2)
theorem fullLedger_0_0_2_2_2_valid : check fullLedger_0_0_2_2_2 (-2251) (-2001) (-2251) (-2001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_2_2_0_valid,fullLedger_0_0_2_2_2_1_valid⟩,fullLedger_0_0_2_2_2_2_valid⟩⟩

def fullLedger_0_0_2_2 : Tree := (.square fullLedger_0_0_2_2_0 fullLedger_0_0_2_2_1 fullLedger_0_0_2_2_2)
theorem fullLedger_0_0_2_2_valid : check fullLedger_0_0_2_2 (-2501) (-2001) (-2501) (-2001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_2_0_valid,fullLedger_0_0_2_2_1_valid⟩,fullLedger_0_0_2_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
