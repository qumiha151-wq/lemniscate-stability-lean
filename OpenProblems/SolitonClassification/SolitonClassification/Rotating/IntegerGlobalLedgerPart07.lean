import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_0_2_1_0 : Tree := (.second (.first (.axis 135 207 false) (.axis 151 207 false)) (.axis 143 239 false))
theorem fullLedger_0_0_2_1_0_valid : check fullLedger_0_0_2_1_0 (-3001) (-2751) (-2501) (-2001)=true := by
  decide +kernel

def fullLedger_0_0_2_1_1_0_0 : Tree := (.second (.first (.axis 163 199 false) (.axis 171 199 false)) (.axis 167 215 false))
theorem fullLedger_0_0_2_1_1_0_0_valid : check fullLedger_0_0_2_1_1_0_0 (-2751) (-2626) (-2501) (-2251)=true := by
  decide +kernel

def fullLedger_0_0_2_1_1_0_1_0 : Tree := (.first (.second (.axis 179 195 true) (.axis 179 203 false)) (.second (.first (.axis 185 195 true) (.second (.first (.axis 188 193 true) (.second Tree.short (.axis 190 194 false))) (.axis 189 197 false))) (.first (.axis 185 203 false) (.axis 189 203 false))))
theorem fullLedger_0_0_2_1_1_0_1_0_valid : check fullLedger_0_0_2_1_1_0_1_0 (-2626) (-2501) (-2501) (-2376)=true := by
  decide +kernel

def fullLedger_0_0_2_1_1_0_1_1 : Tree := (.first (.axis 179 215 false) (.axis 187 215 false))
theorem fullLedger_0_0_2_1_1_0_1_1_valid : check fullLedger_0_0_2_1_1_0_1_1 (-2626) (-2501) (-2376) (-2251)=true := by
  decide +kernel

def fullLedger_0_0_2_1_1_0_1 : Tree := (.second fullLedger_0_0_2_1_1_0_1_0 fullLedger_0_0_2_1_1_0_1_1)
theorem fullLedger_0_0_2_1_1_0_1_valid : check fullLedger_0_0_2_1_1_0_1 (-2626) (-2501) (-2501) (-2251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_1_1_0_1_0_valid,fullLedger_0_0_2_1_1_0_1_1_valid⟩

def fullLedger_0_0_2_1_1_0 : Tree := (.first fullLedger_0_0_2_1_1_0_0 fullLedger_0_0_2_1_1_0_1)
theorem fullLedger_0_0_2_1_1_0_valid : check fullLedger_0_0_2_1_1_0 (-2751) (-2501) (-2501) (-2251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_1_1_0_0_valid,fullLedger_0_0_2_1_1_0_1_valid⟩

def fullLedger_0_0_2_1_1_1 : Tree := (.first (.axis 167 239 false) (.second (.axis 183 231 false) (.axis 183 247 false)))
theorem fullLedger_0_0_2_1_1_1_valid : check fullLedger_0_0_2_1_1_1 (-2751) (-2501) (-2251) (-2001)=true := by
  decide +kernel

def fullLedger_0_0_2_1_1 : Tree := (.second fullLedger_0_0_2_1_1_0 fullLedger_0_0_2_1_1_1)
theorem fullLedger_0_0_2_1_1_valid : check fullLedger_0_0_2_1_1 (-2751) (-2501) (-2501) (-2001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_1_1_0_valid,fullLedger_0_0_2_1_1_1_valid⟩

def fullLedger_0_0_2_1 : Tree := (.first fullLedger_0_0_2_1_0 fullLedger_0_0_2_1_1)
theorem fullLedger_0_0_2_1_valid : check fullLedger_0_0_2_1 (-3001) (-2501) (-2501) (-2001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_1_0_valid,fullLedger_0_0_2_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
