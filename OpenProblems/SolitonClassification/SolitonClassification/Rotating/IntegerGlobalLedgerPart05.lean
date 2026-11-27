import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_0_1_0 : Tree := (.second (.first (.axis 15 159 false) (.axis 47 159 false)) (.axis 31 223 false))
theorem fullLedger_0_0_1_0_valid : check fullLedger_0_0_1_0 (-4001) (-3501) (-3001) (-2001)=true := by
  decide +kernel

def fullLedger_0_0_1_1_0_0 : Tree := (.second (.first (.axis 71 143 false) (.axis 87 143 false)) (.axis 79 175 false))
theorem fullLedger_0_0_1_1_0_0_valid : check fullLedger_0_0_1_1_0_0 (-3501) (-3251) (-3001) (-2501)=true := by
  decide +kernel

def fullLedger_0_0_1_1_0_1_0_0 : Tree := (.second (.first (.axis 99 135 false) (.second (.axis 107 131 false) (.axis 107 139 false))) (.axis 103 151 false))
theorem fullLedger_0_0_1_1_0_1_0_0_valid : check fullLedger_0_0_1_1_0_1_0_0 (-3251) (-3126) (-3001) (-2751)=true := by
  decide +kernel

def fullLedger_0_0_1_1_0_1_0_1_0_0 : Tree := (.second (.first (.axis 113 131 false) (.second (.axis 117 129 false) (.axis 117 133 false))) (.axis 115 139 false))
theorem fullLedger_0_0_1_1_0_1_0_1_0_0_valid : check fullLedger_0_0_1_1_0_1_0_1_0_0 (-3126) (-3064) (-3001) (-2876)=true := by
  decide +kernel

def fullLedger_0_0_1_1_0_1_0_1_0_1 : Tree := (.second (.first (.second (.axis 121 129 false) (.axis 121 133 false)) (.second (.first (.axis 124 129 false) (.second Tree.short (.axis 126 130 false))) (.axis 125 133 true))) (.axis 123 139 false))
theorem fullLedger_0_0_1_1_0_1_0_1_0_1_valid : check fullLedger_0_0_1_1_0_1_0_1_0_1 (-3064) (-3001) (-3001) (-2876)=true := by
  decide +kernel

def fullLedger_0_0_1_1_0_1_0_1_0 : Tree := (.first fullLedger_0_0_1_1_0_1_0_1_0_0 fullLedger_0_0_1_1_0_1_0_1_0_1)
theorem fullLedger_0_0_1_1_0_1_0_1_0_valid : check fullLedger_0_0_1_1_0_1_0_1_0 (-3126) (-3001) (-3001) (-2876)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_1_1_0_1_0_1_0_0_valid,fullLedger_0_0_1_1_0_1_0_1_0_1_valid⟩

def fullLedger_0_0_1_1_0_1_0_1_1 : Tree := (.first (.axis 115 151 false) (.axis 123 151 false))
theorem fullLedger_0_0_1_1_0_1_0_1_1_valid : check fullLedger_0_0_1_1_0_1_0_1_1 (-3126) (-3001) (-2876) (-2751)=true := by
  decide +kernel

def fullLedger_0_0_1_1_0_1_0_1 : Tree := (.second fullLedger_0_0_1_1_0_1_0_1_0 fullLedger_0_0_1_1_0_1_0_1_1)
theorem fullLedger_0_0_1_1_0_1_0_1_valid : check fullLedger_0_0_1_1_0_1_0_1 (-3126) (-3001) (-3001) (-2751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_1_1_0_1_0_1_0_valid,fullLedger_0_0_1_1_0_1_0_1_1_valid⟩

def fullLedger_0_0_1_1_0_1_0 : Tree := (.first fullLedger_0_0_1_1_0_1_0_0 fullLedger_0_0_1_1_0_1_0_1)
theorem fullLedger_0_0_1_1_0_1_0_valid : check fullLedger_0_0_1_1_0_1_0 (-3251) (-3001) (-3001) (-2751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_1_1_0_1_0_0_valid,fullLedger_0_0_1_1_0_1_0_1_valid⟩

def fullLedger_0_0_1_1_0_1_1 : Tree := (.first (.axis 103 175 false) (.axis 119 175 false))
theorem fullLedger_0_0_1_1_0_1_1_valid : check fullLedger_0_0_1_1_0_1_1 (-3251) (-3001) (-2751) (-2501)=true := by
  decide +kernel

def fullLedger_0_0_1_1_0_1 : Tree := (.second fullLedger_0_0_1_1_0_1_0 fullLedger_0_0_1_1_0_1_1)
theorem fullLedger_0_0_1_1_0_1_valid : check fullLedger_0_0_1_1_0_1 (-3251) (-3001) (-3001) (-2501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_1_1_0_1_0_valid,fullLedger_0_0_1_1_0_1_1_valid⟩

def fullLedger_0_0_1_1_0 : Tree := (.first fullLedger_0_0_1_1_0_0 fullLedger_0_0_1_1_0_1)
theorem fullLedger_0_0_1_1_0_valid : check fullLedger_0_0_1_1_0 (-3501) (-3001) (-3001) (-2501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_1_1_0_0_valid,fullLedger_0_0_1_1_0_1_valid⟩

def fullLedger_0_0_1_1_1 : Tree := (.first (.axis 79 223 false) (.axis 111 223 false))
theorem fullLedger_0_0_1_1_1_valid : check fullLedger_0_0_1_1_1 (-3501) (-3001) (-2501) (-2001)=true := by
  decide +kernel

def fullLedger_0_0_1_1 : Tree := (.second fullLedger_0_0_1_1_0 fullLedger_0_0_1_1_1)
theorem fullLedger_0_0_1_1_valid : check fullLedger_0_0_1_1 (-3501) (-3001) (-3001) (-2001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_1_1_0_valid,fullLedger_0_0_1_1_1_valid⟩

def fullLedger_0_0_1 : Tree := (.first fullLedger_0_0_1_0 fullLedger_0_0_1_1)
theorem fullLedger_0_0_1_valid : check fullLedger_0_0_1 (-4001) (-3001) (-3001) (-2001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_1_0_valid,fullLedger_0_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
