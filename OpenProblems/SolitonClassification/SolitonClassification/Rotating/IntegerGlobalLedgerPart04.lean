import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_0_0_2_0_0_0 : Tree := (.square Tree.short (.first (.axis 64 69 false) (.second Tree.short (.axis 66 70 false))) Tree.short)
theorem fullLedger_0_0_0_2_0_0_0_valid : check fullLedger_0_0_0_2_0_0_0 (-3501) (-3439) (-3501) (-3439)=true := by
  decide +kernel

def fullLedger_0_0_0_2_0_0_1 : Tree := (.second (.first (.axis 65 73 false) (.first (.axis 68 73 true) (.second Tree.short (.axis 70 74 true)))) (.axis 67 77 true))
theorem fullLedger_0_0_0_2_0_0_1_valid : check fullLedger_0_0_0_2_0_0_1 (-3501) (-3439) (-3439) (-3376)=true := by
  decide +kernel

def fullLedger_0_0_0_2_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 72 76 true) Tree.short) (.axis 73 78 true)) Tree.short)
theorem fullLedger_0_0_0_2_0_0_2_valid : check fullLedger_0_0_0_2_0_0_2 (-3439) (-3376) (-3439) (-3376)=true := by
  decide +kernel

def fullLedger_0_0_0_2_0_0 : Tree := (.square fullLedger_0_0_0_2_0_0_0 fullLedger_0_0_0_2_0_0_1 fullLedger_0_0_0_2_0_0_2)
theorem fullLedger_0_0_0_2_0_0_valid : check fullLedger_0_0_0_2_0_0 (-3501) (-3376) (-3501) (-3376)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_2_0_0_0_valid,fullLedger_0_0_0_2_0_0_1_valid⟩,fullLedger_0_0_0_2_0_0_2_valid⟩⟩

def fullLedger_0_0_0_2_0_1 : Tree := (.first (.second (.axis 67 83 false) (.axis 67 91 false)) (.second (.first (.second (.axis 73 81 true) (.axis 73 85 false)) (.second (.first (.axis 76 81 false) (.second Tree.short (.axis 78 82 false))) (.axis 77 85 false))) (.axis 75 91 false)))
theorem fullLedger_0_0_0_2_0_1_valid : check fullLedger_0_0_0_2_0_1 (-3501) (-3376) (-3376) (-3251)=true := by
  decide +kernel

def fullLedger_0_0_0_2_0_2_0 : Tree := (.square Tree.short (.first (.axis 80 85 true) (.second Tree.short (.axis 82 86 true))) Tree.short)
theorem fullLedger_0_0_0_2_0_2_0_valid : check fullLedger_0_0_0_2_0_2_0 (-3376) (-3314) (-3376) (-3314)=true := by
  decide +kernel

def fullLedger_0_0_0_2_0_2_1 : Tree := (.second (.first (.axis 81 89 true) (.first (.axis 84 89 true) (.second Tree.short (.axis 86 90 true)))) (.first (.axis 81 93 false) (.axis 85 93 false)))
theorem fullLedger_0_0_0_2_0_2_1_valid : check fullLedger_0_0_0_2_0_2_1 (-3376) (-3314) (-3314) (-3251)=true := by
  decide +kernel

def fullLedger_0_0_0_2_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 88 92 false) Tree.short) (.axis 89 94 false)) Tree.short)
theorem fullLedger_0_0_0_2_0_2_2_valid : check fullLedger_0_0_0_2_0_2_2 (-3314) (-3251) (-3314) (-3251)=true := by
  decide +kernel

def fullLedger_0_0_0_2_0_2 : Tree := (.square fullLedger_0_0_0_2_0_2_0 fullLedger_0_0_0_2_0_2_1 fullLedger_0_0_0_2_0_2_2)
theorem fullLedger_0_0_0_2_0_2_valid : check fullLedger_0_0_0_2_0_2 (-3376) (-3251) (-3376) (-3251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_2_0_2_0_valid,fullLedger_0_0_0_2_0_2_1_valid⟩,fullLedger_0_0_0_2_0_2_2_valid⟩⟩

def fullLedger_0_0_0_2_0 : Tree := (.square fullLedger_0_0_0_2_0_0 fullLedger_0_0_0_2_0_1 fullLedger_0_0_0_2_0_2)
theorem fullLedger_0_0_0_2_0_valid : check fullLedger_0_0_0_2_0 (-3501) (-3251) (-3501) (-3251)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_2_0_0_valid,fullLedger_0_0_0_2_0_1_valid⟩,fullLedger_0_0_0_2_0_2_valid⟩⟩

def fullLedger_0_0_0_2_1_0 : Tree := (.second (.first (.axis 67 103 false) (.axis 75 103 false)) (.axis 71 119 false))
theorem fullLedger_0_0_0_2_1_0_valid : check fullLedger_0_0_0_2_1_0 (-3501) (-3376) (-3251) (-3001)=true := by
  decide +kernel

def fullLedger_0_0_0_2_1_1_0_0 : Tree := (.second (.first (.axis 81 99 false) (.second (.axis 85 97 false) (.axis 85 101 false))) (.axis 83 107 false))
theorem fullLedger_0_0_0_2_1_1_0_0_valid : check fullLedger_0_0_0_2_1_1_0_0 (-3376) (-3314) (-3251) (-3126)=true := by
  decide +kernel

def fullLedger_0_0_0_2_1_1_0_1 : Tree := (.second (.first (.axis 89 99 true) (.second (.first (.axis 92 97 true) (.second Tree.short (.axis 94 98 true))) (.axis 93 101 true))) (.first (.axis 89 107 false) (.second (.axis 93 105 false) (.axis 93 109 false))))
theorem fullLedger_0_0_0_2_1_1_0_1_valid : check fullLedger_0_0_0_2_1_1_0_1 (-3314) (-3251) (-3251) (-3126)=true := by
  decide +kernel

def fullLedger_0_0_0_2_1_1_0 : Tree := (.first fullLedger_0_0_0_2_1_1_0_0 fullLedger_0_0_0_2_1_1_0_1)
theorem fullLedger_0_0_0_2_1_1_0_valid : check fullLedger_0_0_0_2_1_1_0 (-3376) (-3251) (-3251) (-3126)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_2_1_1_0_0_valid,fullLedger_0_0_0_2_1_1_0_1_valid⟩

def fullLedger_0_0_0_2_1_1_1 : Tree := (.first (.axis 83 119 false) (.axis 91 119 false))
theorem fullLedger_0_0_0_2_1_1_1_valid : check fullLedger_0_0_0_2_1_1_1 (-3376) (-3251) (-3126) (-3001)=true := by
  decide +kernel

def fullLedger_0_0_0_2_1_1 : Tree := (.second fullLedger_0_0_0_2_1_1_0 fullLedger_0_0_0_2_1_1_1)
theorem fullLedger_0_0_0_2_1_1_valid : check fullLedger_0_0_0_2_1_1 (-3376) (-3251) (-3251) (-3001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_2_1_1_0_valid,fullLedger_0_0_0_2_1_1_1_valid⟩

def fullLedger_0_0_0_2_1 : Tree := (.first fullLedger_0_0_0_2_1_0 fullLedger_0_0_0_2_1_1)
theorem fullLedger_0_0_0_2_1_valid : check fullLedger_0_0_0_2_1 (-3501) (-3251) (-3251) (-3001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_2_1_0_valid,fullLedger_0_0_0_2_1_1_valid⟩

def fullLedger_0_0_0_2_2_0_0 : Tree := (.square Tree.short (.first (.axis 96 101 true) (.second Tree.short (.axis 98 102 true))) Tree.short)
theorem fullLedger_0_0_0_2_2_0_0_valid : check fullLedger_0_0_0_2_2_0_0 (-3251) (-3189) (-3251) (-3189)=true := by
  decide +kernel

def fullLedger_0_0_0_2_2_0_1 : Tree := (.second (.first (.axis 97 105 false) (.first (.axis 100 105 false) (.second Tree.short (.axis 102 106 false)))) (.first (.axis 97 109 false) (.axis 101 109 false)))
theorem fullLedger_0_0_0_2_2_0_1_valid : check fullLedger_0_0_0_2_2_0_1 (-3251) (-3189) (-3189) (-3126)=true := by
  decide +kernel

def fullLedger_0_0_0_2_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 104 108 true) Tree.short) (.axis 105 110 true)) Tree.short)
theorem fullLedger_0_0_0_2_2_0_2_valid : check fullLedger_0_0_0_2_2_0_2 (-3189) (-3126) (-3189) (-3126)=true := by
  decide +kernel

def fullLedger_0_0_0_2_2_0 : Tree := (.square fullLedger_0_0_0_2_2_0_0 fullLedger_0_0_0_2_2_0_1 fullLedger_0_0_0_2_2_0_2)
theorem fullLedger_0_0_0_2_2_0_valid : check fullLedger_0_0_0_2_2_0 (-3251) (-3126) (-3251) (-3126)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_2_2_0_0_valid,fullLedger_0_0_0_2_2_0_1_valid⟩,fullLedger_0_0_0_2_2_0_2_valid⟩⟩

def fullLedger_0_0_0_2_2_1_0 : Tree := (.second (.axis 99 115 false) (.axis 99 123 false))
theorem fullLedger_0_0_0_2_2_1_0_valid : check fullLedger_0_0_0_2_2_1_0 (-3251) (-3189) (-3126) (-3001)=true := by
  decide +kernel

def fullLedger_0_0_0_2_2_1_1 : Tree := (.second (.first (.axis 105 115 true) (.second (.first (.axis 108 113 true) (.second Tree.short (.axis 110 114 false))) (.axis 109 117 false))) (.first (.axis 105 123 false) (.second (.axis 109 121 false) (.axis 109 125 false))))
theorem fullLedger_0_0_0_2_2_1_1_valid : check fullLedger_0_0_0_2_2_1_1 (-3189) (-3126) (-3126) (-3001)=true := by
  decide +kernel

def fullLedger_0_0_0_2_2_1 : Tree := (.first fullLedger_0_0_0_2_2_1_0 fullLedger_0_0_0_2_2_1_1)
theorem fullLedger_0_0_0_2_2_1_valid : check fullLedger_0_0_0_2_2_1 (-3251) (-3126) (-3126) (-3001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_2_2_1_0_valid,fullLedger_0_0_0_2_2_1_1_valid⟩

def fullLedger_0_0_0_2_2_2_0 : Tree := (.square Tree.short (.first (.axis 112 117 false) (.second Tree.short (.axis 114 118 false))) Tree.short)
theorem fullLedger_0_0_0_2_2_2_0_valid : check fullLedger_0_0_0_2_2_2_0 (-3126) (-3064) (-3126) (-3064)=true := by
  decide +kernel

def fullLedger_0_0_0_2_2_2_1 : Tree := (.second (.first (.axis 113 121 true) (.first (.axis 116 121 true) (.second Tree.short (.axis 118 122 true)))) (.axis 115 125 true))
theorem fullLedger_0_0_0_2_2_2_1_valid : check fullLedger_0_0_0_2_2_2_1 (-3126) (-3064) (-3064) (-3001)=true := by
  decide +kernel

def fullLedger_0_0_0_2_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 120 124 true) Tree.short) (.axis 121 126 true)) Tree.short)
theorem fullLedger_0_0_0_2_2_2_2_valid : check fullLedger_0_0_0_2_2_2_2 (-3064) (-3001) (-3064) (-3001)=true := by
  decide +kernel

def fullLedger_0_0_0_2_2_2 : Tree := (.square fullLedger_0_0_0_2_2_2_0 fullLedger_0_0_0_2_2_2_1 fullLedger_0_0_0_2_2_2_2)
theorem fullLedger_0_0_0_2_2_2_valid : check fullLedger_0_0_0_2_2_2 (-3126) (-3001) (-3126) (-3001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_2_2_2_0_valid,fullLedger_0_0_0_2_2_2_1_valid⟩,fullLedger_0_0_0_2_2_2_2_valid⟩⟩

def fullLedger_0_0_0_2_2 : Tree := (.square fullLedger_0_0_0_2_2_0 fullLedger_0_0_0_2_2_1 fullLedger_0_0_0_2_2_2)
theorem fullLedger_0_0_0_2_2_valid : check fullLedger_0_0_0_2_2 (-3251) (-3001) (-3251) (-3001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_2_2_0_valid,fullLedger_0_0_0_2_2_1_valid⟩,fullLedger_0_0_0_2_2_2_valid⟩⟩

def fullLedger_0_0_0_2 : Tree := (.square fullLedger_0_0_0_2_0 fullLedger_0_0_0_2_1 fullLedger_0_0_0_2_2)
theorem fullLedger_0_0_0_2_valid : check fullLedger_0_0_0_2 (-3501) (-3001) (-3501) (-3001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_2_0_valid,fullLedger_0_0_0_2_1_valid⟩,fullLedger_0_0_0_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
