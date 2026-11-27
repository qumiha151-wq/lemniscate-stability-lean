import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_0_0_0_0_0_0 : Tree := (.square Tree.short (.first (.axis 0 5 false) (.second Tree.short (.axis 2 6 false))) Tree.short)
theorem fullLedger_0_0_0_0_0_0_0_valid : check fullLedger_0_0_0_0_0_0_0 (-4001) (-3939) (-4001) (-3939)=true := by
  decide +kernel

def fullLedger_0_0_0_0_0_0_1 : Tree := (.second (.first (.axis 1 9 true) (.first (.axis 4 9 true) (.second Tree.short (.axis 6 10 true)))) (.axis 3 13 true))
theorem fullLedger_0_0_0_0_0_0_1_valid : check fullLedger_0_0_0_0_0_0_1 (-4001) (-3939) (-3939) (-3876)=true := by
  decide +kernel

def fullLedger_0_0_0_0_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 8 12 true) Tree.short) (.axis 9 14 true)) Tree.short)
theorem fullLedger_0_0_0_0_0_0_2_valid : check fullLedger_0_0_0_0_0_0_2 (-3939) (-3876) (-3939) (-3876)=true := by
  decide +kernel

def fullLedger_0_0_0_0_0_0 : Tree := (.square fullLedger_0_0_0_0_0_0_0 fullLedger_0_0_0_0_0_0_1 fullLedger_0_0_0_0_0_0_2)
theorem fullLedger_0_0_0_0_0_0_valid : check fullLedger_0_0_0_0_0_0 (-4001) (-3876) (-4001) (-3876)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_0_0_0_valid,fullLedger_0_0_0_0_0_0_1_valid⟩,fullLedger_0_0_0_0_0_0_2_valid⟩⟩

def fullLedger_0_0_0_0_0_1_0 : Tree := (.second (.first (.axis 1 19 false) (.second (.axis 5 17 false) (.axis 5 21 false))) (.axis 3 27 false))
theorem fullLedger_0_0_0_0_0_1_0_valid : check fullLedger_0_0_0_0_0_1_0 (-4001) (-3939) (-3876) (-3751)=true := by
  decide +kernel

def fullLedger_0_0_0_0_0_1_1 : Tree := (.second (.first (.second (.axis 9 17 false) (.axis 9 21 false)) (.second (.first (.axis 12 17 false) (.second Tree.short (.axis 14 18 false))) (.axis 13 21 false))) (.axis 11 27 false))
theorem fullLedger_0_0_0_0_0_1_1_valid : check fullLedger_0_0_0_0_0_1_1 (-3939) (-3876) (-3876) (-3751)=true := by
  decide +kernel

def fullLedger_0_0_0_0_0_1 : Tree := (.first fullLedger_0_0_0_0_0_1_0 fullLedger_0_0_0_0_0_1_1)
theorem fullLedger_0_0_0_0_0_1_valid : check fullLedger_0_0_0_0_0_1 (-4001) (-3876) (-3876) (-3751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_0_1_0_valid,fullLedger_0_0_0_0_0_1_1_valid⟩

def fullLedger_0_0_0_0_0_2_0 : Tree := (.square Tree.short (.first (.axis 16 21 true) (.second Tree.short (.axis 18 22 true))) Tree.short)
theorem fullLedger_0_0_0_0_0_2_0_valid : check fullLedger_0_0_0_0_0_2_0 (-3876) (-3814) (-3876) (-3814)=true := by
  decide +kernel

def fullLedger_0_0_0_0_0_2_1 : Tree := (.second (.first (.axis 17 25 true) (.first (.axis 20 25 false) (.second Tree.short (.axis 22 26 false)))) (.first (.axis 17 29 false) (.axis 21 29 false)))
theorem fullLedger_0_0_0_0_0_2_1_valid : check fullLedger_0_0_0_0_0_2_1 (-3876) (-3814) (-3814) (-3751)=true := by
  decide +kernel

def fullLedger_0_0_0_0_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 24 28 false) Tree.short) (.axis 25 30 true)) Tree.short)
theorem fullLedger_0_0_0_0_0_2_2_valid : check fullLedger_0_0_0_0_0_2_2 (-3814) (-3751) (-3814) (-3751)=true := by
  decide +kernel

def fullLedger_0_0_0_0_0_2 : Tree := (.square fullLedger_0_0_0_0_0_2_0 fullLedger_0_0_0_0_0_2_1 fullLedger_0_0_0_0_0_2_2)
theorem fullLedger_0_0_0_0_0_2_valid : check fullLedger_0_0_0_0_0_2 (-3876) (-3751) (-3876) (-3751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_0_2_0_valid,fullLedger_0_0_0_0_0_2_1_valid⟩,fullLedger_0_0_0_0_0_2_2_valid⟩⟩

def fullLedger_0_0_0_0_0 : Tree := (.square fullLedger_0_0_0_0_0_0 fullLedger_0_0_0_0_0_1 fullLedger_0_0_0_0_0_2)
theorem fullLedger_0_0_0_0_0_valid : check fullLedger_0_0_0_0_0 (-4001) (-3751) (-4001) (-3751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_0_0_valid,fullLedger_0_0_0_0_0_1_valid⟩,fullLedger_0_0_0_0_0_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
