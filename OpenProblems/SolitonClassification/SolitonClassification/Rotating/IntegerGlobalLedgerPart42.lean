import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_0_1_1_1_0 : Tree := (.second (.first (.axis 674 994 true) (.second (.first (.axis 680 990 true) (.axis 684 990 false)) (.axis 682 998 true))) (.first (.axis 674 1010 true) (.second (.axis 682 1006 false) (.axis 682 1014 false))))
theorem fullLedger_2_1_0_1_0_1_1_1_0_valid : check fullLedger_2_1_0_1_0_1_1_1_0 1250 1375 2750 3000=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_1_1 : Tree := (.second (.first (.axis 700 994 false) (.axis 725 994 false)) (.axis 721 1010 false))
theorem fullLedger_2_1_0_1_0_1_1_1_1_valid : check fullLedger_2_1_0_1_0_1_1_1_1 1375 1500 2750 3000=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_1 : Tree := (.first fullLedger_2_1_0_1_0_1_1_1_0 fullLedger_2_1_0_1_0_1_1_1_1)
theorem fullLedger_2_1_0_1_0_1_1_1_valid : check fullLedger_2_1_0_1_0_1_1_1 1250 1500 2750 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_1_0_valid,fullLedger_2_1_0_1_0_1_1_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
