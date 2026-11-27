import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_0_1_1_0_1_0_1 : Tree := (.second (.first (.second (.axis 723 931 true) (.axis 723 937 true)) (.axis 727 933 true)) (.axis 725 966 true))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_1 1437 1500 2500 2625=true := by
  decide +kernel


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
