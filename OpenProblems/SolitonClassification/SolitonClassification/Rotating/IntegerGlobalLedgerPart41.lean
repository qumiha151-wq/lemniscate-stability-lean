import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_0_1_1_0_1_1 : Tree := (.first (.second (.axis 700 974 true) (.second (.axis 700 980 true) (.axis 700 984 false))) (.axis 725 978 true))
theorem fullLedger_2_1_0_1_0_1_1_0_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_1 1375 1500 2625 2750=true := by
  decide +kernel


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
