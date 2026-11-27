import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_0_1_1_0_0 : Tree := (.second (.first (.second (.axis 674 933 false) (.axis 674 966 true)) (.second (.axis 682 933 false) (.first (.axis 680 966 false) (.second (.axis 684 964 false) (.axis 684 968 false))))) (.first (.axis 674 978 true) (.second (.axis 682 974 true) (.axis 682 982 true))))
theorem fullLedger_2_1_0_1_0_1_1_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_0 1250 1375 2500 2750=true := by
  decide +kernel


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
