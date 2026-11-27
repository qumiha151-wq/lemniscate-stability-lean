import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_1_0_0_0 : Tree := (.first (.second (.axis 737 840 false) (.first (.axis 733 856 false) (.axis 741 856 false))) (.second (.axis 769 840 false) (.first (.axis 755 856 false) (.second (.first (.axis 782 852 false) (.axis 788 852 false)) (.axis 786 869 true)))))
theorem fullLedger_2_1_0_1_1_0_0_0_valid : check fullLedger_2_1_0_1_1_0_0_0 1500 1750 2000 2250=true := by
  decide +kernel


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
