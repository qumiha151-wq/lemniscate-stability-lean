import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_0 : Tree := (.second (.axis 687 958 false) (.axis 687 965 false))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_0 1375 1390 2562 2593=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_0 : Tree := (.second (.axis 690 954 false) (.first (.axis 689 962 false) (.second (.axis 691 960 false) (.axis 691 963 false))))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_0 1390 1398 2562 2577=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_0 : Tree := (.second (.axis 694 952 false) (.first (.axis 693 956 false) (.second (.axis 695 955 false) (.axis 695 957 false))))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_0 1398 1402 2562 2569=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_0 : Tree := (.first (.second (.axis 697 951 false) (.axis 697 953 false)) (.second (.first (.axis 698 951 false) (.chord 699 700 951 952 1 0)) (.first (.second (.axis 698 952 false) (.chord 698 699 953 954 1 0)) (.second (.chord 699 700 952 953 1 0) (.chord 699 700 953 954 (-6124) 4420)))))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_0 1402 1406 2562 2565=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_1 : Tree := (.first (.second (.first (.axis 696 955 false) (.second (.chord 697 698 954 955 1 0) (.chord 697 698 955 956 1 0))) (.axis 697 957 true)) (.second (.first (.second (.chord 698 699 954 955 1 0) (.chord 698 699 955 956 0 1)) (.second (.chord 699 700 954 955 0 1) (.chord 699 700 955 956 0 1))) (.axis 699 957 true)))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_1 1402 1406 2565 2569=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1 1402 1406 2562 2569=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0 1398 1406 2562 2569=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_1 : Tree := (.first (.second (.first (.second (.axis 693 959 false) (.axis 693 961 false)) (.axis 695 960 true)) (.axis 694 963 true)) (.axis 698 962 true))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_1 1398 1406 2569 2577=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1 1398 1406 2562 2577=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0 1390 1406 2562 2577=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_1 : Tree := (.first (.axis 690 965 true) (.axis 696 965 true))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_1 1390 1406 2577 2593=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1 1390 1406 2562 2593=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0 1375 1406 2562 2593=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_0 : Tree := (.second (.first (.second (.first (.second (.chord 700 701 951 952 1 0) (.second (.chord 700 701 952 953 (-6243) 4249) (.chord 700 701 953 954 0 1))) (.second (.first (.chord 701 702 951 952 (-6356) 4080) (.chord 702 703 951 952 0 1)) (.axis 702 953 true))) (.axis 701 956 true)) (.axis 705 954 true)) (.axis 703 962 true))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_0 1406 1413 2562 2577=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_1 : Tree := (.axis 711 958 true)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_1 1413 1421 2562 2577=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0 1406 1421 2562 2577=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_1 : Tree := (.axis 707 965 true)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_1 1406 1421 2577 2593=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0 1406 1421 2562 2593=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_1 : Tree := (.axis 719 964 true)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_1 1421 1437 2562 2593=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1 1406 1437 2562 2593=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0 1375 1437 2562 2593=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_1 : Tree := (.first (.axis 688 968 true) (.axis 715 968 true))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_1 1375 1437 2593 2625=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_1 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_1 1375 1437 2562 2625=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
