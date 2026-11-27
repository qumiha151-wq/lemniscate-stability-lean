import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_0 : Tree := (.second (.axis 688 931 false) (.first (.axis 687 937 false) (.second (.axis 692 935 false) (.first (.axis 690 943 false) (.second (.axis 696 939 false) (.first (.axis 694 947 false) (.second (.axis 698 945 false) (.axis 698 949 true))))))))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_0 1375 1406 2500 2562=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_0 : Tree := (.axis 715 931 false)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_0 1406 1437 2500 2531=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_0 : Tree := (.axis 707 935 false)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_0 1406 1421 2531 2546=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_0 : Tree := (.first (.second (.axis 703 938 false) (.axis 703 941 false)) (.first (.second (.axis 709 938 false) (.first (.axis 708 941 false) (.axis 710 941 false))) (.second (.axis 713 938 false) (.first (.second (.axis 712 940 false) (.axis 712 942 true)) (.axis 714 941 true)))))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_0 1406 1421 2546 2554=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_0 : Tree := (.first (.axis 701 945 false) (.first (.second (.axis 704 944 false) (.axis 704 946 false)) (.second (.axis 706 944 false) (.first (.second (.axis 705 945 false) (.chord 705 706 946 947 1 0)) (.second (.chord 706 707 945 946 1 0) (.chord 706 707 946 947 (-6810) 3268))))))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_0 1406 1413 2554 2558=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_0 : Tree := (.first (.axis 700 948 false) (.first (.axis 701 948 false) (.second (.axis 702 947 false) (.chord 702 703 948 949 1 0))))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_0 1406 1409 2558 2560=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_1 : Tree := (.first (.second (.axis 700 949 false) (.chord 700 701 950 951 1 0)) (.first (.second (.chord 701 702 949 950 1 0) (.chord 701 702 950 951 1 0)) (.second (.chord 702 703 949 950 1 0) (.chord 702 703 950 951 (-6461) 3911))))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_1 1406 1409 2560 2562=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0 1406 1409 2558 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_0 : Tree := (.second (.first (.second (.chord 703 704 947 948 1 0) (.chord 703 704 948 949 1 0)) (.second (.chord 704 705 947 948 1 0) (.chord 704 705 948 949 (-6648) 3583))) (.first (.second (.chord 703 704 949 950 (-6558) 3747) (.chord 703 704 950 951 0 1)) (.second (.chord 704 705 949 950 0 1) (.chord 704 705 950 951 1 0))))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_0 1409 1411 2558 2562=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_1 : Tree := (.second (.first (.second (.chord 705 706 947 948 (-6731) 3424) (.chord 705 706 948 949 0 1)) (.second (.chord 706 707 947 948 0 1) (.chord 706 707 948 949 0 1))) (.axis 706 950 true))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_1 1411 1413 2558 2562=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1 1409 1413 2558 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1 1406 1413 2558 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0 1406 1413 2554 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_0 : Tree := (.first (.second (.first (.axis 707 944 false) (.second (.axis 708 943 false) (.chord 708 709 944 945 1 0))) (.first (.second (.chord 707 708 945 946 1 0) (.chord 707 708 946 947 0 1)) (.second (.chord 708 709 945 946 0 1) (.chord 708 709 946 947 0 1)))) (.second (.axis 710 944 true) (.axis 710 946 true)))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_0 1413 1417 2554 2558=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_1 : Tree := (.axis 709 949 true)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_1 1413 1417 2558 2562=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0 1413 1417 2554 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_1 : Tree := (.axis 713 947 true)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_1 1417 1421 2554 2562=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1 1413 1421 2554 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1 1406 1421 2554 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1 1406 1421 2546 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0 1406 1421 2531 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_1 : Tree := (.second (.first (.axis 717 935 false) (.second (.axis 720 934 false) (.axis 720 936 true))) (.first (.second (.first (.second (.axis 716 938 false) (.axis 716 941 true)) (.axis 718 939 true)) (.axis 717 947 true)) (.axis 720 943 true)))
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_1 1421 1437 2531 2562=true := by
  decide +kernel

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1 1406 1437 2531 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1 1406 1437 2500 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0_0 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0_0 1375 1437 2500 2562=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
