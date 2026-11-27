import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_0 : Tree := (.second (.axis 751 893 false) (.first (.axis 749 911 false) (.second (.axis 753 909 false) (.axis 753 913 true))))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_0 1625 1656 2375 2437=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_0 : Tree := (.axis 757 893 false)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_0 1656 1671 2375 2406=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_0 : Tree := (.axis 763 891 true)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_0 1671 1687 2375 2390=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_0 : Tree := (.axis 761 899 false)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_0 1671 1679 2390 2406=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_0 : Tree := (.first (.axis 764 895 false) (.second (.axis 767 894 false) (.axis 767 897 false)))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_0 1679 1687 2390 2398=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_1 : Tree := (.first (.second (.axis 764 900 false) (.axis 764 903 false)) (.second (.first (.axis 766 900 false) (.chart true)) (.first (.second (.first (.axis 765 902 false) (.second (.chart true) (.chord 766 767 902 903 1 0))) (.axis 766 904 true)) (.axis 768 903 true))))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_1 1679 1687 2398 2406=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1 : Tree := (.second fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_0 fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1 1679 1687 2390 2406=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_0 fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1 1671 1687 2390 2406=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1 : Tree := (.second fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_0 fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1 1671 1687 2375 2406=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_0 fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0 1656 1687 2375 2406=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_0 : Tree := (.second (.first (.axis 756 909 false) (.second (.axis 758 907 false) (.axis 758 910 true))) (.second (.axis 757 912 true) (.first (.axis 756 914 true) (.axis 758 914 false))))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_0 1656 1671 2406 2437=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_1 : Tree := (.second (.first (.second (.first (.axis 760 907 false) (.second (.axis 762 906 false) (.axis 762 908 true))) (.axis 761 910 true)) (.second (.first (.second (.axis 764 906 true) (.axis 764 908 true)) (.axis 767 907 true)) (.axis 765 910 false))) (.axis 763 913 false))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_1 1671 1687 2406 2437=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_0 fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1 1656 1687 2406 2437=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1 : Tree := (.second fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0 fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1 1656 1687 2375 2437=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_0 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_0 fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_0 1625 1687 2375 2437=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_0 : Tree := (.first (.axis 749 919 true) (.second (.first (.axis 752 917 true) (.axis 754 917 true)) (.first (.second (.axis 752 920 false) (.axis 752 922 false)) (.axis 754 921 false))))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_0 1625 1656 2437 2468=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_1 : Tree := (.first (.second (.first (.second (.axis 756 916 true) (.axis 756 918 false)) (.axis 758 917 false)) (.axis 757 921 false)) (.axis 763 919 false))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_1 1656 1687 2437 2468=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_0 fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0 1625 1687 2437 2468=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_1 : Tree := (.first (.second (.first (.second (.first (.axis 748 924 false) (.axis 750 924 false)) (.axis 749 926 false)) (.axis 753 925 false)) (.first (.axis 749 928 false) (.axis 753 928 false))) (.axis 759 927 false))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_1 1625 1687 2468 2500=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_0_1 : Tree := (.second fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0 fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0_1 1625 1687 2437 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_0 : Tree := (.second fullLedger_2_1_0_1_1_0_0_1_1_1_0_0 fullLedger_2_1_0_1_1_0_0_1_1_1_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_0 1625 1687 2375 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_0 : Tree := (.first (.axis 772 891 true) (.axis 780 891 true))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_0 1687 1702 2375 2390=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_0 : Tree := (.second (.first (.axis 770 894 true) (.axis 774 894 true)) (.first (.second (.axis 770 896 true) (.chart true)) (.first (.second (.axis 773 896 true) (.chart true)) (.second (.axis 775 896 false) (.axis 775 898 false)))))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_0 1687 1694 2390 2398=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_1 : Tree := (.first (.second (.first (.axis 777 894 true) (.axis 779 894 false)) (.axis 778 897 false)) (.axis 781 895 false))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_1 1694 1702 2390 2398=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_0 fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0 1687 1702 2390 2398=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_1 : Tree := (.first (.second (.first (.chart true) (.first (.chart true) (.axis 775 900 false))) (.first (.second (.first (.axis 769 902 true) (.axis 771 902 false)) (.axis 770 904 false)) (.axis 774 903 false))) (.axis 780 901 false))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_1 1687 1702 2398 2406=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1 : Tree := (.second fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0 fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1 1687 1702 2390 2406=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0 : Tree := (.second fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_0 fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0 1687 1702 2375 2406=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_1 : Tree := (.second (.first (.second (.axis 783 890 false) (.axis 783 892 false)) (.axis 785 891 false)) (.axis 784 899 false))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_1 1702 1718 2375 2406=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0 fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0 1687 1718 2375 2406=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_1 : Tree := (.first (.second (.first (.second (.axis 772 907 false) (.axis 772 910 false)) (.axis 780 909 false)) (.axis 776 913 false)) (.axis 784 911 false))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_1 1687 1718 2406 2437=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0 : Tree := (.second fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0 fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0 1687 1718 2375 2437=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_1 : Tree := (.second (.first (.second (.axis 787 891 false) (.axis 787 899 false)) (.axis 789 893 false)) (.axis 788 911 false))
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_1 1718 1750 2375 2437=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_0 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0 fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_0 1687 1750 2375 2437=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1_1_1 : Tree := (.axis 786 923 false)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1_1 1687 1750 2437 2500=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_0_1_1_1_1 : Tree := (.second fullLedger_2_1_0_1_1_0_0_1_1_1_1_0 fullLedger_2_1_0_1_1_0_0_1_1_1_1_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1_1 1687 1750 2375 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_1_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1_1 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_1_1_0 fullLedger_2_1_0_1_1_0_0_1_1_1_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1_1 1625 1750 2375 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_1_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
