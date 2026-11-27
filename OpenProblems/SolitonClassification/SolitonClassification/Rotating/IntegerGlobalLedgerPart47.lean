import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_1_0_1_1_0_1_0_0_0 : Tree := (.first (.axis 794 840 false) (.axis 812 840 true))
theorem fullLedger_2_1_0_1_1_0_1_0_0_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_0 1750 1875 2000 2125=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_0 : Tree := (.first (.second (.axis 792 850 false) (.axis 792 854 false)) (.second (.axis 796 850 false) (.first (.axis 795 854 false) (.axis 798 854 true))))
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_0 1750 1812 2125 2187=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_0 : Tree := (.axis 792 860 true)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_0 1750 1781 2187 2218=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_0 : Tree := (.second (.axis 795 858 false) (.axis 795 864 true))
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_0 1781 1796 2187 2218=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_0 : Tree := (.first (.axis 797 858 false) (.second (.axis 800 857 false) (.first (.axis 799 859 false) (.axis 802 859 false))))
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_0 1796 1812 2187 2202=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_0 : Tree := (.second (.axis 797 862 true) (.axis 797 867 true))
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_0 1796 1804 2202 2218=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_1 : Tree := (.second (.first (.second (.axis 799 861 false) (.axis 799 863 true)) (.second (.first (.axis 801 861 false) (.axis 803 861 true)) (.chart false))) (.first (.axis 799 867 true) (.second (.first (.axis 801 865 true) (.axis 803 865 true)) (.axis 802 868 false))))
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_1 1804 1812 2202 2218=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1 : Tree := (.first fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_0 fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1 1796 1812 2202 2218=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1 : Tree := (.second fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_0 fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1 1796 1812 2187 2218=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1 : Tree := (.first fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_0 fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1 1781 1812 2187 2218=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0 : Tree := (.first fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_0 fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0 1750 1812 2187 2218=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_1 : Tree := (.first (.axis 792 871 true) (.second (.axis 796 870 true) (.axis 796 872 true)))
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_1 1750 1812 2218 2250=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_0_1 : Tree := (.second fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0 fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0_1 1750 1812 2187 2250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0_1_0 : Tree := (.second fullLedger_2_1_0_1_1_0_1_0_0_1_0_0 fullLedger_2_1_0_1_1_0_1_0_0_1_0_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_0 1750 1812 2125 2250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_0_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0_1_1_0 : Tree := (.axis 812 852 true)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_1_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_1_0 1812 1875 2125 2187=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_0 : Tree := (.axis 808 858 true)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_0 1812 1827 2187 2202=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_1 : Tree := (.second (.first (.second (.axis 806 861 true) (.first (.chart false) (.axis 807 863 true))) (.axis 809 862 true)) (.first (.second (.first (.second (.chart false) (.axis 805 866 false)) (.axis 807 865 false)) (.axis 806 868 false)) (.axis 809 867 false)))
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_1 1812 1827 2202 2218=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0 : Tree := (.second fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_0 fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0 1812 1827 2187 2218=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_1 : Tree := (.axis 811 860 true)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_1 1827 1843 2187 2218=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0 : Tree := (.first fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0 fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0 1812 1843 2187 2218=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_1 : Tree := (.second (.first (.axis 808 870 false) (.axis 811 870 false)) (.axis 810 872 false))
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_1 1812 1843 2218 2250=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0 : Tree := (.second fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0 fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0 1812 1843 2187 2250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_1 : Tree := (.second (.axis 814 860 true) (.axis 814 871 false))
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_1 1843 1875 2187 2250=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_0_1_1_1 : Tree := (.first fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0 fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_1_1 1812 1875 2187 2250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0_1_1 : Tree := (.second fullLedger_2_1_0_1_1_0_1_0_0_1_1_0 fullLedger_2_1_0_1_1_0_1_0_0_1_1_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1_1 1812 1875 2125 2250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_1_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0_1 : Tree := (.first fullLedger_2_1_0_1_1_0_1_0_0_1_0 fullLedger_2_1_0_1_1_0_1_0_0_1_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_1_valid : check fullLedger_2_1_0_1_1_0_1_0_0_1 1750 1875 2125 2250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_1_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_0 : Tree := (.second fullLedger_2_1_0_1_1_0_1_0_0_0 fullLedger_2_1_0_1_1_0_1_0_0_1)
theorem fullLedger_2_1_0_1_1_0_1_0_0_valid : check fullLedger_2_1_0_1_1_0_1_0_0 1750 1875 2000 2250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_0_valid,fullLedger_2_1_0_1_1_0_1_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0_1_0 : Tree := (.first (.axis 820 840 true) (.second (.first (.axis 826 836 true) (.second (.first (.axis 829 834 true) (.second Tree.short (.axis 831 835 true))) (.axis 830 838 true))) (.axis 828 844 true)))
theorem fullLedger_2_1_0_1_1_0_1_0_1_0_valid : check fullLedger_2_1_0_1_1_0_1_0_1_0 1875 2000 2000 2125=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_1_1 : Tree := (.first (.second (.axis 820 852 true) (.axis 820 869 false)) (.axis 828 856 false))
theorem fullLedger_2_1_0_1_1_0_1_0_1_1_valid : check fullLedger_2_1_0_1_1_0_1_0_1_1 1875 2000 2125 2250=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_0_1 : Tree := (.second fullLedger_2_1_0_1_1_0_1_0_1_0 fullLedger_2_1_0_1_1_0_1_0_1_1)
theorem fullLedger_2_1_0_1_1_0_1_0_1_valid : check fullLedger_2_1_0_1_1_0_1_0_1 1875 2000 2000 2250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_1_0_valid,fullLedger_2_1_0_1_1_0_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_0 : Tree := (.first fullLedger_2_1_0_1_1_0_1_0_0 fullLedger_2_1_0_1_1_0_1_0_1)
theorem fullLedger_2_1_0_1_1_0_1_0_valid : check fullLedger_2_1_0_1_1_0_1_0 1750 2000 2000 2250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_0_valid,fullLedger_2_1_0_1_1_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_1_0_0 : Tree := (.first (.second (.first (.axis 792 877 false) (.axis 796 877 false)) (.second (.axis 794 883 false) (.first (.axis 792 887 false) (.axis 796 887 false)))) (.second (.axis 812 877 false) (.axis 812 885 false)))
theorem fullLedger_2_1_0_1_1_0_1_1_0_0_valid : check fullLedger_2_1_0_1_1_0_1_1_0_0 1750 1875 2250 2375=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_1_0_1 : Tree := (.first (.second (.axis 794 905 true) (.axis 794 923 false)) (.axis 812 915 false))
theorem fullLedger_2_1_0_1_1_0_1_1_0_1_valid : check fullLedger_2_1_0_1_1_0_1_1_0_1 1750 1875 2375 2500=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_1_0 : Tree := (.second fullLedger_2_1_0_1_1_0_1_1_0_0 fullLedger_2_1_0_1_1_0_1_1_0_1)
theorem fullLedger_2_1_0_1_1_0_1_1_0_valid : check fullLedger_2_1_0_1_1_0_1_1_0 1750 1875 2250 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_1_0_0_valid,fullLedger_2_1_0_1_1_0_1_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_1_1_1 : Tree := (.second (.axis 824 881 false) (.axis 824 915 false))
theorem fullLedger_2_1_0_1_1_0_1_1_1_valid : check fullLedger_2_1_0_1_1_0_1_1_1 1875 2000 2250 2500=true := by
  decide +kernel

def fullLedger_2_1_0_1_1_0_1_1 : Tree := (.first fullLedger_2_1_0_1_1_0_1_1_0 fullLedger_2_1_0_1_1_0_1_1_1)
theorem fullLedger_2_1_0_1_1_0_1_1_valid : check fullLedger_2_1_0_1_1_0_1_1 1750 2000 2250 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_1_0_valid,fullLedger_2_1_0_1_1_0_1_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_1 : Tree := (.second fullLedger_2_1_0_1_1_0_1_0 fullLedger_2_1_0_1_1_0_1_1)
theorem fullLedger_2_1_0_1_1_0_1_valid : check fullLedger_2_1_0_1_1_0_1 1750 2000 2000 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_1_0_valid,fullLedger_2_1_0_1_1_0_1_1_valid⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
