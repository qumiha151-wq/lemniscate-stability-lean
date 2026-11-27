import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_2_0_0_0_0_0 : Tree := (.square Tree.short (.first (.axis 833 838 true) (.second Tree.short (.axis 835 839 false))) Tree.short)
theorem fullLedger_2_2_0_0_0_0_0_valid : check fullLedger_2_2_0_0_0_0_0 2000 2062 2000 2062=true := by
  decide +kernel

def fullLedger_2_2_0_0_0_0_1 : Tree := (.second (.first (.axis 834 842 false) (.first (.axis 837 842 false) (.second Tree.short (.axis 839 843 false)))) (.axis 836 846 false))
theorem fullLedger_2_2_0_0_0_0_1_valid : check fullLedger_2_2_0_0_0_0_1 2000 2062 2062 2125=true := by
  decide +kernel

def fullLedger_2_2_0_0_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 841 845 false) Tree.short) (.axis 842 847 false)) Tree.short)
theorem fullLedger_2_2_0_0_0_0_2_valid : check fullLedger_2_2_0_0_0_0_2 2062 2125 2062 2125=true := by
  decide +kernel

def fullLedger_2_2_0_0_0_0 : Tree := (.square fullLedger_2_2_0_0_0_0_0 fullLedger_2_2_0_0_0_0_1 fullLedger_2_2_0_0_0_0_2)
theorem fullLedger_2_2_0_0_0_0_valid : check fullLedger_2_2_0_0_0_0 2000 2125 2000 2125=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_0_0_0_0_valid,fullLedger_2_2_0_0_0_0_1_valid⟩,fullLedger_2_2_0_0_0_0_2_valid⟩⟩

def fullLedger_2_2_0_0_0_1 : Tree := (.first (.axis 836 856 false) (.second (.first (.axis 842 852 false) (.second (.first (.axis 845 850 false) (.second Tree.short (.axis 847 851 false))) (.axis 846 854 false))) (.axis 844 869 false)))
theorem fullLedger_2_2_0_0_0_1_valid : check fullLedger_2_2_0_0_0_1 2000 2125 2125 2250=true := by
  decide +kernel

def fullLedger_2_2_0_0_0_2_0 : Tree := (.square Tree.short (.first (.axis 849 854 true) (.second Tree.short (.axis 851 855 true))) Tree.short)
theorem fullLedger_2_2_0_0_0_2_0_valid : check fullLedger_2_2_0_0_0_2_0 2125 2187 2125 2187=true := by
  decide +kernel

def fullLedger_2_2_0_0_0_2_1 : Tree := (.second (.first (.axis 850 860 true) (.first (.axis 853 860 true) (.second Tree.short (.axis 855 864 true)))) (.axis 852 871 true))
theorem fullLedger_2_2_0_0_0_2_1_valid : check fullLedger_2_2_0_0_0_2_1 2125 2187 2187 2250=true := by
  decide +kernel

def fullLedger_2_2_0_0_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 858 870 false) Tree.short) (.axis 860 872 false)) Tree.short)
theorem fullLedger_2_2_0_0_0_2_2_valid : check fullLedger_2_2_0_0_0_2_2 2187 2250 2187 2250=true := by
  decide +kernel

def fullLedger_2_2_0_0_0_2 : Tree := (.square fullLedger_2_2_0_0_0_2_0 fullLedger_2_2_0_0_0_2_1 fullLedger_2_2_0_0_0_2_2)
theorem fullLedger_2_2_0_0_0_2_valid : check fullLedger_2_2_0_0_0_2 2125 2250 2125 2250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_0_0_2_0_valid,fullLedger_2_2_0_0_0_2_1_valid⟩,fullLedger_2_2_0_0_0_2_2_valid⟩⟩

def fullLedger_2_2_0_0_0 : Tree := (.square fullLedger_2_2_0_0_0_0 fullLedger_2_2_0_0_0_1 fullLedger_2_2_0_0_0_2)
theorem fullLedger_2_2_0_0_0_valid : check fullLedger_2_2_0_0_0 2000 2250 2000 2250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_0_0_0_valid,fullLedger_2_2_0_0_0_1_valid⟩,fullLedger_2_2_0_0_0_2_valid⟩⟩

def fullLedger_2_2_0_0_1_0 : Tree := (.second (.axis 840 881 false) (.axis 840 915 false))
theorem fullLedger_2_2_0_0_1_0_valid : check fullLedger_2_2_0_0_1_0 2000 2125 2250 2500=true := by
  decide +kernel

def fullLedger_2_2_0_0_1_1_0 : Tree := (.first (.axis 852 881 false) (.second (.first (.axis 860 877 false) (.second (.first (.axis 870 875 false) (.second Tree.short (.axis 872 876 false))) (.axis 871 879 false))) (.first (.axis 860 885 false) (.axis 871 885 true))))
theorem fullLedger_2_2_0_0_1_1_0_valid : check fullLedger_2_2_0_0_1_1_0 2125 2250 2250 2375=true := by
  decide +kernel

def fullLedger_2_2_0_0_1_1_1 : Tree := (.first (.axis 852 915 false) (.axis 869 915 true))
theorem fullLedger_2_2_0_0_1_1_1_valid : check fullLedger_2_2_0_0_1_1_1 2125 2250 2375 2500=true := by
  decide +kernel

def fullLedger_2_2_0_0_1_1 : Tree := (.second fullLedger_2_2_0_0_1_1_0 fullLedger_2_2_0_0_1_1_1)
theorem fullLedger_2_2_0_0_1_1_valid : check fullLedger_2_2_0_0_1_1 2125 2250 2250 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_0_1_1_0_valid,fullLedger_2_2_0_0_1_1_1_valid⟩

def fullLedger_2_2_0_0_1 : Tree := (.first fullLedger_2_2_0_0_1_0 fullLedger_2_2_0_0_1_1)
theorem fullLedger_2_2_0_0_1_valid : check fullLedger_2_2_0_0_1 2000 2250 2250 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_0_1_0_valid,fullLedger_2_2_0_0_1_1_valid⟩

def fullLedger_2_2_0_0_2_0_0 : Tree := (.square Tree.short (.first (.axis 874 879 false) (.second Tree.short (.axis 876 880 true))) Tree.short)
theorem fullLedger_2_2_0_0_2_0_0_valid : check fullLedger_2_2_0_0_2_0_0 2250 2312 2250 2312=true := by
  decide +kernel

def fullLedger_2_2_0_0_2_0_1 : Tree := (.second (.first (.axis 875 883 true) (.first (.axis 878 883 true) (.second Tree.short (.axis 880 884 true)))) (.axis 877 887 true))
theorem fullLedger_2_2_0_0_2_0_1_valid : check fullLedger_2_2_0_0_2_0_1 2250 2312 2312 2375=true := by
  decide +kernel

def fullLedger_2_2_0_0_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 882 886 true) Tree.short) (.axis 883 888 true)) Tree.short)
theorem fullLedger_2_2_0_0_2_0_2_valid : check fullLedger_2_2_0_0_2_0_2 2312 2375 2312 2375=true := by
  decide +kernel

def fullLedger_2_2_0_0_2_0 : Tree := (.square fullLedger_2_2_0_0_2_0_0 fullLedger_2_2_0_0_2_0_1 fullLedger_2_2_0_0_2_0_2)
theorem fullLedger_2_2_0_0_2_0_valid : check fullLedger_2_2_0_0_2_0 2250 2375 2250 2375=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_0_2_0_0_valid,fullLedger_2_2_0_0_2_0_1_valid⟩,fullLedger_2_2_0_0_2_0_2_valid⟩⟩

def fullLedger_2_2_0_0_2_1 : Tree := (.first (.axis 877 915 true) (.second (.first (.axis 883 905 true) (.second (.first (.axis 886 893 true) (.second Tree.short (.axis 888 899 true))) (.axis 887 911 true))) (.first (.axis 883 923 true) (.axis 887 923 false))))
theorem fullLedger_2_2_0_0_2_1_valid : check fullLedger_2_2_0_0_2_1 2250 2375 2375 2500=true := by
  decide +kernel

def fullLedger_2_2_0_0_2_2_0 : Tree := (.square Tree.short (.first (.axis 891 911 true) (.second Tree.short (.axis 899 913 false))) Tree.short)
theorem fullLedger_2_2_0_0_2_2_0_valid : check fullLedger_2_2_0_0_2_2_0 2375 2437 2375 2437=true := by
  decide +kernel

def fullLedger_2_2_0_0_2_2_1 : Tree := (.second (.first (.axis 893 919 false) (.first (.axis 909 919 false) (.second Tree.short (.axis 913 921 false)))) (.axis 905 927 false))
theorem fullLedger_2_2_0_0_2_2_1_valid : check fullLedger_2_2_0_0_2_2_1 2375 2437 2437 2500=true := by
  decide +kernel

def fullLedger_2_2_0_0_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 917 925 false) Tree.short) (.axis 919 928 true)) Tree.short)
theorem fullLedger_2_2_0_0_2_2_2_valid : check fullLedger_2_2_0_0_2_2_2 2437 2500 2437 2500=true := by
  decide +kernel

def fullLedger_2_2_0_0_2_2 : Tree := (.square fullLedger_2_2_0_0_2_2_0 fullLedger_2_2_0_0_2_2_1 fullLedger_2_2_0_0_2_2_2)
theorem fullLedger_2_2_0_0_2_2_valid : check fullLedger_2_2_0_0_2_2 2375 2500 2375 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_0_2_2_0_valid,fullLedger_2_2_0_0_2_2_1_valid⟩,fullLedger_2_2_0_0_2_2_2_valid⟩⟩

def fullLedger_2_2_0_0_2 : Tree := (.square fullLedger_2_2_0_0_2_0 fullLedger_2_2_0_0_2_1 fullLedger_2_2_0_0_2_2)
theorem fullLedger_2_2_0_0_2_valid : check fullLedger_2_2_0_0_2 2250 2500 2250 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_0_2_0_valid,fullLedger_2_2_0_0_2_1_valid⟩,fullLedger_2_2_0_0_2_2_valid⟩⟩

def fullLedger_2_2_0_0 : Tree := (.square fullLedger_2_2_0_0_0 fullLedger_2_2_0_0_1 fullLedger_2_2_0_0_2)
theorem fullLedger_2_2_0_0_valid : check fullLedger_2_2_0_0 2000 2500 2000 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_0_0_valid,fullLedger_2_2_0_0_1_valid⟩,fullLedger_2_2_0_0_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
