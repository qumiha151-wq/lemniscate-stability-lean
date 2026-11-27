import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_2_0_2_0_0_0 : Tree := (.square Tree.short (.first (.axis 930 937 false) (.second Tree.short (.axis 932 943 false))) Tree.short)
theorem fullLedger_2_2_0_2_0_0_0_valid : check fullLedger_2_2_0_2_0_0_0 2500 2562 2500 2562=true := by
  decide +kernel

def fullLedger_2_2_0_2_0_0_1 : Tree := (.second (.first (.axis 931 964 false) (.first (.axis 935 964 true) (.second Tree.short (.axis 943 965 true)))) (.axis 933 968 true))
theorem fullLedger_2_2_0_2_0_0_1_valid : check fullLedger_2_2_0_2_0_0_1 2500 2562 2562 2625=true := by
  decide +kernel

def fullLedger_2_2_0_2_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 958 967 true) Tree.short) (.axis 964 969 true)) Tree.short)
theorem fullLedger_2_2_0_2_0_0_2_valid : check fullLedger_2_2_0_2_0_0_2 2562 2625 2562 2625=true := by
  decide +kernel

def fullLedger_2_2_0_2_0_0 : Tree := (.square fullLedger_2_2_0_2_0_0_0 fullLedger_2_2_0_2_0_0_1 fullLedger_2_2_0_2_0_0_2)
theorem fullLedger_2_2_0_2_0_0_valid : check fullLedger_2_2_0_2_0_0 2500 2625 2500 2625=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_2_0_0_0_valid,fullLedger_2_2_0_2_0_0_1_valid⟩,fullLedger_2_2_0_2_0_0_2_valid⟩⟩

def fullLedger_2_2_0_2_0_1 : Tree := (.first (.axis 933 978 true) (.second (.first (.axis 964 974 true) (.second (.first (.axis 967 972 true) (.second Tree.short (.axis 969 973 true))) (.axis 968 976 true))) (.first (.second (.axis 964 980 false) (.axis 964 984 false)) (.axis 968 982 false))))
theorem fullLedger_2_2_0_2_0_1_valid : check fullLedger_2_2_0_2_0_1 2500 2625 2625 2750=true := by
  decide +kernel

def fullLedger_2_2_0_2_0_2_0 : Tree := (.square Tree.short (.first (.axis 971 976 false) (.second Tree.short (.axis 973 977 false))) Tree.short)
theorem fullLedger_2_2_0_2_0_2_0_valid : check fullLedger_2_2_0_2_0_2_0 2625 2687 2625 2687=true := by
  decide +kernel

def fullLedger_2_2_0_2_0_2_1 : Tree := (.second (.first (.axis 972 980 false) (.first (.axis 975 980 false) (.second Tree.short (.axis 977 981 false)))) (.axis 974 984 false))
theorem fullLedger_2_2_0_2_0_2_1_valid : check fullLedger_2_2_0_2_0_2_1 2625 2687 2687 2750=true := by
  decide +kernel

def fullLedger_2_2_0_2_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 979 983 true) Tree.short) (.axis 980 985 true)) Tree.short)
theorem fullLedger_2_2_0_2_0_2_2_valid : check fullLedger_2_2_0_2_0_2_2 2687 2750 2687 2750=true := by
  decide +kernel

def fullLedger_2_2_0_2_0_2 : Tree := (.square fullLedger_2_2_0_2_0_2_0 fullLedger_2_2_0_2_0_2_1 fullLedger_2_2_0_2_0_2_2)
theorem fullLedger_2_2_0_2_0_2_valid : check fullLedger_2_2_0_2_0_2 2625 2750 2625 2750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_2_0_2_0_valid,fullLedger_2_2_0_2_0_2_1_valid⟩,fullLedger_2_2_0_2_0_2_2_valid⟩⟩

def fullLedger_2_2_0_2_0 : Tree := (.square fullLedger_2_2_0_2_0_0 fullLedger_2_2_0_2_0_1 fullLedger_2_2_0_2_0_2)
theorem fullLedger_2_2_0_2_0_valid : check fullLedger_2_2_0_2_0 2500 2750 2500 2750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_2_0_0_valid,fullLedger_2_2_0_2_0_1_valid⟩,fullLedger_2_2_0_2_0_2_valid⟩⟩

def fullLedger_2_2_0_2_1_0 : Tree := (.second (.first (.axis 933 994 false) (.second (.axis 966 990 false) (.axis 966 998 false))) (.axis 951 1010 false))
theorem fullLedger_2_2_0_2_1_0_valid : check fullLedger_2_2_0_2_1_0 2500 2625 2750 3000=true := by
  decide +kernel

def fullLedger_2_2_0_2_1_1_0_0 : Tree := (.second (.axis 974 990 false) (.axis 974 998 false))
theorem fullLedger_2_2_0_2_1_1_0_0_valid : check fullLedger_2_2_0_2_1_1_0_0 2625 2687 2750 2875=true := by
  decide +kernel

def fullLedger_2_2_0_2_1_1_0_1 : Tree := (.second (.first (.axis 980 990 false) (.second (.first (.axis 983 988 false) (.second Tree.short (.axis 985 989 false))) (.axis 984 992 false))) (.first (.axis 980 998 false) (.second (.axis 984 996 false) (.axis 984 1000 false))))
theorem fullLedger_2_2_0_2_1_1_0_1_valid : check fullLedger_2_2_0_2_1_1_0_1 2687 2750 2750 2875=true := by
  decide +kernel

def fullLedger_2_2_0_2_1_1_0 : Tree := (.first fullLedger_2_2_0_2_1_1_0_0 fullLedger_2_2_0_2_1_1_0_1)
theorem fullLedger_2_2_0_2_1_1_0_valid : check fullLedger_2_2_0_2_1_1_0 2625 2750 2750 2875=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_2_1_1_0_0_valid,fullLedger_2_2_0_2_1_1_0_1_valid⟩

def fullLedger_2_2_0_2_1_1_1 : Tree := (.first (.axis 974 1010 false) (.second (.axis 982 1006 false) (.axis 982 1014 false)))
theorem fullLedger_2_2_0_2_1_1_1_valid : check fullLedger_2_2_0_2_1_1_1 2625 2750 2875 3000=true := by
  decide +kernel

def fullLedger_2_2_0_2_1_1 : Tree := (.second fullLedger_2_2_0_2_1_1_0 fullLedger_2_2_0_2_1_1_1)
theorem fullLedger_2_2_0_2_1_1_valid : check fullLedger_2_2_0_2_1_1 2625 2750 2750 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_2_1_1_0_valid,fullLedger_2_2_0_2_1_1_1_valid⟩

def fullLedger_2_2_0_2_1 : Tree := (.first fullLedger_2_2_0_2_1_0 fullLedger_2_2_0_2_1_1)
theorem fullLedger_2_2_0_2_1_valid : check fullLedger_2_2_0_2_1 2500 2750 2750 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_2_1_0_valid,fullLedger_2_2_0_2_1_1_valid⟩

def fullLedger_2_2_0_2_2_0_0 : Tree := (.square Tree.short (.first (.axis 987 992 false) (.second Tree.short (.axis 989 993 true))) Tree.short)
theorem fullLedger_2_2_0_2_2_0_0_valid : check fullLedger_2_2_0_2_2_0_0 2750 2812 2750 2812=true := by
  decide +kernel

def fullLedger_2_2_0_2_2_0_1 : Tree := (.second (.first (.axis 988 996 true) (.first (.axis 991 996 true) (.second Tree.short (.axis 993 997 true)))) (.axis 990 1000 true))
theorem fullLedger_2_2_0_2_2_0_1_valid : check fullLedger_2_2_0_2_2_0_1 2750 2812 2812 2875=true := by
  decide +kernel

def fullLedger_2_2_0_2_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 995 999 true) Tree.short) (.axis 996 1001 true)) Tree.short)
theorem fullLedger_2_2_0_2_2_0_2_valid : check fullLedger_2_2_0_2_2_0_2 2812 2875 2812 2875=true := by
  decide +kernel

def fullLedger_2_2_0_2_2_0 : Tree := (.square fullLedger_2_2_0_2_2_0_0 fullLedger_2_2_0_2_2_0_1 fullLedger_2_2_0_2_2_0_2)
theorem fullLedger_2_2_0_2_2_0_valid : check fullLedger_2_2_0_2_2_0 2750 2875 2750 2875=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_2_2_0_0_valid,fullLedger_2_2_0_2_2_0_1_valid⟩,fullLedger_2_2_0_2_2_0_2_valid⟩⟩

def fullLedger_2_2_0_2_2_1 : Tree := (.first (.second (.axis 990 1006 true) (.axis 990 1014 false)) (.second (.first (.second (.axis 996 1004 true) (.axis 996 1008 false)) (.second (.first (.axis 999 1004 false) (.second Tree.short (.axis 1001 1005 false))) (.axis 1000 1008 false))) (.axis 998 1014 false)))
theorem fullLedger_2_2_0_2_2_1_valid : check fullLedger_2_2_0_2_2_1 2750 2875 2875 3000=true := by
  decide +kernel

def fullLedger_2_2_0_2_2_2_0 : Tree := (.square Tree.short (.first (.axis 1003 1008 false) (.second Tree.short (.axis 1005 1009 true))) Tree.short)
theorem fullLedger_2_2_0_2_2_2_0_valid : check fullLedger_2_2_0_2_2_2_0 2875 2937 2875 2937=true := by
  decide +kernel

def fullLedger_2_2_0_2_2_2_1 : Tree := (.second (.first (.axis 1004 1012 true) (.first (.axis 1007 1012 true) (.second Tree.short (.axis 1009 1013 false)))) (.first (.axis 1004 1016 false) (.axis 1008 1016 false)))
theorem fullLedger_2_2_0_2_2_2_1_valid : check fullLedger_2_2_0_2_2_2_1 2875 2937 2937 3000=true := by
  decide +kernel

def fullLedger_2_2_0_2_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 1011 1015 false) Tree.short) (.axis 1012 1017 false)) Tree.short)
theorem fullLedger_2_2_0_2_2_2_2_valid : check fullLedger_2_2_0_2_2_2_2 2937 3000 2937 3000=true := by
  decide +kernel

def fullLedger_2_2_0_2_2_2 : Tree := (.square fullLedger_2_2_0_2_2_2_0 fullLedger_2_2_0_2_2_2_1 fullLedger_2_2_0_2_2_2_2)
theorem fullLedger_2_2_0_2_2_2_valid : check fullLedger_2_2_0_2_2_2 2875 3000 2875 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_2_2_2_0_valid,fullLedger_2_2_0_2_2_2_1_valid⟩,fullLedger_2_2_0_2_2_2_2_valid⟩⟩

def fullLedger_2_2_0_2_2 : Tree := (.square fullLedger_2_2_0_2_2_0 fullLedger_2_2_0_2_2_1 fullLedger_2_2_0_2_2_2)
theorem fullLedger_2_2_0_2_2_valid : check fullLedger_2_2_0_2_2 2750 3000 2750 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_2_2_0_valid,fullLedger_2_2_0_2_2_1_valid⟩,fullLedger_2_2_0_2_2_2_valid⟩⟩

def fullLedger_2_2_0_2 : Tree := (.square fullLedger_2_2_0_2_0 fullLedger_2_2_0_2_1 fullLedger_2_2_0_2_2)
theorem fullLedger_2_2_0_2_valid : check fullLedger_2_2_0_2 2500 3000 2500 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_2_0_valid,fullLedger_2_2_0_2_1_valid⟩,fullLedger_2_2_0_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
