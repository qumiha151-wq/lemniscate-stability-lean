import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_0_2_2_0_0_0 : Tree := (.square Tree.short (.first (.axis 730 735 false) (.second Tree.short (.axis 732 736 true))) Tree.short)
theorem fullLedger_2_0_2_2_0_0_0_valid : check fullLedger_2_0_2_2_0_0_0 1500 1562 1500 1562=true := by
  decide +kernel

def fullLedger_2_0_2_2_0_0_1 : Tree := (.second (.first (.axis 731 739 true) (.first (.axis 734 739 true) (.second Tree.short (.axis 736 740 true)))) (.axis 733 743 true))
theorem fullLedger_2_0_2_2_0_0_1_valid : check fullLedger_2_0_2_2_0_0_1 1500 1562 1562 1625=true := by
  decide +kernel

def fullLedger_2_0_2_2_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 738 742 true) Tree.short) (.axis 739 745 true)) Tree.short)
theorem fullLedger_2_0_2_2_0_0_2_valid : check fullLedger_2_0_2_2_0_0_2 1562 1625 1562 1625=true := by
  decide +kernel

def fullLedger_2_0_2_2_0_0 : Tree := (.square fullLedger_2_0_2_2_0_0_0 fullLedger_2_0_2_2_0_0_1 fullLedger_2_0_2_2_0_0_2)
theorem fullLedger_2_0_2_2_0_0_valid : check fullLedger_2_0_2_2_0_0 1500 1625 1500 1625=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_2_0_0_0_valid,fullLedger_2_0_2_2_0_0_1_valid⟩,fullLedger_2_0_2_2_0_0_2_valid⟩⟩

def fullLedger_2_0_2_2_0_1 : Tree := (.first (.axis 733 769 true) (.second (.first (.axis 739 755 true) (.second (.first (.axis 742 751 true) (.second Tree.short (.axis 745 753 true))) (.axis 743 759 true))) (.axis 741 786 false)))
theorem fullLedger_2_0_2_2_0_1_valid : check fullLedger_2_0_2_2_0_1 1500 1625 1625 1750=true := by
  decide +kernel

def fullLedger_2_0_2_2_0_2_0 : Tree := (.square Tree.short (.first (.axis 749 759 false) (.second Tree.short (.axis 753 763 false))) Tree.short)
theorem fullLedger_2_0_2_2_0_2_0_valid : check fullLedger_2_0_2_2_0_2_0 1625 1687 1625 1687=true := by
  decide +kernel

def fullLedger_2_0_2_2_0_2_1 : Tree := (.second (.first (.axis 751 782 false) (.first (.axis 757 782 false) (.second Tree.short (.axis 763 784 false)))) (.axis 755 788 false))
theorem fullLedger_2_0_2_2_0_2_1_valid : check fullLedger_2_0_2_2_0_2_1 1625 1687 1687 1750=true := by
  decide +kernel

def fullLedger_2_0_2_2_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 776 787 false) Tree.short) (.axis 782 789 true)) Tree.short)
theorem fullLedger_2_0_2_2_0_2_2_valid : check fullLedger_2_0_2_2_0_2_2 1687 1750 1687 1750=true := by
  decide +kernel

def fullLedger_2_0_2_2_0_2 : Tree := (.square fullLedger_2_0_2_2_0_2_0 fullLedger_2_0_2_2_0_2_1 fullLedger_2_0_2_2_0_2_2)
theorem fullLedger_2_0_2_2_0_2_valid : check fullLedger_2_0_2_2_0_2 1625 1750 1625 1750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_2_0_2_0_valid,fullLedger_2_0_2_2_0_2_1_valid⟩,fullLedger_2_0_2_2_0_2_2_valid⟩⟩

def fullLedger_2_0_2_2_0 : Tree := (.square fullLedger_2_0_2_2_0_0 fullLedger_2_0_2_2_0_1 fullLedger_2_0_2_2_0_2)
theorem fullLedger_2_0_2_2_0_valid : check fullLedger_2_0_2_2_0 1500 1750 1500 1750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_2_0_0_valid,fullLedger_2_0_2_2_0_1_valid⟩,fullLedger_2_0_2_2_0_2_valid⟩⟩

def fullLedger_2_0_2_2_1_0 : Tree := (.second (.first (.axis 733 804 false) (.axis 741 804 false)) (.axis 737 824 false))
theorem fullLedger_2_0_2_2_1_0_valid : check fullLedger_2_0_2_2_1_0 1500 1625 1750 2000=true := by
  decide +kernel

def fullLedger_2_0_2_2_1_1 : Tree := (.second (.first (.axis 755 804 true) (.second (.first (.axis 782 794 true) (.second (.first (.axis 787 792 true) (.second Tree.short (.axis 789 793 true))) (.axis 788 796 true))) (.axis 786 812 true))) (.axis 769 824 false))
theorem fullLedger_2_0_2_2_1_1_valid : check fullLedger_2_0_2_2_1_1 1625 1750 1750 2000=true := by
  decide +kernel

def fullLedger_2_0_2_2_1 : Tree := (.first fullLedger_2_0_2_2_1_0 fullLedger_2_0_2_2_1_1)
theorem fullLedger_2_0_2_2_1_valid : check fullLedger_2_0_2_2_1 1500 1750 1750 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_2_1_0_valid,fullLedger_2_0_2_2_1_1_valid⟩

def fullLedger_2_0_2_2_2_0_0 : Tree := (.square Tree.short (.first (.axis 791 796 true) (.second Tree.short (.axis 793 798 true))) Tree.short)
theorem fullLedger_2_0_2_2_2_0_0_valid : check fullLedger_2_0_2_2_2_0_0 1750 1812 1750 1812=true := by
  decide +kernel

def fullLedger_2_0_2_2_2_0_1 : Tree := (.second (.first (.axis 792 810 true) (.first (.axis 795 810 true) (.second Tree.short (.axis 798 811 false)))) (.axis 794 814 true))
theorem fullLedger_2_0_2_2_2_0_1_valid : check fullLedger_2_0_2_2_2_0_1 1750 1812 1812 1875=true := by
  decide +kernel

def fullLedger_2_0_2_2_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 808 813 false) Tree.short) (.axis 810 815 false)) Tree.short)
theorem fullLedger_2_0_2_2_2_0_2_valid : check fullLedger_2_0_2_2_2_0_2 1812 1875 1812 1875=true := by
  decide +kernel

def fullLedger_2_0_2_2_2_0 : Tree := (.square fullLedger_2_0_2_2_2_0_0 fullLedger_2_0_2_2_2_0_1 fullLedger_2_0_2_2_2_0_2)
theorem fullLedger_2_0_2_2_2_0_valid : check fullLedger_2_0_2_2_2_0 1750 1875 1750 1875=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_2_2_0_0_valid,fullLedger_2_0_2_2_2_0_1_valid⟩,fullLedger_2_0_2_2_2_0_2_valid⟩⟩

def fullLedger_2_0_2_2_2_1 : Tree := (.first (.axis 794 824 false) (.second (.first (.axis 810 820 false) (.second (.first (.axis 813 818 false) (.second Tree.short (.axis 815 819 false))) (.axis 814 822 false))) (.axis 812 828 false)))
theorem fullLedger_2_0_2_2_2_1_valid : check fullLedger_2_0_2_2_2_1 1750 1875 1875 2000=true := by
  decide +kernel

def fullLedger_2_0_2_2_2_2_0 : Tree := (.square Tree.short (.first (.axis 817 822 false) (.second Tree.short (.axis 819 823 false))) Tree.short)
theorem fullLedger_2_0_2_2_2_2_0_valid : check fullLedger_2_0_2_2_2_2_0 1875 1937 1875 1937=true := by
  decide +kernel

def fullLedger_2_0_2_2_2_2_1 : Tree := (.second (.first (.axis 818 826 false) (.first (.axis 821 826 false) (.second Tree.short (.axis 823 827 false)))) (.axis 820 830 false))
theorem fullLedger_2_0_2_2_2_2_1_valid : check fullLedger_2_0_2_2_2_2_1 1875 1937 1937 2000=true := by
  decide +kernel

def fullLedger_2_0_2_2_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 825 829 false) Tree.short) (.axis 826 831 true)) Tree.short)
theorem fullLedger_2_0_2_2_2_2_2_valid : check fullLedger_2_0_2_2_2_2_2 1937 2000 1937 2000=true := by
  decide +kernel

def fullLedger_2_0_2_2_2_2 : Tree := (.square fullLedger_2_0_2_2_2_2_0 fullLedger_2_0_2_2_2_2_1 fullLedger_2_0_2_2_2_2_2)
theorem fullLedger_2_0_2_2_2_2_valid : check fullLedger_2_0_2_2_2_2 1875 2000 1875 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_2_2_2_0_valid,fullLedger_2_0_2_2_2_2_1_valid⟩,fullLedger_2_0_2_2_2_2_2_valid⟩⟩

def fullLedger_2_0_2_2_2 : Tree := (.square fullLedger_2_0_2_2_2_0 fullLedger_2_0_2_2_2_1 fullLedger_2_0_2_2_2_2)
theorem fullLedger_2_0_2_2_2_valid : check fullLedger_2_0_2_2_2 1750 2000 1750 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_2_2_0_valid,fullLedger_2_0_2_2_2_1_valid⟩,fullLedger_2_0_2_2_2_2_valid⟩⟩

def fullLedger_2_0_2_2 : Tree := (.square fullLedger_2_0_2_2_0 fullLedger_2_0_2_2_1 fullLedger_2_0_2_2_2)
theorem fullLedger_2_0_2_2_valid : check fullLedger_2_0_2_2 1500 2000 1500 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_2_0_valid,fullLedger_2_0_2_2_1_valid⟩,fullLedger_2_0_2_2_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
