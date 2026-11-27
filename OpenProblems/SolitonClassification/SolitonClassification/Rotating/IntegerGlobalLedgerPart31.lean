import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_2_0_2_0_0_0_0 : Tree := (.square Tree.short (.first (.axis 639 644 false) (.second Tree.short (.axis 641 645 false))) Tree.short)
theorem fullLedger_2_0_2_0_0_0_0_valid : check fullLedger_2_0_2_0_0_0_0 1000 1062 1000 1062=true := by
  decide +kernel

def fullLedger_2_0_2_0_0_0_1 : Tree := (.second (.first (.axis 640 648 false) (.first (.axis 643 648 true) (.second Tree.short (.axis 645 649 true)))) (.axis 642 652 true))
theorem fullLedger_2_0_2_0_0_0_1_valid : check fullLedger_2_0_2_0_0_0_1 1000 1062 1062 1125=true := by
  decide +kernel

def fullLedger_2_0_2_0_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 647 651 true) Tree.short) (.axis 648 653 true)) Tree.short)
theorem fullLedger_2_0_2_0_0_0_2_valid : check fullLedger_2_0_2_0_0_0_2 1062 1125 1062 1125=true := by
  decide +kernel

def fullLedger_2_0_2_0_0_0 : Tree := (.square fullLedger_2_0_2_0_0_0_0 fullLedger_2_0_2_0_0_0_1 fullLedger_2_0_2_0_0_0_2)
theorem fullLedger_2_0_2_0_0_0_valid : check fullLedger_2_0_2_0_0_0 1000 1125 1000 1125=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_0_0_0_0_valid,fullLedger_2_0_2_0_0_0_1_valid⟩,fullLedger_2_0_2_0_0_0_2_valid⟩⟩

def fullLedger_2_0_2_0_0_1 : Tree := (.first (.second (.axis 642 658 true) (.axis 642 666 false)) (.second (.first (.axis 648 658 true) (.second (.first (.axis 651 656 true) (.second Tree.short (.axis 653 657 false))) (.axis 652 660 false))) (.first (.axis 648 666 false) (.axis 652 666 false))))
theorem fullLedger_2_0_2_0_0_1_valid : check fullLedger_2_0_2_0_0_1 1000 1125 1125 1250=true := by
  decide +kernel

def fullLedger_2_0_2_0_0_2_0 : Tree := (.square Tree.short (.first (.axis 655 660 false) (.second Tree.short (.axis 657 661 false))) Tree.short)
theorem fullLedger_2_0_2_0_0_2_0_valid : check fullLedger_2_0_2_0_0_2_0 1125 1187 1125 1187=true := by
  decide +kernel

def fullLedger_2_0_2_0_0_2_1 : Tree := (.second (.first (.axis 656 664 true) (.first (.axis 659 664 true) (.second Tree.short (.axis 661 665 true)))) (.axis 658 668 true))
theorem fullLedger_2_0_2_0_0_2_1_valid : check fullLedger_2_0_2_0_0_2_1 1125 1187 1187 1250=true := by
  decide +kernel

def fullLedger_2_0_2_0_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 663 667 true) Tree.short) (.axis 664 669 true)) Tree.short)
theorem fullLedger_2_0_2_0_0_2_2_valid : check fullLedger_2_0_2_0_0_2_2 1187 1250 1187 1250=true := by
  decide +kernel

def fullLedger_2_0_2_0_0_2 : Tree := (.square fullLedger_2_0_2_0_0_2_0 fullLedger_2_0_2_0_0_2_1 fullLedger_2_0_2_0_0_2_2)
theorem fullLedger_2_0_2_0_0_2_valid : check fullLedger_2_0_2_0_0_2 1125 1250 1125 1250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_0_0_2_0_valid,fullLedger_2_0_2_0_0_2_1_valid⟩,fullLedger_2_0_2_0_0_2_2_valid⟩⟩

def fullLedger_2_0_2_0_0 : Tree := (.square fullLedger_2_0_2_0_0_0 fullLedger_2_0_2_0_0_1 fullLedger_2_0_2_0_0_2)
theorem fullLedger_2_0_2_0_0_valid : check fullLedger_2_0_2_0_0 1000 1250 1000 1250=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_0_0_0_valid,fullLedger_2_0_2_0_0_1_valid⟩,fullLedger_2_0_2_0_0_2_valid⟩⟩

def fullLedger_2_0_2_0_1_0 : Tree := (.second (.first (.axis 642 678 false) (.axis 650 678 false)) (.axis 646 721 false))
theorem fullLedger_2_0_2_0_1_0_valid : check fullLedger_2_0_2_0_1_0 1000 1125 1250 1500=true := by
  decide +kernel

def fullLedger_2_0_2_0_1_1_0 : Tree := (.first (.second (.axis 658 674 false) (.axis 658 682 false)) (.second (.first (.axis 664 674 false) (.second (.first (.axis 667 672 false) (.second Tree.short (.axis 669 673 false))) (.axis 668 676 false))) (.first (.axis 664 682 false) (.axis 668 682 true))))
theorem fullLedger_2_0_2_0_1_1_0_valid : check fullLedger_2_0_2_0_1_1_0 1125 1250 1250 1375=true := by
  decide +kernel

def fullLedger_2_0_2_0_1_1_1 : Tree := (.first (.axis 658 721 false) (.axis 666 721 false))
theorem fullLedger_2_0_2_0_1_1_1_valid : check fullLedger_2_0_2_0_1_1_1 1125 1250 1375 1500=true := by
  decide +kernel

def fullLedger_2_0_2_0_1_1 : Tree := (.second fullLedger_2_0_2_0_1_1_0 fullLedger_2_0_2_0_1_1_1)
theorem fullLedger_2_0_2_0_1_1_valid : check fullLedger_2_0_2_0_1_1 1125 1250 1250 1500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_0_1_1_0_valid,fullLedger_2_0_2_0_1_1_1_valid⟩

def fullLedger_2_0_2_0_1 : Tree := (.first fullLedger_2_0_2_0_1_0 fullLedger_2_0_2_0_1_1)
theorem fullLedger_2_0_2_0_1_valid : check fullLedger_2_0_2_0_1 1000 1250 1250 1500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_0_1_0_valid,fullLedger_2_0_2_0_1_1_valid⟩

def fullLedger_2_0_2_0_2_0_0 : Tree := (.square Tree.short (.first (.axis 671 676 true) (.second Tree.short (.axis 673 677 true))) Tree.short)
theorem fullLedger_2_0_2_0_2_0_0_valid : check fullLedger_2_0_2_0_2_0_0 1250 1312 1250 1312=true := by
  decide +kernel

def fullLedger_2_0_2_0_2_0_1 : Tree := (.second (.first (.axis 672 680 true) (.first (.axis 675 680 true) (.second Tree.short (.axis 677 681 true)))) (.axis 674 684 true))
theorem fullLedger_2_0_2_0_2_0_1_valid : check fullLedger_2_0_2_0_2_0_1 1250 1312 1312 1375=true := by
  decide +kernel

def fullLedger_2_0_2_0_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 679 683 true) Tree.short) (.axis 680 685 true)) Tree.short)
theorem fullLedger_2_0_2_0_2_0_2_valid : check fullLedger_2_0_2_0_2_0_2 1312 1375 1312 1375=true := by
  decide +kernel

def fullLedger_2_0_2_0_2_0 : Tree := (.square fullLedger_2_0_2_0_2_0_0 fullLedger_2_0_2_0_2_0_1 fullLedger_2_0_2_0_2_0_2)
theorem fullLedger_2_0_2_0_2_0_valid : check fullLedger_2_0_2_0_2_0 1250 1375 1250 1375=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_0_2_0_0_valid,fullLedger_2_0_2_0_2_0_1_valid⟩,fullLedger_2_0_2_0_2_0_2_valid⟩⟩

def fullLedger_2_0_2_0_2_1 : Tree := (.first (.second (.axis 674 700 true) (.axis 674 725 false)) (.second (.first (.axis 680 700 false) (.second (.first (.axis 683 688 false) (.second Tree.short (.axis 685 692 false))) (.axis 684 715 false))) (.first (.axis 680 725 false) (.axis 684 725 false))))
theorem fullLedger_2_0_2_0_2_1_valid : check fullLedger_2_0_2_0_2_1 1250 1375 1375 1500=true := by
  decide +kernel

def fullLedger_2_0_2_0_2_2_0 : Tree := (.square Tree.short (.first (.axis 687 715 false) (.second Tree.short (.axis 692 719 true))) Tree.short)
theorem fullLedger_2_0_2_0_2_2_0_valid : check fullLedger_2_0_2_0_2_2_0 1375 1437 1375 1437=true := by
  decide +kernel

def fullLedger_2_0_2_0_2_2_1 : Tree := (.second (.first (.axis 688 723 true) (.first (.axis 707 723 true) (.second Tree.short (.axis 719 724 true)))) (.axis 700 727 true))
theorem fullLedger_2_0_2_0_2_2_1_valid : check fullLedger_2_0_2_0_2_2_1 1375 1437 1437 1500=true := by
  decide +kernel

def fullLedger_2_0_2_0_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 722 726 true) Tree.short) (.axis 723 728 true)) Tree.short)
theorem fullLedger_2_0_2_0_2_2_2_valid : check fullLedger_2_0_2_0_2_2_2 1437 1500 1437 1500=true := by
  decide +kernel

def fullLedger_2_0_2_0_2_2 : Tree := (.square fullLedger_2_0_2_0_2_2_0 fullLedger_2_0_2_0_2_2_1 fullLedger_2_0_2_0_2_2_2)
theorem fullLedger_2_0_2_0_2_2_valid : check fullLedger_2_0_2_0_2_2 1375 1500 1375 1500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_0_2_2_0_valid,fullLedger_2_0_2_0_2_2_1_valid⟩,fullLedger_2_0_2_0_2_2_2_valid⟩⟩

def fullLedger_2_0_2_0_2 : Tree := (.square fullLedger_2_0_2_0_2_0 fullLedger_2_0_2_0_2_1 fullLedger_2_0_2_0_2_2)
theorem fullLedger_2_0_2_0_2_valid : check fullLedger_2_0_2_0_2 1250 1500 1250 1500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_0_2_0_valid,fullLedger_2_0_2_0_2_1_valid⟩,fullLedger_2_0_2_0_2_2_valid⟩⟩

def fullLedger_2_0_2_0 : Tree := (.square fullLedger_2_0_2_0_0 fullLedger_2_0_2_0_1 fullLedger_2_0_2_0_2)
theorem fullLedger_2_0_2_0_valid : check fullLedger_2_0_2_0 1000 1500 1000 1500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_0_0_valid,fullLedger_2_0_2_0_1_valid⟩,fullLedger_2_0_2_0_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
