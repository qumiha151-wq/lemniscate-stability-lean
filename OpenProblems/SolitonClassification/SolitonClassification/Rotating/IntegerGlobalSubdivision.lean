import SolitonClassification.Rotating.IntegerGlobalLedger
import SolitonClassification.Rotating.IntegerGlobalLedgerPart00
import SolitonClassification.Rotating.IntegerGlobalLedgerPart01
import SolitonClassification.Rotating.IntegerGlobalLedgerPart02
import SolitonClassification.Rotating.IntegerGlobalLedgerPart03
import SolitonClassification.Rotating.IntegerGlobalLedgerPart04
import SolitonClassification.Rotating.IntegerGlobalLedgerPart05
import SolitonClassification.Rotating.IntegerGlobalLedgerPart06
import SolitonClassification.Rotating.IntegerGlobalLedgerPart07
import SolitonClassification.Rotating.IntegerGlobalLedgerPart08
import SolitonClassification.Rotating.IntegerGlobalLedgerPart09
import SolitonClassification.Rotating.IntegerGlobalLedgerPart10
import SolitonClassification.Rotating.IntegerGlobalLedgerPart11
import SolitonClassification.Rotating.IntegerGlobalLedgerPart12
import SolitonClassification.Rotating.IntegerGlobalLedgerPart13
import SolitonClassification.Rotating.IntegerGlobalLedgerPart14
import SolitonClassification.Rotating.IntegerGlobalLedgerPart15
import SolitonClassification.Rotating.IntegerGlobalLedgerPart16
import SolitonClassification.Rotating.IntegerGlobalLedgerPart17
import SolitonClassification.Rotating.IntegerGlobalLedgerPart18
import SolitonClassification.Rotating.IntegerGlobalLedgerPart19
import SolitonClassification.Rotating.IntegerGlobalLedgerPart20
import SolitonClassification.Rotating.IntegerGlobalLedgerPart21
import SolitonClassification.Rotating.IntegerGlobalLedgerPart22
import SolitonClassification.Rotating.IntegerGlobalLedgerPart23
import SolitonClassification.Rotating.IntegerGlobalLedgerPart24
import SolitonClassification.Rotating.IntegerGlobalLedgerPart25
import SolitonClassification.Rotating.IntegerGlobalLedgerPart26
import SolitonClassification.Rotating.IntegerGlobalLedgerPart27
import SolitonClassification.Rotating.IntegerGlobalLedgerPart28
import SolitonClassification.Rotating.IntegerGlobalLedgerPart29
import SolitonClassification.Rotating.IntegerGlobalLedgerPart30
import SolitonClassification.Rotating.IntegerGlobalLedgerPart31
import SolitonClassification.Rotating.IntegerGlobalLedgerPart32
import SolitonClassification.Rotating.IntegerGlobalLedgerPart33
import SolitonClassification.Rotating.IntegerGlobalLedgerPart34
import SolitonClassification.Rotating.IntegerGlobalLedgerPart35
import SolitonClassification.Rotating.IntegerGlobalLedgerPart36
import SolitonClassification.Rotating.IntegerGlobalLedgerPart37
import SolitonClassification.Rotating.IntegerGlobalLedgerPart38
import SolitonClassification.Rotating.IntegerGlobalLedgerPart39
import SolitonClassification.Rotating.IntegerGlobalLedgerPart40
import SolitonClassification.Rotating.IntegerGlobalLedgerPart41
import SolitonClassification.Rotating.IntegerGlobalLedgerPart42
import SolitonClassification.Rotating.IntegerGlobalLedgerPart43
import SolitonClassification.Rotating.IntegerGlobalLedgerPart44
import SolitonClassification.Rotating.IntegerGlobalLedgerPart45
import SolitonClassification.Rotating.IntegerGlobalLedgerPart46
import SolitonClassification.Rotating.IntegerGlobalLedgerPart47
import SolitonClassification.Rotating.IntegerGlobalLedgerPart48
import SolitonClassification.Rotating.IntegerGlobalLedgerPart49
import SolitonClassification.Rotating.IntegerGlobalLedgerPart50
import SolitonClassification.Rotating.IntegerGlobalLedgerPart51
import SolitonClassification.Rotating.IntegerGlobalLedgerPart52
import SolitonClassification.Rotating.IntegerGlobalLedgerPart53
import SolitonClassification.Rotating.IntegerGlobalLedgerPart54
import SolitonClassification.Rotating.IntegerGlobalLedgerPart55
import SolitonClassification.Rotating.IntegerGlobalLedgerPart56
import SolitonClassification.Rotating.IntegerGlobalLedgerPart57
import SolitonClassification.Rotating.IntegerGlobalLedgerPart58
import SolitonClassification.Rotating.IntegerGlobalLedgerPart59
import SolitonClassification.Rotating.IntegerGlobalLedgerPart60

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_0_0_0 : Tree := (.square fullLedger_0_0_0_0_0 fullLedger_0_0_0_0_1 fullLedger_0_0_0_0_2)
theorem fullLedger_0_0_0_0_valid : check fullLedger_0_0_0_0 (-4001) (-3501) (-4001) (-3501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_0_valid,fullLedger_0_0_0_0_1_valid⟩,fullLedger_0_0_0_0_2_valid⟩⟩

def fullLedger_0_0_0 : Tree := (.square fullLedger_0_0_0_0 fullLedger_0_0_0_1 fullLedger_0_0_0_2)
theorem fullLedger_0_0_0_valid : check fullLedger_0_0_0 (-4001) (-3001) (-4001) (-3001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_0_valid,fullLedger_0_0_0_1_valid⟩,fullLedger_0_0_0_2_valid⟩⟩

def fullLedger_0_0_2 : Tree := (.square fullLedger_0_0_2_0 fullLedger_0_0_2_1 fullLedger_0_0_2_2)
theorem fullLedger_0_0_2_valid : check fullLedger_0_0_2 (-3001) (-2001) (-3001) (-2001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_valid,fullLedger_0_0_2_1_valid⟩,fullLedger_0_0_2_2_valid⟩⟩

def fullLedger_0_0 : Tree := (.square fullLedger_0_0_0 fullLedger_0_0_1 fullLedger_0_0_2)
theorem fullLedger_0_0_valid : check fullLedger_0_0 (-4001) (-2001) (-4001) (-2001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_0_valid,fullLedger_0_0_1_valid⟩,fullLedger_0_0_2_valid⟩⟩

def fullLedger_0_2_0 : Tree := (.square fullLedger_0_2_0_0 fullLedger_0_2_0_1 fullLedger_0_2_0_2)
theorem fullLedger_0_2_0_valid : check fullLedger_0_2_0 (-2001) (-1001) (-2001) (-1001)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_0_valid,fullLedger_0_2_0_1_valid⟩,fullLedger_0_2_0_2_valid⟩⟩

def fullLedger_0_2_2_0 : Tree := (.square fullLedger_0_2_2_0_0 fullLedger_0_2_2_0_1 fullLedger_0_2_2_0_2)
theorem fullLedger_0_2_2_0_valid : check fullLedger_0_2_2_0 (-1001) (-501) (-1001) (-501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_0_valid,fullLedger_0_2_2_0_1_valid⟩,fullLedger_0_2_2_0_2_valid⟩⟩

def fullLedger_0_2_2_2 : Tree := (.square fullLedger_0_2_2_2_0 fullLedger_0_2_2_2_1 fullLedger_0_2_2_2_2)
theorem fullLedger_0_2_2_2_valid : check fullLedger_0_2_2_2 (-501) 0 (-501) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_2_0_valid,fullLedger_0_2_2_2_1_valid⟩,fullLedger_0_2_2_2_2_valid⟩⟩

def fullLedger_0_2_2 : Tree := (.square fullLedger_0_2_2_0 fullLedger_0_2_2_1 fullLedger_0_2_2_2)
theorem fullLedger_0_2_2_valid : check fullLedger_0_2_2 (-1001) 0 (-1001) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_2_0_valid,fullLedger_0_2_2_1_valid⟩,fullLedger_0_2_2_2_valid⟩⟩

def fullLedger_0_2 : Tree := (.square fullLedger_0_2_0 fullLedger_0_2_1 fullLedger_0_2_2)
theorem fullLedger_0_2_valid : check fullLedger_0_2 (-2001) 0 (-2001) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_2_0_valid,fullLedger_0_2_1_valid⟩,fullLedger_0_2_2_valid⟩⟩

def fullLedger_0 : Tree := (.square fullLedger_0_0 fullLedger_0_1 fullLedger_0_2)
theorem fullLedger_0_valid : check fullLedger_0 (-4001) 0 (-4001) 0=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_valid,fullLedger_0_1_valid⟩,fullLedger_0_2_valid⟩⟩

def fullLedger_1 : Tree := (.first fullLedger_1_0 fullLedger_1_1)
theorem fullLedger_1_valid : check fullLedger_1 (-4001) 0 0 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_1_0_valid,fullLedger_1_1_valid⟩

def fullLedger_2_0_0_0 : Tree := (.square fullLedger_2_0_0_0_0 fullLedger_2_0_0_0_1 fullLedger_2_0_0_0_2)
theorem fullLedger_2_0_0_0_valid : check fullLedger_2_0_0_0 0 500 0 500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_0_valid,fullLedger_2_0_0_0_1_valid⟩,fullLedger_2_0_0_0_2_valid⟩⟩

def fullLedger_2_0_0_2 : Tree := (.square fullLedger_2_0_0_2_0 fullLedger_2_0_0_2_1 fullLedger_2_0_0_2_2)
theorem fullLedger_2_0_0_2_valid : check fullLedger_2_0_0_2 500 1000 500 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_2_0_valid,fullLedger_2_0_0_2_1_valid⟩,fullLedger_2_0_0_2_2_valid⟩⟩

def fullLedger_2_0_0 : Tree := (.square fullLedger_2_0_0_0 fullLedger_2_0_0_1 fullLedger_2_0_0_2)
theorem fullLedger_2_0_0_valid : check fullLedger_2_0_0 0 1000 0 1000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_0_valid,fullLedger_2_0_0_1_valid⟩,fullLedger_2_0_0_2_valid⟩⟩

def fullLedger_2_0_2 : Tree := (.square fullLedger_2_0_2_0 fullLedger_2_0_2_1 fullLedger_2_0_2_2)
theorem fullLedger_2_0_2_valid : check fullLedger_2_0_2 1000 2000 1000 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_2_0_valid,fullLedger_2_0_2_1_valid⟩,fullLedger_2_0_2_2_valid⟩⟩

def fullLedger_2_0 : Tree := (.square fullLedger_2_0_0 fullLedger_2_0_1 fullLedger_2_0_2)
theorem fullLedger_2_0_valid : check fullLedger_2_0 0 2000 0 2000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_0_valid,fullLedger_2_0_1_valid⟩,fullLedger_2_0_2_valid⟩⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0_0 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0_0 1375 1437 2500 2625=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1_0 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_1_0_0 fullLedger_2_1_0_1_0_1_1_0_1_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0_1_0 1375 1500 2500 2625=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0_1 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0_1_0 fullLedger_2_1_0_1_0_1_1_0_1_1)
theorem fullLedger_2_1_0_1_0_1_1_0_1_valid : check fullLedger_2_1_0_1_0_1_1_0_1 1375 1500 2500 2750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_1_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_0_1_1_0 : Tree := (.first fullLedger_2_1_0_1_0_1_1_0_0 fullLedger_2_1_0_1_0_1_1_0_1)
theorem fullLedger_2_1_0_1_0_1_1_0_valid : check fullLedger_2_1_0_1_0_1_1_0 1250 1500 2500 2750=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_0_valid,fullLedger_2_1_0_1_0_1_1_0_1_valid⟩

def fullLedger_2_1_0_1_0_1_1 : Tree := (.second fullLedger_2_1_0_1_0_1_1_0 fullLedger_2_1_0_1_0_1_1_1)
theorem fullLedger_2_1_0_1_0_1_1_valid : check fullLedger_2_1_0_1_0_1_1 1250 1500 2500 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_1_0_valid,fullLedger_2_1_0_1_0_1_1_1_valid⟩

def fullLedger_2_1_0_1_0_1 : Tree := (.first fullLedger_2_1_0_1_0_1_0 fullLedger_2_1_0_1_0_1_1)
theorem fullLedger_2_1_0_1_0_1_valid : check fullLedger_2_1_0_1_0_1 1000 1500 2500 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_1_0_valid,fullLedger_2_1_0_1_0_1_1_valid⟩

def fullLedger_2_1_0_1_0 : Tree := (.second fullLedger_2_1_0_1_0_0 fullLedger_2_1_0_1_0_1)
theorem fullLedger_2_1_0_1_0_valid : check fullLedger_2_1_0_1_0 1000 1500 2000 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_0_valid,fullLedger_2_1_0_1_0_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1_1 : Tree := (.second fullLedger_2_1_0_1_1_0_0_1_1_0 fullLedger_2_1_0_1_1_0_0_1_1_1)
theorem fullLedger_2_1_0_1_1_0_0_1_1_valid : check fullLedger_2_1_0_1_1_0_0_1_1 1625 1750 2250 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_1_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_0_1 : Tree := (.first fullLedger_2_1_0_1_1_0_0_1_0 fullLedger_2_1_0_1_1_0_0_1_1)
theorem fullLedger_2_1_0_1_1_0_0_1_valid : check fullLedger_2_1_0_1_1_0_0_1 1500 1750 2250 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_1_0_valid,fullLedger_2_1_0_1_1_0_0_1_1_valid⟩

def fullLedger_2_1_0_1_1_0_0 : Tree := (.second fullLedger_2_1_0_1_1_0_0_0 fullLedger_2_1_0_1_1_0_0_1)
theorem fullLedger_2_1_0_1_1_0_0_valid : check fullLedger_2_1_0_1_1_0_0 1500 1750 2000 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_0_valid,fullLedger_2_1_0_1_1_0_0_1_valid⟩

def fullLedger_2_1_0_1_1_0 : Tree := (.first fullLedger_2_1_0_1_1_0_0 fullLedger_2_1_0_1_1_0_1)
theorem fullLedger_2_1_0_1_1_0_valid : check fullLedger_2_1_0_1_1_0 1500 2000 2000 2500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_0_valid,fullLedger_2_1_0_1_1_0_1_valid⟩

def fullLedger_2_1_0_1_1 : Tree := (.second fullLedger_2_1_0_1_1_0 fullLedger_2_1_0_1_1_1)
theorem fullLedger_2_1_0_1_1_valid : check fullLedger_2_1_0_1_1 1500 2000 2000 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_1_0_valid,fullLedger_2_1_0_1_1_1_valid⟩

def fullLedger_2_1_0_1 : Tree := (.first fullLedger_2_1_0_1_0 fullLedger_2_1_0_1_1)
theorem fullLedger_2_1_0_1_valid : check fullLedger_2_1_0_1 1000 2000 2000 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_1_0_valid,fullLedger_2_1_0_1_1_valid⟩

def fullLedger_2_1_0 : Tree := (.first fullLedger_2_1_0_0 fullLedger_2_1_0_1)
theorem fullLedger_2_1_0_valid : check fullLedger_2_1_0 0 2000 2000 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_0_valid,fullLedger_2_1_0_1_valid⟩

def fullLedger_2_1 : Tree := (.second fullLedger_2_1_0 fullLedger_2_1_1)
theorem fullLedger_2_1_valid : check fullLedger_2_1 0 2000 2000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_2_1_0_valid,fullLedger_2_1_1_valid⟩

def fullLedger_2_2_0 : Tree := (.square fullLedger_2_2_0_0 fullLedger_2_2_0_1 fullLedger_2_2_0_2)
theorem fullLedger_2_2_0_valid : check fullLedger_2_2_0 2000 3000 2000 3000=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_0_valid,fullLedger_2_2_0_1_valid⟩,fullLedger_2_2_0_2_valid⟩⟩

def fullLedger_2_2_2_0 : Tree := (.square fullLedger_2_2_2_0_0 fullLedger_2_2_2_0_1 fullLedger_2_2_2_0_2)
theorem fullLedger_2_2_2_0_valid : check fullLedger_2_2_2_0 3000 3500 3000 3500=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_0_valid,fullLedger_2_2_2_0_1_valid⟩,fullLedger_2_2_2_0_2_valid⟩⟩

def fullLedger_2_2_2_2 : Tree := (.square fullLedger_2_2_2_2_0 fullLedger_2_2_2_2_1 fullLedger_2_2_2_2_2)
theorem fullLedger_2_2_2_2_valid : check fullLedger_2_2_2_2 3500 4001 3500 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_2_0_valid,fullLedger_2_2_2_2_1_valid⟩,fullLedger_2_2_2_2_2_valid⟩⟩

def fullLedger_2_2_2 : Tree := (.square fullLedger_2_2_2_0 fullLedger_2_2_2_1 fullLedger_2_2_2_2)
theorem fullLedger_2_2_2_valid : check fullLedger_2_2_2 3000 4001 3000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_2_0_valid,fullLedger_2_2_2_1_valid⟩,fullLedger_2_2_2_2_valid⟩⟩

def fullLedger_2_2 : Tree := (.square fullLedger_2_2_0 fullLedger_2_2_1 fullLedger_2_2_2)
theorem fullLedger_2_2_valid : check fullLedger_2_2 2000 4001 2000 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_2_0_valid,fullLedger_2_2_1_valid⟩,fullLedger_2_2_2_valid⟩⟩

def fullLedger_2 : Tree := (.square fullLedger_2_0 fullLedger_2_1 fullLedger_2_2)
theorem fullLedger_2_valid : check fullLedger_2 0 4001 0 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_2_0_valid,fullLedger_2_1_valid⟩,fullLedger_2_2_valid⟩⟩

def fullLedger : Tree := (.square fullLedger_0 fullLedger_1 fullLedger_2)
theorem fullLedger_valid : check fullLedger (-4001) 4001 (-4001) 4001=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_valid,fullLedger_1_valid⟩,fullLedger_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
