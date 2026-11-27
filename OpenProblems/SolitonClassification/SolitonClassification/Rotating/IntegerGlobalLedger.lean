import SolitonClassification.Rotating.IntegerGlobalReferences
namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount

def mid (a b : ℤ) := (a+b)/2
def nodeRadius (a b : ℤ) (n : RefPoint) := 100+7553*max |a-n.index| |b-n.index|
def coord (n : RefPoint) (axis : Bool) := if axis then n.y else n.x
def linear (u v : ℤ) (n : RefPoint) := u*n.x+v*n.y

abbrev ShortPass (a b c d : ℤ) := d-a≤32 ∨ 7970≤c-b
abbrev ChartPass (a b c d : ℤ) (k : Bool) := if k then
    1684≤a ∧ b≤1692 ∧ 2395≤c ∧ d≤2403 else
    1807≤a ∧ b≤1815 ∧ 2204≤c ∧ d≤2212
abbrev AxisPass (a b c d : ℤ) (i j : ℕ) (axis : Bool) :=
  i<1146 ∧ j<1146 ∧ nodeRadius a b (refPoint i)+nodeRadius c d (refPoint j) <
    |coord (refPoint i) axis-coord (refPoint j) axis|
abbrev ChordPass (a b c d : ℤ) (i j m n : ℕ) (u v : ℤ) :=
  i<1146 ∧ j<1146 ∧ m<1146 ∧ n<1146 ∧
  (refPoint i).index=a ∧ (refPoint j).index=b ∧ (refPoint m).index=c ∧ (refPoint n).index=d ∧
  b=a+1 ∧ d=c+1 ∧
  (max (linear u v (refPoint i)) (linear u v (refPoint j))+1400*(|u|+|v|) <
      min (linear u v (refPoint m)) (linear u v (refPoint n)) ∨
   max (linear u v (refPoint m)) (linear u v (refPoint n))+1400*(|u|+|v|) <
      min (linear u v (refPoint i)) (linear u v (refPoint j)))

inductive Tree where
  | short
  | chart (k : Bool)
  | axis (i j : ℕ) (dir : Bool)
  | chord (i j m n : ℕ) (u v : ℤ)
  | first (l r : Tree)
  | second (l r : Tree)
  | square (l m r : Tree)

def check : Tree → ℤ → ℤ → ℤ → ℤ → Bool
  | .short,a,b,c,d => decide (ShortPass a b c d)
  | .chart k,a,b,c,d => decide (ChartPass a b c d k)
  | .axis i j dir,a,b,c,d => decide (AxisPass a b c d i j dir)
  | .chord i j m n u v,a,b,c,d => decide (ChordPass a b c d i j m n u v)
  | .first l r,a,b,c,d => check l a (mid a b) c d && check r (mid a b) b c d
  | .second l r,a,b,c,d => check l a b c (mid c d) && check r a b (mid c d) d
  | .square l m r,a,b,c,d => decide (a=c ∧ b=d) &&
      (check l a (mid a b) a (mid a b) && check m a (mid a b) (mid a b) b && check r (mid a b) b (mid a b) b)

abbrev Inside (x y : ℝ) (a b c d : ℤ) := a≤x ∧ x≤b ∧ c≤y ∧ y≤d

structure LeafRules (x y : ℝ) (C : Prop) : Prop where
  short : ∀a b c d, ShortPass a b c d → Inside x y a b c d → C
  chart : ∀a b c d k, ChartPass a b c d k → Inside x y a b c d → C
  axis : ∀a b c d i j dir, AxisPass a b c d i j dir → Inside x y a b c d → C
  chord : ∀a b c d i j m n u v, ChordPass a b c d i j m n u v → Inside x y a b c d → C

theorem check_sound {x y : ℝ} {C : Prop} (order : x≤y) (leaf : LeafRules x y C)
    (t : Tree) (a b c d : ℤ) (ok : check t a b c d=true) (point : Inside x y a b c d) : C := by
  induction t generalizing a b c d with
  | short => exact leaf.short _ _ _ _ (of_decide_eq_true ok) point
  | chart k => exact leaf.chart _ _ _ _ k (of_decide_eq_true ok) point
  | axis i j dir => exact leaf.axis _ _ _ _ i j dir (of_decide_eq_true ok) point
  | chord i j m n u v => exact leaf.chord _ _ _ _ i j m n u v (of_decide_eq_true ok) point
  | first l r il ir =>
    obtain ⟨L,R⟩ := Bool.and_eq_true_iff.mp ok
    rcases le_total x ((mid a b:ℤ):ℝ) with H|H
    · exact il _ _ _ _ L ⟨point.1,H,point.2.2⟩
    · exact ir _ _ _ _ R ⟨H,point.2⟩
  | second l r il ir =>
    obtain ⟨L,R⟩ := Bool.and_eq_true_iff.mp ok
    rcases le_total y ((mid c d:ℤ):ℝ) with H|H
    · exact il _ _ _ _ L ⟨point.1,point.2.1,point.2.2.1,H⟩
    · exact ir _ _ _ _ R ⟨point.1,point.2.1,H,point.2.2.2⟩
  | square l m r il im ir =>
    obtain ⟨ends,checks⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨rfl,rfl⟩ := of_decide_eq_true ends
    obtain ⟨lm,R⟩ := Bool.and_eq_true_iff.mp checks
    obtain ⟨L,M⟩ := Bool.and_eq_true_iff.mp lm
    by_cases Y : y≤((mid a b:ℤ):ℝ)
    · exact il _ _ _ _ L ⟨point.1,order.trans Y,point.2.2.1,Y⟩
    · have Y' := le_of_lt (lt_of_not_ge Y)
      rcases le_total x ((mid a b:ℤ):ℝ) with X|X
      · exact im _ _ _ _ M ⟨point.1,X,Y',point.2.2.2⟩
      · exact ir _ _ _ _ R ⟨X,point.2.1,Y',point.2.2.2⟩

end SolitonClassification.Rotating.IntegerTarget.GlobalCount
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCount.check_sound

