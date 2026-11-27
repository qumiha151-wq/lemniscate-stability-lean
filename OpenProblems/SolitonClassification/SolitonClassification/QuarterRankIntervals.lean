import SolitonClassification.Rotating.RationalBall
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith

namespace ClosedSimilarity.RotatingBifurcation.QuarterBounds
open SolitonClassification.Rotating
abbrev Input := Fin 18
inductive Expression
  | var (i : Input)
  | add (p q : Expression)
  | neg (p : Expression)
  | mul (p q : Expression)

def Expression.real (x : Input→ℝ) : Expression→ℝ
  | .var i => x i
  | .add p q => p.real x + q.real x
  | .neg p => -(p.real x)
  | .mul p q => p.real x * q.real x

def Expression.ball (x : Input→RationalBall) : Expression→RationalBall
  | .var i => x i
  | .add p q => (p.ball x).add (q.ball x)
  | .neg p => (p.ball x).neg
  | .mul p q => (p.ball x).mul (q.ball x)

theorem contains_expression {b : Input→RationalBall} {x : Input→ℝ}
    (h : ∀ i, (b i).Contains (x i)) (e : Expression) :
    (e.ball b).Contains (e.real x) := by
  induction e with
  | var i => exact h i
  | add _ _ p q => exact RationalBall.contains_add p q
  | neg _ p => exact RationalBall.contains_neg p
  | mul _ _ p q => exact RationalBall.contains_mul p q

private def sub (p q : Expression) := p.add q.neg
private def entry (r c : Nat) := Expression.var (Fin.ofNat 18 (4*r+c))
private def minor (a b c d : Expression) := sub (a.mul d) (b.mul c)

def evenMinor := minor (entry 0 0) (entry 0 2) (entry 2 0) (entry 2 2)
def pitchMinor := minor (entry 0 1) (.var 16) (entry 2 1) (.var 17)

private def triple (a b c : Nat) :=
  let u := fun i j => minor (entry b i) (entry b j) (entry c i) (entry c j)
  (sub ((entry a 0).mul (u 2 3)) ((entry a 2).mul (u 0 3))).add ((entry a 3).mul (u 0 2))

/-- Twice the v-th inverse row applied to R times the v-th column.
    Each of the four cofactor signs multiplied by R's matching sign is -1. -/
def halfTrace :=
  let t := ((((triple 1 2 3).mul (entry 0 1)).add ((triple 0 2 3).mul (entry 1 1))).add
    ((triple 0 1 3).mul (entry 2 1))).add ((triple 0 1 2).mul (entry 3 1))
  (t.add t).neg

def units : Fin 12 → Input → ℤ := ![![3038805,4470102,-4736427,-612063,-15939415,-24591401,25160400,23939105,1577523,2190533,-2083293,-317738,2395090,3334607,-3575299,1353833,-3141229,804181],
  ![-1766646,-2671610,2874635,637535,7475586,11092060,-9624557,-14704672,385950,241429,-24310,-139279,4170430,6174209,-6141692,-4547258,1457947,1796022],
  ![790081,1343570,-1427877,-568279,-3779163,-3476362,677213,7678875,1567144,1748762,-1655629,-1127195,1265652,1959320,-2093475,-1381490,-793297,886885],
  ![-574328,-672129,709746,445175,8516099,14763943,-16501846,-7111281,-2230190,-4719748,5724819,1728672,16370828,24923289,-25648298,-15534675,-869683,5247314],
  ![4605805,5068218,-3552877,-5462784,-15986716,-17064165,15353639,14217198,6639881,6721092,-4313755,-7875330,-7290686,-8150051,6273277,8147188,189045,3606708],
  ![-229885,289422,-439827,630306,-591801,1505796,-4092318,1171979,365533,-765107,2507911,-1002232,-1123347,-4003934,7111439,530698,-1029621,203266],
  ![-95806,1790278,-4316081,362053,-323342,148334,-2246873,-407488,-215207,301614,151807,813268,-330684,2631173,-5632946,2041101,100867,-519780],
  ![-108506,-463583,1123686,518347,310841,-755266,3341660,-57017,-6124,876462,-2975462,29253,26553,-4788342,10016345,-3085391,-1116944,-318898],
  ![35273,-1988705,5444782,-201866,494324,-258564,2773428,-599935,-118089,-86605,-509519,675822,419003,3150796,-7953078,-1487355,302746,-560651],
  ![-96929,559080,-1591833,650960,-346450,288719,-2663065,273679,22002,-879037,3266235,-147762,-865223,-5279241,12960117,2473221,-1429154,-218940],
  ![-35260,2088965,-6434042,268319,-321729,221244,-3020611,-253080,-71865,-6245,743470,546875,-173905,3553149,-10156388,2349047,-236264,-645350],
  ![-64842,-621397,2011830,558673,278958,36893,2036488,132482,-10753,867511,-3509341,92649,-24167,-5708283,15801330,-3484970,-1528424,-406634]]

def enclosure (i : Fin 12) (j : Input) : RationalBall :=
  ⟨(units i j : ℚ)/10^6,1/10^6⟩

private def margin (i : Fin 12) (e : Expression) (r : ℚ) : Prop :=
  (e.ball (enclosure i)).radius+r < |(e.ball (enclosure i)).center|

private instance (i : Fin 12) (e : Expression) (r : ℚ) : Decidable (margin i e r) :=
  inferInstanceAs (Decidable (_ < _))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem all_margins :
    ∀ i : Fin 12, margin i evenMinor 0 ∧ margin i pitchMinor 0 ∧ margin i halfTrace 2 := by
  decide +kernel

private theorem near_away (b : RationalBall) (x r : ℝ) (h : b.Contains x)
    (g : (b.radius:ℝ)+r < |(b.center:ℝ)|) : r < |x| := by
  have tri := abs_add_le ((b.center:ℝ)-x) x
  rw [sub_add_cancel] at tri
  rw [abs_sub_comm] at tri
  change |x-(b.center:ℝ)|≤(b.radius:ℝ) at h
  linarith

/-- Rechecks every two-by-two determinant and the complete fourth-degree
    cofactor trace over eighteen independent rational boxes at each root. -/
theorem twelve_quarter_boxes (i : Fin 12) {x : Input→ℝ}
    (h : ∀j, (enclosure i j).Contains (x j)) :
    evenMinor.real x≠0 ∧ pitchMinor.real x≠0 ∧ 2 < |halfTrace.real x| := by
  have proof (e : Expression) (r : ℚ) (g : margin i e r) : (r:ℝ) < |e.real x| := by
    apply near_away (e.ball (enclosure i)) _ _ (contains_expression h e)
    unfold margin at g
    exact_mod_cast g
  obtain ⟨a,b,c⟩ := all_margins i
  exact ⟨abs_pos.mp (by simpa using proof evenMinor 0 a),abs_pos.mp (by simpa using proof pitchMinor 0 b),
    by simpa using proof halfTrace 2 c⟩

end ClosedSimilarity.RotatingBifurcation.QuarterBounds
#print axioms ClosedSimilarity.RotatingBifurcation.QuarterBounds.twelve_quarter_boxes
