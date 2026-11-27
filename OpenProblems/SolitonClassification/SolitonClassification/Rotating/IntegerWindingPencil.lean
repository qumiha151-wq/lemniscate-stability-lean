import SolitonClassification.Rotating.FloquetPencil

namespace SolitonClassification.Rotating.IntegerWindingPencil
open Matrix Set
open SolitonClassification.Rotating.FloquetPencil (Four detFour detFour_contains)

def plus : Four ℚ := ![![(-69684055938982135:ℚ)/10^14,(4016186828775490:ℚ)/10^14,(-17820952552231221:ℚ)/10^14,(60631053174837830:ℚ)/10^14],
  ![(787163402490211:ℚ)/10^14,(-48971817000530:ℚ)/10^14,(244325393754148:ℚ)/10^14,(-801717160666522:ℚ)/10^14],
  ![(-5428574951509563:ℚ)/10^14,(316536865390325:ℚ)/10^14,(-1440297683433479:ℚ)/10^14,(4852114755018533:ℚ)/10^14],
  ![(-3023075934528346:ℚ)/10^14,(172167205213753:ℚ)/10^14,(-852698085393995:ℚ)/10^14,(2641451433498989:ℚ)/10^14]]

def minus : Four ℚ := ![![(75578781328445428:ℚ)/10^14,(4525327106415827:ℚ)/10^14,(-4272488783576166:ℚ)/10^14,(62739667937252034:ℚ)/10^14],
  ![(111894550249381:ℚ)/10^14,(-18051618989670:ℚ)/10^14,(-130032880859440:ℚ)/10^14,(-259697019288224:ℚ)/10^14],
  ![(14064168186117841:ℚ)/10^14,(809183154478645:ℚ)/10^14,(-948879188637344:ℚ)/10^14,(11195834361736591:ℚ)/10^14],
  ![(3853747027215991:ℚ)/10^14,(228979669447074:ℚ)/10^14,(-239468271416914:ℚ)/10^14,(3181173482753067:ℚ)/10^14]]

def ball (x : ℚ) : RationalBall := ⟨x,2/10^12⟩
def pencilBall (x : ℚ) (i j : Fin 4) := RationalBall.add (ball (plus i j))
    (RationalBall.neg (RationalBall.mul (RationalBall.point x) (ball (minus i j))))
def bound (x : ℚ) := detFour RationalBall.add RationalBall.mul RationalBall.neg (pencilBall x)
noncomputable def D (A B : Four ℝ) (x : ℝ) := (A - x • B).det

theorem bounds_real {A B : Four ℝ}
    (hA : ∀ i j, (ball (plus i j)).Contains (A i j))
    (hB : ∀ i j, (ball (minus i j)).Contains (B i j)) (x : ℚ) :
    (bound x).Contains (D A B x) := by
  apply detFour_contains
  intro i j
  simpa [pencilBall,sub_eq_add_neg] using RationalBall.contains_add (hA i j)
    (RationalBall.contains_neg (RationalBall.contains_mul (RationalBall.contains_point x) (hB i j)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem finite_bounds :
    (bound (-1000)).radius < (bound (-1000)).center ∧
    (bound (-700)).center < -(bound (-700)).radius ∧
    (bound (-1/1000)).center < -(bound (-1/1000)).radius ∧
    (bound (-1/10000)).radius < (bound (-1/10000)).center ∧
    (bound 3).center < -(bound 3).radius ∧
    (bound 5).radius < (bound 5).center := by decide +kernel

theorem signed_pencil {A B : Four ℝ}
    (hA : ∀ i j, (ball (plus i j)).Contains (A i j))
    (hB : ∀ i j, (ball (minus i j)).Contains (B i j)) :
    0 < D A B (-1000) ∧ D A B (-700)<0 ∧ D A B (-1/1000)<0 ∧
    0<D A B (-1/10000) ∧ D A B 3<0 ∧ 0<D A B 5 := by
  have pos (x : ℚ) (hx : (bound x).radius < (bound x).center) : 0<D A B x := by
    have hr := (abs_le.mp (bounds_real hA hB x)).1
    have := Rat.cast_lt (K:=ℝ) |>.mpr hx
    linarith
  have neg (x : ℚ) (hx : (bound x).center < -(bound x).radius) : D A B x<0 := by
    have hr := (abs_le.mp (bounds_real hA hB x)).2
    have hcast : ((bound x).center:ℝ) < -((bound x).radius:ℝ) := by exact_mod_cast hx
    linarith
  obtain ⟨a,b,c,d,e,f⟩ := finite_bounds
  exact ⟨by simpa using pos _ a,by simpa using neg _ b,by exact_mod_cast neg _ c,
    by exact_mod_cast pos _ d,by simpa using neg _ e,by simpa using pos _ f⟩

theorem three_real_multipliers {A B : Four ℝ}
    (hA : ∀ i j, (ball (plus i j)).Contains (A i j))
    (hB : ∀ i j, (ball (minus i j)).Contains (B i j)) :
    (∃ x ∈ Ioo (-1000:ℝ) (-700), D A B x=0) ∧
    (∃ x ∈ Ioo (-1/1000:ℝ) (-1/10000), D A B x=0) ∧
    (∃ x ∈ Ioo (3:ℝ) 5, D A B x=0) := by
  obtain ⟨a,b,c,d,e,f⟩ := signed_pencil hA hB
  have hc : Continuous (D A B) := by
    unfold D
    fun_prop
  exact ⟨intermediate_value_Ioo' (by norm_num) hc.continuousOn ⟨b,a⟩,
    intermediate_value_Ioo (by norm_num) hc.continuousOn ⟨c,d⟩,
    intermediate_value_Ioo (by norm_num) hc.continuousOn ⟨e,f⟩⟩


end SolitonClassification.Rotating.IntegerWindingPencil

#print axioms SolitonClassification.Rotating.IntegerWindingPencil.three_real_multipliers
