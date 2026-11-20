import SolitonClassification.GeometricSimilarity
import SolitonClassification.ReflectedMarker
import SolitonClassification.SupportFlowContinuity

noncomputable section
open Set
open scoped ContDiff
namespace ClosedSimilarity.ReflectedArc

def HasUniqueCentreMarker {L b : ℝ} (P : ZeroTurnExpander L b) :=
  ∀ s, P.X s=0 → P.Y s=0 → P.k s=0 → |deriv P.k s|=b

namespace ZeroTurnExpander
variable {L b : ℝ} (P : ZeroTurnExpander L b)

def cartesianSupport (s : ℝ) : Support := ![P.k s,deriv P.k s,
  -P.X s*deriv P.Y s+P.Y s*deriv P.X s,P.X s*deriv P.X s+P.Y s*deriv P.Y s]

theorem cartesianSupport_zero : P.cartesianSupport 0=![0,b,0,0] := by
  obtain ⟨x,y,k,v⟩ := P.center_crossing
  simp [cartesianSupport,x,y,k,v]

theorem cartesianSupport_solves : ReflectedMarker.Solves P.cartesianSupport := by
  intro s
  have dx := (P.X_smooth.differentiable (by simp) s).hasDerivAt
  have dy := (P.Y_smooth.differentiable (by simp) s).hasDerivAt
  have dx' := ((contDiff_infty_iff_deriv.mp P.X_smooth).2.differentiable (by simp) s).hasDerivAt
  have dy' := ((contDiff_infty_iff_deriv.mp P.Y_smooth).2.differentiable (by simp) s).hasDerivAt
  have dnorm := (dx'.pow 2).add (dy'.pow 2)
  change HasDerivAt (fun s => deriv P.X s^2+deriv P.Y s^2) _ s at dnorm
  rw [show (fun s => deriv P.X s^2+deriv P.Y s^2)=(fun _=>1) from funext P.unit_speed] at dnorm
  have dot : deriv P.X s*deriv (deriv P.X) s+deriv P.Y s*deriv (deriv P.Y) s=0 := by
    have H := dnorm.unique (hasDerivAt_const s 1)
    norm_num at H
    linarith only [H]
  have xpp : deriv (deriv P.X) s= -P.k s*deriv P.Y s := by
    linear_combination -(deriv (deriv P.X) s)*P.unit_speed s +deriv P.X s*dot-
      deriv P.Y s*P.curvature s
  have ypp : deriv (deriv P.Y) s=P.k s*deriv P.X s := by
    linear_combination -(deriv (deriv P.Y) s)*P.unit_speed s +deriv P.Y s*dot+
      deriv P.X s*P.curvature s
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (P.k_smooth.differentiable (by simp) s).hasDerivAt
  · convert! ((contDiff_infty_iff_deriv.mp P.k_smooth).2.differentiable (by simp) s).hasDerivAt using 1
    change -(P.k s)^3/2-(-P.X s*deriv P.Y s+P.Y s*deriv P.X s)=deriv (deriv P.k) s
    linarith only [P.dilation_equation s]
  · convert! ((dx.neg.mul dy').add (dy.mul dx')) using 1
    change -P.k s*(P.X s*deriv P.X s+P.Y s*deriv P.Y s)=_
    rw [xpp,ypp]; simp only [Pi.neg_apply]; ring
  · convert! ((dx.mul dx').add (dy.mul dy')) using 1
    change 1+P.k s*(-P.X s*deriv P.Y s+P.Y s*deriv P.X s)=_
    rw [xpp,ypp]
    linear_combination -(P.unit_speed s)

/-- Every smooth coefficient-one profile with the given centre mark has
    exactly the normalized global support trajectory shot from that mark. -/
theorem cartesianSupport_eq_solution :
    P.cartesianSupport=GlobalSupport.solution 1 ![0,b,0,0] :=
  ReflectedMarker.support_unique P.cartesianSupport_solves
    (GlobalSupport.solution_derivative 1 _) (P.cartesianSupport_zero.trans
      (GlobalSupport.solution_zero 1 _).symm)

/-- This applies to every profile carrying the same initial slope when
    its normalized support passes the two axial seam tests. -/
theorem unique_marker_of_seam (hb : 0<b) {l : ℝ} (hl : 0<l)
    (hv : P.cartesianSupport l 1=0) (hq : P.cartesianSupport l 3=0) :
    HasUniqueCentreMarker P := by
  obtain ⟨_,_,_,_,centres⟩ := ReflectedMarker.primitive_marker_of_seams
    P.cartesianSupport_solves hb hl P.cartesianSupport_zero hv hq
  intro s x y k
  exact (centres s k (by simp [cartesianSupport,x,y]) (by simp [cartesianSupport,x,y])).2

end ZeroTurnExpander

/-- The absolute curvature slope at every zero-curvature return to the
    dilation centre is the same as at the initial marked crossing. -/
theorem marked_of_quarter {z : ℝ → Support} {l b : ℝ} (hl : 0<l) (hb : 0<b)
    (cz : Continuous z) (hz : ∀ t∈Icc 0 l, HasDerivAt z (supportField (z t)) t)
    (hi : z 0=![0,b,0,0]) (hv : z l 1=0) (hq : z l 3=0) :
    ∃ P : ZeroTurnExpander (4*l) b, HasUniqueCentreMarker P := by
  obtain ⟨P⟩ := exists_zeroTurnExpander_of_quarter hl cz hz hi hv hq
  obtain ⟨y,_,_,dy,agree,_,_⟩ := closed_state_of_quarter hl cz hz hi hv hq
  let S := ReflectedMarker.support y
  have hS : ReflectedMarker.Solves S := by
    intro t
    apply hasDerivAt_pi.mpr
    intro i
    have D := hasDerivAt_pi.mp (dy t)
    fin_cases i
    · exact D 0
    · exact D 1
    · exact D 2
    · exact D 3
  have equalAt (s : ℝ) (hs : s∈Icc 0 l) : S s=z s := by
    ext i
    fin_cases i <;> simp [S,ReflectedMarker.support,agree s hs,withAngle]
  have eq := ReflectedMarker.support_unique P.cartesianSupport_solves hS
    (P.cartesianSupport_zero.trans ((equalAt 0 ⟨le_rfl,hl.le⟩).trans hi).symm)
  have endEq := (congrFun eq l).trans (equalAt l ⟨hl.le,le_rfl⟩)
  exact ⟨P,P.unique_marker_of_seam hb hl (endEq ▸ hv) (endEq ▸ hq)⟩

/-- A similarity between immersed profiles with unique centre markers
    preserves the positive marker exactly, including under covers. -/
theorem GeometricSimilarity.marker_eq {L b T d : ℝ} {P : ZeroTurnExpander L b}
    {Q : ZeroTurnExpander T d} (S : GeometricSimilarity P Q) (hb : 0<b)
    (Qmark : HasUniqueCentreMarker Q) : b=d := by
  obtain ⟨A,_,_,_⟩ := S.lifted
  obtain ⟨a4,ax,ay⟩ := A.scale_and_centre hb.ne'
  obtain ⟨px,py,pk,pv⟩ := P.center_crossing
  have x : Q.X A.offset=0 := by simpa [px,py,ax] using A.first 0
  have y : Q.Y A.offset=0 := by simpa [px,py,ay] using A.second 0
  have k : Q.k A.offset=0 := by
    have e := A.pull_curvature 0
    simp [pk,pow_ne_zero _ A.regular] at e
    exact e
  have ab : |A.m*A.q-A.n*A.p|=1 := by
    simpa using (sq_eq_sq_iff_abs_eq_abs (A.m*A.q-A.n*A.p) 1).mp (by simpa [a4] using A.area)
  have h := congrArg abs (A.pull_slope 0)
  simpa [a4,abs_mul,ab,pv,abs_of_pos hb,Qmark A.offset x y k] using h.symm

theorem GeometricSimilarity.abs_marker_eq {L b T d : ℝ} {P : ZeroTurnExpander L b}
    {Q : ZeroTurnExpander T d} (S : GeometricSimilarity P Q)
    (Pmark : HasUniqueCentreMarker P) (Qmark : HasUniqueCentreMarker Q) : |b|=|d| := by
  obtain ⟨px,py,pk,_⟩ := P.center_crossing
  have nonneg : 0≤b := (abs_nonneg _).trans_eq (Pmark 0 px py pk)
  rcases nonneg.lt_or_eq with pos|zero
  · exact congrArg abs (S.marker_eq pos Qmark)
  subst b
  let line : ℝ → Support := fun s => ![0,0,0,s]
  have solves : ReflectedMarker.Solves line := by
    intro s
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;> simp [line,supportField] <;> first | exact hasDerivAt_const s 0 | exact hasDerivAt_id s
  have eq := ReflectedMarker.support_unique P.cartesianSupport_solves solves P.cartesianSupport_zero
  have K (s : ℝ) : P.k s=0 := congrFun (congrFun eq s) 0
  obtain ⟨A,_,_,_⟩ := S.lifted
  have flat : Q.k=fun _ => 0 := by
    funext t
    let s := (t-A.offset)/A.a
    have h := A.pull_curvature s
    have st : A.a*s+A.offset=t := by dsimp [s]; field_simp [A.regular]; ring
    simpa [K,st,A.regular] using h
  have v := Q.center_crossing.2.2.2
  simp [flat] at v
  simp [← v]

end ClosedSimilarity.ReflectedArc
#print axioms ClosedSimilarity.ReflectedArc.marked_of_quarter
#print axioms ClosedSimilarity.ReflectedArc.GeometricSimilarity.marker_eq
#print axioms ClosedSimilarity.ReflectedArc.GeometricSimilarity.abs_marker_eq
