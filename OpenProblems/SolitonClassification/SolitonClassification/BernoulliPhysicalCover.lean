import SolitonClassification.BernoulliFrenetMatch
import SolitonClassification.BernoulliScaleLaw
import SolitonClassification.LowBendingCircles

noncomputable section
open Complex
namespace ClosedSimilarity.BernoulliGeometry

/-- The explicit lemniscate is traversed a positive integer number of
times in the actual period. Its given arclength parametrization is global. -/
def IsBernoulliCover (c : ClosedUnitFrenetCurve) (a vx vy : ℝ) : Prop :=
  ∃ (s₀ d : ℝ) (R : ℂ) (m : ℕ),0<d ∧ ‖R‖=1 ∧ 0<m ∧ a*d^4=15/2 ∧
    a*c.x s₀+vx=0 ∧ a*c.y s₀+vy=0 ∧ c.period=d*((m:ℝ)*arc (2*Real.pi)) ∧
    ∀u, position c (s₀+d*arc u)=position c s₀+(d:ℂ)*R*beta u

/-- The equality of full traces follows from the surjectivity of the
arclength coordinate, including both lobes and their common center. -/
theorem IsBernoulliCover.range_eq {c : ClosedUnitFrenetCurve} {a vx vy : ℝ}
    (h : IsBernoulliCover c a vx vy) : ∃ (O R : ℂ) (d : ℝ),0<d ∧ ‖R‖=1 ∧
      Set.range (position c)=Set.range (fun u=>O+(d:ℂ)*R*beta u) := by
  obtain ⟨s₀,d,R,_,dp,mr,_,_,_,_,_,eq⟩ := h
  refine ⟨position c s₀,R,d,dp,mr,Set.ext (fun p=>⟨?_,?_⟩)⟩
  · rintro ⟨s,rfl⟩
    obtain ⟨u,hu⟩ := arc_surjective ((s-s₀)/d)
    refine ⟨u,(eq u).symm.trans ?_⟩
    congr 1
    rw [hu]
    field_simp
    ring
  · rintro ⟨u,rfl⟩
    exact ⟨_,eq u⟩

end ClosedSimilarity.BernoulliGeometry
namespace ClosedSimilarity.ClosedUnitFrenetCurve
open BernoulliGeometry
set_option backward.isDefEq.respectTransparency false

/-- The cubic oscillator branch is the actual classical lemniscate in
position and arclength, for every admissible spatial scale and covering
multiplicity. A rotational similarity term on this branch vanishes. -/
theorem bernoulli_of_cubic_oscillator (c : ClosedUnitFrenetCurve) (a b vx vy : ℝ)
    (law : ∀s,c.positionForce s= -a*c.normalSupport s-b*c.tangentSupport s+
      vx*c.ty s-vy*c.tx s)
    (oscillator : ∀s,deriv (deriv c.k) s+2/9*c.k s^3=0) :
    b=0 ∧ IsBernoulliCover c a vx vy := by
  by_cases zero : a^2+b^2=0
  · have ha : a=0 := by nlinarith only [zero,sq_nonneg b,sq_nonneg a]
    have hb : b=0 := by nlinarith only [zero,sq_nonneg a,sq_nonneg b]
    exact False.elim (c.no_closed_translator_position_force vx vy (fun s=>by
      simpa [ha,hb] using law s))
  let x₀ := (-a*vx-b*vy)/(a^2+b^2)
  let y₀ := (b*vx-a*vy)/(a^2+b^2)
  let g := c.lowBendingRecenter x₀ y₀
  have shape (s : ℝ) : g.positionForce s= -a*g.normalSupport s-b*g.tangentSupport s := by
    rw [g.positionForce_eq]
    change c.force s=_
    rw [←c.positionForce_eq,law]
    dsimp only [g,lowBendingRecenter,normalSupport,tangentSupport,x₀,y₀]
    field_simp [zero]
    ring
  let z := g.centeredSupportProfile shape
  have dv (s : ℝ) : HasDerivAt c.v (-2/9*c.k s^3) s := by
    have e := oscillator s
    rw [show deriv c.k=c.v from funext (fun t=>(c.dk t).deriv),(c.dv s).deriv] at e
    convert c.dv s using 1
    linarith
  obtain ⟨s₀,ks,vs⟩ := oscillator_marker z c.period_pos dv
  obtain ⟨bz,pz,qz,rate⟩ := marker_similarity_data z c.period_pos dv ks vs
  obtain ⟨d,dp,initial,matchj⟩ := oscillator_matches c.dk dv ks vs
  obtain ⟨m,mp,len⟩ := full_turn_count c.period_pos dp c.periodic_v initial (fun t=>(matchj t).2)
  obtain ⟨R,mag,pos⟩ := frenet_match c (fun t=>(matchj t).1)
  have scale : a*d^4=15/2 := calc
    _=5/6*(d^2*c.v s₀)^2 := by rw [rate];change 5/6*c.v s₀^2*d^4=_;ring
    _=_ := by rw [initial];norm_num
  change g.normalSupport s₀=0 at pz
  change g.tangentSupport s₀=0 at qz
  have xz : g.x s₀=0 := calc
    _=g.tangentSupport s₀*g.tx s₀-g.normalSupport s₀*g.ty s₀ := by
      dsimp only [tangentSupport,normalSupport]
      linear_combination -(g.x s₀)*(g.unit s₀)
    _=_ := by rw [qz,pz];ring
  have yz : g.y s₀=0 := calc
    _=g.tangentSupport s₀*g.ty s₀+g.normalSupport s₀*g.tx s₀ := by
      dsimp only [tangentSupport,normalSupport]
      linear_combination -(g.y s₀)*(g.unit s₀)
    _=_ := by rw [qz,pz];ring
  change c.x s₀-x₀=0 at xz
  change c.y s₀-y₀=0 at yz
  refine ⟨bz,s₀,d,R,m,dp,mag,mp,scale,?_,?_,len,pos⟩
  · rw [sub_eq_zero.mp xz]
    dsimp only [x₀]
    rw [bz] at zero ⊢
    field_simp [zero]
    ring
  · rw [sub_eq_zero.mp yz]
    dsimp only [y₀]
    rw [bz] at zero ⊢
    field_simp [zero]
    ring

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.bernoulli_of_cubic_oscillator
