import SolitonClassification.CountableCurvatureClassification
import SolitonClassification.Rotating.IntegerFinalDoublePoints

noncomputable section
open Function Complex
open scoped ContDiff
namespace SolitonClassification.Rotating.IntegerTarget.Physical
open ClosedSimilarity ClosedSimilarity.MeromorphicCurvature
set_option backward.isDefEq.respectTransparency false

private theorem derivative_period {f : ℝ → ℝ} {v : ℝ} (per : Periodic f v) :
    Periodic (deriv f) v := by
  intro x
  calc deriv f (x+v) = deriv (fun z=>f (z+v)) x := (deriv_comp_add_const f v x).symm
       _ = deriv f x := by rw [show (fun z=>f (z+v))=f from funext per]

private def frenetSeed (P : Seed) : ClosedUnitFrenetCurve := by
  let J := P.I
  have idK : J.k=(fun s=>deriv J.x s*deriv (deriv J.y) s-deriv J.y s*deriv (deriv J.x) s) :=
    funext (fun s=>(J.curvature s).symm)
  have smooth : ContDiff ℝ ∞ J.k := rotatingK_smooth_of_closed_profile P
  have perK : Periodic J.k P.L := by
    rw [idK]
    exact ((derivative_period J.periodX).mul (derivative_period (derivative_period J.periodY))).sub
      ((derivative_period J.periodY).mul (derivative_period (derivative_period J.periodX)))
  exact {
    period:=P.L,period_pos:=P.positive,x:=J.x,y:=J.y,tx:=fun s=>Real.cos (J.theta s),
    ty:=fun s=>Real.sin (J.theta s),k:=J.k,v:=deriv J.k,w:=deriv (deriv J.k),
    dx:=J.tangentX,dy:=J.tangentY,
    dtx:=fun s=>((J.angleDerivative s).cos.congr_deriv (by ring)),
    dty:=fun s=>((J.angleDerivative s).sin.congr_deriv (by ring)),
    dk:=fun s=>(smooth.differentiable (by simp) s).hasDerivAt,
    dv:=fun s=>((show ContDiff ℝ ∞ (deriv J.k) from smooth.deriv').differentiable (by simp) s).hasDerivAt,
    continuous_w:=(show ContDiff ℝ ∞ (deriv (deriv J.k)) from smooth.deriv'.deriv').continuous,
    unit:=fun s=>Real.cos_sq_add_sin_sq _,
    periodic_x:=J.periodX,periodic_y:=J.periodY,periodic_k:=perK,periodic_v:=derivative_period perK,
    periodic_tx:=fun s=>by simp only [J.turning,Real.cos_sub_two_pi],
    periodic_ty:=fun s=>by simp only [J.turning,Real.sin_sub_two_pi] }

private theorem seed_shape (P : Seed) (s : ℝ) :
    (frenetSeed P).positionForce s= -(1:ℝ)*(frenetSeed P).normalSupport s-P.b*(frenetSeed P).tangentSupport s+
      0*(frenetSeed P).ty s-0*(frenetSeed P).tx s := by
  rw [(frenetSeed P).positionForce_eq]
  have eq := P.I.soliton s
  rw [(P.I.tangentX s).deriv,(P.I.tangentY s).deriv] at eq
  change deriv (deriv P.I.k) s+P.I.k s^3/2=_
  dsimp only [frenetSeed,ClosedUnitFrenetCurve.normalSupport,ClosedUnitFrenetCurve.tangentSupport]
  linarith only [eq]

theorem genuinely_rotating_curvature_not_meromorphic {P : Seed} (ev : PrimitiveEvolution P) :
    ¬GlobalMeromorphicTrace P.I.k := by
  intro e
  let c:=frenetSeed P
  obtain cir|ber := c.meromorphic_curvature_circle_or_bernoulli 1 P.b 0 0 (seed_shape P) e
  · obtain ⟨K,_,_,_,_,hk,_⟩ := cir
    obtain ⟨s,sn⟩ := ev.negative_curvature
    have eq : P.I.k s=P.I.k 0 := (hk s).trans (hk 0).symm
    linarith only [eq,sn,ev.positive_curvature]
  · linarith only [ber.1,ev.rotation_range.1]

theorem genuinely_rotating_curvature_not_elliptic {P : Seed} (ev : PrimitiveEvolution P) :
    IsEmpty (EllipticExtension P.I.k) := ⟨fun e=>genuinely_rotating_curvature_not_meromorphic ev
      ⟨e.extension,fun x=>(e.normal x).meromorphicAt,e.analytic_real,e.restrict_real⟩⟩

theorem exists_nonmeromorphic_two_crossing_solution :
    ∃P : Seed, DoublePointEvolution P ∧ ¬GlobalMeromorphicTrace P.I.k := by
  obtain ⟨P,hP⟩:=exists_primitive_two_double_point_evolution
  exact ⟨P,hP,genuinely_rotating_curvature_not_meromorphic hP.evolution⟩

/-- In particular, the two-crossing closed solution is a genuine example
outside the elliptic-curvature classification. -/
theorem exists_nonelliptic_two_crossing_solution :
    ∃P : Seed, DoublePointEvolution P ∧ IsEmpty (EllipticExtension P.I.k) := by
  obtain ⟨P,hP⟩:=exists_primitive_two_double_point_evolution
  exact ⟨P,hP,genuinely_rotating_curvature_not_elliptic hP.evolution⟩

/-- Even excising a closed countable family of nonreal arclengths cannot give
the rotating example a single-valued meromorphic continuation. -/
theorem genuinely_rotating_curvature_no_countable_trace {P : Seed} (ev : PrimitiveEvolution P) :
    ¬CountableExceptionalTrace P.I.k := by
  intro traceH
  obtain ⟨p,hk⟩:=(frenetSeed P).exists_centered_profile_with_curvature 1 P.b 0 0 (seed_shape P)
  have tr : CountableExceptionalTrace p.k := hk ▸ traceH
  have m:=(countable_exceptional_trace_iff_global p (frenetSeed P).period_pos).mp tr
  rw [hk] at m
  exact genuinely_rotating_curvature_not_meromorphic ev m

theorem exists_two_crossing_solution_no_countable_trace :
    ∃P : Seed, DoublePointEvolution P ∧ ¬CountableExceptionalTrace P.I.k := by
  obtain ⟨P,hP⟩:=exists_primitive_two_double_point_evolution
  exact ⟨P,hP,genuinely_rotating_curvature_no_countable_trace hP.evolution⟩

end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.exists_nonelliptic_two_crossing_solution
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.exists_two_crossing_solution_no_countable_trace

