import SolitonClassification.LemniscaticBallContinuation
import SolitonClassification.EllipticNormalization
import SolitonClassification.BernoulliArcMatch

noncomputable section
open Complex Filter Set Function
open scoped Topology
namespace ClosedSimilarity.LemniscaticExtension
open MeromorphicCurvature BernoulliGeometry
set_option backward.isDefEq.respectTransparency false

/-- The normalized real lemniscatic sine has a global meromorphic extension
with a nonreal period. The second period comes from the quarter-turn
symmetry, starting from the actual finite positive arclength period. -/
theorem realU_elliptic : Nonempty (EllipticExtension realU) := by
  obtain ⟨f,hm,ha,he,qs⟩ := existence_meromorphic_quarter
  let P := arc (2*Real.pi)
  have pp : 0<P := by
    simpa only [arc_zero] using arc_strictMono (show 0<2*Real.pi by positivity)
  have pr (x : ℂ) : (fun z=>f (z+(P:ℂ)))=ᶠ[𝓝[≠] x] f := by
    have mm (y : ℂ) : MeromorphicAt (fun z=>f (z+(P:ℂ))-f z) y :=
      (meromorphicAt_fun_comp_add_const_iff_meromorphicAt.mpr (hm _)).sub (hm y)
    have rr (t : ℝ) : f ((t:ℂ)+(P:ℂ))-f (t:ℂ)=0 := by
      rw [←Complex.ofReal_add,he,he,show realU (t+P)=realU t from real_period t,sub_self]
    exact (real_axis_meromorphic_identity mm rr x).mono (fun _ h=>sub_eq_zero.mp h)
  refine exists_normal_extension hm ha he (v:=I*(P:ℂ)) (by simpa using pp.ne') ?_
  intro x
  have lim : Tendsto (fun z:ℂ=> -I*z) (𝓝[≠] x) (𝓝[≠] (-I*x)) := by
    apply (continuous_const.mul continuous_id).continuousWithinAt.tendsto_nhdsWithin
    intro t ht
    exact fun eq=>ht (mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) eq)
  filter_upwards [(pr _).comp_tendsto lim] with z eq
  change f (-I*z+(P:ℂ))=f (-I*z) at eq
  have alg (t : ℂ) : I*(-I*t)=t := by linear_combination -t*I_sq
  calc
    f (z+I*(P:ℂ))=f (I*(-I*z+P)) := by rw [mul_add,alg]
    _=I*f (-I*z+P) := qs _
    _=I*f (-I*z) := congrArg (I*·) eq
    _=f z := by rw [←qs,alg]

/-- Meromorphic ellipticity persists under spatial scaling and shifts of
the arclength origin. -/
theorem scaled_realU_elliptic (s₀ d A : ℝ) (dp : 0<d) :
    Nonempty (EllipticExtension (fun t=>A*realU ((t-s₀)/d))) := by
  obtain ⟨e⟩ := realU_elliptic
  obtain ⟨v,vn,per⟩ := e.transverse
  let clock (z : ℂ) := (z-(s₀:ℂ))/(d:ℂ)
  let F (z : ℂ) := (A:ℂ)*e.extension (clock z)
  have da (z : ℂ) : AnalyticAt ℂ clock z := by unfold clock;fun_prop
  have dn : (d:ℂ)≠0 := by exact_mod_cast dp.ne'
  have hm (z : ℂ) : MeromorphicAt F z := (MeromorphicAt.const _ _).mul
    ((e.normal _).meromorphicAt.comp_analyticAt (da z))
  have clk (t : ℝ) : clock (t:ℂ)=(((t-s₀)/d:ℝ):ℂ) := by dsimp only [clock];push_cast;rfl
  have ha (t : ℝ) : AnalyticAt ℂ F (t:ℂ) :=
    analyticAt_const.mul ((show AnalyticAt ℂ e.extension (clock (t:ℂ)) by rw [clk];exact e.analytic_real _).comp (da _))
  have eq (t : ℝ) : F (t:ℂ)=((A*realU ((t-s₀)/d):ℝ):ℂ) := by simp only [F,clk,e.restrict_real,Complex.ofReal_mul]
  refine exists_normal_extension hm ha eq (v:=(d:ℂ)*v) (by simpa using mul_ne_zero dp.ne' vn) ?_
  intro z
  apply Eventually.of_forall
  intro u
  change (A:ℂ)*e.extension (clock (u+d*v))=(A:ℂ)*e.extension (clock u)
  rw [show clock (u+d*v)=clock u+v by dsimp [clock];field_simp;ring,per]

/-- In particular, the signed arclength curvature of the standard
Bernoulli parametrization has both real and nonreal elliptic periods. -/
theorem canonical_curvature_elliptic :
    Nonempty (EllipticExtension (fun t=>curvature (angle t))) := by
  have e : (fun t:ℝ=>3*realU ((t-0)/1))=(fun t=>curvature (angle t)) := by
    funext t
    simp only [sub_zero,div_one,realU]
    ring
  exact e ▸ scaled_realU_elliptic 0 1 3 (by norm_num)

/-- Every actual classical profile on the quartic oscillator branch has
elliptic curvature at its own physical scale and arclength origin. -/
theorem profile_oscillator_elliptic {a b L : ℝ} (z : PeriodicSupportProfile a b L)
    (hL : 0<L) (dv : ∀s,HasDerivAt z.v (-2/9*z.k s^3) s) : Nonempty (EllipticExtension z.k) := by
  obtain ⟨s₀,k0,v0⟩ := oscillator_marker z hL dv
  obtain ⟨d,dp,_,mat⟩ := oscillator_matches z.dk dv k0 v0
  have rep (t : ℝ) : z.k t=3/d*realU ((t-s₀)/d) := by
    have h := (mat ((t-s₀)/d)).1
    rw [show s₀+d*((t-s₀)/d)=t by field_simp;ring] at h
    dsimp [realU]
    field_simp
    linear_combination h
  rw [show z.k=(fun t=>3/d*realU ((t-s₀)/d)) from funext rep]
  exact scaled_realU_elliptic _ _ _ dp

end ClosedSimilarity.LemniscaticExtension
#print axioms ClosedSimilarity.LemniscaticExtension.canonical_curvature_elliptic
#print axioms ClosedSimilarity.LemniscaticExtension.profile_oscillator_elliptic
