import SolitonClassification.LemniscaticLocalIdentities
import SolitonClassification.LemniscaticDyadic

noncomputable section
open Complex Set Filter Function Metric
open scoped Topology
namespace ClosedSimilarity.LemniscaticExtension
set_option backward.isDefEq.respectTransparency false

private theorem iter_real (n : ℕ) (t : ℝ) :
    (double^[n]) (realPair t)=realPair ((2:ℝ)^n*t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,real_double,pow_succ]
    congr 1
    ring

private theorem iter_analytic {seed : ℂ→ℂ × ℂ} {z : ℂ} {s : ℝ} (h1 : AnalyticAt ℂ (fun t=>(seed t).1) z)
    (h2 : AnalyticAt ℂ (fun t=>(seed t).2) z) (real : seed z=realPair s) (n : ℕ) :
    AnalyticAt ℂ (fun t=>((double^[n]) (seed t)).1) z ∧
    AnalyticAt ℂ (fun t=>((double^[n]) (seed t)).2) z := by
  induction n with
  | zero => exact ⟨h1,h2⟩
  | succ n ih =>
    have den : 1+((double^[n]) (seed z)).1^4≠0 := by
      rw [real,iter_real]
      change 1+(realU (2^n*s):ℂ)^4≠0
      exact_mod_cast (show (1:ℝ)+realU (2^n*s)^4≠0 by positivity)
    simp_rw [Function.iterate_succ_apply']
    exact ⟨(((analyticAt_const.mul ih.1).mul ih.2).div (analyticAt_const.add (ih.1.pow 4)) den),
      (((analyticAt_const.sub (analyticAt_const.mul (ih.1.pow 4))).add (ih.1.pow 8)).div
        ((analyticAt_const.add (ih.1.pow 4)).pow 2) (pow_ne_zero 2 den))⟩

/-- The lemniscatic sine has a global meromorphic representative with the
original smooth real restriction and the exact quarter-turn symmetry. -/
theorem existence_meromorphic_quarter :
    ∃ f : ℂ→ℂ, Meromorphic f ∧ (∀t:ℝ,AnalyticAt ℂ f (t:ℂ)) ∧
      (∀t:ℝ,f (t:ℂ)=(realU t:ℂ)) ∧ ∀z,f (I*z)=I*f z := by
  obtain ⟨g⟩ := local_oscillator_exists
  obtain ⟨rc,rp,ball1⟩ := Metric.mem_nhds_iff.mp
    ((((g.hu.eventually_analyticAt.and g.hv.eventually_analyticAt).and g.double_local)).and g.quarter_symmetry)
  obtain ⟨rr,rp',ball2⟩ := Metric.mem_nhds_iff.mp g.real_match
  let r := min rc rr
  have pos : 0<r := lt_min rp rp'
  have bc {x : ℂ} (hx : ‖x‖<r) := ball1 (show x∈ball (0:ℂ) rc from mem_ball_zero_iff.mpr (hx.trans_le (min_le_left _ _)))
  have br {x : ℝ} (hx : ‖x‖<r) := ball2 (show x∈ball (0:ℝ) rr from mem_ball_zero_iff.mpr (hx.trans_le (min_le_right _ _)))
  have law (z : ℂ) (hz : z∈ball 0 r) := (bc (mem_ball_zero_iff.mp hz)).1.2
  have hol (z : ℂ) (hz : z∈ball 0 r) := (bc (mem_ball_zero_iff.mp hz)).1.1
  let F := global g.pair pos
  have all := global_meromorphic (seed:=g.pair) pos hol law
  have axis (t : ℝ) : AnalyticAt ℂ (fun z=>(F z).1) (t:ℂ) ∧ F (t:ℂ)=realPair t := by
    obtain ⟨n,good⟩ := find_inside pos (t:ℂ)
    let s := t/(2:ℝ)^n
    have small := small_of_inside good
    have cl : ((t:ℂ)/2^n)=(s:ℂ) := by dsimp only [s];push_cast;rfl
    have rs : ‖s‖<r := by simpa only [cl,Complex.norm_real] using mem_ball_zero_iff.mp small
    have base : g.pair ((t:ℂ)/2^n)=realPair s := cl ▸ br rs
    have eq := global_locally_approx pos law good
    have cn : AnalyticAt ℂ (fun p:ℂ=>p/2^n) (t:ℂ) := by fun_prop
    obtain ⟨a,b⟩ := hol _ small
    have q := (iter_analytic (seed:=fun z=>g.pair (z/2^n))
      (a.comp (f:=fun z:ℂ=>z/2^n) cn) (b.comp (f:=fun z:ℂ=>z/2^n) cn) base n).1
    refine ⟨q.congr (eq.fun_comp Prod.fst).symm,?_⟩
    change global g.pair pos (t:ℂ)=_
    rw [global_eq_approx pos law good,approx,base,iter_real]
    congr 1
    dsimp only [s]
    field_simp
  refine ⟨fun z=>(F z).1,all.1,fun t=>(axis t).1,fun t=>congrArg Prod.fst (axis t).2,fun z=>?_⟩
  obtain ⟨n,good⟩ := find_inside pos z
  have good' : ‖I*z‖<(2:ℝ)^n*r := by simpa only [norm_mul,norm_I,one_mul] using good
  have small := small_of_inside good
  have sym := (bc (mem_ball_zero_iff.mp small)).2
  have comm : Function.Commute double quarterTurn := double_quarterTurn
  have q : F (I*z)=quarterTurn (F z) := by
    change global g.pair pos (I*z)=quarterTurn (global g.pair pos z)
    rw [global_eq_approx pos law good',global_eq_approx pos law good]
    unfold approx
    rw [show I*z/(2:ℂ)^n=I*(z/2^n) by ring,sym]
    exact (comm.iterate_left n) (g.pair (z/2^n))
  exact congrArg Prod.fst q

end ClosedSimilarity.LemniscaticExtension
