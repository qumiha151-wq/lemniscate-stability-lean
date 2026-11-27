import SolitonClassification.BernoulliArcMatch
import SolitonClassification.LemniscaticDuplicate

noncomputable section
open ClosedSimilarity.BernoulliGeometry
namespace ClosedSimilarity.LemniscaticExtension
set_option backward.isDefEq.respectTransparency false

def realU (s : ℝ) := curvature (angle s)/3
def realV (s : ℝ) := slope (angle s)/3
def realPair (s : ℝ) : ℂ × ℂ := ((realU s:ℂ),(realV s:ℂ))

@[simp] theorem init_realU : realU 0=0 := by simp [realU]
@[simp] theorem init_realV : realV 0=1 := by norm_num [realV]

theorem realU_deriv (s : ℝ) : HasDerivAt realU (realV s) s := (canonical_dk s).div_const 3
theorem realV_deriv (s : ℝ) : HasDerivAt realV (-2*realU s^3) s := by
  convert! (canonical_dv s).div_const 3 using 1
  dsimp only [realU]
  ring

theorem real_energy (s : ℝ) : realV s^2+realU s^4=1 := by
  have d (t : ℝ) : HasDerivAt (fun x=>realV x^2+realU x^4) 0 t := by
    convert! ((realV_deriv t).pow 2).add ((realU_deriv t).pow 4) using 1
    ring
  simpa using is_const_of_deriv_eq_zero (fun t=>(d t).differentiableAt) (fun t=>(d t).deriv) s 0

theorem real_double (s : ℝ) : double (realPair s)=realPair (2*s) := by
  let f (t : ℝ) := U (realU t) (realV t)
  let g (t : ℝ) := V (realU t)
  have nf (t : ℝ) : 1+realU t^4≠0 := by positivity
  have df (t : ℝ) : HasDerivAt f (2*g t) t :=
    derivative_U (realU_deriv _) (realV_deriv _) (real_energy _) (nf t)
  have dg (t : ℝ) : HasDerivAt g (-4*f t^3) t :=
    derivative_V (realU_deriv _) (real_energy _) (nf t)
  have clk (t : ℝ) : HasDerivAt (fun t:ℝ=>2*t) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
  have d1 (t : ℝ) : HasDerivAt (fun t=>6*f t) (12*g t) t := by
    convert! (df t).const_mul 6 using 1;ring
  have d2 (t : ℝ) : HasDerivAt (fun t=>12*g t) (-2/9*(6*f t)^3) t := by
    convert! (dg t).const_mul 12 using 1;ring
  have d3 (t : ℝ) : HasDerivAt (fun t=>6*realU (2*t)) (12*realV (2*t)) t := by
    convert! ((realU_deriv _).comp t (clk t)).const_mul 6 using 1;ring
  have d4 (t : ℝ) : HasDerivAt (fun t=>12*realV (2*t)) (-2/9*(6*realU (2*t))^3) t := by
    convert! ((realV_deriv _).comp t (clk t)).const_mul 12 using 1;ring
  have eq := oscillator_unique d1 d2 d3 d4 (s₀:=0) (by norm_num [f,U]) (by norm_num [g,V]) s
  have e1 : f s=realU (2*s) := by linarith [eq.1]
  have e2 : g s=realV (2*s) := by linarith [eq.2]
  apply Prod.ext
  · change U (realU s:ℂ) (realV s:ℂ)=(realU (2*s):ℂ)
    dsimp only [f,U] at e1 ⊢
    exact_mod_cast e1
  · change V (realU s:ℂ)=(realV (2*s):ℂ)
    dsimp only [g,V] at e2 ⊢
    exact_mod_cast e2

theorem real_period : Function.Periodic realU (arc (2*Real.pi)) := by
  intro s
  have shift : angle (s+arc (2*Real.pi))=angle s+2*Real.pi := by
    apply arc_strictMono.injective
    rw [arc_angle,arc_period,arc_angle]
  simp [realU,shift,curvature,height,root]

end ClosedSimilarity.LemniscaticExtension
