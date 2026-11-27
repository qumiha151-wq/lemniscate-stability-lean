import LengthGrowth.ActualFlow.TrigonometricClosureAveraging
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Function Set Real MeasureTheory
namespace LengthGrowth.Multicover.Outward.TrigonometricClosure

def phase (s : ℝ) := 2*sin s+sin (3*s)/96
def fastMean (c : ℝ) := average (fun s=>cos (c*phase s))
def horizontal (N : ℕ) (a c : ℝ) :=
  average (fun s=>cos (a*sin s+c*phase (N*s)))

theorem phase_periodic : Periodic phase (2*Real.pi) := by
  intro s
  simp only [phase,sin_three_mul,sin_add_two_pi]

theorem phase_odd (s : ℝ) : phase (-s)= -phase s := by
  simp only [phase,mul_neg,sin_neg];ring

theorem phase_cont : Continuous phase := by unfold phase; fun_prop

private theorem phase_error (s : ℝ) : |phase s-2*sin s|≤1/96 := by
  rw [show phase s-2*sin s=sin (3*s)/96 by unfold phase;ring,abs_div,abs_of_pos (by norm_num : (0:ℝ)<96)]
  exact div_le_div_of_nonneg_right (abs_sin_le_one _) (by norm_num)

private theorem phase_bound (s : ℝ) : |phase s|≤3 := by
  have h := abs_add_le (phase s-2*sin s) (2*sin s)
  rw [sub_add_cancel,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  linarith [phase_error s,abs_sin_le_one s]

theorem fastMean_lower {c : ℝ} (hc : |c-1|≤1/2000) : 1/5<fastMean c := by
  have p (s : ℝ) : |cos (c*phase s)-cos (2*sin s)|≤3/2000+1/96 := by
    apply (abs_cos_sub_cos_le _ _).trans
    rw [show c*phase s-2*sin s=(c-1)*phase s+(phase s-2*sin s) by ring]
    apply (abs_add_le ..).trans
    rw [abs_mul]
    have h := mul_le_mul hc (phase_bound s) (abs_nonneg _) (by norm_num)
    linarith [phase_error s]
  have cf : Continuous (fun s=>cos (c*phase s)) := continuous_cos.comp (continuous_const.mul phase_cont)
  have cg : Continuous (fun s=>cos (2*sin s)) := continuous_cos.comp (continuous_const.mul continuous_sin)
  have b := average_abs_bound (f:=fun s=>cos (c*phase s)-cos (2*sin s)) (cf.sub cg) (fun s _=>p s)
  rw [average_sub cf cg] at b
  change |fastMean c-J 2|≤_ at b
  linarith [(abs_le.mp b).1,J_endpoints.1]

theorem horizontal_error (N : ℕ) (n : 0<N) (a c : ℝ) (ha : 0≤a) :
    |horizontal N a c-J a*fastMean c|≤8*Real.pi*a/N := by
  let l := fun s=>cos (a*sin s)
  let v := fun s=>sin (a*sin s)
  let q := fun s=>cos (c*phase s)
  let w := fun s=>sin (c*phase s)
  have cq : Continuous q := continuous_cos.comp (continuous_const.mul phase_cont)
  have cw : Continuous w := continuous_sin.comp (continuous_const.mul phase_cont)
  have cl : Continuous l := continuous_cos.comp (continuous_const.mul continuous_sin)
  have cv : Continuous v := continuous_sin.comp (continuous_const.mul continuous_sin)
  have pq : Periodic q (2*Real.pi) := fun s=>by dsimp [q];rw [phase_periodic]
  have pw : Periodic w (2*Real.pi) := fun s=>by dsimp [w];rw [phase_periodic]
  have base (s : ℝ) : |a*cos s|≤a := by
    rw [abs_mul,abs_of_nonneg ha]
    simpa using mul_le_mul_of_nonneg_left (abs_cos_le_one s) ha
  have b (r s : ℝ) (br : |r|≤1) : |r*(a*cos s)|≤a := by
    rw [abs_mul]
    simpa using mul_le_mul br (base s) (abs_nonneg _) (by norm_num)
  have el := mixing cq pq (fun s=>abs_cos_le_one _)
    (fun s=>((hasDerivAt_sin s).const_mul a).cos) (by fun_prop)
    (fun s=>b _ s (by rw [abs_neg];exact abs_sin_le_one _)) n
  have ev := mixing cw pw (fun s=>abs_sin_le_one _)
    (fun s=>((hasDerivAt_sin s).const_mul a).sin) (by fun_prop)
    (fun s=>b _ s (abs_cos_le_one _)) n
  have zw : average w=0 := zero_of_periodic_odd pw (fun s=>by simp only [w,phase_odd,mul_neg,sin_neg])
  change |average (fun s=>v s*w (N*s))-average v*average w|≤_ at ev
  rw [zw,mul_zero,sub_zero] at ev
  change |average (fun s=>l s*q (N*s))-J a*fastMean c|≤_ at el
  have eq : horizontal N a c=average (fun s=>l s*q (N*s))-average (fun s=>v s*w (N*s)) := by
    unfold horizontal
    simp only [cos_add]
    exact average_sub (cl.mul (cq.comp (continuous_const.mul continuous_id))) (cv.mul (cw.comp (continuous_const.mul continuous_id)))
  rw [eq,show ∀u v r:ℝ,u-v-r=(u-r)-v by intros;ring]
  exact (abs_sub _ _).trans ((add_le_add el ev).trans_eq (by ring))

end LengthGrowth.Multicover.Outward.TrigonometricClosure
#print axioms LengthGrowth.Multicover.Outward.TrigonometricClosure.horizontal_error
