import LengthGrowth.ActualFlow.TrigonometricClosureEndpoints
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
set_option maxHeartbeats 155000
open Function Set Real MeasureTheory
namespace LengthGrowth.Multicover.Outward.TrigonometricClosure

private theorem horizontal_cont (N : ℕ) : Continuous (fun z:ℝ×ℝ=>horizontal N z.1 z.2) := by
  have ci : Continuous (fun z:ℝ×ℝ=>∫s in (0:ℝ)..2*Real.pi,cos (z.1*sin s+z.2*phase (N*s))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f:=fun (z:ℝ×ℝ) (s:ℝ)=>cos (z.1*sin s+z.2*phase (N*s)))
      (by unfold Function.uncurry phase;fun_prop) 0 (2*Real.pi)
  exact ci.div_const _

private theorem vertical_zero (N : ℕ) (a c : ℝ) :
    average (fun s=>sin (a*sin s+c*phase (N*s)))=0 := by
  apply zero_of_periodic_odd
  · intro s
    have v := phase_periodic.nat_mul N ((N:ℝ)*s)
    change phase ((N:ℝ)*s+N*(2*Real.pi))=phase (N*s) at v
    simp only [mul_add,sin_add_two_pi,v]
  · intro s;simp only [mul_neg,sin_neg,phase_odd,←neg_add,sin_neg]

private theorem ratio_close {N : ℕ} (nn : (2000:ℝ)≤N) {b:ℝ} (near : |b-(N:ℝ)|≤1) :
    |b/N-1|≤1/2000 := by
  have np : (0:ℝ)<N := by linarith
  rw [show b/N-1=(b-N)/N by field_simp,abs_div,abs_of_pos np]
  exact ((div_le_div_iff_of_pos_right np).mpr near).trans
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) nn)

private theorem at_zero {N : ℕ} (n : 0<N) {c:ℝ} (clos : |c-1|≤1/2000) :
    0≤horizontal N 0 c := by
  have e := horizontal_error N n 0 c le_rfl
  have h : J 0=1 := by simp only [J,zero_mul,cos_zero,average_const]
  rw [h,one_mul,mul_zero,zero_div] at e
  linarith only [(abs_le.mp e).1,fastMean_lower clos]

private theorem at_three {N : ℕ} (n : 0<N) (nn : (2000:ℝ)≤N) {c:ℝ} (clos : |c-1|≤1/2000) :
    horizontal N 3 c≤0 := by
  have np : (0:ℝ)<N := by linarith
  have e := (abs_le.mp (horizontal_error N n 3 c (by norm_num))).2
  have f := fastMean_lower clos
  have j : J 3≤ -(1/4:ℝ) := by linarith only [J_endpoints.2]
  have m := mul_le_mul_of_nonneg_right j (by linarith only [f] : 0≤fastMean c)
  have k : 8*Real.pi*3/N≤1/20 := by
    apply (div_le_iff₀ np).mpr
    linarith only [Real.pi_lt_four,nn]
  linarith only [m,k,e,f]

private theorem toIntegral {f : ℝ→ℝ} (v : average f=0) : (∫s in (0:ℝ)..2*Real.pi,f s)=0 := by
  change (∫s in (0:ℝ)..2*Real.pi,f s)/(2*Real.pi)=0 at v
  exact (div_eq_zero_iff.mp v).resolve_right (by positivity)

/-- For every continuous amplitude within one unit of the fast integer, a slow
amplitude in [0,3] makes both components of the displacement vanish. -/
theorem zero_turn_closes {N : ℕ} (hN : 2000≤N) (A : ℝ→ℝ)
    (cA : ContinuousOn A (Icc 0 3)) (near : ∀a∈Icc 0 3, |A a-(N:ℝ)|≤1) :
    ∃a∈Icc (0:ℝ) 3, (∫s in 0..2*Real.pi,cos (a*sin s+(A a/N)*phase (N*s)))=0 ∧
      (∫s in 0..2*Real.pi,sin (a*sin s+(A a/N)*phase (N*s)))=0 := by
  have n : 0<N := by omega
  have nn : (2000:ℝ)≤N := by exact_mod_cast hN
  let H : ℝ→ℝ := fun a=>horizontal N a (A a/N)
  have cont : ContinuousOn H (Icc 0 3) := (horizontal_cont N).comp_continuousOn
    (f:=fun a:ℝ=>(a,A a/(N:ℝ))) (continuousOn_id.prodMk (cA.div_const _))
  have pos0 : 0≤H 0 := at_zero n (ratio_close nn (near 0 ⟨le_rfl,by norm_num⟩))
  have neg3 : H 3≤0 := at_three n nn (ratio_close nn (near 3 ⟨by norm_num,le_rfl⟩))
  obtain ⟨a,ha,z⟩ := intermediate_value_Icc' (f:=H) (by norm_num : (0:ℝ)≤3) cont
    (show (0:ℝ)∈Icc (H 3) (H 0) from ⟨neg3,pos0⟩)
  refine ⟨a,ha,?_,?_⟩
  · exact toIntegral (f:=fun s=>cos (a*sin s+(A a/N)*phase (N*s))) z
  · exact toIntegral (f:=fun s=>sin (a*sin s+(A a/N)*phase (N*s))) (vertical_zero N a (A a/N))

end LengthGrowth.Multicover.Outward.TrigonometricClosure
#print axioms LengthGrowth.Multicover.Outward.TrigonometricClosure.zero_turn_closes
