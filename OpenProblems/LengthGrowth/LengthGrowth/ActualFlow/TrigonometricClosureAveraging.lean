import LengthGrowth.ActualFlow.TrigonometricClosureMean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open Real Function Set MeasureTheory
namespace LengthGrowth.Multicover.Outward.TrigonometricClosure

theorem average_const (c : ℝ) : average (fun _=>c)=c := by
  simp only [average,intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  field_simp

theorem average_sub {f g : ℝ→ℝ} (cf : Continuous f) (cg : Continuous g) :
    average (fun s=>f s-g s)=average f-average g := by
  simp only [average,intervalIntegral.integral_sub (cf.intervalIntegrable ..) (cg.intervalIntegrable ..),sub_div]

theorem average_mul_const (f : ℝ→ℝ) (c : ℝ) :
    average (fun s=>f s*c)=average f*c := by
  unfold average;rw [intervalIntegral.integral_mul_const];ring

theorem average_abs_bound {f : ℝ→ℝ} (cf : Continuous f) {K : ℝ}
    (bounds : ∀s∈Icc 0 (2*Real.pi), |f s|≤K) : |average f|≤K := by
  apply abs_le.mpr
  constructor
  · rw [←average_const (-K)]
    exact average_mono continuous_const cf (fun s hs=>(abs_le.mp (bounds s hs)).1)
  · rw [←average_const K]
    exact average_mono cf continuous_const (fun s hs=>(abs_le.mp (bounds s hs)).2)

theorem zero_of_periodic_odd {f : ℝ→ℝ} (hp : Periodic f (2*Real.pi)) (odd : ∀s,f (-s)= -f s) :
    average f=0 := by
  have sym : (fun s=>f (2*Real.pi-s))=(fun s=> -f s) := by
    funext s;rw [show 2*Real.pi-s= -s+2*Real.pi by ring,hp,odd]
  have z := intervalIntegral.integral_comp_sub_left (f:=f) (a:=0) (b:=2*Real.pi) (2*Real.pi)
  rw [sym,intervalIntegral.integral_neg,sub_self,sub_zero] at z
  unfold average
  rw [show (∫s in (0:ℝ)..2*Real.pi,f s)=0 by linarith,zero_div]

/-- Products with a periodic fast wave decouple at rate O(1/N). The
primitive is bounded on each fast period, independent of the integer N. -/
theorem mixing {q l dl : ℝ→ℝ} (cq : Continuous q) (pq : Periodic q (2*Real.pi))
    (qbound : ∀s, |q s|≤1) (ld : ∀s, HasDerivAt l (dl s) s) (cd : Continuous dl)
    {a : ℝ} (db : ∀s, |dl s|≤a) {N : ℕ} (n : 0<N) :
    |average (fun s=>l s*q (N*s))-average l*average q|≤4*Real.pi*a/N := by
  let P := 2*Real.pi
  let m := average q
  let g := fun s=>q s-m
  let G := fun s=>∫u in 0..s,g u
  have pp : 0<P := by dsimp only [P];positivity
  have np : (0:ℝ)<N := by exact_mod_cast n
  have cg : Continuous g := cq.sub continuous_const
  have cl : Continuous l := continuous_iff_continuousAt.mpr fun s=>(ld s).continuousAt
  have dg (s : ℝ) : HasDerivAt G (g s) s := intervalIntegral.integral_hasDerivAt_right
    (cg.intervalIntegrable 0 s) cg.stronglyMeasurable.stronglyMeasurableAtFilter cg.continuousAt
  have pg : Periodic g P := fun s=>by dsimp [g,P];rw [pq]
  have zero : G P=0 := by
    change (∫s in 0..P,q s-m)=0
    rw [intervalIntegral.integral_sub (cq.intervalIntegrable ..) (continuous_const.intervalIntegrable ..),
      intervalIntegral.integral_const,sub_zero,smul_eq_mul]
    change _-P*((∫s in 0..P,q s)/P)=0
    field_simp [pp.ne'];ring
  have pG : Periodic G P := by
    intro s
    have split := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (cg.intervalIntegrable 0 s) (cg.intervalIntegrable s (s+P))
    have one := pg.intervalIntegral_add_eq s 0
    rw [zero_add] at one
    change _=G P at one
    rw [one,zero,add_zero] at split
    exact split.symm
  have bm : |m|≤1 := average_abs_bound cq (fun s _=>qbound s)
  have bG (s : ℝ) : |G s|≤2*P := by
    obtain ⟨z,hz,eq⟩ := pG.exists_mem_Ico₀ pp s
    rw [eq]
    have hi := intervalIntegral.integral_mono_on (μ:=volume) hz.1 (cg.abs.intervalIntegrable ..)
      ((continuous_const (y:=(2:ℝ))).intervalIntegrable ..)
      (fun u _=>show |g u|≤2 from (abs_sub _ _).trans (by linarith [qbound u,bm]))
    rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hi
    exact (intervalIntegral.abs_integral_le_integral_abs hz.1).trans (hi.trans (by linarith [hz.2]))
  let H := fun s:ℝ=>G (N*s)/(N:ℝ)
  have dH (s : ℝ) : HasDerivAt H (g (N*s)) s := by
    apply (((dg (N*s)).comp s ((hasDerivAt_id s).const_mul (N:ℝ))).div_const (N:ℝ)).congr_deriv
    field_simp
  have ch : Continuous H := continuous_iff_continuousAt.mpr fun s=>(dH s).continuousAt
  have h0 : H 0=0 := by simp [H,G]
  have hP : H P=0 := by
    have z := pG.nat_mul N 0
    simp only [zero_add] at z
    change G (N*P)/N=0
    rw [z];simp [G]
  have bH (s : ℝ) : |H s|≤2*P/N := by
    rw [show H s=G (N*s)/N from rfl,abs_div,abs_of_pos np]
    exact div_le_div_of_nonneg_right (bG _) np.le
  have cgN : Continuous (fun s:ℝ=>g (N*s)) := cg.comp (continuous_const.mul continuous_id)
  have parts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a:=0) (b:=P)
    (fun s _=>ld s) (fun s _=>dH s) (cd.intervalIntegrable ..) (cgN.intervalIntegrable ..)
  rw [hP,h0,mul_zero,mul_zero,sub_zero,zero_sub] at parts
  have v : average (fun s=>l s*g (N*s))= -average (fun s=>dl s*H s) := by
    change (∫s in 0..P,l s*g (N*s))/P= -((∫s in 0..P,dl s*H s)/P)
    rw [parts,neg_div]
  have eq : (fun s:ℝ=>l s*g (N*s))=fun s=>l s*q (N*s)-l s*m := by
    funext s;dsimp only [g];ring
  rw [eq, average_sub (f:=fun s=>l s*q (N*s)) (g:=fun s=>l s*m) (cl.mul (cq.comp (continuous_const.mul continuous_id))) (cl.mul continuous_const),
    average_mul_const] at v
  rw [show average q=m from rfl,v,abs_neg]
  apply (average_abs_bound (f:=fun s=>dl s*H s) (cd.mul ch) (fun s _=>?_)).trans_eq (show a*(2*P/N)=4*Real.pi*a/N by dsimp only [P];ring)
  rw [abs_mul]
  exact mul_le_mul (db s) (bH s) (abs_nonneg _) (le_trans (abs_nonneg _) (db s))

end LengthGrowth.Multicover.Outward.TrigonometricClosure
#print axioms LengthGrowth.Multicover.Outward.TrigonometricClosure.mixing
