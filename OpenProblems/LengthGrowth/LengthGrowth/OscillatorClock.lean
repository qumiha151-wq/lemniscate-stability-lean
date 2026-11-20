import LengthGrowth.OscillatorPhase
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace LengthGrowth.OscillatorMean
open Set Real MeasureTheory

def anglePosition (c r θ : ℝ) := c+r*cos θ
def inverseRadical (c r θ : ℝ) := 1/√((anglePosition c r θ+c)^2+orbitOffset c r)
def denominator (c r : ℝ) := ∫ θ in 0..π,inverseRadical c r θ
def numerator (c r : ℝ) := ∫ θ in 0..π,anglePosition c r θ*inverseRadical c r θ
def physicalPeriod (c r : ℝ) := 4*denominator c r
def periodMean (c r : ℝ) := numerator c r/denominator c r

theorem anglePosition_cont (c r : ℝ) : Continuous (anglePosition c r) :=
  (continuous_cos.const_mul r).const_add c

theorem inv_radical_cont {c r : ℝ} (hd : 0<orbitOffset c r) :
    Continuous (inverseRadical c r) := by
  unfold inverseRadical
  apply continuous_const.div
  · exact Real.continuous_sqrt.comp ((((anglePosition_cont c r).add continuous_const).pow 2).add continuous_const)
  · intro θ
    exact (sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) hd)).ne'

private theorem fold_half {f : ℝ → ℝ} (hf : Continuous f) (href : ∀ x,f (2*π-x)=f x) :
    (∫ x in 0..2*π,f x)=2*∫ x in 0..π,f x := by
  have h := intervalIntegral.integral_comp_sub_left (a:=0) (b:=π) f (2*π)
  simp only [href,show 2*π-π=π by ring,sub_zero] at h
  have add := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hf.intervalIntegrable 0 π) (hf.intervalIntegrable π (2*π))
  linarith

theorem period_bounds {c r : ℝ} (hd : 1/4≤orbitOffset c r) :
    0<physicalPeriod c r ∧ physicalPeriod c r≤8*π := by
  have hdp : 0<orbitOffset c r := by linarith
  have ci := inv_radical_cont hdp
  have lo : 0<denominator c r := intervalIntegral.intervalIntegral_pos_of_pos
    (ci.intervalIntegrable 0 π) (fun x => by
      dsimp [inverseRadical]; positivity) pi_pos
  have hi := intervalIntegral.integral_mono_on (f:=inverseRadical c r) (g:=fun _ => (2:ℝ))
    (μ:=volume) pi_pos.le (ci.intervalIntegrable 0 π) (continuous_const.intervalIntegrable 0 π)
    (fun θ _ => (div_le_iff₀ (sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) hdp))).mpr (by
      have sq := sq_sqrt (show 0≤(anglePosition c r θ+c)^2+orbitOffset c r by positivity)
      nlinarith only [hd,sq,sqrt_nonneg ((anglePosition c r θ+c)^2+orbitOffset c r),
        sq_nonneg (anglePosition c r θ+c)]))
  rw [intervalIntegral.integral_const] at hi
  change _≤(π-0)*2 at hi
  change 0<4*denominator c r ∧ 4*denominator c r≤8*π
  change (∫ θ in 0..π,inverseRadical c r θ)≤_ at hi
  dsimp only [denominator] at *
  constructor <;> linarith

theorem periodMean_pos {c r : ℝ} (hr : 0<r) (hV : quarticPotential (c+r)=quarticPotential (c-r)) :
    0<periodMean c r := by
  obtain ⟨_,_,_,hd⟩ := turning_parameters hr hV
  have hD := (period_bounds hd).1
  have hN := period_numerator_pos_of_equal_potential hr hV
  have he (θ : ℝ) : anglePosition c r θ*inverseRadical c r θ =
      (c+r*cos θ)/√((2*c+r*cos θ)^2+(2*c^2+r^2-1)) := by
    unfold anglePosition inverseRadical orbitOffset
    simp only [anglePosition]
    rw [show c+r*cos θ+c=2*c+r*cos θ by ring]
    ring
  have positive : 0<numerator c r := by simpa only [numerator,he] using hN
  exact div_pos positive (by dsimp [physicalPeriod] at hD; linarith)

namespace QuarticOrbit
variable (o : QuarticOrbit)

/-- The measured trajectory returns after the angular clock advances by one
turn, regardless of its initial position, velocity or phase. -/
theorem actual_time_quadrature {c r : ℝ} (hr : 0<r) (hp : quarticPotential (c+r)=o.energy 0)
    (hm : quarticPotential (c-r)=o.energy 0) :
    Function.Periodic o.z (physicalPeriod c r) ∧
    (∀ s, (∫ t in s..s+physicalPeriod c r,o.z t)=4*numerator c r) ∧
    (∀ y,∃ t∈Icc 0 (physicalPeriod c r),o.z t=anglePosition c r y) := by
  obtain ⟨_,_,_,hd⟩ := turning_parameters hr (hp.trans hm.symm)
  have hdp : 0<orbitOffset c r := by linarith
  obtain ⟨θ,dθ,hz⟩ := o.actual_phase hr hp hm
  let w : ℝ → ℝ := fun t => √((o.z t+c)^2+orbitOffset c r)/2
  let g : ℝ → ℝ := fun x => 2*inverseRadical c r x
  let h : ℝ → ℝ := fun x => 2*(anglePosition c r x*inverseRadical c r x)
  have cZ : Continuous o.z := continuous_iff_continuousAt.mpr (fun t => (o.dz t).continuousAt)
  have cw : Continuous w :=
    (Real.continuous_sqrt.comp (((cZ.add continuous_const).pow 2).add continuous_const)).div_const 2
  have ci := inv_radical_cont hdp
  have cg : Continuous g := ci.const_mul 2
  have ch : Continuous h := ((anglePosition_cont c r).mul ci).const_mul 2
  have gp : Function.Periodic g (2*π) := by
    intro x
    simp only [g,inverseRadical,anglePosition,cos_add_two_pi]
  have hp' : Function.Periodic h (2*π) := by
    intro x
    simp only [h,inverseRadical,anglePosition,cos_add_two_pi]
  have fullg : (∫ x in 0..2*π,g x)=physicalPeriod c r := by
    rw [fold_half cg (fun x => by simp only [g,inverseRadical,anglePosition,cos_two_pi_sub])]
    dsimp only [g,physicalPeriod,denominator]
    rw [intervalIntegral.integral_const_mul]
    ring
  have fullh : (∫ x in 0..2*π,h x)=4*numerator c r := by
    rw [fold_half ch (fun x => by simp only [h,inverseRadical,anglePosition,cos_two_pi_sub])]
    dsimp only [h,numerator]
    rw [intervalIntegral.integral_const_mul]
    ring
  have gg (t : ℝ) : (g ∘ θ) t*w t=1 := by
    change 2*(1/√((anglePosition c r (θ t)+c)^2+orbitOffset c r))*
      (√((o.z t+c)^2+orbitOffset c r)/2)=1
    rw [← show o.z t=anglePosition c r (θ t) from hz t]
    field_simp [(sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) hdp)).ne']
  have gh (t : ℝ) : (h ∘ θ) t*w t=o.z t := by
    have e : (h ∘ θ) t=anglePosition c r (θ t)*(g ∘ θ) t := by
      dsimp only [Function.comp_apply,h,g]; ring
    rw [e,mul_assoc,gg,mul_one,← show o.z t=anglePosition c r (θ t) from hz t]
  let clock : ℝ → ℝ := fun x => ∫ a in 0..x,g a
  have inc : StrictMono clock := strictMono_of_hasDerivAt_pos (primitive_derivative cg)
    (fun x => by dsimp [g,inverseRadical]; positivity)
  have drift (s t : ℝ) : clock (θ t)-clock (θ s)=t-s := by
    have hs := intervalIntegral.integral_comp_mul_deriv (a:=s) (b:=t)
      (f:=θ) (f':=w) (g:=g) (fun t _ => dθ t) cw.continuousOn cg
    rw [show (fun t => (g ∘ θ) t*w t)=(fun _ => (1:ℝ)) from funext gg,
      intervalIntegral.integral_const] at hs
    have add := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      (cg.intervalIntegrable 0 (θ s)) (cg.intervalIntegrable (θ s) (θ t))
    simp only [smul_eq_mul,mul_one] at hs
    dsimp [clock]
    linarith
  have turnθ (s : ℝ) : θ (s+physicalPeriod c r)=θ s+2*π := by
    apply inc.injective
    have shift := gp.intervalIntegral_add_eq_add 0 (θ s) cg.intervalIntegrable
    rw [zero_add,fullg] at shift
    change clock (θ s+2*π)=clock (θ s)+physicalPeriod c r at shift
    linarith only [drift s (s+physicalPeriod c r),shift]
  refine ⟨?_,?_,?_⟩
  · intro s
    rw [hz,hz s,turnθ,cos_add_two_pi]
  · intro s
    have hs := intervalIntegral.integral_comp_mul_deriv (a:=s) (b:=s+physicalPeriod c r)
      (f:=θ) (f':=w) (g:=h) (fun t _ => dθ t) cw.continuousOn ch
    rw [show (fun t => (h ∘ θ) t*w t)=o.z from funext gh,turnθ,hp'.intervalIntegral_add_eq (θ s) 0,
      zero_add,fullh] at hs
    exact hs
  · intro y
    have cθ : Continuous θ := continuous_iff_continuousAt.mpr (fun u => (dθ u).continuousAt)
    obtain ⟨a,ha,hcos⟩ := cos_periodic.exists_mem_Ico (by positivity) y (θ 0)
    have endθ : θ (physicalPeriod c r)=θ 0+2*π := by simpa using turnθ 0
    have mem : a∈Icc (θ 0) (θ (physicalPeriod c r)) := ⟨ha.1,endθ ▸ ha.2.le⟩
    obtain ⟨t,ht,eqt⟩ := intermediate_value_Icc (period_bounds hd).1.le cθ.continuousOn mem
    exact ⟨t,ht,by rw [hz t,eqt,← hcos]; rfl⟩

end QuarticOrbit
end LengthGrowth.OscillatorMean
