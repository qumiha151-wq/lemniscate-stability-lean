import LengthGrowth.ActualFlow.DefectHalfAngle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
open MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- Closing the tangent forces quantization of its signed curvature integral. -/
theorem curvature_turns_integer :
    ∃ n : ℤ, (∫ s in 0..c.period,c.curvature s)=(n:ℝ)*(2*Real.pi) := by
  let K := ∫ s in 0..c.period,c.curvature s
  have turn := c.tangent_eq_exp_integral_curvature 0 c.period
  have per : c.tangent c.period=c.tangent 0 := by simpa using c.tangent_periodic 0
  rw [per] at turn
  have nz : c.tangent 0≠0 := by
    intro h
    have := c.tangent_unit 0
    rw [h,norm_zero] at this
    norm_num at this
  have ex : Complex.exp ((K:ℂ)*Complex.I)=1 := by
    apply mul_right_cancel₀ nz
    simpa only [one_mul] using turn.symm
  obtain ⟨n,hn⟩ := Complex.exp_eq_one_iff.mp ex
  refine ⟨n,?_⟩
  have ei := congrArg Complex.im hn
  simpa [Complex.mul_im,Complex.mul_re,K] using ei

/-- A zero signed turning angle costs at least 8π² in the physical
length times the integral of squared curvature. -/
theorem zero_turn_product_floor
    (zero : (∫ s in 0..c.period,c.curvature s)=0) : 8*Real.pi^2≤2*c.energy*c.period := by
  let L := c.period
  let θ := fun x => ∫ s in 0..x,c.curvature s
  let S := fun s => Complex.exp (((θ s/2:ℝ):ℂ)*Complex.I)
  let v := fun s => S s*((c.curvature s/2:ℝ):ℂ)*Complex.I
  have lp : 0<L := c.period_pos
  have dθ (s : ℝ) : HasDerivAt θ (c.curvature s) s :=
    intervalIntegral.integral_hasDerivAt_right (c.curvature_continuous.intervalIntegrable 0 s)
      c.curvature_continuous.stronglyMeasurable.stronglyMeasurableAtFilter c.curvature_continuous.continuousAt
  have ds (s : ℝ) : HasDerivAt S (v s) s := by
    apply (((((dθ s).div_const 2).ofReal_comp).mul_const Complex.I).cexp).congr_deriv
    dsimp [v,S]
    ring
  have cs := continuous_iff_continuousAt.mpr (fun s => (ds s).continuousAt)
  have cv : Continuous v := (cs.mul (Complex.continuous_ofReal.comp
    (c.curvature_continuous.div_const 2))).mul continuous_const
  have unit (s : ℝ) : ‖S s‖=1 := by simp [S,Complex.norm_exp]
  have s0 : S 0=1 := by simp [S,θ]
  have sL : S L=1 := by simp [S,θ,L,zero]
  have comp (s : ℝ) : S s^2*c.tangent 0=c.tangent s := by
    rw [c.tangent_eq_exp_integral_curvature 0 s]
    dsimp only [S]
    rw [pow_two,←Complex.exp_add]
    push_cast
    congr 2
    ring
  have nonzero : c.tangent 0≠0 := by
    intro h
    have hw := c.tangent_unit 0
    simp [h] at hw
  have square : (∫ s in 0..L,S s^2)=0 := by
    apply mul_right_cancel₀ nonzero
    rw [zero_mul,←intervalIntegral.integral_mul_const]
    simp_rw [comp]
    exact c.tangent_integral_zero
  let m := (∫ s in 0..L,S s)/(L:ℂ)
  have floor := BendingSublevel.spinor_variance lp cs unit square
  change L≤2*(∫ s in 0..L,‖S s-m‖^2) at floor
  have cm : (∫ s in 0..L,S s-m)=0 := by
    rw [intervalIntegral.integral_sub (cs.intervalIntegrable ..) intervalIntegrable_const,
      intervalIntegral.integral_const,sub_zero,Complex.real_smul]
    dsimp only [m]
    have lm : (L:ℂ)≠0 := by exact_mod_cast lp.ne'
    field_simp
    ring
  have wir := LengthGrowth.periodic_wirtinger lp (fun s => S s-m) v
    (by rw [sL,s0]) (fun s => (ds s).sub_const m) cv cm
  have vn (s : ℝ) : ‖v s‖^2=(1/4:ℝ)*c.curvature s^2 := by
    simp only [v,norm_mul,unit,one_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    ring
  simp_rw [vn] at wir
  rw [intervalIntegral.integral_const_mul] at wir
  have he : (∫ s in 0..L,c.curvature s^2)=2*c.energy := by unfold energy; ring
  rw [he] at wir
  apply le_of_mul_le_mul_left (a:=L) _ lp
  change L*(8*Real.pi^2)≤L*(2*c.energy*L)
  linarith only [mul_le_mul_of_nonneg_left floor (sq_nonneg (2*Real.pi)),wir]

/-- Every slice in the defect-36 sublevel has signed turning angle ±2π. -/
theorem low_product_turning
    (below : 2*c.energy*c.period≤4*Real.pi^2+36) :
    (∫ s in 0..c.period,c.curvature s)=2*Real.pi ∨
      (∫ s in 0..c.period,c.curvature s)= -(2*Real.pi) := by
  obtain ⟨n,h⟩ := c.curvature_turns_integer
  have cs := LengthGrowth.interval_integral_mul_sq_le (f:=fun _ : ℝ => (1:ℝ))
    continuous_const c.curvature_continuous c.period_pos.le
  have cc : (∫ s in 0..c.period,c.curvature s)^2≤2*c.energy*c.period := by
    unfold energy
    have bound : (∫ s in 0..c.period,c.curvature s)^2≤c.period*(∫ s in 0..c.period,c.curvature s^2) := by
      simpa using cs
    linarith only [bound]
  have pgt : 9<Real.pi^2 := by nlinarith only [Real.pi_gt_three,sq_nonneg (Real.pi-3)]
  have nz : n≠0 := by
    rintro rfl
    simp only [Int.cast_zero,zero_mul] at h
    linarith only [c.zero_turn_product_floor h,below,pgt]
  rw [h] at cc
  have small : (n:ℝ)^2<4 := by
    by_contra! large
    nlinarith only [cc,below,mul_le_mul_of_nonneg_right large (sq_nonneg (2*Real.pi)),pgt]
  have nsq : n^2<4 := by exact_mod_cast small
  have vals : n=1 ∨ n= -1 := by
    have hi : n<2 := by nlinarith only [nsq,sq_nonneg (n-2)]
    have lo : -2<n := by nlinarith only [nsq,sq_nonneg (n+2)]
    omega
  rcases vals with rfl|rfl
  · left; simpa using h
  · right; simpa using h

end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.low_product_turning
