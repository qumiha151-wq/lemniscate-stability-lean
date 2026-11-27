import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! The Bernoulli expander in the clock given by minus the logarithm of
bending energy. Normal material labels have a nonzero uniform angular
speed in this clock even after compensation by any rigid rotation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.LemniscateAngularClock
open Real Set

def x (u : ℝ) := cos u / (1+sin u^2)
def y (u : ℝ) := x u * sin u
def dx (u : ℝ) := -sin u*(3-sin u^2)/(1+sin u^2)^2
def dy (u : ℝ) := (1-3*sin u^2)/(1+sin u^2)^2
def angle (u : ℝ) := π/2+3*arctan (sin u)
def drift (u : ℝ) := 2*sin u*cos u/(1+sin u^2)
def rate (u : ℝ) := 6*sin u*(1-sin u^2)/(1+sin u^2)^2

theorem position_derivatives (u : ℝ) : HasDerivAt x (dx u) u ∧ HasDerivAt y (dy u) u := by
  have hd : 1+sin u^2≠0 := by positivity
  have hx : HasDerivAt x (dx u) u := by
    convert! (hasDerivAt_cos u).div (((hasDerivAt_sin u).pow 2).const_add 1) hd using 1
    dsimp [dx]; field_simp
    linear_combination 2*sin u*(sin_sq_add_cos_sq u)
  refine ⟨hx,?_⟩
  convert! hx.mul (hasDerivAt_sin u) using 1
  dsimp [dy,dx,x]; field_simp
  linear_combination -(1+sin u^2)*(sin_sq_add_cos_sq u)

private theorem identities (u : ℝ) :
    dx u^2+dy u^2=1/(1+sin u^2) ∧
    (x u*dx u+y u*dy u)= -drift u/(1+sin u^2) := by
  have hd : 1+sin u^2≠0 := by positivity
  constructor <;> dsimp [x,y,dx,dy,drift] <;> field_simp <;> ring

/-- The lift is the angle of the actual positive unit tangent. -/
theorem tangent_angle (u : ℝ) :
    cos (angle u)=dx u*sqrt (1+sin u^2) ∧ sin (angle u)=dy u*sqrt (1+sin u^2) := by
  let s := sin u
  have hp : 0<1+s^2 := by positivity
  let w := sqrt (1+s^2)
  have hw : w^2=1+s^2 := Real.sq_sqrt hp.le
  have hn : w≠0 := (Real.sqrt_pos.mpr hp).ne'
  have sn : sin (arctan s)=s/w := sin_arctan s
  have cs : cos (arctan s)=1/w := cos_arctan s
  change cos (π/2+3*arctan s)=(-s*(3-s^2)/(1+s^2)^2)*w ∧
    sin (π/2+3*arctan s)=((1-3*s^2)/(1+s^2)^2)*w
  rw [cos_add,sin_add,cos_pi_div_two,sin_pi_div_two,cos_three_mul,sin_three_mul,sn,cs]
  constructor <;> rw [← hw] <;> field_simp <;> ring_nf <;> grind

theorem material_rate {σ u : ℝ → ℝ} {t a v : ℝ}
    (dσ : HasDerivAt σ a t) (du : HasDerivAt u v t) (pos : 0<σ t)
    (normal : deriv (fun r => σ r*x (u r)) t*dx (u t)+deriv (fun r => σ r*y (u r)) t*dy (u t)=0) :
    HasDerivAt (fun r => angle (u r)) ((a/σ t)*rate (u t)) t := by
  obtain ⟨fx,fy⟩ := position_derivatives (u t)
  change deriv (σ*(x ∘ u)) t*dx (u t)+deriv (σ*(y ∘ u)) t*dy (u t)=0 at normal
  rw [(dσ.mul (fx.comp t du)).deriv,(dσ.mul (fy.comp t du)).deriv] at normal
  have ortho : a*(x (u t)*dx (u t)+y (u t)*dy (u t))+
      σ t*v*(dx (u t)^2+dy (u t)^2)=0 := by
    convert! normal using 1; dsimp; ring
  rw [(identities _).1,(identities _).2] at ortho
  have hd : 1+sin (u t)^2≠0 := by positivity
  field_simp at ortho
  have clock : v=(a/σ t)*drift (u t) := by field_simp; linarith only [ortho]
  have dangle := (((hasDerivAt_arctan _).comp (u t) (hasDerivAt_sin _)).const_mul 3).const_add (π/2)
  convert! dangle.comp t du using 1
  rw [clock]
  dsimp [rate,drift]; field_simp
  linear_combination -(6*a*sin (u t))*(sin_sq_add_cos_sq (u t))

theorem max_rate (u : ℝ) : |rate u|≤3/2 := by
  let s := |sin u|
  have hs : s^2=sin u^2 := sq_abs _
  have h : sin u^2≤1 := by nlinarith [sin_sq_add_cos_sq u,sq_nonneg (cos u)]
  have denominator : |(1+sin u^2)^2|=(1+sin u^2)^2 := abs_of_nonneg (sq_nonneg _)
  have factor : |1-sin u^2|=1-sin u^2 := abs_of_nonneg (sub_nonneg.mpr h)
  have six : |(6:ℝ)|=6 := by norm_num
  unfold rate
  rw [abs_div,abs_mul,abs_mul,factor,six,denominator]
  apply (div_le_iff₀ (by positivity)).mpr
  change 6*s*(1-sin u^2) ≤ _
  rw [← hs]
  nlinarith only [sq_nonneg (s^2+2*s-1)]

theorem two_extremes : ∃ u v : ℝ, rate u=3/2 ∧ rate v= -(3/2) := by
  let a := sqrt 2-1
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have am : -1≤a := by dsimp [a]; linarith [sqrt_nonneg (2:ℝ)]
  have ap : a≤1 := by dsimp [a]; nlinarith [sqrt_nonneg (2:ℝ)]
  let u := arcsin a
  have su : sin u=a := sin_arcsin am ap
  have ha : a^2+2*a-1=0 := by dsimp [a]; nlinarith
  have val : rate u=3/2 := by
    rw [rate,su]
    field_simp
    linear_combination -(a^2+2*a-1)*ha*3
  refine ⟨u,-u,val,?_⟩
  rw [← val]
  dsimp [rate]; rw [sin_neg]; ring

/-- Even after subtracting an arbitrary common angular velocity, the
supremum over material labels is at least 3/2 in the energy clock;
zero common velocity attains that sharp bound. -/
theorem sharp_compensated_rate {v : ℝ → ℝ} (onto : Function.Surjective v) (c : ℝ) :
    (∃ u, 3/2 ≤ |rate (v u)-c|) ∧ ∀u, |rate (v u)|≤3/2 := by
  obtain ⟨a,b,ha,hb⟩ := two_extremes
  obtain ⟨u,hu⟩ := onto a
  obtain ⟨w,hw⟩ := onto b
  refine ⟨?_,fun _ => max_rate _⟩
  rcases le_total 0 c with cp | cn
  · refine ⟨w,?_⟩
    rw [hw,hb,abs_of_nonpos (by linarith)]
    linarith
  · refine ⟨u,?_⟩
    rw [hu,ha,abs_of_nonneg (by linarith)]
    linarith

/-- For the bending energy of a dilated profile, the relative logarithmic
energy loss is the logarithmic dilation rate. Every pure-normal
parametrization attains the sharp compensated angular bound at each time. -/
theorem sharp_bending_clock {σ : ℝ → ℝ} {t a E₀ : ℝ} (positive : 0<σ t) (growth : 0<a)
    (energy : 0<E₀) (dσ : HasDerivAt σ a t) (u : ℝ → ℝ → ℝ)
    (smooth : ∀ j, DifferentiableAt ℝ (u j) t) (onto : Function.Surjective (fun j => u j t))
    (normal : ∀j, deriv (fun r => σ r*x (u j r)) t*dx (u j t)+
      deriv (fun r => σ r*y (u j r)) t*dy (u j t)=0) (c : ℝ) :
    let E := fun r => E₀/σ r
    let speed := fun j => deriv (fun r => angle (u j r)) t / (-deriv E t/E t)
    (∃j, 3/2 ≤ |speed j-c|) ∧ ∀j, |speed j|≤3/2 := by
  dsimp only
  have ed := ((hasDerivAt_const t E₀).div dσ positive.ne').deriv
  change deriv (fun r => E₀/σ r) t = _ at ed
  have eq (j : ℝ) : deriv (fun r => angle (u j r)) t / (-deriv (fun r => E₀/σ r) t / (E₀/σ t))=rate (u j t) := by
    rw [(material_rate dσ (smooth j).hasDerivAt positive (normal j)).deriv,ed]
    field_simp [positive.ne', growth.ne', energy.ne']
    ring
  simpa only [eq] using (sharp_compensated_rate onto c)

end LengthGrowth.ActualFlow.LemniscateAngularClock
#print axioms LengthGrowth.ActualFlow.LemniscateAngularClock.tangent_angle
#print axioms LengthGrowth.ActualFlow.LemniscateAngularClock.material_rate
#print axioms LengthGrowth.ActualFlow.LemniscateAngularClock.sharp_compensated_rate
#print axioms LengthGrowth.ActualFlow.LemniscateAngularClock.sharp_bending_clock
