import LengthGrowth.OscillatorPeriodNumerator
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace LengthGrowth.OscillatorMean
open Real Set MeasureTheory

/-- The actual Newton equation, expressed by its two first derivatives. -/
structure QuarticOrbit where
  z : ℝ → ℝ
  v : ℝ → ℝ
  dz : ∀ t, HasDerivAt z (v t) t
  dv : ∀ t, HasDerivAt v (-(z t)^3/2+z t/4+1/4) t

lemma constant_of_zero_velocity {f : ℝ → ℝ} (hd : ∀ t,HasDerivAt f 0 t) (t : ℝ) :
    f t=f 0 := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=t)
    (fun s _ => hd s) (continuous_const.intervalIntegrable 0 t)
  exact sub_eq_zero.mp (by simpa using hi.symm)

lemma potential_distance (x : ℝ) :
    quarticPotential 1+(x-1)^2/8 ≤ quarticPotential x := by
  dsimp [quarticPotential]
  nlinarith only [mul_nonneg (sq_nonneg (x-1)) (sq_nonneg (x+1))]

lemma turning_values {H : ℝ} (hH : quarticPotential 1<H) :
    ∃ c r : ℝ, 0<r ∧ quarticPotential (c+r)=H ∧ quarticPotential (c-r)=H := by
  let M := 8*(H-quarticPotential 1)+2
  have hm : 0<M := by dsimp [M]; linarith
  have hcut : H≤quarticPotential 1+M^2/8 := by dsimp [M]; nlinarith [sq_nonneg (H-quarticPotential 1)]
  have continuousV : Continuous quarticPotential := by unfold quarticPotential; fun_prop
  obtain ⟨l,hl,el⟩ := intermediate_value_Icc' (show 1-M≤1 by linarith) continuousV.continuousOn
    (show H∈Icc (quarticPotential 1) (quarticPotential (1-M)) from
      ⟨hH.le,by nlinarith only [potential_distance (1-M),hcut]⟩)
  obtain ⟨u,hu,eu⟩ := intermediate_value_Icc (show 1≤1+M by linarith) continuousV.continuousOn
    (show H∈Icc (quarticPotential 1) (quarticPotential (1+M)) from
      ⟨hH.le,by nlinarith only [potential_distance (1+M),hcut]⟩)
  have l1 : l<1 := lt_of_le_of_ne hl.2 (fun h => hH.ne (h ▸ el))
  refine ⟨(l+u)/2,(u-l)/2,by linarith [hu.1],?_,?_⟩
  · simpa only [show (l+u)/2+(u-l)/2=u by ring] using eu
  · simpa only [show (l+u)/2-(u-l)/2=l by ring] using el

lemma turning_parameters {c r : ℝ} (hr : 0<r) (hV : quarticPotential (c+r)=quarticPotential (c-r)) :
    0<c ∧ c<1 ∧ 2*c*r^2=1+c-2*c^3 ∧ 1/4≤orbitOffset c r := by
  have ej : r*(2*c*r^2-(1+c-2*c^3))=0 := by
    dsimp [quarticPotential] at hV
    nlinarith only [hV]
  have turn := sub_eq_zero.mp ((mul_eq_zero.mp ej).resolve_left hr.ne')
  have poly : 0<2*c^2+2*c+1 := by nlinarith [sq_nonneg (c+1/2)]
  have fact : 2*c*r^2=(1-c)*(2*c^2+2*c+1) := by linarith only [turn]
  have hc : 0<c := by
    by_contra! h
    linarith only [fact,mul_nonpos_of_nonpos_of_nonneg (by linarith only [h] : 2*c≤0) (sq_nonneg r),
      mul_pos (by linarith only [h] : 0<1-c) poly]
  have h1 : c<1 := by
    have lhs : 0<2*c*r^2 := by positivity
    rw [fact] at lhs
    linarith only [(mul_pos_iff_of_pos_right poly).mp lhs]
  refine ⟨hc,h1,turn,?_⟩
  have e : 2*c*(orbitOffset c r-c^2)=1-c := by dsimp [orbitOffset]; nlinarith only [turn]
  by_cases h : c<1/2
  · apply (le_of_mul_le_mul_left (a:=2*c) _ (by positivity))
    nlinarith only [e,h,pow_nonneg hc.le 3]
  · have hn := (mul_nonneg_iff_of_pos_left (show 0<2*c by positivity)).mp
      (show 0≤2*c*(orbitOffset c r-c^2) by rw [e]; linarith)
    nlinarith [sq_nonneg (c-1/2)]

namespace QuarticOrbit
variable (o : QuarticOrbit)

def energy (t : ℝ) := (o.v t)^2/2+quarticPotential (o.z t)
theorem energy_eq (t : ℝ) : o.energy t=o.energy 0 := by
  apply constant_of_zero_velocity (fun s => ?_) t
  have d := (((o.dv s).pow 2).div_const 2).add
    (((((o.dz s).pow 4).sub ((o.dz s).pow 2)).sub ((o.dz s).const_mul 2)).div_const 8)
  convert d using 1 <;> first | rfl | ring

theorem equilibrium_or_turning :
    (∀ t,o.z t=1) ∨
    ∃ c r : ℝ, 0<r ∧ quarticPotential (c+r)=o.energy 0 ∧ quarticPotential (c-r)=o.energy 0 := by
  by_cases h : quarticPotential 1<o.energy 0
  · exact Or.inr (turning_values h)
  · left
    intro t
    have he := o.energy_eq t
    change (o.v t)^2/2+quarticPotential (o.z t)=o.energy 0 at he
    nlinarith only [le_of_not_gt h,he,potential_distance (o.z t),sq_nonneg (o.v t),
      sq_nonneg (o.z t-1)]

lemma velocity_squared {c r : ℝ} (hr : 0<r) (hp : quarticPotential (c+r)=o.energy 0)
    (hm : quarticPotential (c-r)=o.energy 0) (t : ℝ) :
    4*(o.v t)^2=(r^2-(o.z t-c)^2)*((o.z t+c)^2+orbitOffset c r) := by
  obtain ⟨_,_,turn,_⟩ := turning_parameters hr (hp.trans hm.symm)
  have he := (o.energy_eq t).trans hp.symm
  dsimp [energy,quarticPotential] at he
  dsimp [orbitOffset]
  linear_combination 8*he + (2*c+2*r-2*o.z t)*turn

end QuarticOrbit
end LengthGrowth.OscillatorMean
