import SolitonClassification.Reflected.Event
import SolitonClassification.Rotating.FlowJoint
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace SolitonClassification.Reflected
open SolitonClassification.Rotating Set
noncomputable section
set_option maxHeartbeats 4000000

def center : ℝ := 570216430671656/100000000000000
def width : ℝ := 1/10000
def leftSlope : ℝ := 719266732593/10^12-1/10^8
def rightSlope : ℝ := 719266732593/10^12+1/10^8
def slopes := Icc leftSlope rightSlope
def times := Icc (center-width) (center+width)
def initial (b : ℝ) : State := ![0,b/8,0,0,0,0]
def shot (b t : ℝ) : State := Flow t (initial b)
def velocity (z : ℝ×ℝ) : ℝ := 8*shot z.1 z.2 1
def tangentSupport (z : ℝ×ℝ) : ℝ := shot z.1 z.2 3

structure MidData : Prop where
  k : ∀ b∈slopes, shot b center 0 ∈ Icc (-(225:ℝ)/100) (-223/100)
  p : ∀ b∈slopes, shot b center 2 ∈ Icc (65/100:ℝ) (66/100)
  v : ∀ b∈slopes, |velocity (b,center)| ≤ 1/5000
  q : ∀ b∈slopes, |tangentSupport (b,center)| ≤ 1/1000
  vl : |velocity (leftSlope,center)| ≤ 4/10^8
  vr : |velocity (rightSlope,center)| ≤ 4/10^8
  ql : tangentSupport (leftSlope,center) ≤ -(18:ℝ)/10^9
  qr : 18/10^9 ≤ tangentSupport (rightSlope,center)

private theorem cont_initial : Continuous initial := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [initial] <;> fun_prop

private theorem cont_shot : ContinuousOn (fun z : ℝ×ℝ => shot z.1 z.2) (slopes ×ˢ times) := by
  apply (supportFlow_joint_lipschitz 1 (by norm_num) 6).continuousOn.comp
    (continuous_snd.prodMk (cont_initial.comp continuous_fst)).continuousOn
  rintro ⟨b,t⟩ ⟨_,ht⟩
  change t∈Icc (center-width) (center+width) at ht
  exact ⟨⟨by linarith [ht.1,show (0:ℝ)≤center-width by norm_num [center,width]],
    by linarith [ht.2,show center+width≤6 by norm_num [center,width]]⟩,mem_univ _⟩

private theorem cont_v : ContinuousOn velocity (slopes ×ˢ times) :=
  continuousOn_const.mul ((continuous_apply 1).comp_continuousOn' cont_shot)

private theorem cont_q : ContinuousOn tangentSupport (slopes ×ˢ times) :=
  (continuous_apply 3).comp_continuousOn' cont_shot

theorem shot_pitch_zero (b t : ℝ) : shot b t 4=0 := by
  have h:=supportFlow_coordinate_displacement 1 (by norm_num) (initial b) t 4
  simpa [shot,Flow,initial,coordinateSpeed] using h

private theorem moved (b : ℝ) {t : ℝ} (ht : t∈times) (i : Fin 6) :
    |shot b t i - shot b center i| ≤ coordinateSpeed i * width := by
  have h:=supportFlow_coordinate_displacement 1 (by norm_num) (shot b center) (t-center) i
  have e : Flow (t-center) (shot b center)=shot b t := by
    unfold shot; rw [← flow_restart]; congr 1; ring
  change |Flow (t-center) (shot b center) i-shot b center i|≤_ at h
  rw [e] at h
  exact h.trans (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩)
    (coordinateSpeed_nonneg _))

theorem actual_event_derivatives (h : MidData) {b t : ℝ} (hb : b∈slopes) (ht : t∈times) :
    shot b t ∈ outerTube ∧
      ∃v q, HasDerivAt (fun r => velocity (b,r)) v t ∧ 3≤v ∧
        HasDerivAt (fun r => tangentSupport (b,r)) q t ∧ |q|≤1 := by
  have e0:=abs_le.mp (moved b ht 0)
  have e1:=abs_le.mp (moved b ht 1)
  have e2:=abs_le.mp (moved b ht 2)
  have e3:=abs_le.mp (moved b ht 3)
  rw [show coordinateSpeed 2=75 from rfl] at e2
  rw [show coordinateSpeed 3=75 from rfl] at e3
  norm_num [coordinateSpeed,width] at e0 e1 e2 e3
  have hk:=h.k b hb
  have hp:=h.p b hb
  have hv:=abs_le.mp (h.v b hb)
  have hq:=abs_le.mp (h.q b hb)
  simp only [velocity,tangentSupport] at hv hq
  have hk₁ : 22/10 ≤ -shot b t 0 := by linarith [hk.2]
  have hk₂ : -shot b t 0 ≤ 23/10 := by linarith [hk.1]
  have hp₁ : 64/100 ≤ shot b t 2 := by linarith [hp.1]
  have hp₂ : shot b t 2 ≤ 68/100 := by linarith [hp.2]
  have htube : shot b t ∈ outerTube := by
    refine ⟨abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨by linarith,by linarith⟩,
      abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
    rw [shot_pitch_zero]; norm_num
  have hd := supportFlow_original_derivative 1 (by norm_num) (initial b) t htube
  rw [one_smul] at hd
  have hdv := (hasDerivAt_pi.mp hd 1).const_mul 8
  have hdq := hasDerivAt_pi.mp hd 3
  refine ⟨htube,_,_,hdv,?_,hdq,?_⟩
  · change 3 ≤ 8*(-(shot b t 0)^3/16-shot b t 2/8-shot b t 4*shot b t 3/8)
    rw [shot_pitch_zero]
    have hpow:=pow_le_pow_left₀ (by norm_num : (0:ℝ)≤22/10) hk₁ 3
    nlinarith
  · change |1+shot b t 0*shot b t 2|≤1
    have hprod:=mul_le_mul hk₂ hp₂ (by linarith : 0≤shot b t 2) (by norm_num)
    have hnn:=mul_nonneg (by linarith : 0≤-shot b t 0) (by linarith : 0≤shot b t 2)
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

theorem zero_from_midData (h : MidData) :
    ∃b∈slopes, ∃t∈times, velocity (b,t)=0 ∧ tangentSupport (b,t)=0 := by
  classical
  have hbc : leftSlope≤rightSlope := by norm_num [leftSlope,rightSlope]
  have hc : center∈times := by constructor <;> norm_num [width,center]
  have vd (b:ℝ) (hb:b∈slopes) := fun t (ht:t∈times) =>
    (actual_event_derivatives h hb ht).2
  have inc (b:ℝ) (hb:b∈slopes) : ∀x∈times, ∀y∈times, x≤y →
      3*(y-x)≤velocity (b,y)-velocity (b,x) := by
    apply (convex_Icc _ _).mul_sub_le_image_sub_of_le_deriv
    · exact cont_v.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hx => ⟨hb,hx⟩)
    · intro t ht
      obtain ⟨_,_,hv,_,_,_⟩:=vd b hb t (interior_subset ht)
      exact hv.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨_,_,hv,hv',_,_⟩:=vd b hb t (interior_subset ht)
      rwa [hv.deriv]
  have qtime (b:ℝ) (hb:b∈slopes) (t:ℝ) (ht:t∈times) :
      |tangentSupport (b,t)-tangentSupport (b,center)|≤|t-center| := by
    choose v q hv hv' hq hq' using vd b hb
    let w (t:ℝ) := if h:t∈times then q t h else 0
    have h1 (t:ℝ) (ht:t∈times) : HasDerivWithinAt (fun r => tangentSupport (b,r)) (w t) times t :=
      (by simpa only [w,dif_pos ht] using (hq t ht).hasDerivWithinAt)
    have h2 (t:ℝ) (ht:t∈times) : ‖w t‖≤1 := by simpa [w,ht] using hq' t ht
    simpa only [Real.norm_eq_abs,one_mul] using
      (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le h1 h2 hc ht
  have at_zero (b:ℝ) (hb:b∈slopes) {t:ℝ} (ht:t∈times) (hz:velocity (b,t)=0) :
      3*|t-center|≤|velocity (b,center)| := by
    by_cases hx : center≤t
    · rw [abs_of_nonneg (sub_nonneg.mpr hx)]
      have hh:=inc b hb center hc t ht hx
      rw [hz,zero_sub] at hh
      exact hh.trans (neg_le_abs _)
    · rw [abs_of_nonpos (by linarith : t-center≤0)]
      have hh:=inc b hb t ht center hc (le_of_not_ge hx)
      rw [hz,sub_zero] at hh
      linarith [le_abs_self (velocity (b,center))]
  apply event_rectangle hbc (by norm_num : (0:ℝ)<3) (by norm_num [width]) velocity tangentSupport
    cont_v cont_q inc
  · intro b hb
    exact (h.v b hb).trans (by norm_num [width])
  · intro t ht hz
    have hb : leftSlope∈slopes := ⟨le_rfl,hbc⟩
    linarith [(abs_le.mp (qtime _ hb t ht)).2,at_zero _ hb ht hz,h.vl,h.ql]
  · intro t ht hz
    have hb : rightSlope∈slopes := ⟨hbc,le_rfl⟩
    linarith [(abs_le.mp (qtime _ hb t ht)).1,at_zero _ hb ht hz,h.vr,h.qr]

end
end SolitonClassification.Reflected
#print axioms SolitonClassification.Reflected.zero_from_midData
