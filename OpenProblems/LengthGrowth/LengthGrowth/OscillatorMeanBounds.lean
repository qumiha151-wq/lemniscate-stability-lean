import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform pointwise estimates for the paired quartic oscillator. -/
noncomputable section
namespace LengthGrowth.OscillatorMean
open Real
set_option maxHeartbeats 900000

def den (c : ℝ) := 1+(c-2*c^3)
def scale (c : ℝ) := 2*c^3/den c
def offset (c : ℝ) := (1-(c-2*c^3))/den c
def q (c y : ℝ) := 4*scale c+y^2+offset c
def discr (c y : ℝ) := (4*scale c-y^2)^2+2*offset c*(4*scale c+y^2)+(offset c)^2
def weight (c y : ℝ) := √(2*q c y/discr c y+2/√(discr c y))
def factor (c y : ℝ) := 1-4*y^2/(q c y+√(discr c y))
def baseline (y : ℝ) := (4-7*y^2)/(4+7*y^2)
def angular (c θ : ℝ) := weight c (cos θ)*factor c (cos θ)

theorem parameters {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1/2) :
    0 ≤ scale c ∧ scale c ≤ 1/4 ∧ 4/7 ≤ offset c ∧ offset c ≤ 1 := by
  have c2 : c^2≤1/4 := by nlinarith [mul_nonneg hc (sub_nonneg.mpr hc')]
  have c3 : c^3≤1/8 := by nlinarith [mul_nonneg hc (show 0≤1/4-c^2 by linarith)]
  have zlo : 0≤c-2*c^3 := by nlinarith [mul_nonneg hc (show 0≤1-2*c^2 by linarith)]
  have zhi : c-2*c^3≤3/11 := by
    nlinarith [mul_nonneg (sq_nonneg (c-49/120)) (show 0≤c+2*(49/120) by linarith)]
  have hd : 0<den c := by dsimp [den]; linarith
  refine ⟨div_nonneg (by positivity) hd.le, (div_le_iff₀ hd).mpr ?_,
    (le_div_iff₀ hd).mpr ?_, (div_le_iff₀ hd).mpr ?_⟩ <;> dsimp [den] <;> linarith

theorem discr_positive {c : ℝ} (hc : 0≤c) (hc' : c≤1/2) (y : ℝ) :
    0<discr c y ∧ 0<q c y := by
  obtain ⟨ht,_,he,_⟩ := parameters hc hc'
  have he' : 0<offset c := by linarith
  dsimp [discr,q]
  constructor
  · positivity
  · positivity

theorem pointwise {c y : ℝ} (hc : 0≤c) (hc' : c≤1/2) (hy : y^2≤1) :
    8/7 ≤ weight c y ∧ weight c y ≤ 8/3 ∧ baseline y ≤ factor c y := by
  obtain ⟨ht,htu,he,heu⟩ := parameters hc hc'
  obtain ⟨hD,hQ⟩ := discr_positive hc hc' y
  have hep : 0<offset c := by linarith
  have hS := sqrt_pos.mpr hD
  have hS2 := sq_sqrt hD.le
  have d_le : discr c y ≤ (q c y)^2 := by
    dsimp [discr,q]
    nlinarith [mul_nonneg ht (sq_nonneg y)]
  have s_le : √(discr c y) ≤ q c y := by nlinarith
  have le_d : offset c*q c y ≤ discr c y := by
    dsimp [discr,q]
    nlinarith [sq_nonneg (4*scale c-y^2),mul_nonneg hep.le (show 0≤4*scale c+y^2 by positivity)]
  have le_s : offset c ≤ √(discr c y) := by
    have hh : (offset c)^2≤discr c y := by
      dsimp [discr]
      nlinarith [sq_nonneg (4*scale c-y^2),mul_nonneg hep.le (show 0≤4*scale c+y^2 by positivity)]
    exact le_of_sq_le_sq (hh.trans_eq hS2.symm) hS.le
  have hq3 : q c y ≤ 3 := by dsimp [q]; linarith
  have wpos : 0≤2*q c y/discr c y+2/√(discr c y) := by positivity
  have ws : (weight c y)^2=2*q c y/discr c y+2/√(discr c y) := sq_sqrt wpos
  have wn : 0≤weight c y := sqrt_nonneg _
  have d1 : 2/q c y ≤ 2*q c y/discr c y := by
    apply (div_le_div_iff₀ hQ hD).mpr
    nlinarith only [d_le]
  have d2 : 2/q c y ≤ 2/√(discr c y) := by gcongr
  have d3 : (2:ℝ)/3 ≤ 2/q c y := by gcongr
  have u1 : 2*q c y/discr c y ≤ 2/offset c := by
    apply (div_le_div_iff₀ hD hep).mpr
    nlinarith only [le_d]
  have u2 : 2/√(discr c y) ≤ 2/offset c := by gcongr
  have u3 : 2/offset c ≤ 7/2 := (div_le_iff₀ hep).mpr (by linarith)
  refine ⟨by nlinarith only [ws,wn,d1,d2,d3], by nlinarith only [ws,wn,u1,u2,u3], ?_⟩
  have ds : (offset c+y^2-4*scale c)^2 ≤ discr c y := by
    dsimp [discr]
    nlinarith [mul_nonneg ht hep.le]
  have s_ge : offset c+y^2-4*scale c ≤ √(discr c y) := by
    exact le_of_sq_le_sq (ds.trans_eq hS2.symm) hS.le
  have dpos : 0<q c y+√(discr c y) := by positivity
  have dlow : 2*(offset c+y^2) ≤ q c y+√(discr c y) := by unfold q; linarith only [s_ge]
  have dsmall : 0<4+7*y^2 := by positivity
  have hb : baseline y=1-14*y^2/(4+7*y^2) := by
    unfold baseline
    field_simp [dsmall.ne']
    ring
  rw [hb]
  apply sub_le_sub_left _ 1
  apply (div_le_div_iff₀ dpos dsmall).mpr
  nlinarith only [mul_nonneg (sq_nonneg y)
    (show 0≤7*(q c y+√(discr c y))-2*(4+7*y^2) by linarith only [dlow,he])]

theorem continuous_angular {c : ℝ} (hc : 0≤c) (hc' : c≤1/2) : Continuous (angular c) := by
  have cQ : Continuous (q c) := by unfold q; fun_prop
  have cD : Continuous (discr c) := by unfold discr; fun_prop
  have hQ (x : ℝ) := (discr_positive hc hc' x).2
  have hD (x : ℝ) := (discr_positive hc hc' x).1
  have cS := Real.continuous_sqrt.comp cD
  have cW : Continuous (weight c) := Real.continuous_sqrt.comp
    (((cQ.const_mul 2).div cD (fun x => (hD x).ne')).add
      (continuous_const.div cS (fun x => (sqrt_pos.mpr (hD x)).ne')))
  have cB : Continuous (factor c) := continuous_const.sub
    (((continuous_id.pow 2).const_mul 4).div (cQ.add cS)
      (fun x => (add_pos (hQ x) (sqrt_pos.mpr (hD x))).ne'))
  exact (cW.comp continuous_cos).mul (cB.comp continuous_cos)

end LengthGrowth.OscillatorMean
