import LengthGrowth.ActualFlow.FiniteSignIntegrals
import LengthGrowth.ActualFlow.FiniteSignBudget

noncomputable section
open MeasureTheory Function
namespace LengthGrowth.ActualFlow.CriticalDensity

theorem periodic_window {F : ℝ → ℝ} (hF : Continuous F) {P : ℝ} (hp : Periodic F P)
    (c z : ℝ) {l : ℝ} (hl : 0≤l) (hl1 : l≤P) :
    (∫ x in z..z+l, |F x|) ≤ c*l + Real.sqrt (l * ∫ x in (0:ℝ)..P, (|F x|-c)^2) := by
  let g := fun x => |F x|-c
  have hg : Continuous g := hF.abs.sub continuous_const
  have hgperiod : Periodic (fun x => g x^2) P := by
    intro x
    simp only [g,hp x]
  have hab : z ≤ z+l := by linarith
  have hsub := intervalIntegral.integral_mono_interval (μ := volume) (le_refl z) hab
    (by linarith : z+l ≤ z+P) (Filter.Eventually.of_forall (fun x => sq_nonneg (g x)))
    ((hg.pow 2).intervalIntegrable z (z+P))
  rw [hgperiod.intervalIntegral_add_eq z 0,zero_add] at hsub
  have hcs := LengthGrowth.interval_integral_mul_sq_le (f := fun _ : ℝ => (1:ℝ))
    continuous_const hg hab
  simp only [one_mul,one_pow,intervalIntegral.integral_const,smul_eq_mul,mul_one,add_sub_cancel_left] at hcs
  have hsq := hcs.trans (mul_le_mul_of_nonneg_left hsub hl)
  have hR : 0 ≤ ∫ x in (0:ℝ)..P, g x^2 :=
    intervalIntegral.integral_nonneg_of_forall (hl.trans hl1) (fun x => sq_nonneg _)
  have hbound : (∫ x in z..z+l, g x) ≤ Real.sqrt (l*∫ x in (0:ℝ)..P, g x^2) := by
    nlinarith [Real.sq_sqrt (mul_nonneg hl hR),Real.sqrt_nonneg (l*∫ x in (0:ℝ)..P, g x^2),
      sq_nonneg ((∫ x in z..z+l, g x)-Real.sqrt (l*∫ x in (0:ℝ)..P, g x^2))]
  have hdiff : (∫ x in z..z+l, g x) = (∫ x in z..z+l, |F x|)-l*c := by
    rw [show g = fun x => |F x|-c from rfl,intervalIntegral.integral_sub (hF.abs.intervalIntegrable _ _)
      intervalIntegrable_const,intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left]
  change _ ≤ c*l+Real.sqrt (l*∫ x in (0:ℝ)..P, g x^2)
  linarith


theorem residual_mass (F : ℝ→ℝ) (hF : Continuous F) (P : ℝ) :
    (∫s in (0:ℝ)..P,(|F s|-1/2)^2)=(∫s in (0:ℝ)..P,F s^2)-(∫s in (0:ℝ)..P,|F s|)+P/4 := by
  have he (s:ℝ) : (|F s|-1/2)^2=(F s^2-|F s|)+1/4 := by nlinarith only [sq_abs (F s)]
  simp_rw [he]
  rw [intervalIntegral.integral_add (f:=fun s=>F s^2-|F s|) (g:=fun _=>1/4)
    (((hF.pow 2).sub hF.abs).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_sub (f:=fun s=>F s^2) (g:=fun s=>|F s|) ((hF.pow 2).intervalIntegrable _ _)
      (hF.abs.intervalIntegrable _ _),intervalIntegral.integral_const,smul_eq_mul,sub_zero]
  ring

theorem amplitude_from_cost {a m R : ℝ} (ha : 2≤a) (hm : 1≤m)
    (hR : R≤16*m*a) (hc : a^2/4 < (1/2)*(200*m/a)+Real.sqrt (200*m/a*R)) :
    a ≤ 32*Real.sqrt m := by
  have ha0 : 0<a := by linarith
  have hm0 : 0≤m := by linarith
  have sq : (200*m/a)*R ≤ (60*m)^2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ha0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hR (show 0≤200*m by positivity),
      mul_nonneg (sq_nonneg m) ha0.le]
  have root : Real.sqrt (200*m/a*R)≤60*m := (Real.sqrt_le_iff).mpr ⟨by positivity,sq⟩
  have quo : 200*m/a≤100*m := (div_le_iff₀ ha0).mpr (by nlinarith only [mul_le_mul_of_nonneg_left ha hm0])
  have bound : a^2≤440*m := by linarith
  have hmroot:=Real.sq_sqrt hm0
  by_contra! h
  have h2:=mul_self_lt_mul_self (show 0≤32*Real.sqrt m by positivity) h
  nlinarith only [h2,hmroot,hm0,bound]

end LengthGrowth.ActualFlow.CriticalDensity
#print axioms LengthGrowth.ActualFlow.CriticalDensity.amplitude_from_cost
