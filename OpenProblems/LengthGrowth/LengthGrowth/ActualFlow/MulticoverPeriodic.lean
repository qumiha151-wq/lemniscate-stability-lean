import LengthGrowth.ActualFlow.MulticoverIntegral

noncomputable section
open MeasureTheory Set Function
namespace LengthGrowth.Multicover

theorem deriv_mass_zero (P : ℝ) (a b : Fn) (pa : Periodic a P) (da : ∀t,HasDerivAt a (b t) t) :
    mass P b=0 := by
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=P) (fun t _=>da t) (b.continuous.intervalIntegrable ..)
  simpa [mass,show a P=a 0 from (zero_add P) ▸ pa 0] using eq

theorem gradient_norm_sq (P : ℝ) (hp : 0≤P) (a b c : Fn) (pa : Periodic a P) (pb : Periodic b P)
    (da : ∀t,HasDerivAt a (b t) t) (db : ∀t,HasDerivAt b (c t) t) :
    (norm2 P b)^2 ≤ norm2 P a*norm2 P c := by
  have iz := deriv_mass_zero P (a*b) (b^2+a*c) (fun t=>by simp [pa t,pb t]) (fun t=>by
    apply ((da t).mul (db t)).congr_deriv
    simp [pow_two])
  rw [map_add] at iz
  rw [norm_sq P hp]
  linarith only [iz,(abs_le.mp (abs_mass_product P hp a c)).1]

private theorem oscillation (P : ℝ) (hp : 0<P) (a b : Fn) (pa : Periodic a P) (pb : Periodic b P)
    (da : ∀t,HasDerivAt a (b t) t) (x y : ℝ) (xy : x≤y) (yx : y≤x+P) :
    |a y^2-a x^2|≤norm2 P a*norm2 P b := by
  let z:=fun t=>2*(a t*b t)
  have dz (t) : HasDerivAt (fun t=>a t^2) (z t) t := by
    apply ((da t).pow 2).congr_deriv; dsimp [z];ring
  have cz : Continuous z := (a.continuous.mul b.continuous).const_mul 2
  have trip (l r) (hr : l≤r) : |a r^2-a l^2|≤∫t in l..r,|z t| := by
    rw [←intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>dz t) (cz.intervalIntegrable l r)]
    exact intervalIntegral.abs_integral_le_integral_abs hr
  have one := trip x y xy
  have two := trip y (x+P) yx
  rw [pa x,abs_sub_comm] at two
  have add := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (cz.abs.intervalIntegrable x y) (cz.abs.intervalIntegrable y (x+P))
  have periodic : Periodic (fun t=>|z t|) P := fun t=>by simp [z,pa t,pb t]
  have eq := periodic.intervalIntegral_add_eq x 0
  rw [zero_add] at eq
  have factor : (∫t in 0..P,|z t|)=2*(∫t in 0..P,|a t*b t|) := by
    have f : (fun t=>|z t|)=(fun t=>(2:ℝ)*|a t*b t|) := by
      funext t; dsimp only [z]; rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    rw [f,intervalIntegral.integral_const_mul]
  have cs := LengthGrowth.interval_integral_abs_mul_le a.continuous b.continuous hp.le
  change (∫t in 0..P,|a t*b t|)≤norm2 P a*norm2 P b at cs
  linarith only [one,two,add,eq,factor,cs]

theorem sup_square (P : ℝ) (hp : 0<P) (a b : Fn) (pa : Periodic a P) (pb : Periodic b P)
    (da : ∀t,HasDerivAt a (b t) t) (y : ℝ) (hy : y∈Icc 0 P) :
    a y^2 ≤ mass P (a^2)/P + norm2 P a*norm2 P b := by
  obtain ⟨x,hx,minimal⟩ := isCompact_Icc.exists_isMinOn (show (Icc (0:ℝ) P).Nonempty from ⟨0,le_rfl,hp.le⟩)
    (a.continuous.pow 2).continuousOn
  have m : P*a x^2≤mass P (a^2) := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hp.le (intervalIntegrable_const (a:=0) (b:=P))
      ((a.continuous.pow 2).intervalIntegrable ..) (fun t ht => minimal ht)
    simpa [mass,smul_eq_mul] using hh
  have dy : |a y^2-a x^2|≤norm2 P a*norm2 P b := by
    rcases le_total x y with xy|yx
    · exact oscillation P hp a b pa pb da x y xy (by linarith only [hx.1,hy.2])
    · rw [abs_sub_comm]
      exact oscillation P hp a b pa pb da y x yx (by linarith only [hy.1,hx.2])
  have avg : a x^2≤mass P (a^2)/P := (le_div_iff₀ hp).mpr (by linarith only [m])
  linarith only [avg,(abs_le.mp dy).2]

end LengthGrowth.Multicover
