import LengthGrowth.ActualFlow.StrongArcEnergy
import LengthGrowth.ActualFlow.TurningPacking
import LengthGrowth.ActualFlow.TurningFamily

noncomputable section
open Set Function MeasureTheory
open scoped ContDiff
namespace LengthGrowth.ActualFlow.MacroscopicTurning

private theorem exact_family {a b : ℝ} {k:ℝ→ℝ} (U:Finset (ℝ × ℝ))
    (good : ∀J∈U, a≤J.1 ∧ J.1<J.2 ∧ J.2≤b ∧ |∫x in J.1..J.2,k x|=1/4)
    (dis : ∀I∈U,∀J∈U,I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2)) :
    ExcursionFamily k a b U.card := by
  refine ⟨U,rfl,?_,dis⟩
  intro J hj
  obtain ⟨l,lt,r,eq⟩:=good J hj
  exact ⟨l,lt,r,eq.ge⟩

theorem scalar_excursions_of_low_force {P M : ℝ} (hP:0<P) {k:ℝ→ℝ}
    (hk:ContDiff ℝ ∞ k) (period:Periodic k P)
    (rms:(∫x in 0..P,k x^2)=P) (force:(∫x in 0..P,|FiniteSignWindow.force k x|)≤P/2)
    (cap:∀x,|k x|≤M) (absturn:1/4≤∫x in 0..P,|k x|) :
    ∃ a m, ExcursionFamily k a (a+P) m ∧ P≤(m:ℝ)*M := by
  have m0:0≤M := (abs_nonneg _).trans (cap 0)
  by_cases zero : ∃a, k a=0
  · obtain ⟨a,za⟩:=zero
    have dk:=(contDiff_infty_iff_deriv.mp hk).2
    have pk':=actual_deriv_periodic period (hk.differentiable (by simp))
    have pk'':=actual_deriv_periodic pk' (dk.differentiable (by simp))
    have pf:Periodic (fun x=>|FiniteSignWindow.force k x|) P := by
      intro x
      dsimp only [FiniteSignWindow.force]
      rw [pk'' x,period x]
    have ps:Periodic (fun x=>k x^2) P := fun x => congrArg (fun t:ℝ => t^2) (period x)
    have r : (∫x in a..a+P,k x^2)=(a+P)-a := by
      rw [ps.intervalIntegral_add_eq a 0,zero_add,rms]
      ring
    have f : (∫x in a..a+P,|FiniteSignWindow.force k x|)≤((a+P)-a)/2 := by
      rw [pf.intervalIntegral_add_eq a 0,zero_add,add_sub_cancel_left]
      exact force
    obtain ⟨S,good,dis,big,mass⟩:=large_lobe_energy hk (le_add_of_nonneg_right hP.le)
      za ((period a).trans za) (fun x _=>cap x) r f
    obtain ⟨U,_,turn,part,hd⟩:=pack_quarter_turn_lobes hk.continuous good dis big
    refine ⟨a,U.card,exact_family U part hd,?_⟩
    nlinarith only [mass,mul_le_mul_of_nonneg_left turn m0]
  · have sign : (∀x∈Ioo 0 P,0≤k x) ∨ (∀x∈Ioo 0 P,k x≤0) := by
      by_contra! bad
      obtain ⟨⟨x,_,hx⟩,y,_,hy⟩:=bad
      exact zero (intermediate_value_univ x y hk.continuous ⟨hx.le,hy.le⟩)
    obtain ⟨U,_,turn,part,hd⟩:=pack_quarter_turn_sign hk.continuous hP.le sign absturn
    refine ⟨0,U.card,by simpa using exact_family U part hd,?_⟩
    have top:=intervalIntegral.integral_mono_on (μ:=volume) hP.le ((hk.continuous.pow 2).intervalIntegrable _ _)
      ((hk.continuous.abs.const_mul M).intervalIntegrable _ _) (fun x _ => show k x^2≤M*|k x| by
        nlinarith only [mul_le_mul_of_nonneg_right (cap x) (abs_nonneg (k x)),sq_abs (k x)])
    change (∫x in 0..P,k x^2) ≤ ∫x in 0..P,M*|k x| at top
    rw [rms,intervalIntegral.integral_const_mul] at top
    nlinarith only [top,mul_le_mul_of_nonneg_left turn m0,hP]

end LengthGrowth.ActualFlow.MacroscopicTurning
#print axioms LengthGrowth.ActualFlow.MacroscopicTurning.scalar_excursions_of_low_force
