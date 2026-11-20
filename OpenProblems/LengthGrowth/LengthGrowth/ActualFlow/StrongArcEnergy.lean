import LengthGrowth.ActualFlow.StrongArcIntegrals
import LengthGrowth.ActualFlow.SmallTurnArcs

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace LengthGrowth.ActualFlow.MacroscopicTurning

private theorem point_excess (t : ℝ) : max (t^2-1/4) 0 ≤ |t|^3 := by
  have h:=sq_abs t
  have q:=mul_nonneg (sq_nonneg (|t|-2/3)) (show 0≤|t|+1/3 by positivity)
  apply max_le _ (by positivity)
  nlinarith only [q,h]

/-- On a low-force RMS slice cut at a zero, at least half of its normalized
energy is bounded by the maximum curvature times the combined turning
of finitely many complete sign lobes with angle above a quarter radian. -/
theorem large_lobe_energy {a b M : ℝ} {k:ℝ→ℝ} (hk:ContDiff ℝ ∞ k)
    (hab : a≤b) (ha:k a=0) (hb:k b=0)
    (cap:∀x∈Icc a b, |k x|≤M)
    (rms:(∫x in a..b,k x^2)=b-a)
    (force:(∫x in a..b,|FiniteSignWindow.force k x|)≤(b-a)/2) :
    ∃ B : Finset (ℝ × ℝ), (∀I∈B,Lobe k a b I) ∧
      (∀I∈B,∀J∈B,I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2)) ∧
      (∀I∈B,1/4 < ∫x in I.1..I.2,|k x|) ∧
      (b-a)/2 ≤ M*∑I∈B,∫x in I.1..I.2,|k x| := by
  classical
  let θ := fun I : ℝ × ℝ => ∫x in I.1..I.2, |k x|
  let J := fun I : ℝ × ℝ => ∫x in I.1..I.2, |FiniteSignWindow.force k x|
  let v := fun x => max (k x^2-1/4) 0
  have cv : Continuous v := ((hk.continuous.pow 2).sub continuous_const).max continuous_const
  have cf := (FiniteSignWindow.force_continuous hk).abs
  obtain ⟨S,good,dis,covers⟩ := finite_lobe_cover hk.continuous ha hb (by norm_num : (0:ℝ)<1/2)
  let B:=S.filter (fun I => 1/4<θ I)
  have hs (I) (hi:I∈B) : I∈S := (Finset.mem_filter.mp hi).1
  refine ⟨B,fun I hi => good I (hs I hi),fun I hi J hj => dis I (hs I hi) J (hs J hj),
    fun _ hi => (Finset.mem_filter.mp hi).2,?_⟩
  have mass:=sum_lobe_integrals_eq hab good dis cv (by
    intro x hx nz
    apply covers x ⟨hx.1.le,hx.2.le⟩
    by_contra! hh
    have hh2 := mul_self_le_mul_self (abs_nonneg (k x)) hh.le
    apply nz
    dsimp [v]
    apply max_eq_right
    nlinarith only [hh2,sq_abs (k x)])
  have almost := intervalIntegral.integral_mono_on (μ:=volume) hab
    (((hk.continuous.pow 2).sub continuous_const).intervalIntegrable _ _)
    (cv.intervalIntegrable a b) (fun x _ => (le_max_left (k x^2-1/4) (0:ℝ)))
  change (∫x in a..b,k x^2-1/4)≤∫x in a..b,v x at almost
  rw [intervalIntegral.integral_sub (f:=fun x=>k x^2) (g:=fun _ => (1/4:ℝ))
    ((hk.continuous.pow 2).intervalIntegrable _ _) intervalIntegrable_const,
    rms,intervalIntegral.integral_const,smul_eq_mul,←mass] at almost
  have piece (I) (hi:I∈S) : (∫x in I.1..I.2,v x) ≤ (3/16)*J I +
      (if 1/4<θ I then M*θ I else 0) := by
    have g:=good I hi
    have nonneg : 0≤J I := intervalIntegral.integral_nonneg_of_forall g.ordered.le (fun _=>abs_nonneg _)
    by_cases high : 1/4<θ I
    · rw [if_pos high]
      have top:=intervalIntegral.integral_mono_on (μ:=volume) g.ordered.le (cv.intervalIntegrable _ _)
        ((hk.continuous.abs.const_mul M).intervalIntegrable _ _) (fun x hx => show v x≤M*|k x| by
          have h:=mul_le_mul_of_nonneg_right (cap x ⟨g.left.trans hx.1,hx.2.trans g.right⟩) (abs_nonneg (k x))
          have h0:=sq_nonneg (k x)
          dsimp [v]
          apply max_le <;> nlinarith only [h,h0,sq_abs (k x)])
      change (∫x in I.1..I.2,v x) ≤ ∫x in I.1..I.2,M*|k x| at top
      rw [intervalIntegral.integral_const_mul] at top
      dsimp only [θ]
      linarith only [top,nonneg]
    · rw [if_neg high,add_zero]
      have top:=intervalIntegral.integral_mono_on (μ:=volume) g.ordered.le (cv.intervalIntegrable _ _)
        ((hk.continuous.abs.pow 3).intervalIntegrable _ _) (fun x _ => point_excess (k x))
      have h:=small_turn_cubic_of_le hk g.ordered.le g.zero_left g.zero_right (le_of_not_gt high) (le_refl (1/4:ℝ))
      change (∫x in I.1..I.2, v x) ≤ ∫x in I.1..I.2, |k x|^3 at top
      change (∫x in I.1..I.2, |k x|^3) ≤ 3*(1/4:ℝ)^2*J I at h
      nlinarith only [top,h]
  have summed:=Finset.sum_le_sum piece
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_filter,←Finset.mul_sum] at summed
  have total:=sum_lobe_integrals_le hab good dis cf (fun x=>abs_nonneg (FiniteSignWindow.force k x))
  change (∑I∈S,J I) ≤ _ at total
  change _ ≤ (3/16)*(∑I∈S,J I)+M*∑I∈B,θ I at summed
  change _ ≤ M*∑I∈B,θ I
  linarith only [almost,summed,total,force,hab]

end LengthGrowth.ActualFlow.MacroscopicTurning
#print axioms LengthGrowth.ActualFlow.MacroscopicTurning.large_lobe_energy
