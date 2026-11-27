import LengthGrowth.ActualFlow.CyclicTurnEnvelope
import LengthGrowth.ActualFlow.MaterialTurnPrimitives
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open Set Finset Function MeasureTheory
namespace LengthGrowth.ActualFlow.TurningEnvelope

private theorem order_sum {G : ℝ→ℝ} (mono : Monotone G) (n : ℕ) (l r : Fin n→ℝ)
    {a b : ℝ} (ab : a≤b) (left : ∀i,a≤l i) (gap : ∀i j,i<j → r i≤l j) (right : ∀i,r i≤b) :
    ∑i,(G (r i)-G (l i)) ≤ G b-G a := by
  induction n generalizing a with
  | zero => simpa using sub_nonneg.mpr (mono ab)
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have rest := ih (fun i => l i.succ) (fun i => r i.succ) (right 0)
      (fun (i : Fin n) => gap 0 i.succ (Nat.zero_lt_succ i.val))
      (fun i j h => gap i.succ j.succ (Nat.succ_lt_succ h)) (fun i => right i.succ)
    linarith [mono (left 0)]

/-- One fixed smooth slice bounds the starting angular gain independently
    of the number of disjoint arcs. -/
theorem initial_gain_bound (p : PeriodicRegularPosition) :
    ∃ A≥0, ∀n,∀ e : Ends n, Ordered p.period e →
      |gain (fun u => arcTurn p.position 0 u) e|≤A := by
  let k := fun u => curvature p.position u*speed p.position u
  let G := fun u => ∫v in 0..u, |k v|
  have ct : Continuous k := (curvature_smooth p.smooth p.regular).continuous.mul
    (speed_smooth p.smooth p.regular).continuous
  have changeG (a b : ℝ) : G b-G a=∫v in a..b, |k v| := by
    have join := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      (ct.abs.intervalIntegrable 0 a) (ct.abs.intervalIntegrable a b)
    change (∫v in 0..b,|k v|)-(∫v in 0..a,|k v|)=_
    linarith
  have mono : Monotone G := by
    intro a b ab
    have v := intervalIntegral.integral_nonneg (μ:=volume) ab (fun u _ => abs_nonneg (k u))
    linarith [changeG a b]
  have ppos : 0≤2*p.period := by positivity [p.period_pos]
  refine ⟨G (2*p.period)-G 0,sub_nonneg.mpr (mono ppos),?_⟩
  intro n e he
  obtain ⟨q,hq,eq⟩ := boxed_representative p.period_pos e he _ p.arcTurn_periodic_increment
  rw [←eq]
  calc
    _ ≤ ∑ i, |arcTurn p.position 0 (q.2 i)-arcTurn p.position 0 (q.1 i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (G (q.2 i)-G (q.1 i)) := by
      apply sum_le_sum
      intro i _
      rw [p.arcTurn_between_primitives,changeG]
      simpa only [arcTurn,Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (μ:=volume) (f:=k) (hq.1.1 i)
    _ ≤ _ := order_sum mono n q.1 q.2 ppos hq.2.1.1 hq.1.2.1 hq.2.2.2

end LengthGrowth.ActualFlow.TurningEnvelope
#print axioms LengthGrowth.ActualFlow.TurningEnvelope.initial_gain_bound
