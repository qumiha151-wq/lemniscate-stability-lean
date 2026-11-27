import SolitonClassification.CentreOscillatorParity
import SolitonClassification.PhysicalCrossingResponse

noncomputable section
open Set MeasureTheory
namespace ClosedSimilarity.CrossingResponse
open CentreOscillator

/-- The frozen windows in the real centre shot have equally spaced positive
    heights, nonzero crossing velocity, and alternating first responses. -/
theorem oscillator_window_data :
    ∃ H>0, ∃ d>0, ∃ C<0, ∀ n : ℕ,
      (K 0 ((n:ℝ)*H)=0 ∧ V 0 ((n:ℝ)*H)≠0 ∧ Y 0 ((n:ℝ)*H)=(n:ℝ)*d) ∧
      (-(∫ t in (0:ℝ)..(n:ℝ)*(2*H), K 0 t ^ 5)/3=0 ∧
        -(∫ t in (0:ℝ)..((n:ℝ)*(2*H)+H), K 0 t ^ 5)/3=C) := by
  obtain ⟨H,hH,pos,anti,u0,w0,_,_⟩ := positive_half_period
  have ku : K 0 = U := rfl
  have vw : V 0 = w := rfl
  have cU := continuous_iff_continuousAt.mpr (fun t => (CentreOscillator.dU t).continuousAt)
  have cw := continuous_iff_continuousAt.mpr (fun t => (CentreOscillator.dw t).continuousAt)
  let f := fun t => U t^2/2
  have cf : Continuous f := (cU.pow 2).div_const 2
  have Yeq (t : ℝ) : Y 0 t = ∫ x in (0:ℝ)..t, f x := by
    change (∫ x in (0:ℝ)..t, ty 0 x) = _
    exact intervalIntegral.integral_congr (fun x _ => (frozen_tangent x).2)
  have inc (s : ℝ) : Y 0 (s+H) = Y 0 s+Y 0 H := by
    have translate := intervalIntegral.integral_comp_add_right (f := f) (a := 0) (b := s) H
    rw [zero_add] at translate
    have equal : (∫ t in H..s+H, f t) = ∫ t in (0:ℝ)..s, f t := by
      rw [← translate]
      apply intervalIntegral.integral_congr
      intro x _
      simp [f,(anti x).1]
    have glue := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      (cf.intervalIntegrable 0 H) (cf.intervalIntegrable H (s+H))
    rw [Yeq,Yeq,Yeq,←glue,equal,add_comm]
  have dpos : 0<Y 0 H := by
    rw [Yeq]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (cf.intervalIntegrable ..)
      (fun t ht => div_pos (pow_pos (pos t ht) 2) (by norm_num)) hH
  have coords (n : ℕ) : U ((n:ℝ)*H)=0 ∧ w ((n:ℝ)*H)≠0 ∧ Y 0 ((n:ℝ)*H)=(n:ℝ)*Y 0 H := by
    induction n with
    | zero => simp [u0,w0,Yeq]
    | succ n ih =>
      rw [Nat.cast_succ,add_mul,one_mul,(anti _).1,(anti _).2,inc,ih.1,ih.2.2]
      exact ⟨neg_zero,neg_ne_zero.mpr ih.2.1,by ring⟩
  obtain ⟨cneg,parity⟩ := CrossingParity.horizontalRate_parity U w G hH cw
    CentreOscillator.dU CentreOscillator.dG u0 (fun s => (anti s).1) pos
  refine ⟨H,hH,Y 0 H,dpos,_,cneg,fun n => ⟨coords n,?_⟩⟩
  obtain ⟨e,o⟩ := parity n
  have uz : U ((n:ℝ)*(2*H))=0 := by
    convert! (coords (2*n)).1 using 2
    push_cast
    ring
  have uo : U ((n:ℝ)*(2*H)+H)=0 := by rw [(anti _).1,uz,neg_zero]
  rw [CrossingParity.integral_horizontalRate_of_zeros U w G cw CentreOscillator.dU
    CentreOscillator.dG u0 uz] at e
  rw [CrossingParity.integral_horizontalRate_of_zeros U w G cw CentreOscillator.dU
    CentreOscillator.dG u0 uo] at o
  exact ⟨e,o⟩

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.oscillator_window_data
