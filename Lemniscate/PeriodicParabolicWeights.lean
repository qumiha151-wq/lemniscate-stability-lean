import Lemniscate.LinearParabolicEnergy
import Mathlib.Tactic.LinearCombination

/-! Fourier Sobolev weights in the finite parabolic energy estimate.

The constants are uniform in the frequencies, the number of modes, and
the positive physical time scale tau. No scalar ODE is reconstructed here.
-/
namespace Lemniscate
open MeasureTheory
open scoped BigOperators

private theorem parabolic_mode_weights (x : ℝ) (hx : 0 ≤ x) :
    let a := 1+4*x^4
    let W2 := 1+x^2+x^4
    let W4 := 1+x^2+x^4+x^6+x^8
    W2 ≤ 2*a ∧ a ≤ 4*W2 ∧ W4 ≤ 5*a^2 := by
  dsimp only
  have h2 : 0 ≤ x^2 := sq_nonneg x
  have h4 : 0 ≤ x^4 := pow_nonneg hx 4
  have h8 : 0 ≤ x^8 := pow_nonneg hx 8
  have h3 : (0:ℝ) ≤ 3 := by norm_num
  refine ⟨?_,?_,?_⟩
  · linear_combination (sq_nonneg (x^2-1))+6*h4+h2
  · linear_combination 4*h2+h3
  · linear_combination (sq_nonneg (x^2-1))+
      (1/2:ℝ)*(sq_nonneg (x^4-x^2))+h2+(75/2:ℝ)*h4+(157/2:ℝ)*h8+h3

set_option maxHeartbeats 800000 in
/-- The finite-mode energy controls the H2 trace, the time H4 norm and
the physical velocity, with the normalized-time derivative `u' = tau v`.
The same bound holds at every time between zero and the terminal time. -/
theorem finite_mode_parabolic_sobolev_energy {ι : Type*} [Fintype ι]
    (u v : ι → ℝ → ℂ) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (τ t : ℝ) (hτ : 0 < τ) (ht : 0 ≤ t)
    (hd : ∀ i r, HasDerivAt (u i) (τ • v i r) r)
    (hv : ∀ i, Continuous (v i)) :
    let a : ι → ℝ := fun i => 1+4*(x i)^4
    let W2 : ι → ℝ := fun i => 1+(x i)^2+(x i)^4
    let W4 : ι → ℝ := fun i => 1+(x i)^2+(x i)^4+(x i)^6+(x i)^8
    ∀ s ∈ Set.Icc (0:ℝ) t,
      τ*(∫ r in (0:ℝ)..t, ∑ i, (‖v i r‖^2+W4 i*‖u i r‖^2))+
          (∑ i, W2 i*‖u i s‖^2) ≤
        40*(τ*(∫ r in (0:ℝ)..t, ∑ i, ‖v i r+a i • u i r‖^2)+
          (∑ i, W2 i*‖u i 0‖^2)) := by
  dsimp only
  let a : ι → ℝ := fun i => 1+4*(x i)^4
  let W2 : ι → ℝ := fun i => 1+(x i)^2+(x i)^4
  let W4 : ι → ℝ := fun i => 1+(x i)^2+(x i)^4+(x i)^6+(x i)^8
  let D : ℝ → ℝ := fun r => ∑ i, (‖v i r‖^2+(a i)^2*‖u i r‖^2)
  let DW : ℝ → ℝ := fun r => ∑ i, (‖v i r‖^2+W4 i*‖u i r‖^2)
  let F : ℝ → ℝ := fun r => ∑ i, ‖v i r+a i • u i r‖^2
  let E : ℝ → ℝ := fun r => ∑ i, a i*‖u i r‖^2
  let EW : ℝ → ℝ := fun r => ∑ i, W2 i*‖u i r‖^2
  let vτ : ι → ℝ → ℂ := fun i r => τ • v i r
  let aτ : ι → ℝ := fun i => τ*a i
  have ha : ∀ i, 0 < a i := by intro i; dsimp only [a]; positivity
  have haτ : ∀ i, 0 < aτ i := fun i => mul_pos hτ (ha i)
  have hvτ : ∀ i, Continuous (vτ i) := fun i => (hv i).const_smul τ
  have hu : ∀ i, Continuous (u i) := fun i =>
    continuous_iff_continuousAt.mpr fun r => (hd i r).continuousAt
  have hDc : Continuous D := continuous_finsetSum _ (fun i _ =>
    ((hv i).norm.pow 2).add (continuous_const.mul ((hu i).norm.pow 2)))
  have hDWc : Continuous DW := continuous_finsetSum _ (fun i _ =>
    ((hv i).norm.pow 2).add (continuous_const.mul ((hu i).norm.pow 2)))
  have hscaleD (r : ℝ) :
      (∑ i, (‖vτ i r‖^2+(aτ i)^2*‖u i r‖^2)) = τ^2*D r := by
    simp only [vτ,aτ,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,D,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hscaleF (r : ℝ) :
      (∑ i, ‖vτ i r+aτ i • u i r‖^2) = τ^2*F r := by
    calc
      (∑ i, ‖vτ i r+aτ i • u i r‖^2) =
          ∑ i, ‖τ • (v i r+a i • u i r)‖^2 := by
        simp only [vτ,aτ,smul_add,smul_smul]
      _ = τ^2*F r := by
        simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,F,Finset.mul_sum]
  have hscaleE (r : ℝ) : (∑ i, aτ i*‖u i r‖^2) = τ*E r := by
    simp only [aτ,E,Finset.mul_sum,mul_assoc]
  have hstandard (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) t) :
      τ*(∫ r in (0:ℝ)..t, D r)+E s ≤
        2*(τ*(∫ r in (0:ℝ)..t, F r)+E 0) := by
    have h := (finite_mode_parabolic_energy u vτ aτ t ht haτ hd hvτ).2 s hs
    change (∫ r in (0:ℝ)..t, ∑ i, (‖vτ i r‖^2+(aτ i)^2*‖u i r‖^2))+
        (∑ i, aτ i*‖u i s‖^2) ≤
      2*((∫ r in (0:ℝ)..t, ∑ i, ‖vτ i r+aτ i • u i r‖^2)+
        (∑ i, aτ i*‖u i 0‖^2)) at h
    simp_rw [hscaleD,hscaleF,hscaleE] at h
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at h
    have hcancel : τ*(τ*(∫ r in (0:ℝ)..t, D r)+E s) ≤
        τ*(2*(τ*(∫ r in (0:ℝ)..t, F r)+E 0)) := by
      convert h using 1 <;> ring
    exact le_of_mul_le_mul_left hcancel hτ
  have hweights (i : ι) : W2 i ≤ 2*a i ∧ a i ≤ 4*W2 i ∧ W4 i ≤ 5*(a i)^2 :=
    parabolic_mode_weights (x i) (hx i)
  have hDW (r : ℝ) : DW r ≤ 5*D r := by
    have hpoint (i : ι) : ‖v i r‖^2+W4 i*‖u i r‖^2 ≤
        5*(‖v i r‖^2+(a i)^2*‖u i r‖^2) := by
      have h := mul_le_mul_of_nonneg_right (hweights i).2.2 (sq_nonneg ‖u i r‖)
      linear_combination h+4*(sq_nonneg ‖v i r‖)
    simpa only [DW,D,Finset.mul_sum] using Finset.sum_le_sum (fun i _ => hpoint i)
  have hEbound (s : ℝ) : EW s ≤ 2*E s := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right (hweights i).1 (sq_nonneg ‖u i s‖))
    simpa only [EW,E,Finset.mul_sum,mul_assoc] using h
  have hEinitial : E 0 ≤ 4*EW 0 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right (hweights i).2.1 (sq_nonneg ‖u i 0‖))
    simpa only [EW,E,Finset.mul_sum,mul_assoc] using h
  have hEpos (s : ℝ) : 0 ≤ E s :=
    Finset.sum_nonneg fun i _ => mul_nonneg (ha i).le (sq_nonneg ‖u i s‖)
  have hDIntegral : (∫ r in (0:ℝ)..t, DW r) ≤ 5*(∫ r in (0:ℝ)..t, D r) := by
    have h := intervalIntegral.integral_mono (μ := (volume : Measure ℝ))
      ht (hDWc.intervalIntegrable 0 t)
      ((hDc.intervalIntegrable 0 t).const_mul 5) hDW
    simpa only [intervalIntegral.integral_const_mul] using h
  have hFpos : 0 ≤ τ*(∫ r in (0:ℝ)..t, F r) :=
    mul_nonneg hτ.le (intervalIntegral.integral_nonneg_of_forall ht
      (fun r => Finset.sum_nonneg fun i _ => sq_nonneg ‖v i r+a i • u i r‖))
  intro s hs
  change τ*(∫ r in (0:ℝ)..t, DW r)+EW s ≤
    40*(τ*(∫ r in (0:ℝ)..t, F r)+EW 0)
  calc
    τ*(∫ r in (0:ℝ)..t, DW r)+EW s ≤
        τ*(5*(∫ r in (0:ℝ)..t, D r))+2*E s :=
      add_le_add (mul_le_mul_of_nonneg_left hDIntegral hτ.le) (hEbound s)
    _ ≤ 5*(τ*(∫ r in (0:ℝ)..t, D r)+E s) := by
      linear_combination 3*(hEpos s)
    _ ≤ 5*(2*(τ*(∫ r in (0:ℝ)..t, F r)+E 0)) :=
      mul_le_mul_of_nonneg_left (hstandard s hs) (by norm_num)
    _ ≤ 40*(τ*(∫ r in (0:ℝ)..t, F r)+EW 0) := by
      linear_combination 10*hEinitial+30*hFpos

end Lemniscate
