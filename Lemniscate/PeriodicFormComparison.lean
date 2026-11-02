import Lemniscate.PeriodicNeutralInputComparison

/-! Compare symmetric forms by moving derivatives onto the finite-rank
errors. This avoids a maximal-domain or operator-norm comparison theorem. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

private theorem raw_form_difference_bound
    (A Astar : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (hgreen : ∀ f g : circleH4Domain T, inner ℂ (A f) (g:CircleL2 T) = inner ℂ (f:CircleL2 T) (Astar g))
    (hA : ∀ f, ‖A f‖ ≤ 200*circleAngularH4Norm T f)
    (hAstar : ∀ f, ‖Astar f‖ ≤ 200*circleAngularH4Norm T f)
    (L LN R RN : circleH4Domain T) (ε F G : ℝ)
    (hε : 0 ≤ ε) (hF : 0 ≤ F)
    (hL : circleAngularH4Norm T (L-LN) ≤ 5000*ε*F)
    (hR : circleAngularH4Norm T (R-RN) ≤ 5000*ε*G)
    (hLN : ‖LN‖ ≤ 2*F) (hR0 : ‖R‖ ≤ 2*G) :
    ‖inner ℂ (L:CircleL2 T) (A R)-inner ℂ (LN:CircleL2 T) (A RN)‖ ≤ 4000000*ε*F*G := by
  have hid : inner ℂ (L:CircleL2 T) (A R)-inner ℂ (LN:CircleL2 T) (A RN) =
      inner ℂ ((L-LN:circleH4Domain T):CircleL2 T) (A R)+
        inner ℂ (LN:CircleL2 T) (A (R-RN)) := by
    simp only [Submodule.coe_sub,inner_sub_left,map_sub,inner_sub_right]
    ring
  have hmove : inner ℂ ((L-LN:circleH4Domain T):CircleL2 T) (A R) =
      inner ℂ (Astar (L-LN)) (R:CircleL2 T) := by
    have h := congrArg conj (hgreen R (L-LN))
    simpa only [inner_conj_symm] using h
  have hAe := (hA (R-RN)).trans (mul_le_mul_of_nonneg_left hR (by norm_num : (0:ℝ) ≤ 200))
  have hAse := (hAstar (L-LN)).trans (mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ) ≤ 200))
  rw [hid,hmove]
  have h1 := (norm_inner_le_norm (𝕜 := ℂ) (Astar (L-LN)) (R:CircleL2 T)).trans
    (mul_le_mul hAse hR0 (norm_nonneg _) (by positivity : 0 ≤ 200*(5000*ε*F)))
  have h2 := (norm_inner_le_norm (𝕜 := ℂ) (LN:CircleL2 T) (A (R-RN))).trans
    (mul_le_mul hLN hAe (norm_nonneg _) (by positivity : 0 ≤ 2*F))
  have ht := norm_add_le (inner ℂ (Astar (L-LN)) (R:CircleL2 T))
    (inner ℂ (LN:CircleL2 T) (A (R-RN)))
  nlinarith only [ht,h1,h2]

theorem circle_transformed_symmetric_form_difference_bound
    (A Astar : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (hgreen : ∀ f g : circleH4Domain T, inner ℂ (A f) (g:CircleL2 T) = inner ℂ (f:CircleL2 T) (Astar g))
    (hA : ∀ f, ‖A f‖ ≤ 200*circleAngularH4Norm T f)
    (hAstar : ∀ f, ‖Astar f‖ ≤ 200*circleAngularH4Norm T f)
    (L LN R RN : circleH4Domain T → circleH4Domain T) (ε : ℝ) (hε : 0 ≤ ε)
    (hL : ∀ f, circleAngularH4Norm T (L f-LN f) ≤ 5000*ε*‖f‖)
    (hR : ∀ f, circleAngularH4Norm T (R f-RN f) ≤ 5000*ε*‖f‖)
    (hLN : ∀ f, ‖LN f‖ ≤ 2*‖f‖) (hR0 : ∀ f, ‖R f‖ ≤ 2*‖f‖)
    (f g : circleH4Domain T) :
    ‖(1/2:ℂ)*(inner ℂ (L f:CircleL2 T) (A (R g))+inner ℂ (A (R f)) (L g:CircleL2 T))-
      (1/2:ℂ)*(inner ℂ (LN f:CircleL2 T) (A (RN g))+inner ℂ (A (RN f)) (LN g:CircleL2 T))‖
        ≤ 4000000*ε*‖f‖*‖g‖ := by
  have hfg := raw_form_difference_bound T A Astar hgreen hA hAstar
    (L f) (LN f) (R g) (RN g) ε ‖f‖ ‖g‖ hε (norm_nonneg f)
    (hL f) (hR g) (hLN f) (hR0 g)
  have hgf := raw_form_difference_bound T A Astar hgreen hA hAstar
    (L g) (LN g) (R f) (RN f) ε ‖g‖ ‖f‖ hε (norm_nonneg g)
    (hL g) (hR f) (hLN g) (hR0 f)
  have hid : (1/2:ℂ)*(inner ℂ (L f:CircleL2 T) (A (R g))+inner ℂ (A (R f)) (L g:CircleL2 T))-
      (1/2:ℂ)*(inner ℂ (LN f:CircleL2 T) (A (RN g))+inner ℂ (A (RN f)) (LN g:CircleL2 T)) =
      (1/2:ℂ)*((inner ℂ (L f:CircleL2 T) (A (R g))-inner ℂ (LN f:CircleL2 T) (A (RN g)))+
        conj (inner ℂ (L g:CircleL2 T) (A (R f))-inner ℂ (LN g:CircleL2 T) (A (RN f)))) := by
    simp only [map_sub,inner_conj_symm]
    ring
  rw [hid,norm_mul]
  have ht := norm_add_le
    (inner ℂ (L f:CircleL2 T) (A (R g))-inner ℂ (LN f:CircleL2 T) (A (RN g)))
    (conj (inner ℂ (L g:CircleL2 T) (A (R f))-inner ℂ (LN g:CircleL2 T) (A (RN f))))
  simp only [norm_conj] at ht
  norm_num only [norm_div,norm_one,Complex.norm_ofNat] 
  nlinarith only [ht,hfg,hgf]

end Lemniscate
