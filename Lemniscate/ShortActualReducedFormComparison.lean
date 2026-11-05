import Lemniscate.ShortCircleForms
import Lemniscate.ShortEvenFunctions
import Lemniscate.ShortSobolevProjection
import Lemniscate.ShortAdjointEstimate

/-! The actual fixed neutral projection is orthogonal in V.  Consequently
the component errors give one bound for all five reduced Bernstein forms. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
variable (T : ℝ) [Fact (0 < T)]

private theorem short_norm_four (a b c d : ℂ) :
    ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
  linarith only [norm_add_le a b,norm_add_le (a+b) c,norm_add_le (a+b+c) d]

theorem short_reduced_bernstein_difference
    (H H₇ : Fin 5 → circleH4Domain T → circleH4Domain T → ℂ)
    (hH : ∀ (k : Fin 4) (f g : circleH4Domain T),
      f ∈ shortEvenDomain T → g ∈ shortEvenDomain T →
      ‖H k.castSucc f g-H₇ k.castSucc f g‖ ≤
        shortAdjointComponentError k*shortVNorm T f*shortVNorm T g)
    (j : Fin 5) (f : circleH4Domain T) (hf : f ∈ shortEvenDomain T) :
    ‖circleShiftedBernsteinPairing T H j f f-circleShiftedBernsteinPairing T H₇ j f f‖ ≤
      (9801/1280000:ℝ)*shortVNorm T f^2 := by
  let u := circleFixedProjectionH4 T f
  let v := f-u
  let D (k : Fin 5) (x y : circleH4Domain T) := H k x y-H₇ k x y
  let S₀ := D 0 v v+D 1 u v+D 1 v u+D 2 u u
  let S₁ := D 1 v v+D 2 u v+D 2 v u
  let S₂ := D 2 v v+D 3 u v+D 3 v u
  let S₃ := D 3 v v
  let δ (k : Fin 4) := shortAdjointComponentError k
  let N := shortVNorm T f^2
  have hu : u ∈ shortEvenDomain T :=
    (shortEvenDomain T).smul_mem _ (short_neutral_vectors_mem_even T).2.2
  have hv : v ∈ shortEvenDomain T := (shortEvenDomain T).sub_mem hf hu
  have hsplit : shortVNorm T u^2+shortVNorm T v^2 = N :=
    (short_anchor_projection_decomposition T f).2.2.1.symm
  have hcross : 2*shortVNorm T u*shortVNorm T v ≤ N := by
    nlinarith only [hsplit,sq_nonneg (shortVNorm T u-shortVNorm T v)]
  have hu2 : shortVNorm T u^2 ≤ N := by
    nlinarith only [hsplit,sq_nonneg (shortVNorm T v)]
  have hv2 : shortVNorm T v^2 ≤ N := by
    nlinarith only [hsplit,sq_nonneg (shortVNorm T u)]
  have hδ (k : Fin 4) : 0 ≤ δ k := by
    fin_cases k <;> norm_num [δ,shortAdjointComponentError,shortKernelError,shortAdjointError]
  have hD (k : Fin 4) (x y : circleH4Domain T)
      (hx : x ∈ shortEvenDomain T) (hy : y ∈ shortEvenDomain T) :
      ‖D k.castSucc x y‖ ≤ δ k*shortVNorm T x*shortVNorm T y := hH k x y hx hy
  have hD0 (x y : circleH4Domain T) (hx : x ∈ shortEvenDomain T) (hy : y ∈ shortEvenDomain T) :
      ‖D 0 x y‖ ≤ δ 0*shortVNorm T x*shortVNorm T y := hD 0 x y hx hy
  have hD1 (x y : circleH4Domain T) (hx : x ∈ shortEvenDomain T) (hy : y ∈ shortEvenDomain T) :
      ‖D 1 x y‖ ≤ δ 1*shortVNorm T x*shortVNorm T y := hD 1 x y hx hy
  have hD2 (x y : circleH4Domain T) (hx : x ∈ shortEvenDomain T) (hy : y ∈ shortEvenDomain T) :
      ‖D 2 x y‖ ≤ δ 2*shortVNorm T x*shortVNorm T y := hD 2 x y hx hy
  have hD3 (x y : circleH4Domain T) (hx : x ∈ shortEvenDomain T) (hy : y ∈ shortEvenDomain T) :
      ‖D 3 x y‖ ≤ δ 3*shortVNorm T x*shortVNorm T y := hD 3 x y hx hy
  have h₀ : ‖S₀‖ ≤ (δ 0+δ 1+δ 2)*N := by
    dsimp only [S₀]
    have hnorm := short_norm_four (D 0 v v) (D 1 u v) (D 1 v u) (D 2 u u)
    have hm0 := mul_le_mul_of_nonneg_left hv2 (hδ 0)
    have hm1 := mul_le_mul_of_nonneg_left hcross (hδ 1)
    have hm2 := mul_le_mul_of_nonneg_left hu2 (hδ 2)
    nlinarith only [hnorm,hD0 v v hv hv,hD1 u v hu hv,hD1 v u hv hu,
      hD2 u u hu hu,hm0,hm1,hm2]
  have h₁ : ‖S₁‖ ≤ (δ 1+δ 2)*N := by
    dsimp only [S₁]
    have hnorm := (norm_add_le (D 1 v v+D 2 u v) (D 2 v u)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    have hm1 := mul_le_mul_of_nonneg_left hv2 (hδ 1)
    have hm2 := mul_le_mul_of_nonneg_left hcross (hδ 2)
    nlinarith only [hnorm,hD1 v v hv hv,hD2 u v hu hv,hD2 v u hv hu,hm1,hm2]
  have h₂ : ‖S₂‖ ≤ (δ 2+δ 3)*N := by
    dsimp only [S₂]
    have hnorm := (norm_add_le (D 2 v v+D 3 u v) (D 3 v u)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    have hm2 := mul_le_mul_of_nonneg_left hv2 (hδ 2)
    have hm3 := mul_le_mul_of_nonneg_left hcross (hδ 3)
    nlinarith only [hnorm,hD2 v v hv hv,hD3 u v hu hv,hD3 v u hv hu,hm2,hm3]
  have h₃ : ‖S₃‖ ≤ δ 3*N := by
    dsimp only [S₃]
    have hm := mul_le_mul_of_nonneg_left hv2 (hδ 3)
    nlinarith only [hD3 v v hv hv,hm]
  have hid : circleShiftedBernsteinPairing T H j f f-
      circleShiftedBernsteinPairing T H₇ j f f =
      S₀+(shortBernsteinPower j 1:ℂ)*S₁+
        (shortBernsteinPower j 2:ℂ)*S₂+(shortBernsteinPower j 3:ℂ)*S₃ := by
    fin_cases j <;>
      norm_num [circleShiftedBernsteinPairing,circleReducedShiftedCoefficient,
        shortBernsteinWeight,shortBernsteinPower,Fin.sum_univ_succ,Nat.choose,
        S₀,S₁,S₂,S₃,D,u,v] <;> ring
  have hw := short_bernstein_power_bounds j
  have hp1 : ‖(shortBernsteinPower j 1:ℂ)*S₁‖ ≤ (1/2:ℝ)*(δ 1+δ 2)*N := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.1]
    nlinarith only [mul_le_mul hw.2.1 h₁ (norm_nonneg S₁) (by norm_num : (0:ℝ) ≤ 1/2)]
  have hp2 : ‖(shortBernsteinPower j 2:ℂ)*S₂‖ ≤ (1/4:ℝ)*(δ 2+δ 3)*N := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.2.2.1]
    nlinarith only [mul_le_mul hw.2.2.2.1 h₂ (norm_nonneg S₂) (by norm_num : (0:ℝ) ≤ 1/4)]
  have hp3 : ‖(shortBernsteinPower j 3:ℂ)*S₃‖ ≤ (1/8:ℝ)*δ 3*N := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.2.2.2.2.1]
    nlinarith only [mul_le_mul hw.2.2.2.2.2 h₃ (norm_nonneg S₃) (by norm_num : (0:ℝ) ≤ 1/8)]
  rw [hid]
  have ht := short_norm_four S₀ ((shortBernsteinPower j 1:ℂ)*S₁)
    ((shortBernsteinPower j 2:ℂ)*S₂) ((shortBernsteinPower j 3:ℂ)*S₃)
  have hc : δ 0+(3/2:ℝ)*δ 1+(7/4:ℝ)*δ 2+(3/8:ℝ)*δ 3 = 9801/1280000 :=
    short_adjoint_bernstein_common_bound
  nlinarith only [ht,h₀,hp1,hp2,hp3,congrArg (fun x : ℝ => x*N) hc]

end Lemniscate
