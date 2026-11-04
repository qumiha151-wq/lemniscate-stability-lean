import Lemniscate.PeriodicCenteredEvenEnergy
import Lemniscate.PeriodicFrequencyProjection
import Lemniscate.PeriodicFrequencyOperator

/-! Full-space energy for the actual centered Bloch operator. The decomposition
is by parity of Fourier indices. The neutral and Householder maps fix the odd
Fourier block, and the actual Bloch operator preserves the two blocks.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private theorem circle_even_frequency_part_eq_projection (f : CircleL2 T) :
    circleEvenFrequencyPart T f = circleEvenProjection T f := by
  apply circle_fourier_ext T
  intro n
  rw [circle_even_frequency_part_fourier,circle_even_projection_fourier]
  by_cases hn : Odd n
  · rw [if_pos hn,if_neg (Int.not_even_iff_odd.mpr hn),zero_mul]
  · rw [if_neg hn,if_pos (Int.not_odd_iff_even.mp hn),one_mul]

private theorem circle_bloch_even_frequency_part (h h₁ h₂ : C(AddCircle T, ℂ))
    (ho : ∀ n : ℤ, Odd n → fourierCoeff h n = 0)
    (ho₁ : ∀ n : ℤ, Odd n → fourierCoeff h₁ n = 0)
    (ho₂ : ∀ n : ℤ, Odd n → fourierCoeff h₂ n = 0)
    (α : ℝ) (f : circleH4Domain T) :
    circleBlochOperator T h h₁ h₂ α (circleEvenFrequencyPartH4 T f) =
      circleEvenFrequencyPart T (circleBlochOperator T h h₁ h₂ α f) := by
  have hdom : circleEvenFrequencyPartH4 T f = circleEvenProjectionH4 T f := by
    apply Subtype.ext
    exact circle_even_frequency_part_eq_projection T (f:CircleL2 T)
  rw [hdom,circle_even_projection_bloch T h h₁ h₂ ho ho₁ ho₂]
  exact (circle_even_frequency_part_eq_projection T _).symm

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_centered_full_bloch_energy (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T))
    (α : ℝ) (hα0 : 0 ≤ α) (hαhalf : α ≤ 1/2) (f : circleH4Domain T) :
    (inner ℂ (f:CircleL2 T)
      (circleCenteredBlochOperator T q p hq hp (ψ:CircleL2 T) α f)).re ≤
        -(α^2/2)*‖(f:CircleL2 T)‖^2 := by
  let e := circleUnitRotationH4 T q p hq hp
  let U := circleRotationHouseholder T q p
  let U₄ := circleRotationHouseholderH4 T q p hq hp
  let A := circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α
  let B := circleCenteredBlochOperator T q p hq hp (ψ:CircleL2 T) α
  have heEven (n : ℤ) : fourierCoeff (e:CircleL2 T) (2*n+1) = 0 :=
    circle_unit_rotation_no_odd T q p hq ho n
  have hψEven : ∀ n : ℤ, fourierCoeff (ψ:CircleL2 T) (2*n+1) = 0 :=
    (paper_single_period_adjoint_vector_sector T q p hq hp he hqreal hpreal hs hc ho hr
      ψ hnorm hzero).2
  have hUodd (g : CircleL2 T) (hg : InCircleOddSector T g) : U g = g := by
    have hv (n : ℤ) : fourierCoeff
        ((-I) • circleUnitRotation T q p+circleHouseholderAnchor T) (2*n+1) = 0 := by
      rw [circle_fourierCoeff_add,circle_fourierCoeff_smul,
        circle_unit_rotation_no_odd T q p hq ho,circle_householder_anchor_no_odd]
      ring
    have hz := circle_frequency_sectors_orthogonal T _ g hv hg
    simp only [U,circleRotationHouseholder,neutral_householder_apply,hz,
      mul_zero,zero_smul,sub_zero]
  have hTodd (g : CircleL2 T) (hg : InCircleOddSector T g) :
      neutralTransform e (ψ:CircleL2 T) g = g := by
    have hψg := circle_frequency_sectors_orthogonal T (ψ:CircleL2 T) g hψEven hg
    have heg := circle_frequency_sectors_orthogonal T (e:CircleL2 T) g heEven hg
    simp only [neutral_transform_apply,inner_sub_left,hψg,heg,sub_self,zero_smul,add_zero]
  have hTinvOdd (g : CircleL2 T) (hg : InCircleOddSector T g) :
      neutralTransformInv e (ψ:CircleL2 T) g = g := by
    have hψg := circle_frequency_sectors_orthogonal T (ψ:CircleL2 T) g hψEven hg
    have heg := circle_frequency_sectors_orthogonal T (e:CircleL2 T) g heEven hg
    simp only [neutral_transform_inv_apply,inner_sub_left,hψg,heg,sub_self,zero_smul,sub_zero]
  have hU₄odd (g : circleH4Domain T) (hg : InCircleOddSector T (g:CircleL2 T)) :
      U₄ g = g := by
    apply Subtype.ext
    rw [circle_rotation_householder_h4_coe,hUodd _ hg]
  have hTinv₄odd (g : circleH4Domain T) (hg : InCircleOddSector T (g:CircleL2 T)) :
      neutralTransformInvDomain e (ψ:CircleL2 T) g = g := by
    apply Subtype.ext
    rw [neutral_transform_inv_domain_coe,hTinvOdd _ hg]
  have hd₀ := circle_profile_square_deriv T q p hq
  have hd₁ := circle_profile_square_second T q p hq hp he
  have ho₀ (n : ℤ) (hn : Odd n) : fourierCoeff (q^2 : C(AddCircle T, ℂ)) n = 0 := by
    obtain ⟨k,hk⟩ := (odd_frequency_range n).mpr hn
    rw [← hk,ho]
  have ho₁ (n : ℤ) (hn : Odd n) :
      fourierCoeff ((2:ℂ) • (q*p) : C(AddCircle T, ℂ)) n = 0 := by
    rw [fourierCoeff_classical_deriv T _ _ hd₀,ho₀ n hn,mul_zero]
  have ho₂ (n : ℤ) (hn : Odd n) :
      fourierCoeff (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) n = 0 := by
    rw [fourierCoeff_classical_deriv T _ _ hd₁,ho₁ n hn,mul_zero]
  have hAcomm (g : circleH4Domain T) :
      A (circleEvenFrequencyPartH4 T g) = circleEvenFrequencyPart T (A g) :=
    circle_bloch_even_frequency_part T _ _ _ ho₀ ho₁ ho₂ α g
  have hAeven (g : circleH4Domain T)
      (hg : ∀ n : ℤ, fourierCoeff (g:CircleL2 T) (2*n+1) = 0) :
      ∀ n : ℤ, fourierCoeff (A g) (2*n+1) = 0 := by
    have hgin : circleEvenFrequencyPartH4 T g = g :=
      Subtype.ext (circle_even_frequency_part_eq_self T _ hg)
    have hout := hAcomm g
    rw [hgin] at hout
    intro n
    rw [hout]
    exact circle_even_frequency_part_sector T (A g) n
  have hAodd (g : circleH4Domain T) (hg : InCircleOddSector T (g:CircleL2 T)) :
      InCircleOddSector T (A g) := by
    have hgin : circleEvenFrequencyPartH4 T g = 0 := by
      apply Subtype.ext
      apply circle_fourier_ext T
      intro n
      change fourierCoeff (circleEvenFrequencyPart T (g:CircleL2 T)) n =
        fourierCoeff (0:CircleL2 T) n
      rw [circle_even_frequency_part_fourier,circle_fourierCoeff_zero]
      by_cases hn : Odd n
      · rw [if_pos hn]
      · rw [if_neg hn,hg n hn]
    have hout : circleEvenFrequencyPart T (A g) = 0 := by
      rw [← hAcomm g,hgin,map_zero]
    intro n hn
    have h := congrArg (fun z : CircleL2 T => fourierCoeff z n) hout
    simpa only [circle_even_frequency_part_fourier,if_neg hn,circle_fourierCoeff_zero] using h
  have hBodd (g : circleH4Domain T) (hg : InCircleOddSector T (g:CircleL2 T)) :
      B g = A g := by
    change U (neutralTransform e (ψ:CircleL2 T)
      (A (neutralTransformInvDomain e (ψ:CircleL2 T) (U₄ g)))) = A g
    rw [hU₄odd g hg,hTinv₄odd g hg,hTodd (A g) (hAodd g hg),hUodd (A g) (hAodd g hg)]
  have hBeven (g : circleH4Domain T)
      (hg : ∀ n : ℤ, fourierCoeff (g:CircleL2 T) (2*n+1) = 0) :
      ∀ n : ℤ, fourierCoeff (B g) (2*n+1) = 0 := by
    let u := U₄ g
    let v := neutralTransformInvDomain e (ψ:CircleL2 T) u
    have hu (n : ℤ) : fourierCoeff (u:CircleL2 T) (2*n+1) = 0 := by
      rw [circle_rotation_householder_h4_coe]
      exact circle_rotation_householder_no_odd T q p hq ho _ hg n
    have hv (n : ℤ) : fourierCoeff (v:CircleL2 T) (2*n+1) = 0 := by
      change fourierCoeff ((u:CircleL2 T)-
        inner ℂ ((ψ:CircleL2 T)-(e:CircleL2 T)) (u:CircleL2 T) • (e:CircleL2 T)) (2*n+1) = 0
      rw [circle_fourierCoeff_sub,circle_fourierCoeff_smul,hu,heEven]
      ring
    have hAv := hAeven v hv
    have hTAv (n : ℤ) :
        fourierCoeff (neutralTransform e (ψ:CircleL2 T) (A v)) (2*n+1) = 0 := by
      rw [neutral_transform_apply,circle_fourierCoeff_add,circle_fourierCoeff_smul,hAv,heEven]
      ring
    exact circle_rotation_householder_no_odd T q p hq ho _ hTAv
  have hBadd (g k : circleH4Domain T) : B (g+k) = B g+B k := by
    simp only [B,circle_centered_bloch_polynomial,
      ← circle_centered_coefficient_linear_apply,map_add]
    module
  let x := circleEvenFrequencyPartH4 T f
  let y := circleOddFrequencyPartH4 T f
  have hx : ∀ n : ℤ, fourierCoeff (x:CircleL2 T) (2*n+1) = 0 :=
    circle_even_frequency_part_sector T (f:CircleL2 T)
  have hy : InCircleOddSector T (y:CircleL2 T) := circle_odd_frequency_part_sector T (f:CircleL2 T)
  have hBy : InCircleOddSector T (B y) := by rw [hBodd y hy]; exact hAodd y hy
  have hxy : inner ℂ (x:CircleL2 T) (B y) = 0 :=
    circle_frequency_sectors_orthogonal T _ _ hx hBy
  have hyx : inner ℂ (y:CircleL2 T) (B x) = 0 := by
    have h := circle_frequency_sectors_orthogonal T _ _ (hBeven x hx) hy
    rw [← inner_conj_symm,h,map_zero]
  have hsplit : inner ℂ (f:CircleL2 T) (B f) =
      inner ℂ (x:CircleL2 T) (B x)+inner ℂ (y:CircleL2 T) (B y) := by
    have hsum : x+y = f := circle_frequency_h4_parts_sum T f
    have h := congrArg (fun z : circleH4Domain T => inner ℂ (z:CircleL2 T) (B z)) hsum
    simpa only [Submodule.coe_add,hBadd,inner_add_left,inner_add_right,
      hxy,hyx,zero_add,add_zero] using h.symm
  have heven := paper_centered_even_energy T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hnorm hzero hd α hα0 hαhalf x (fun n hn => by
      obtain ⟨k,hk⟩ := (odd_frequency_range n).mpr hn
      rw [← hk,hx])
  have hαsq : 0 ≤ 1-α^2 := by
    have h := (sq_le_sq₀ hα0 (by norm_num : (0:ℝ) ≤ 1/2)).mpr hαhalf
    norm_num at h
    linarith only [h]
  have hscale : α^2*‖(x:CircleL2 T)‖^2 ≤
      α^2*‖circleFixedProjectionH4 T x‖^2+‖x-circleFixedProjectionH4 T x‖^2 := by
    change α^2*‖x‖^2 ≤
      α^2*‖circleFixedProjectionH4 T x‖^2+‖x-circleFixedProjectionH4 T x‖^2
    have hnormx := circle_fixed_projection_l2_norm_split T x
    have hrem := mul_nonneg hαsq (sq_nonneg ‖x-circleFixedProjectionH4 T x‖)
    linear_combination -(α^2)*hnormx+hrem
  have heven' : (inner ℂ (x:CircleL2 T) (B x)).re ≤ -(α^2/2)*‖(x:CircleL2 T)‖^2 := by
    nlinarith only [heven,hscale]
  have hodd : (inner ℂ (y:CircleL2 T) (B y)).re ≤ -‖(y:CircleL2 T)‖^2 := by
    rw [hBodd y hy]
    exact paper_h4_bloch_odd_dissipative T q p hq hp he hs hc hr α hα0 hαhalf y hy
  have hodd' : (inner ℂ (y:CircleL2 T) (B y)).re ≤ -(α^2/2)*‖(y:CircleL2 T)‖^2 := by
    have hrem : 0 ≤ (1-α^2/2)*‖(y:CircleL2 T)‖^2 :=
      mul_nonneg (by nlinarith only [hαsq]) (sq_nonneg _)
    linear_combination hodd+hrem
  have hnormf : ‖(f:CircleL2 T)‖^2 = ‖(x:CircleL2 T)‖^2+‖(y:CircleL2 T)‖^2 :=
    circle_frequency_parts_norm_sq T (f:CircleL2 T)
  change (inner ℂ (f:CircleL2 T) (B f)).re ≤ _
  rw [hsplit,Complex.add_re]
  calc
    (inner ℂ (x:CircleL2 T) (B x)).re+(inner ℂ (y:CircleL2 T) (B y)).re ≤
        -(α^2/2)*‖(x:CircleL2 T)‖^2-(α^2/2)*‖(y:CircleL2 T)‖^2 :=
      by simpa only [sub_eq_add_neg,neg_mul] using add_le_add heven' hodd'
    _ = -(α^2/2)*‖(f:CircleL2 T)‖^2 := by rw [hnormf]; ring


end Profile
end Lemniscate
