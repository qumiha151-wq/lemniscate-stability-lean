import Lemniscate.ShortCircleForms
import Lemniscate.PeriodicBlochCoefficientFourier

/-! Identification of the newly defined real Fourier coefficients with the
actual periodic differential operator, for every pair of even frequencies. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic Finset
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem short_circle_even_fourier (h : C(AddCircle T, ℂ)) (d : ℕ → ℝ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n)=fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ))=(d j:ℂ)) (n : ℤ) :
    fourierCoeff h (2*n)=(d n.natAbs:ℂ) := by
  by_cases hn : 0 ≤ n
  · have he : (n.natAbs:ℤ)=n := by rw [Int.natCast_natAbs,abs_of_nonneg hn]
    simpa only [he] using hc n.natAbs
  · have he : (n.natAbs:ℤ)= -n := by rw [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge hn)]
    rw [show 2*n= -(2*(n.natAbs:ℤ)) by omega, hs,hc]

theorem short_circle_bloch_entry (h : C(AddCircle T, ℂ)) (d : ℕ → ℝ) (r : ℝ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n)=fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ))=(d j:ℂ))
    (hr : (2*Real.pi/T)^2=r) (j : Fin 5) (n m : ℤ) :
    circleBlochCoefficientEntry T h j (2*n) (2*m)=(shortBlochEntry r d j (2*n) (2*m):ℂ) := by
  have hcoef : fourierCoeff h (2*n-2*m)=(d (n-m).natAbs:ℂ) := by
    rw [← mul_sub]
    exact short_circle_even_fourier T h d hs hc (n-m)
  have hidx : (2*n-2*m).natAbs/2=(n-m).natAbs := by
    rw [← mul_sub,Int.natAbs_mul]
    norm_num
  by_cases hnm : n=m
  · subst m
    have hzero : fourierCoeff h 0=(d 0:ℂ) := by simpa using hc 0
    fin_cases j <;>
      simp [circleBlochCoefficientEntry,shortBlochEntry,hr,hzero] <;>
      push_cast <;> ring
  · have hne : (2:ℤ)*n≠2*m := by omega
    fin_cases j <;>
      simp [circleBlochCoefficientEntry,shortBlochEntry,hr,hcoef,hidx,hne] <;>
      push_cast <;> ring

theorem short_circle_bloch_basis_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (d : ℕ → ℝ) (r : ℝ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n)=fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ))=(d j:ℂ))
    (hr : (2*Real.pi/T)^2=r) (j : Fin 5) (n m : ℤ) :
    inner ℂ (fourierBasis (T:=T) (2*n))
      (circleBlochCoefficient T h h₁ h₂ j (circleFourierH4 T (2*m))) =
      (shortBlochEntry r d j (2*n) (2*m):ℂ) := by
  rw [circle_bloch_coefficient_basis_pairing T h h₁ h₂ hh hh₁]
  exact short_circle_bloch_entry T h d r hs hc hr j n m

noncomputable def circleShortHead : (Fin 15 → ℂ) →ₗ[ℂ] circleH4Domain T where
  toFun v := ∑ i : Fin 15, v i • circleFourierH4 T (shortHeadFrequency i)
  map_add' v w := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' z v := by simp [Finset.smul_sum,smul_smul]

theorem short_head_frequency_injective : Function.Injective shortHeadFrequency := by
  intro i j hij
  apply Fin.ext
  dsimp only [shortHeadFrequency] at hij
  omega

theorem circle_short_head_fourier (v : Fin 15 → ℂ) (n : ℤ) :
    fourierCoeff (circleShortHead T v:CircleL2 T) n =
      ∑ i : Fin 15, v i*(if n=shortHeadFrequency i then 1 else 0) := by
  rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  have hb := orthonormal_iff_ite.mp (fourierBasis (T:=T)).orthonormal
  simp only [circleShortHead,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,
    Submodule.coe_smul_of_tower,inner_sum,inner_smul_right,circleFourierH4,hb]

theorem circle_short_head_fourier_at (v : Fin 15 → ℂ) (i : Fin 15) :
    fourierCoeff (circleShortHead T v:CircleL2 T) (shortHeadFrequency i)=v i := by
  rw [circle_short_head_fourier]
  simp only [short_head_frequency_injective.eq_iff]
  simp

theorem circle_short_head_pairing (v : Fin 15 → ℂ) (f : CircleL2 T) :
    inner ℂ (circleShortHead T v:CircleL2 T) f =
      ∑ i : Fin 15, conj (v i)*fourierCoeff f (shortHeadFrequency i) := by
  simp only [circleShortHead,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,
    Submodule.coe_smul_of_tower,sum_inner,inner_smul_left,circleFourierH4]
  apply Finset.sum_congr rfl
  intro i _
  rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]

theorem circle_short_head_inner (v w : Fin 15 → ℂ) :
    inner ℂ (circleShortHead T v:CircleL2 T) (circleShortHead T w:CircleL2 T) =
      ∑ i : Fin 15, conj (v i)*w i := by
  rw [circle_short_head_pairing]
  simp only [circle_short_head_fourier_at]

end Lemniscate
