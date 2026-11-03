import Lemniscate.WeierstrassFourierRows
import Lemniscate.PeriodicFourierProducts
import Lemniscate.FourierSeries
import Lemniscate.FourierSeriesExtraction

/-! Transfer the actual Weierstrass expansion to Fourier modes on its arclength circle. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic

private def weierstrassCircleCoefficient (a : ℝ) (n : ℕ) : ℂ :=
  (evenCoefficient ((Real.pi*a)^2) (Real.exp (-Real.pi)) (n+1):ℂ)

private theorem weierstrass_circle_coefficients_summable (a : ℝ) :
    Summable (fun n : ℕ => ‖weierstrassCircleCoefficient a n‖) := by
  let q := Real.exp (-Real.pi)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos Real.pi_pos)
  have hqn : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hq0] using hq1
  have hm : Summable (fun n : ℕ => ((n+1:ℕ):ℝ)*q^(n+1)) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hqn).summable.comp_injective
      (fun _ _ h => by omega)
  have hs : Summable (fun n : ℕ => evenCoefficient ((Real.pi*a)^2) q (n+1)) :=
    Summable.of_nonneg_of_le
      (fun n => evenCoefficient_nonneg _ q _ (sq_nonneg _) hq0 hq1)
      (fun n => evenCoefficient_majorant _ q _ (sq_nonneg _) hq0 hq1)
      (hm.mul_left (8*((Real.pi*a)^2)/(1-q^2)))
  convert! hs using 1
  funext n
  rw [weierstrassCircleCoefficient,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (evenCoefficient_nonneg _ q _ (sq_nonneg _) hq0 hq1)]

private theorem weierstrass_circle_mode (T a : ℝ) (ha : a ≠ 0) (hT : T = 2/a)
    (m : ℤ) (x : ℝ) :
    Complex.exp (2*Real.pi*I*(a:ℂ)*(x:ℂ)*(m:ℂ)) =
      fourier (2*m) (x:AddCircle T) := by
  rw [fourier_coe_apply,hT]
  congr 1
  have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  push_cast
  field_simp

private theorem weierstrass_circle_pair (T a : ℝ) [Fact (0 < T)]
    (ha : a ≠ 0) (hT : T = 2/a) (n : ℕ) (x : ℝ) :
    evenFourierPair T n (x:AddCircle T) =
      (Complex.exp (2*Real.pi*I*((a*x:ℝ):ℂ)))^(n+1)+
        (Complex.exp (2*Real.pi*I*(-((a*x:ℝ):ℂ))))^(n+1)-2 := by
  have hp : (Complex.exp (2*Real.pi*I*((a*x:ℝ):ℂ)))^(n+1) =
      fourier (2*((n+1:ℕ):ℤ)) (x:AddCircle T) := by
    rw [← Complex.exp_nat_mul]
    calc
      _ = Complex.exp (2*Real.pi*I*(a:ℂ)*(x:ℂ)*((n+1:ℕ):ℂ)) := by
        congr 1
        push_cast
        ring
      _ = _ := by simpa only [Int.cast_natCast] using
        weierstrass_circle_mode T a ha hT ((n+1:ℕ):ℤ) x
  have hn : (Complex.exp (2*Real.pi*I*(-((a*x:ℝ):ℂ))))^(n+1) =
      fourier (-2*((n+1:ℕ):ℤ)) (x:AddCircle T) := by
    rw [← Complex.exp_nat_mul]
    calc
      _ = Complex.exp (2*Real.pi*I*(a:ℂ)*(x:ℂ)*(-((n+1:ℕ):ℂ))) := by
        congr 1
        push_cast
        ring
      _ = _ := by simpa only [Int.cast_neg,Int.cast_natCast,mul_neg,neg_mul] using
        weierstrass_circle_mode T a ha hT (-((n+1:ℕ):ℤ)) x
  simp only [evenFourierPair,ContinuousMap.sub_apply,ContinuousMap.add_apply,
    ContinuousMap.smul_apply,ContinuousMap.one_apply,smul_eq_mul,mul_one,hp,hn]

theorem circle_weierstrass_fourier_series (T a : ℝ) [Fact (0 < T)]
    (ha : a ≠ 0) (hT : T = 2/a)
    (hnorm : 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1)
    (f : C(AddCircle T, ℂ)) (hW : ∀ x : ℝ, f (x:AddCircle T) = normalizedWeierstrass a x) :
    HasSum (fun n : ℕ => weierstrassCircleCoefficient a n • evenFourierPair T n) (f-1) := by
  have hs : Summable (fun n : ℕ => weierstrassCircleCoefficient a n • evenFourierPair T n) := by
    apply Summable.of_norm_bounded ((weierstrass_circle_coefficients_summable a).mul_right 4)
    intro n
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (even_fourier_pair_norm T n) (norm_nonneg _)
  have hpoint (x : ℝ) : HasSum
      (fun n : ℕ => (weierstrassCircleCoefficient a n • evenFourierPair T n) (x:AddCircle T))
      ((f-1) (x:AddCircle T)) := by
    change HasSum _ (f (x:AddCircle T)-1)
    rw [hW x]
    convert! normalized_weierstrass_fourier a hnorm x using 1
    funext n
    simp only [ContinuousMap.smul_apply,smul_eq_mul]
    rw [weierstrass_circle_pair T a ha hT n x]
    dsimp only [weierstrassCircleCoefficient,evenCoefficient]
    push_cast
    ring
  have heq : (∑' n : ℕ, weierstrassCircleCoefficient a n • evenFourierPair T n) = f-1 := by
    ext z
    induction z using QuotientAddGroup.induction_on
    rename_i x
    exact ((ContinuousMap.evalCLM ℂ (x:AddCircle T)).hasSum hs.hasSum).unique (hpoint x)
  simpa only [heq] using hs.hasSum

theorem circle_weierstrass_fourier_data (T a : ℝ) [Fact (0 < T)]
    (ha : a ≠ 0) (hT : T = 2/a)
    (hnorm : 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1)
    (f : C(AddCircle T, ℂ)) (hW : ∀ x : ℝ, f (x:AddCircle T) = normalizedWeierstrass a x) :
    (∀ n : ℤ, fourierCoeff f (-n) = fourierCoeff f n) ∧
    (∀ j : ℕ, fourierCoeff f (2*(j:ℤ)) =
      (fourierCoefficient ((Real.pi*a)^2) (Real.exp (-Real.pi)) j:ℂ)) ∧
    (∀ n : ℤ, Odd n → fourierCoeff f n = 0) := by
  have hf := circle_weierstrass_fourier_series T a ha hT hnorm f hW
  refine ⟨even_fourier_series_symmetric T _ f hf, ?_, even_fourier_series_odd T _ f hf⟩
  intro j
  cases j with
  | zero =>
    change fourierCoeff f 0 = (constantCoefficient ((Real.pi*a)^2) (Real.exp (-Real.pi)):ℂ)
    have hm := even_fourier_series_mean T _ (weierstrass_circle_coefficients_summable a) f hf
    have hsum : (∑' n : ℕ, weierstrassCircleCoefficient a n) =
        ((∑' n : ℕ, evenCoefficient ((Real.pi*a)^2) (Real.exp (-Real.pi)) (n+1):ℝ):ℂ) := by
      exact (Complex.ofReal_tsum _).symm
    rw [hsum] at hm
    rw [constantCoefficient]
    push_cast
    simpa only [Complex.ofReal_tsum] using hm
  | succ j =>
    change fourierCoeff f (2*((j+1:ℕ):ℤ)) = weierstrassCircleCoefficient a j
    exact even_fourier_series_positive T _ f hf j

end Lemniscate
