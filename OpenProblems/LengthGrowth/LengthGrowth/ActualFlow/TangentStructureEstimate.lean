import LengthGrowth.ActualFlow.TangentShift
namespace LengthGrowth.TangentSpectrum
noncomputable section
open Real MeasureTheory

theorem multiplier_lower (x : ℝ) :
    x^2-4*x^4≤4*‖Complex.exp (Complex.I*(x:ℂ))-1‖^2 := by
  let z := Complex.I*(x:ℂ)
  have zn : ‖z‖=|x| := by simp [z]
  by_cases small : |x|≤1/2
  · have b := Complex.norm_exp_sub_one_sub_id_le (x:=z) (by rw [zn]; linarith)
    have tri := norm_sub_le (Complex.exp z-1) (Complex.exp z-1-z)
    rw [sub_sub_cancel] at tri
    rw [zn] at b tri
    have p := mul_le_mul_of_nonneg_left small (abs_nonneg x)
    have low : |x|/2≤‖Complex.exp z-1‖ := by nlinarith only [b,tri,p]
    have sq := pow_le_pow_left₀ (by positivity : 0≤|x|/2) low 2
    rw [div_pow,sq_abs] at sq
    change x^2-4*x^4≤4*‖Complex.exp z-1‖^2
    nlinarith only [sq,sq_nonneg (x^2)]
  · have sq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) (le_of_not_ge small) 2
    rw [sq_abs] at sq
    nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr sq),sq_nonneg (‖Complex.exp (Complex.I*(x:ℂ))-1‖)]

/-- The lower estimate is on an actual arclength increment, with no adjustable
multiplicative constant or unspecified band of frequencies. -/
theorem increment_lower {T : ℝ→ℂ} (ct : Continuous T) (pt : Function.Periodic T 1)
    {X M : ℝ} (xp : 0<X)
    (two : HasSum (fun n=>|omega n|^2*energy T n) (2*X^3))
    (four : HasSum (fun n=>|omega n|^4*energy T n) M) (cap : M≤1024*X^7) :
    let h := 1/(64*X^2)
    h/4194304 ≤ (incrementMoment T h)^2 := by
  let h := 1/(64*X^2)
  have hp : 0<h := by dsimp [h];positivity
  have term (n : ℤ) : h^2*(|omega n|^2*energy T n)-4*h^4*(|omega n|^4*energy T n)≤
      4*(‖character n h-1‖^2*energy T n) := by
    have e := mul_le_mul_of_nonneg_right (multiplier_lower (omega n*h)) (sq_nonneg (‖coeff T n‖))
    change _≤4*‖character n h-1‖^2*energy T n at e
    have a4 : |omega n|^4=(omega n)^4 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,pow_mul,sq_abs]
    rw [sq_abs,a4]
    change ((omega n*h)^2-4*(omega n*h)^4)*energy T n≤_ at e
    nlinarith only [e]
  have sums := hasSum_le term ((two.mul_left (h^2)).sub (four.mul_left (4*h^4))) ((increment_parseval ct pt h).mul_left 4)
  have low : h^2*X^3/4 ≤ incrementMoment T h := by
    have p := mul_le_mul_of_nonneg_left cap (show 0≤4*h^4 by positivity)
    have eq : 4*h^4*(1024*X^7)=h^2*X^3 := by dsimp [h];field_simp;ring
    linarith only [p,eq,sums]
  have sq := pow_le_pow_left₀ (by positivity : 0≤h^2*X^3/4) low 2
  have eq : h/4194304=(h^2*X^3/4)^2 := by dsimp [h];field_simp;ring
  exact eq.le.trans sq

end
end LengthGrowth.TangentSpectrum
#print axioms LengthGrowth.TangentSpectrum.increment_lower

