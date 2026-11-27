import Migration.LowDefectSecondHarmonic

noncomputable section
namespace MigrationGeometry.Flow.LowDefect

/-- The first harmonic controls all but 27 percent of the normalized defect. -/
theorem quarter_mass_bootstrap {D W z : ℝ} (d : 0≤D) (hi : D≤1/4) (w : 0≤W)
    (zw : z^2*(1-W)≤W^2) (crude : W≤D/2) (tail : W≤D/4+3*z^2/4) :
    W≤27/100*D ∧ z≤28/100*D := by
  have step {a b : ℝ} (old : W≤a*D) (ap : 0≤a) (bp : 0<b)
      (q : 0<1-a/4) (num : a^2/4≤b*(1-a/4)) : z^2≤b*D := by
    have low : 1-a/4≤1-W := by linarith [mul_le_mul_of_nonneg_left hi ap]
    have p := mul_le_mul_of_nonneg_left low (sq_nonneg z)
    have s := pow_le_pow_left₀ w old 2
    have k := mul_le_mul_of_nonneg_left hi (mul_nonneg (sq_nonneg a) d)
    have n := mul_le_mul_of_nonneg_right num d
    apply (mul_le_mul_iff_left₀ q).mp
    nlinarith only [p,zw,s,k,n]
  have first := step (a:=1/2) (b:=72/1000) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have next := step (a:=305/1000) (b:=26/1000) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Wb : W≤27/100*D := by linarith
  have ws := pow_le_pow_left₀ w Wb 2
  have zlo := mul_le_mul_of_nonneg_left (show (932/1000:ℝ)≤1-W by linarith) (sq_nonneg z)
  refine ⟨Wb,le_of_sq_le_sq ?_ (by positivity)⟩
  nlinarith only [ws,zlo,zw,sq_nonneg D]

theorem quarter_physical_margins {x : ℝ} (lo : 0≤x) (hi : x≤1/2) :
    (1+x^2)/2*(x*(1755/1000+575/1000*x+14/100*x^2)+95/100*x^2) < 80/100 ∧
    803/1000 < (1+x^2)*(1-575/1000*x-279/1000*x^2) := by
  have xx := pow_le_pow_left₀ lo hi 2
  have innerB := mul_le_mul hi (show 1755/1000+575/1000*x+14/100*x^2≤
      (1755/1000+575/1000*(1/2)+14/100*(1/2)^2:ℝ) by linarith) (by positivity) (by norm_num)
  have bound := mul_le_mul (show (1+x^2)/2≤(1+(1/2)^2)/2 by linarith)
    (show x*(1755/1000+575/1000*x+14/100*x^2)+95/100*x^2≤
      ((1/2)*(1755/1000+575/1000*(1/2)+14/100*(1/2)^2)+95/100*(1/2)^2:ℝ) by linarith) (by positivity) (by norm_num)
  have fac : 0≤(1/2-x)*(575/1000-721/1000*(1/2+x)+575/1000*((1/2)^2+(1/2)*x+x^2)+
          279/1000*((1/2)^3+(1/2)^2*x+(1/2)*x^2+x^3)) := by
    apply mul_nonneg (by linarith)
    nlinarith only [hi,lo,sq_nonneg x,pow_nonneg lo 3]
  constructor <;> nlinarith only [bound,fac]
end MigrationGeometry.Flow.LowDefect
#print axioms MigrationGeometry.Flow.LowDefect.quarter_mass_bootstrap
#print axioms MigrationGeometry.Flow.LowDefect.quarter_physical_margins

