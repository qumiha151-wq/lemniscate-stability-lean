import Migration.DefectFourHull

noncomputable section
namespace MigrationGeometry.Flow.LowDefect

/-- The missing second tangent coefficient has quadratic size in the defect.
Here W is all Fourier mass outside the first harmonic, and z is the
absolute value of the second coefficient. -/
theorem mass_bootstrap {D W z : ℝ} (d : 0 ≤ D) (hi : D ≤ 14/100)
    (w : 0 ≤ W) (zw : z^2*(1-W) ≤ W^2)
    (crude : W ≤ D/2) (tail : W ≤ D/4+3*z^2/4) :
    W ≤ 26/100*D ∧ z ≤ 266/1000*D := by
  have prod (a h : ℝ) (wa : W ≤ a*D) (ha : 0 ≤ a)
      (h0 : 0 ≤ h) (numer : a^2*(14/100) ≤ h*(1-a*(14/100))) :
      z^2 ≤ h*D := by
    have wa2 := pow_le_pow_left₀ w wa 2
    have da := mul_le_mul_of_nonneg_left hi ha
    have wz := mul_le_mul_of_nonneg_left (show 1-a*(14/100) ≤ 1-W by linarith) (sq_nonneg z)
    have de := mul_le_mul_of_nonneg_left hi (mul_nonneg (sq_nonneg a) d)
    have nn := mul_le_mul_of_nonneg_right numer d
    by_cases ah : a*(14/100) < 1
    · apply (mul_le_mul_iff_left₀ (show 0 < 1-a*(14/100) by linarith)).mp
      nlinarith only [zw,wa2,wz,de,nn]
    · have := le_of_not_gt ah
      have lt : 0 < a := by
        by_contra! hn
        have : a=0 := by linarith
        subst a; norm_num at *
      nlinarith [sq_pos_of_pos lt,mul_nonpos_of_nonneg_of_nonpos h0 (show 1-a*(14/100) ≤ 0 by linarith)]
  have z1 := prod (1/2) (38/1000) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have w1 : W ≤ (279/1000)*D := by linarith
  have z2 := prod (279/1000) (12/1000) w1 (by norm_num) (by norm_num) (by norm_num)
  have w2 : W ≤ (26/100)*D := by linarith
  refine ⟨w2,?_⟩
  have wa2 := pow_le_pow_left₀ w w2 2
  have wz := mul_le_mul_of_nonneg_left (show (96/100:ℝ) ≤ 1-W by linarith) (sq_nonneg z)
  nlinarith only [zw,wa2,wz,sq_nonneg D,d]

/-- Sharp two-tail multiplier estimate, with the exceptional positive
second harmonic treated separately. -/
theorem normal_weight {n : ℤ} (nz : n ≠ 0) (nt : n ≠ 2) :
    (1-1/(n:ℝ))^2 ≤ 5/9*((n:ℝ)-1)^2-8/9*((n:ℝ)-1) := by
  have nh : (n:ℝ) ≠ 0 := by exact_mod_cast nz
  apply (le_of_mul_le_mul_left (a:=(n:ℝ)^2) _ (sq_pos_of_ne_zero nh))
  have eq : (n:ℝ)^2 * ((1-1/(n:ℝ))^2) = ((n:ℝ)-1)^2 := by
    field_simp
  rw [eq]
  have fac : 0 ≤ ((n:ℝ)-1)*((n:ℝ)+1)*((n:ℝ)-3)*(5*(n:ℝ)-3) := by
    rcases le_or_gt n (-1) with h|h
    · have hl : (n:ℝ) ≤ -1 := by exact_mod_cast h
      exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
          (by linarith)) (by linarith)
    · rcases eq_or_ne n 1 with h1|h1
      · subst n; norm_num
      · have h3 : (3:ℤ) ≤ n := by omega
        have hl : (3:ℝ) ≤ n := by exact_mod_cast h3
        exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by linarith)
  nlinarith only [fac]

/-- Uniform geometric comparison in energy-radius units. -/
theorem physical_margins {x : ℝ} (lo : 0 ≤ x) (hi : x ≤ 374/1000) :
    (1+x^2)*x*(1750/1000+575/1000*x+133/1000*x^2) < 846/1000 ∧
    852/1000 < (1+x^2)*(1-575/1000*x-265/1000*x^2) := by
  have xx := pow_le_pow_left₀ lo hi 2
  have up := mul_le_mul (a:=1+x^2) (b:=1+(374/1000:ℝ)^2)
    (c:=x) (d:=374/1000) (by linarith) hi lo (by norm_num)
  have top := mul_le_mul up
    (show 1750/1000+575/1000*x+133/1000*x^2 ≤
      (1750/1000+575/1000*(374/1000)+133/1000*(374/1000)^2:ℝ) by linarith) (by positivity) (by norm_num)
  constructor
  · linarith only [top]
  · let a : ℝ := 374/1000
    have xa : x ≤ a := hi
    have a0 : 0 ≤ a := by norm_num [a]
    have f : 0 ≤ (a-x)*(575/1000-735/1000*(a+x)+575/1000*(a^2+a*x+x^2)+
        265/1000*(a^3+a^2*x+a*x^2+x^3)) := by
      apply mul_nonneg (sub_nonneg.mpr xa)
      have h1 : 0 ≤ 575/1000-735/1000*(a+x) := by dsimp [a]; linarith
      positivity
    dsimp [a] at f
    nlinarith only [f]

end MigrationGeometry.Flow.LowDefect
#print axioms MigrationGeometry.Flow.LowDefect.mass_bootstrap
#print axioms MigrationGeometry.Flow.LowDefect.normal_weight
#print axioms MigrationGeometry.Flow.LowDefect.physical_margins
