import Migration.NearRoundDisk
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
open Set
namespace MigrationGeometry.Flow.DefectFour

/-- Second use of the closure estimate for the tangent angle Fourier modes.
Here V1 is the squared norm of modes ±1 and P the squared primitive norm. -/
theorem phase_bootstrap {V V1 P : ℝ} (hV : 0<V) (vmax : V≤16/25)
    (p0 : 0≤P) (pV : P≤V) (modes : V1≤P^2/(4*Real.pi))
    (gap : P≤V/4+3*V1/4) : P≤(13/50)*V := by
  have pi3 := Real.pi_gt_three
  have mp : 4*Real.pi*V1≤P^2 := by
    have eq := (le_div_iff₀ (show 0<4*Real.pi by positivity)).mp modes
    linarith only [eq]
  by_cases vn : V1≤0
  · linarith
  have vp := le_of_lt (lt_of_not_ge vn)
  have weakened : 12*V1≤P^2 := by
    nlinarith only [mp,mul_nonneg (sub_nonneg.mpr pi3.le) vp]
  have pv2 := mul_self_le_mul_self p0 pV
  have step : P≤(29/100)*V := by
    nlinarith only [gap,weakened,pv2,mul_nonneg (sub_nonneg.mpr vmax) hV.le]
  have p2 := mul_self_le_mul_self p0 step
  nlinarith only [gap,weakened,p2,mul_nonneg (sub_nonneg.mpr vmax) hV.le]

/-- Dimensionless lower support and upper centroid mobility at all energy
defects between zero and four. R is the energy radius. -/
theorem margins {x m s κ : ℝ} (x0 : 0≤x) (x2 : x≤2) (m0 : 0≤m)
    (ma : m≤(41/500)*x) (s0 : 0≤s) (sc : s≤38/25)
    (k0 : 1/40≤κ) (ku : κ≤13/500) :
    81/100≤(1+κ*x^2)*(1-m^2/2-s*m) ∧
    (1+κ*x^2)*x*((1+s*m)/(2*(157/50))+(51/100)/(157/50))≤4/5 := by
  have xSq := mul_self_le_mul_self x0 x2
  have msq := mul_self_le_mul_self m0 ma
  have sm := mul_le_mul sc ma m0 (by norm_num)
  have h0 : 1-x/8-(17/5000)*x^2≤1-m^2/2-s*m := by
    nlinarith only [msq,sm,x0,sq_nonneg x]
  have pos : 0≤1-x/8-(17/5000)*x^2 := by nlinarith only [xSq,x2]
  have low := mul_le_mul
    (show 1+x^2/40≤1+κ*x^2 by nlinarith only [mul_le_mul_of_nonneg_right k0 (sq_nonneg x)])
    h0 pos (by nlinarith only [mul_nonneg (show 0≤κ by linarith) (sq_nonneg x)])
  have x3 := mul_le_mul_of_nonneg_right x2 (sq_nonneg x)
  have x4 := mul_le_mul_of_nonneg_right xSq (sq_nonneg x)
  constructor
  · have small : 81/100≤1-x/8+(3/200)*x^2 := by
      nlinarith only [mul_nonneg (show 0≤2-x by linarith)
        (show 0≤1/8-(3/200)*(x+2) by linarith)]
    nlinarith only [low,x3,x4,small,sq_nonneg x]
  · have up : κ*x^2≤(13/500)*4 := by
      exact (mul_le_mul_of_nonneg_right ku (sq_nonneg x)).trans
        (mul_le_mul_of_nonneg_left (by nlinarith only [xSq]) (by norm_num))
    have sm' : s*m≤(38/25)*((41/500)*2) := by nlinarith only [sm,x2]
    have part := mul_le_mul (show 1+κ*x^2≤1+(13/500)*4 by linarith) x2 x0 (by norm_num)
    have rpart : (1+s*m)/(2*(157/50))+(51/100)/(157/50) ≤
        (1+(38/25)*((41/500)*2))/(2*(157/50))+(51/100)/(157/50) := by
      exact add_le_add_left (div_le_div_of_nonneg_right (add_le_add_right sm' 1) (by norm_num)) _
    have prod := mul_le_mul part rpart (by positivity) (by norm_num)
    linarith only [prod]

/-- A global energy-radius comparison gives a common disk in the actual
plane at two times. The strict spare margin covers boundary points. -/
theorem earlier_centroid_disk {A : Set ℂ} {c0 c1 : ℂ} {R0 R : ℝ} (pos : 0<R)
    (drift : ‖c1-c0‖≤(4/5)*(R-R0))
    (support : ∀e : ℂ, ‖e‖=1 → ∃y∈A, inner ℝ e c1 + (81/100)*R ≤ inner ℝ e y) :
    Metric.closedBall c0 ((4/5)*R0+R/200) ⊆ convexHull ℝ A := by
  apply closedBall_subset_convexHull_of_directional_margin (R:=(4/5)*R0+R/100) (by linarith)
  intro e he
  obtain ⟨y,hy,ey⟩ := support e he
  have h := real_inner_le_norm e (c0-c1)
  rw [inner_sub_right,he,one_mul,norm_sub_rev c0 c1] at h
  exact ⟨y,hy,by linarith⟩

end MigrationGeometry.Flow.DefectFour
#print axioms MigrationGeometry.Flow.DefectFour.margins
#print axioms MigrationGeometry.Flow.DefectFour.earlier_centroid_disk
