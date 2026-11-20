import SolitonClassification.FrozenStressOrbit
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Complex.Exponential

/-! A posteriori comparison for the two frozen initial states. -/
noncomputable section
set_option exponentiation.threshold 1024
namespace ClosedSimilarity.FrozenStress.Endpoint
open Set

abbrev State := Fin 4 → ℝ
def state (z : Orbit) (t : ℝ) : State := ![z.k t,z.v t/8,z.p t,z.q t]
def field (x : State) : State := ![8*x 1,-(x 0)^3/16-x 2/8,-x 0*x 3,x 0*x 2]

theorem state_deriv (z : Orbit) (t : ℝ) : HasDerivAt (state z) (field (state z t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt z.k (8*(z.v t/8)) t
    convert! z.dk t using 1; ring
  · change HasDerivAt (fun s => z.v s/8) (-(z.k t)^3/16-z.p t/8) t
    convert! (z.dv t).div_const 8 using 1; ring
  · exact z.dp t
  · exact z.dq t

theorem unit_bounds (z : Orbit) (t : ℝ) : |z.p t|≤1 ∧ |z.q t|≤1 := by
  have h := z.unit t
  constructor <;> apply abs_le.mpr <;> constructor <;> nlinarith [sq_nonneg (z.p t),sq_nonneg (z.q t)]

private theorem displacement {f g : ℝ → ℝ} (hd : ∀s,HasDerivAt f (g s) s)
    (hb : ∀s,|g s|≤1) {t : ℝ} (ht : 0≤t) : |f t-f 0|≤t := by
  have h := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) (fun s _ => hb s)
    (x:=0) (y:=t) (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs,abs_of_nonneg ht] using h

theorem orbit_tube (z : Orbit) (hr : z.radial 0=0) (hb : |z.transverse 0|≤1)
    {t : ℝ} (ht : t∈Icc 0 20) : |z.k t|≤8 := by
  have dR := displacement z.radial_hasDerivAt (fun s => by
    rw [abs_neg,abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (unit_bounds z s).1 2).trans (by norm_num)) ht.1
  have dB := displacement z.transverse_hasDerivAt (fun s => by
    rw [abs_mul]
    exact (mul_le_mul (unit_bounds z s).1 (unit_bounds z s).2 (abs_nonneg _) (by norm_num)).trans (by norm_num)) ht.1
  rw [hr,sub_zero] at dR
  have R : |z.radial t| ≤ 20 := dR.trans ht.2
  have B : |z.transverse t| ≤ 21 := by
    have hh := abs_sub_le (z.transverse t) (z.transverse 0) 0
    simp only [sub_zero] at hh
    linarith [ht.2]
  have RR := pow_le_pow_left₀ (abs_nonneg _) R 2
  have BB := pow_le_pow_left₀ (abs_nonneg _) B 2
  rw [sq_abs] at RR BB
  have h := z.stress_unit t
  rw [z.amplitude_sq] at h
  by_contra! big
  have e : 64 < (z.k t)^2 := by
    have := mul_self_lt_mul_self (by norm_num : (0:ℝ)≤8) big
    rw [←sq,←sq,sq_abs] at this
    linarith
  nlinarith [sq_nonneg (z.v t),mul_self_lt_mul_self (by norm_num : (0:ℝ)≤64) e]

private theorem coord (x y : State) (i : Fin 4) : |x i-y i|≤‖x-y‖ := norm_le_pi_norm (x-y) i

private theorem prod_diff {a b c d E : ℝ} (ha : |a-c|≤E) (hb : |b-d|≤E)
    (h1 : |b|≤1) (h8 : |c|≤8) : |a*b-c*d|≤9*E := by
  have en := (abs_nonneg _).trans ha
  rw [show a*b-c*d=(a-c)*b+c*(b-d) by ring]
  calc
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| * |b|+|c| * |b-d| := by rw [abs_mul,abs_mul]
    _ ≤ E*1+8*E := by gcongr
    _ = _ := by ring

theorem field_comparison (x y : State) (hx : |x 0|≤8) (hy : |y 0|≤8)
    (hp : |x 2|≤1) (hq : |x 3|≤1) : ‖field x-field y‖≤13*‖x-y‖ := by
  let E := ‖x-y‖
  have nn : 0≤E := norm_nonneg _
  have factor : |x 0^2+x 0*y 0+y 0^2|≤192 := by
    calc
      _ ≤ (|x 0^2|+|x 0*y 0|)+|y 0^2| := (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ = (|x 0|^2+|x 0| * |y 0|)+|y 0|^2 := by rw [abs_pow,abs_mul,abs_pow]
      _ ≤ ((8:ℝ)^2+8*8)+8^2 := by gcongr
      _ = _ := by norm_num
  have cube : |x 0^3-y 0^3|≤E*192 := by
    rw [show x 0^3-y 0^3=(x 0-y 0)*(x 0^2+x 0*y 0+y 0^2) by ring,abs_mul]
    exact mul_le_mul (coord x y 0) factor (abs_nonneg _) nn
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · change |8*x 1-8*y 1|≤13*E
    rw [←mul_sub,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤8)]
    linarith [coord x y 1]
  · change |(-(x 0)^3/16-x 2/8)-(-(y 0)^3/16-y 2/8)|≤13*E
    rw [show (-(x 0)^3/16-x 2/8)-(-(y 0)^3/16-y 2/8)= -((x 0^3-y 0^3)/16+(x 2-y 2)/8) by ring,
      abs_neg]
    calc
      _ ≤ |(x 0^3-y 0^3)/16|+|(x 2-y 2)/8| := abs_add_le _ _
      _ ≤ 13*E := by rw [abs_div,abs_div]; norm_num; linarith [coord x y 2]
  · change |-x 0*x 3-(-y 0*y 3)|≤13*E
    rw [show -x 0*x 3-(-y 0*y 3)= -(x 0*x 3-y 0*y 3) by ring,abs_neg]
    linarith [prod_diff (coord x y 0) (coord x y 3) hq hy]
  · change |x 0*x 2-y 0*y 2|≤13*E
    linarith [prod_diff (coord x y 0) (coord x y 2) hp hy]

/-- A continuous piecewise polynomial can use the derivative from the right
at every interior mesh junction. The last endpoint needs only continuity. -/
theorem orbit_error (z : Orbit) (hr : z.radial 0=0) (hb : |z.transverse 0|≤1)
    (y dy : ℝ → State) (hc : ContinuousOn y (Icc 0 20))
    (hd : ∀t∈Ico 0 20,HasDerivWithinAt y (dy t) (Ici t) t)
    (hy : ∀t∈Ico 0 20,|y t 0|≤8)
    (defect : ∀t∈Ico 0 20,‖dy t-field (y t)‖≤1/2^432)
    (init : y 0=state z 0) : ‖state z 20-y 20‖≤1/2^20 := by
  have hcx : Continuous (state z) := continuous_iff_continuousAt.mpr (fun t => (state_deriv z t).continuousAt)
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (K:=13) (ε:=1/2^432)
    (hcx.continuousOn.sub hc)
    (fun t ht => (state_deriv z t).hasDerivWithinAt.sub (hd t ht))
    (δ:=0) (by simp [init]) (fun t ht => by
      have f := field_comparison (state z t) (y t) (orbit_tube z hr hb (Ico_subset_Icc_self ht))
        (hy t ht) (unit_bounds z t).1 (unit_bounds z t).2
      have d := defect t ht
      rw [norm_sub_rev] at d
      exact (norm_sub_le_norm_sub_add_norm_sub _ (field (y t)) _).trans (add_le_add f d))
    20 ⟨by norm_num,le_rfl⟩
  simp only [Pi.sub_apply,sub_zero,gronwallBound_of_K_ne_0 (by norm_num : (13:ℝ)≠0),
    zero_mul,zero_add] at h
  have expbound : Real.exp (13*20) ≤ (3:ℝ)^260 := by
    rw [show (13:ℝ)*20=(260:ℕ)*1 by norm_num,Real.exp_nat_mul]
    have hfrac : Real.exp (1/16)≤16/15 := by
      exact (Real.exp_bound_div_one_sub_of_interval (by norm_num : (0:ℝ)≤1/16) (by norm_num)).trans (by norm_num)
    have hone : Real.exp 1 ≤ 3 := by
      rw [show (1:ℝ)=(16:ℕ)*(1/16:ℝ) by norm_num,Real.exp_nat_mul]
      exact (pow_le_pow_left₀ (Real.exp_pos _).le hfrac 16).trans (by norm_num)
    exact pow_le_pow_left₀ (Real.exp_pos _).le hone _
  apply h.trans
  calc
    _ ≤ 1/2^432/13*((3:ℝ)^260-1) := by gcongr
    _ ≤ _ := by norm_num

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.orbit_error
