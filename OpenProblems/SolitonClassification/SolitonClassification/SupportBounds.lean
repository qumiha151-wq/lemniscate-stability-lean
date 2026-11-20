import SolitonClassification.SupportCutoff
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace ClosedSimilarity.GlobalSupport
open Set
open scoped Topology

def positionSize (x : Phase) := Real.sqrt (1 + (x 2)^2 + (x 3)^2)
def stressSize (x : Phase) := Real.sqrt (1 + ((x 0)^2/2)^2 + (x 1)^2)

lemma position_sq (x : Phase) : (positionSize x)^2 = 1+(x 2)^2+(x 3)^2 :=
  Real.sq_sqrt (by positivity)
lemma stress_sq (x : Phase) : (stressSize x)^2 = 1+((x 0)^2/2)^2+(x 1)^2 :=
  Real.sq_sqrt (by positivity)

lemma position_pos (x : Phase) : 0 < positionSize x := Real.sqrt_pos.2 (by positivity)
lemma stress_pos (x : Phase) : 0 < stressSize x := Real.sqrt_pos.2 (by positivity)

lemma coordinate_bounds (x : Phase) :
    |x 2| ≤ positionSize x ∧ |x 3| ≤ positionSize x ∧
    |x 1| ≤ stressSize x ∧ |x 0| ≤ 2*stressSize x+1 := by
  have hp := position_sq x
  have hs := stress_sq x
  have h₀ : (x 0)^2/2 ≤ stressSize x :=
    le_of_sq_le_sq (by nlinarith [sq_nonneg (x 1)]) (stress_pos x).le
  refine ⟨le_of_sq_le_sq (by rw [sq_abs]; nlinarith [sq_nonneg (x 3)]) (position_pos x).le,
    le_of_sq_le_sq (by rw [sq_abs]; nlinarith [sq_nonneg (x 2)]) (position_pos x).le,
    le_of_sq_le_sq (by rw [sq_abs]; nlinarith [sq_nonneg ((x 0)^2/2)]) (stress_pos x).le,?_⟩
  nlinarith only [h₀, sq_nonneg (|x 0|-1), sq_abs (x 0)]

theorem size_derivatives {f : ℝ → Phase} {t d μ : ℝ}
    (hf : HasDerivAt f (μ • rhs d (f t)) t) :
    HasDerivAt (fun s => positionSize (f s)) (μ*d*(f t 3)/positionSize (f t)) t ∧
    HasDerivAt (fun s => stressSize (f s)) (-(μ*(f t 2)*(f t 1))/stressSize (f t)) t := by
  have dh := hasDerivAt_pi.mp hf
  have dk : HasDerivAt (fun s => f s 0) (μ*(f t 1)) t := dh 0
  have dv : HasDerivAt (fun s => f s 1) (μ*(-(f t 0)^3/2-f t 2)) t := dh 1
  have dp : HasDerivAt (fun s => f s 2) (μ*(-f t 0*f t 3)) t := dh 2
  have dq : HasDerivAt (fun s => f s 3) (μ*(d+f t 0*f t 2)) t := dh 3
  have hp : HasDerivAt (fun s => 1+(f s 2)^2+(f s 3)^2) (2*μ*d*f t 3) t := by
    convert! (((dp.pow 2).const_add 1).add (dq.pow 2)) using 1
    ring
  have hs : HasDerivAt (fun s => 1+((f s 0)^2/2)^2+(f s 1)^2) (-2*μ*(f t 2)*(f t 1)) t := by
    convert! (((((dk.pow 2).div_const 2).pow 2).const_add 1).add (dv.pow 2)) using 1
    simp only [Pi.pow_apply]
    ring
  constructor
  · convert! hp.sqrt (by positivity) using 1
    change _ = _/(2*positionSize _)
    field_simp [(position_pos _).ne']
  · convert! hs.sqrt (by positivity) using 1
    change _ = _/(2*stressSize _)
    field_simp [(stress_pos _).ne']

lemma rate_bound {a b c r : ℝ} (ha : |a| ≤ 1) (hc : |c| ≤ r) (hr : 0 < r) :
    |a*b*c/r| ≤ |b| := by
  rw [abs_div,abs_mul,abs_mul,abs_of_pos hr,div_le_iff₀ hr]
  exact (mul_le_mul (mul_le_mul_of_nonneg_right ha (abs_nonneg b)) hc (abs_nonneg _) (by positivity)).trans
    (by rw [one_mul])

def radius (d T : ℝ) (x : Phase) :=
  let P := positionSize x + |d| * T
  2*(stressSize x + P*T) + 1 + P

lemma radius_pos (d : ℝ) {T : ℝ} (hT : 0 ≤ T) (x : Phase) : 0 < radius d T x := by
  unfold radius
  have hp := position_pos x
  have hs := stress_pos x
  positivity

theorem confinement {f : ℝ → Phase} {μ : ℝ → ℝ} {d T : ℝ} (hT : 0 ≤ T)
    (hm : ∀ t, |μ t| ≤ 1) (hf : ∀ t, HasDerivAt f (μ t • rhs d (f t)) t)
    {t : ℝ} (ht : |t| ≤ T) : ‖f t‖ ≤ radius d T (f 0) := by
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith,hT⟩
  have dp (s : ℝ) := (size_derivatives (hf s)).1
  have ds (s : ℝ) := (size_derivatives (hf s)).2
  let P := positionSize (f 0)+|d| * T
  have hP : 0 ≤ P := add_nonneg (position_pos _).le (mul_nonneg (abs_nonneg _) hT)
  have hb (s : ℝ) (h : s ∈ Icc (-T) T) : positionSize (f s) ≤ P := by
    have hbound (u : ℝ) (_ : u ∈ Icc (-T) T) :
        ‖deriv (fun v => positionSize (f v)) u‖ ≤ |d| := by
      rw [(dp u).deriv, Real.norm_eq_abs]
      exact rate_bound (hm u) (coordinate_bounds _).2.1 (position_pos _)
    have est := Convex.norm_image_sub_le_of_norm_deriv_le (fun u _ => (dp u).differentiableAt)
      hbound (convex_Icc (-T) T) h0 h
    simp only [Real.norm_eq_abs,sub_zero] at est
    exact (sub_le_iff_le_add.mp ((le_abs_self _).trans est)).trans
      (by dsimp [P]; linarith [mul_le_mul_of_nonneg_left (abs_le.mpr h) (abs_nonneg d)])
  have hbound (u : ℝ) (h : u ∈ Icc (-T) T) :
      ‖deriv (fun v => stressSize (f v)) u‖ ≤ P := by
    rw [(ds u).deriv,Real.norm_eq_abs,neg_div,abs_neg]
    exact (rate_bound (hm u) (coordinate_bounds _).2.2.1 (stress_pos _)).trans
      ((coordinate_bounds _).1.trans (hb u h))
  have ht' : t ∈ Icc (-T) T := abs_le.mp ht
  have est := Convex.norm_image_sub_le_of_norm_deriv_le (fun u _ => (ds u).differentiableAt)
    hbound (convex_Icc (-T) T) h0 ht'
  simp only [Real.norm_eq_abs,sub_zero] at est
  have hs : stressSize (f t) ≤ stressSize (f 0)+P*T := by
    linarith [le_abs_self (stressSize (f t)-stressSize (f 0)),mul_le_mul_of_nonneg_left ht hP]
  have hp := hb t ht'
  have hc := coordinate_bounds (f t)
  have hs0 := (stress_pos (f t)).le
  apply (pi_norm_le_iff_of_nonneg (radius_pos d hT _).le).mpr
  intro i
  change |f t i| ≤ 2*(stressSize (f 0)+P*T)+1+P
  fin_cases i <;> dsimp <;> linarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

end ClosedSimilarity.GlobalSupport
