import Lemniscate.BernoulliArclength
import Lemniscate.WeierstrassProfile
import Lemniscate.WeierstrassPeriods

/-! The half-period symmetry and exact period of the actual curvature profile. -/
namespace Lemniscate
open MeasureTheory Complex

private theorem bernoulli_arclength_symmetry (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖) :
    let T := e (2*Real.pi)
    (∀ x, bernoulliProfileQ (e.symm (x+T/2)) = -bernoulliProfileQ (e.symm x)) ∧
    ∀ x, 0 < x → x < T/4 → 0 < bernoulliProfileQ (e.symm x) := by
  let v : ℝ → ℝ := fun u => Real.sqrt 2*‖bernoulliVelocity u‖
  have he' (u : ℝ) : e u = ∫ t in (0:ℝ)..u, v t := he u
  have hvel : Continuous bernoulliVelocity :=
    continuous_iff_continuousAt.mpr (fun u => (bernoulli_curve_geometry u).2.1.continuousAt)
  have hv : Continuous v := continuous_const.mul hvel.norm
  have hper : Function.Periodic v Real.pi := by
    intro u
    dsimp only [v]
    rw [(bernoulli_curve_geometry (u+Real.pi)).2.2.1,
      (bernoulli_curve_geometry u).2.2.1,Real.sin_add_pi,neg_sq]
  have hreflect (u : ℝ) : v (Real.pi-u) = v u := by
    dsimp only [v]
    rw [(bernoulli_curve_geometry (Real.pi-u)).2.2.1,
      (bernoulli_curve_geometry u).2.2.1,Real.sin_pi_sub]
  have hshift (u : ℝ) : e (u+Real.pi) = e u+e Real.pi := by
    simpa only [he',zero_add] using
      hper.intervalIntegral_add_eq_add 0 u (fun a b => hv.intervalIntegrable a b)
  have hT : e (2*Real.pi) = 2*e Real.pi := by
    have h := hshift Real.pi
    rw [show Real.pi+Real.pi = 2*Real.pi by ring] at h
    linarith
  have hint : (∫ t in (0:ℝ)..Real.pi/2, v t) = ∫ t in Real.pi/2..Real.pi, v t := by
    have h := intervalIntegral.integral_comp_sub_left v Real.pi (a := 0) (b := Real.pi/2)
    rw [show (fun t => v (Real.pi-t)) = v from funext hreflect] at h
    simpa only [sub_zero,show Real.pi-Real.pi/2 = Real.pi/2 by ring] using h
  have hquarter : e (Real.pi/2) = e (2*Real.pi)/4 := by
    have h : (∫ t in (0:ℝ)..Real.pi/2, v t) + (∫ t in Real.pi/2..Real.pi, v t) =
        ∫ t in (0:ℝ)..Real.pi, v t := intervalIntegral.integral_add_adjacent_intervals
      (hv.intervalIntegrable 0 (Real.pi/2)) (hv.intervalIntegrable (Real.pi/2) Real.pi)
    rw [← hint,← he' (Real.pi/2),← he' Real.pi] at h
    linarith
  have hinv (x : ℝ) : e.symm (x+e (2*Real.pi)/2) = e.symm x+Real.pi := by
    apply e.injective
    rw [e.apply_symm_apply,hshift,e.apply_symm_apply]
    linarith
  refine ⟨?_,?_⟩
  · intro x
    rw [hinv]
    simp only [bernoulliProfileQ,Real.cos_add_pi,Real.sin_add_pi,neg_sq,neg_div]
  · intro x hx hxt
    have he0 : e 0 = 0 := by rw [he']; simp
    have hi0 : e.symm 0 = 0 := by
      apply e.injective
      rw [e.apply_symm_apply,he0]
    have hlo := e.symm.strictMono hx
    rw [hi0] at hlo
    have hhi := e.symm.strictMono hxt
    rw [← hquarter,e.symm_apply_apply] at hhi
    have hcos : 0 < Real.cos (e.symm x) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith only [Real.pi_pos,hlo],hhi⟩
    exact div_pos hcos (Real.sqrt_pos.mpr (by nlinarith only [sq_nonneg (Real.sin (e.symm x))]))

theorem bernoulli_weierstrass_period (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    (a : ℝ) (ha : 0 < a)
    (hnorm : 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1)
    (hident : ∀ x : ℝ, (bernoulliProfileQ (e.symm x):ℂ)^2 = normalizedWeierstrass a x) :
    e (2*Real.pi) = 2/a := by
  let T := e (2*Real.pi)
  have he0 : e 0 = 0 := by rw [he]; simp
  have hT : 0 < T := by
    have h := e.strictMono (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)
    simpa only [he0,T] using h
  obtain ⟨hanti,hfirst⟩ := bernoulli_arclength_symmetry e he
  have hWper (x : ℝ) : normalizedWeierstrass a (x+T/2) = normalizedWeierstrass a x := by
    rw [← hident (x+T/2),← hident x,hanti,Complex.ofReal_neg,neg_sq]
  have haC : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hcoeff : (-2:ℂ)*(a:ℂ)^2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 haC)
  have hregular (x : ℝ) : (x:ℂ)+I/2 ∉ unitSquarePeriods.lattice := by
    simpa only [Complex.ofReal_one,one_mul] using unit_square_midline_regular 1 x
  have hp (y : ℝ) :
      unitSquarePeriods.weierstrassP ((y:ℂ)+I/2+((a*T/2:ℝ):ℂ)) =
        unitSquarePeriods.weierstrassP ((y:ℂ)+I/2) := by
    have h := hWper (y/a)
    dsimp only [normalizedWeierstrass] at h
    have harg0 : (a:ℂ)*((y/a:ℝ):ℂ)+I/2 = (y:ℂ)+I/2 := by
      push_cast
      field_simp [haC]
    have harg1 : (a:ℂ)*((y/a+T/2:ℝ):ℂ)+I/2 =
        (y:ℂ)+I/2+((a*T/2:ℝ):ℂ) := by
      push_cast
      field_simp [haC]
      ring
    rw [harg0,harg1] at h
    exact mul_left_cancel₀ hcoeff h
  have hmem := weierstrass_real_line_period_mem unitSquarePeriods (I/2) (a*T/2)
    (by simpa only [Complex.ofReal_zero,zero_add] using hregular 0)
    (by simpa only [add_comm] using hregular (a*T/2)) hp
  obtain ⟨m,n,hmn⟩ := PeriodPair.mem_lattice.mp hmem
  have hm : (m:ℝ) = a*T/2 := by
    have h := congrArg Complex.re hmn
    norm_num [unitSquarePeriods] at h
    exact h
  have hmpos : (0:ℝ) < (m:ℝ) := by rw [hm]; positivity
  have hmZ : 0 < m := by exact_mod_cast hmpos
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ m by omega)
  have hlo : 2 ≤ a*T := by linarith
  obtain ⟨_,_,hzero,_⟩ := normalized_weierstrass_data a hnorm
  have hqzero : bernoulliProfileQ (e.symm (1/(2*a))) = 0 := by
    have hs : (bernoulliProfileQ (e.symm (1/(2*a))):ℂ)^2 = 0 :=
      (hident (1/(2*a))).trans hzero
    exact Complex.ofReal_eq_zero.mp (sq_eq_zero_iff.mp hs)
  have hfirstzero : T/4 ≤ 1/(2*a) := by
    by_contra h
    have hpos := hfirst (1/(2*a)) (by positivity) (lt_of_not_ge h)
    rw [hqzero] at hpos
    exact lt_irrefl _ hpos
  have hhi : a*T ≤ 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2*a)).mp hfirstzero
    nlinarith
  apply (eq_div_iff ha.ne').mpr
  change T*a = 2
  nlinarith

end Lemniscate
