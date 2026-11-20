import SolitonClassification.FrozenStressOrbit

noncomputable section
namespace ClosedSimilarity.FrozenStress

private theorem dot_le_one {a b c d : ℝ} (u : a^2+b^2=1) (v : c^2+d^2=1) :
    |a*c+b*d| ≤ 1 := by
  have idn : (a*c+b*d)^2+(a*d-b*c)^2=1 := by
    calc _ = (a^2+b^2)*(c^2+d^2) := by ring
         _ = 1 := by rw [u,v]; norm_num
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (a*d-b*c)],by nlinarith [sq_nonneg (a*d-b*c)]⟩

private theorem abs_coords {a b : ℝ} (h : a^2+b^2=1) :
    |a|≤1 ∧ |b|≤1 ∧ |a*b|≤1/2 := by
  exact ⟨abs_le.mpr ⟨by nlinarith [sq_nonneg b],by nlinarith [sq_nonneg b]⟩,
    abs_le.mpr ⟨by nlinarith [sq_nonneg a],by nlinarith [sq_nonneg a]⟩,
    abs_le.mpr ⟨by nlinarith [sq_nonneg (a+b)],by nlinarith [sq_nonneg (a-b)]⟩⟩

private theorem small_U {U w : ℝ} (h : (U^2/2)^2+w^2=1) : |U|≤1.415 := by
  have bound := (abs_le.mp (abs_coords h).1).2
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

private theorem double_unit {a b : ℝ} (h : a^2+b^2=1) :
    (a^2-b^2)^2+(2*a*b)^2=1 := by
  calc _ = (a^2+b^2)^2 := by ring
       _ = 1 := by rw [h]; norm_num

theorem psi_bound {U w a b : ℝ} (osc : (U^2/2)^2+w^2=1) (unit : a^2+b^2=1) :
    |psi U w a b| ≤ 0.472 := by
  let X:=a^2-b^2
  let Y:=2*a*b
  have circle : X^2+Y^2=1 := double_unit unit
  have dual : (U^2/2)^2+(-w)^2=1 := by nlinarith only [osc]
  have lin := dot_le_one dual circle
  have eqn : psi U w a b = U^3/24+U*((U^2/2)*X+(-w)*Y)/4 := by
    dsimp [psi,X,Y]
    linear_combination U^3/24 * unit
  have Ulim := small_U osc
  have u2 : |U|^2≤2 := by
    rw [sq_abs]
    linarith [(abs_le.mp (abs_coords osc).1).2]
  rw [eqn]
  apply (abs_add_le ..).trans
  rw [abs_div,abs_div,abs_pow,abs_mul]
  norm_num
  simp only [neg_mul] at lin
  nlinarith only [mul_le_mul_of_nonneg_left u2 (abs_nonneg U),
    mul_le_mul_of_nonneg_left lin (abs_nonneg U),Ulim]

theorem chi_bound {U w a b : ℝ} (osc : (U^2/2)^2+w^2=1) (unit : a^2+b^2=1) :
    |chi U w a b| ≤ 0.472 := by
  have dual : w^2+(U^2/2)^2=1 := by linarith only [osc]
  have lin := dot_le_one dual (double_unit unit)
  have e : chi U w a b = U*(w*(a^2-b^2)+(U^2/2)*(2*a*b))/3 := by unfold chi; ring
  rw [e,abs_div,abs_mul]
  norm_num
  nlinarith only [mul_le_mul_of_nonneg_left lin (abs_nonneg U),small_U osc]

private theorem remJ_estimate {U w a b p t : ℝ} (osc : (U^2/2)^2+w^2=1) (unit : a^2+b^2=1)
    (normP : |p|≤1) (cross : |a*b|≤t) :
    |remJ U w a b p| ≤ 1.415*(1/6+(3/4)*t) := by
  let u:=U^2/2
  have uc : u^2+w^2=1 := osc
  have e₁ : |a^2/3+b^2/12|≤1/3 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith only [unit,sq_nonneg b]
  have e₂ : |u^2/2+3*w^2/4|≤3/4 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith only [uc,sq_nonneg u]
  have l := mul_le_mul (abs_coords uc).2.2 e₁ (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
  have rr := mul_le_mul e₂ cross (abs_nonneg _) (by norm_num : (0:ℝ)≤3/4)
  have core : |-(u*w)*(a^2/3+b^2/12)+(u^2/2+3*w^2/4)*(a*b)| ≤ 1/6+(3/4)*t := by
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_neg,abs_mul (u^2/2+3*w^2/4)]
    linarith
  have factor := mul_le_mul normP (small_U osc) (abs_nonneg _) zero_le_one
  have e : remJ U w a b p = p*U*(-(u*w)*(a^2/3+b^2/12)+(u^2/2+3*w^2/4)*(a*b)) := by
    unfold remJ; dsimp [u]; ring
  rw [e,abs_mul,abs_mul p U]
  exact mul_le_mul (by simpa using factor) core (abs_nonneg _) (by norm_num)

theorem remJ_bound {U w a b p : ℝ} (osc : (U^2/2)^2+w^2=1) (unit : a^2+b^2=1)
    (normP : |p|≤1) : |remJ U w a b p| < 0.77 := by
  exact (remJ_estimate osc unit normP (abs_coords unit).2.2).trans_lt (by norm_num)

theorem remJ_small_bound {U w a b p : ℝ} (osc : (U^2/2)^2+w^2=1) (unit : a^2+b^2=1)
    (normP : |p|≤1) (cross : |b|≤0.121) : |remJ U w a b p| < 0.37 := by
  have t : |a*b|≤0.121 := by
    rw [abs_mul]
    simpa using mul_le_mul (abs_coords unit).1 cross (abs_nonneg _) zero_le_one
  exact (remJ_estimate osc unit normP t).trans_lt (by norm_num)

theorem remH_bound {U w a b p : ℝ} (osc : (U^2/2)^2+w^2=1) (unit : a^2+b^2=1)
    (normP : |p|≤1) : |remH U w a b p| < 1.66 := by
  let u:=U^2/2
  have uc : u^2+w^2=1 := osc
  have ux := abs_coords uc
  have dual : (-u)^2+w^2=1 := by nlinarith only [uc]
  have lin := dot_le_one dual (double_unit unit)
  have e0 : |p^2-(1+a^2)/3|≤2/3 := by
    obtain ⟨pl,pr⟩:=abs_le.mp normP
    have p2 : p^2≤1 := by nlinarith [mul_nonneg (by linarith : 0≤1-p) (by linarith : 0≤1+p)]
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg b,sq_nonneg p],by nlinarith [sq_nonneg a]⟩
  let D:=4*U*w*a*b/3+U^3*(b^2-a^2)/3
  have de : D=2*(U*((-u)*(a^2-b^2)+w*(2*a*b)))/3 := by dsimp [D,u]; ring
  have dbd : |D|≤0.944 := by
    rw [de,abs_div,abs_mul,abs_mul U]
    norm_num
    simp only [neg_mul] at lin
    linarith [mul_le_mul_of_nonneg_left lin (abs_nonneg U),small_U osc]
  have f1 := mul_le_mul (mul_le_mul e0 (small_U osc) (abs_nonneg _) (by norm_num : (0:ℝ)≤2/3))
    normP (abs_nonneg _) (by norm_num : (0:ℝ)≤(2/3)*1.415)
  have f2 := mul_le_mul (mul_le_mul normP ux.1 (abs_nonneg _) zero_le_one)
    dbd (abs_nonneg _) (by norm_num : (0:ℝ)≤1*1)
  have f3 := mul_le_mul (mul_le_mul (chi_bound osc unit) normP (abs_nonneg _) (by norm_num : (0:ℝ)≤0.472))
    ux.2.1 (abs_nonneg _) (by norm_num : (0:ℝ)≤0.472*1)
  change |(-((p^2-(1+a^2)/3)*U*p/2) + p*u*D - chi U w a b*p*w/2)| < _
  rw [sub_eq_add_neg (-((p^2-(1+a^2)/3)*U*p/2) + p*u*D)]
  apply (abs_add_le ..).trans_lt
  have t := abs_add_le (-((p^2-(1+a^2)/3)*U*p/2)) (p*u*D)
  simp only [abs_neg,abs_mul,abs_div] at t ⊢
  norm_num at t ⊢
  linarith only [t,f1,f2,f3]

namespace Orbit
variable (z : Orbit)

/-- Uniform bounds on the errors in both derivatives for each actual frozen
polynomial trajectory at every arclength with positive stress amplitude. -/
theorem corrector_rates_bounded (s : ℝ) (A : 0<z.amplitude s) :
    |deriv (correctedImpact z.root z.shape z.slope z.along z.across) s|
        < 0.77/z.root s^4 ∧
    |deriv (correctedOutgoing z.root z.shape z.slope z.along z.across) s
        -(1+z.along s^2)/3| < 1.66/z.root s^3 := by
  have rates := z.normalized_rates s A
  have osc : z.slope s^2+(z.shape s^2/2)^2=1 := by linarith only [rates.oscillator]
  have p := dot_le_one osc rates.unit
  rw [(z.corrected_impact_rate s A).deriv,(z.corrected_outgoing_rate s A).deriv,
    add_sub_cancel_left]
  constructor
  · rw [abs_div,abs_of_pos (pow_pos rates.pos 4)]
    exact div_lt_div_of_pos_right (remJ_bound rates.oscillator rates.unit p) (pow_pos rates.pos 4)
  · rw [abs_div,abs_of_pos (pow_pos rates.pos 3)]
    exact div_lt_div_of_pos_right (remH_bound rates.oscillator rates.unit p) (pow_pos rates.pos 3)

theorem corrector_impact_small (s : ℝ) (A : 0<z.amplitude s) (across : |z.across s| ≤ 0.121) :
    |deriv (correctedImpact z.root z.shape z.slope z.along z.across) s| < 0.37/z.root s^4 := by
  have rates := z.normalized_rates s A
  have osc : z.slope s^2+(z.shape s^2/2)^2=1 := by linarith only [rates.oscillator]
  rw [(z.corrected_impact_rate s A).deriv,abs_div,abs_of_pos (pow_pos rates.pos 4)]
  exact div_lt_div_of_pos_right (remJ_small_bound rates.oscillator rates.unit
    (dot_le_one osc rates.unit) across) (pow_pos rates.pos 4)

end Orbit
end ClosedSimilarity.FrozenStress
