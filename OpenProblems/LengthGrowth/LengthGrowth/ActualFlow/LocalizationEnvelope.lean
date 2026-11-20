import LengthGrowth.ActualFlow.LocalizationClock
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

private theorem common_window (hf : c.IsNormalFEF) : ∃ m>0,∀t≥1,m≤c.length t := by
  have hp := c.energy_pos (by norm_num : (0:ℝ)≤1)
  refine ⟨1/c.energy 1,one_div_pos.mpr hp,?_⟩
  intro t ht
  have tp : 0≤t := by linarith
  have e := c.energy_le_of_le hf (by norm_num : (0:ℝ)≤1) ht
  have h := c.sharp_energy_length tp
  apply (div_le_iff₀ hp).mpr
  nlinarith only [h,mul_le_mul_of_nonneg_right e (c.length_nonneg t),
    Real.pi_gt_three,sq_nonneg (Real.pi-3)]

private theorem initial_mass_bound : ∃U : ℝ, 0<U ∧ ∀(l : ℂ →L[ℝ] ℝ), (∀z,|l z|≤‖z‖) →
    ∀a : ℝ,0<a → a≤1 → c.interior.materialExponentialMass l a 1≤U := by
  let x := c.position 1
  have sm := c.position_slice_smooth (by norm_num : (0:ℝ)≤1)
  have reg := c.immersion 1 (by norm_num)
  have cx : Continuous x := sm.continuous
  obtain ⟨u,_,mx⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr c.period_pos.le) cx.norm.continuousOn
  let R := ‖x u‖
  let f := fun w => Real.exp R*(curvature x w^2/2+1)*speed x w
  have ck := (curvature_smooth sm reg).continuous
  have cg := (speed_smooth sm reg).continuous
  have cf : Continuous f := by dsimp only [f,x]; fun_prop
  refine ⟨max 1 (∫y in 0..c.period,f y), lt_of_lt_of_le (by norm_num) (le_max_left ..),?_⟩
  intro l hl a ha a1
  apply le_trans _ (le_max_right ..)
  let mass := fun w => Real.exp (a*l (x w))*(curvature x w^2/2+a^2)*speed x w
  have cm : Continuous mass := by dsimp only [mass,x]; fun_prop
  apply intervalIntegral.integral_mono_on (μ:=volume) c.period_pos.le (cm.intervalIntegrable _ _) (cf.intervalIntegrable _ _)
  intro w hw
  have hr : l (x w)≤R := (le_abs_self _).trans ((hl _).trans (mx hw))
  have sin : a*l (x w)≤R := (mul_le_mul_of_nonneg_left hr ha.le).trans
    (by simpa using mul_le_mul_of_nonneg_right a1 (norm_nonneg (x u)))
  dsimp only [mass,f]
  apply mul_le_mul_of_nonneg_right _ (speed_pos reg _).le
  apply mul_le_mul (Real.exp_le_exp.mpr sin) _ (by positivity) (Real.exp_pos _).le
  nlinarith only [mul_self_le_mul_self ha.le a1]

private theorem finite_log_mass (hf : c.IsNormalFEF) (l : ℂ →L[ℝ] ℝ) (hl : ∀z,|l z|≤‖z‖)
    {a : ℝ} (ap : 0<a) {m : ℝ} (mp : 0<m) (ml : ∀t≥1,m≤c.length t) {t : ℝ} (ht : 1≤t) :
    Real.log (c.interior.materialExponentialMass l a t) ≤
      Real.log (c.interior.materialExponentialMass l a 1)+256*(a^4*t+a^2*c.localizationClock t) := by
  let Q := c.interior.materialExponentialMass l a
  let W := fun x => Real.log (Q x)-256*(a^4*x+a^2*c.localizationClock x)
  have dQ {x : ℝ} (hx : 1≤x) : DifferentiableAt ℝ Q x :=
    (c.interior.materialExponentialMass_hasDerivAt (c.interior_isNormalFEF hf) l a
      (show x∈Ioi (0:ℝ) by change 0<x; linarith)).differentiableAt
  have qp {x : ℝ} (hx : 1≤x) : 0<Q x := by
    have dx := c.interior.material_exponential_detection (show x∈Ioi (0:ℝ) by change 0<x; linarith)
      l hl ap.le mp.le (ml x hx) 0
    exact lt_of_lt_of_le (by positivity) dx
  have derivW {x : ℝ} (hx : 1≤x) : HasDerivAt W (deriv Q x/Q x-
      256*(a^4+a^2*c.localizationDensity x)) x := by
    convert! (((dQ hx).hasDerivAt.log (qp hx).ne').sub
      ((((hasDerivAt_id x).const_mul (a^4)).add ((c.localizationClock_hasDerivAt x).const_mul (a^2))).const_mul 256)) using 1
    ring
  have mono : AntitoneOn W (Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) (fun x hx => (derivW hx).continuousAt.continuousWithinAt)
    · rw [interior_Ici]
      exact fun x hx => (derivW (mem_Ioi.mp hx).le).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      have x1 := (mem_Ioi.mp hx).le
      have x0 : x∈Ioi (0:ℝ) := (by change 0<x; linarith)
      have br : ∀u∈Icc 0 c.period, |curvature (c.position x) u|≤Real.sqrt (c.localizationDensity x) := by
        intro u _
        apply (Real.le_sqrt (abs_nonneg _) (c.localizationDensity_nonneg x)).mpr
        rw [sq_abs]; exact c.curvature_sq_le_localizationDensity x1 u
      have rate := c.interior.material_exponential_rate (c.interior_isNormalFEF hf) l hl a
        (Real.sqrt (c.localizationDensity x)) x0 br
      rw [Real.sq_sqrt (c.localizationDensity_nonneg x)] at rate
      rw [(derivW x1).deriv]
      exact sub_nonpos.mpr ((div_le_iff₀ (qp x1)).mpr rate)
  have e := mono (show (1:ℝ)∈Ici 1 from mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  dsimp only [W,Q] at e
  have z : c.localizationClock 1=0 := intervalIntegral.integral_same
  rw [z] at e
  linarith only [e,show 0≤a^4 by positivity]

/-- A common finite-time exponential envelope for the norm of every material
point, valid for every admissible exponential weight. -/
theorem localization_position_envelope (hf : c.IsNormalFEF) : ∃C : ℝ,∀t≥1,∀a : ℝ,0<a → a≤1 →
    ∀u : ℝ,a*‖c.position t u‖≤C-2*Real.log a+256*(a^4*t+a^2*c.localizationClock t) := by
  obtain ⟨m,mp,ml⟩ := c.common_window hf
  obtain ⟨U,up,init⟩ := c.initial_mass_bound
  refine ⟨m+Real.log U-Real.log m,?_⟩
  intro t ht a ap a1 u
  let y := c.position t u
  let v := ‖y‖⁻¹ • y
  let l := innerSL ℝ v
  have vn : ‖v‖≤1 := by
    dsimp only [v]; rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg y)]
    by_cases h : ‖y‖=0 <;> simp [h]
  have hl (z : ℂ) : |l z|≤‖z‖ := (abs_real_inner_le_norm v z).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right vn (norm_nonneg z))
  have hval : l (c.position t u)=‖c.position t u‖ := by
    change inner ℝ (‖y‖⁻¹ • y) y=‖y‖
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    by_cases h : ‖y‖=0
    · simp [h]
    · field_simp
  have qp (x : ℝ) (hx : 1≤x) := c.interior.material_exponential_detection
    (show x∈Ioi (0:ℝ) by change 0<x; linarith) l hl ap.le mp.le (ml x hx) u
  have q1 := qp 1 le_rfl
  have q1p : 0<c.interior.materialExponentialMass l a 1 := lt_of_lt_of_le (by positivity) q1
  have e1 := Real.log_le_log q1p (init l hl a ap a1)
  have fin := c.finite_log_mass hf l hl ap mp ml ht
  have det := qp t ht
  change m*a^2*Real.exp (a*(l (c.position t u)-m))≤_ at det
  rw [hval] at det
  have elog := Real.log_le_log (show 0<m*a^2*Real.exp (a*(‖c.position t u‖-m)) by positivity) det
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',Real.log_mul mp.ne' (by positivity),
    Real.log_pow,Real.log_exp] at elog
  norm_num only [Nat.cast_ofNat] at elog
  nlinarith only [elog,e1,fin,mul_le_mul_of_nonneg_right a1 mp.le]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.localization_position_envelope
