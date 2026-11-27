import LengthGrowth.ActualFlow.SpatialLocalization
import LengthGrowth.ActualFlow.RadiusMomentClock

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- A finite-horizon estimate for the full image at every earlier physical
time, retaining the value of the physical curvature clock at the horizon. -/
theorem radius_prefix_clock_bound (hf : c.IsNormalFEF) (O : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → 1 ≤ Real.log t → c.localizationClock t ≤ t^2 →
      ∀ s ∈ Icc 1 t, c.fixedOriginRadius O s ≤ C * Real.log t *
        max 1 (max (Real.sqrt (Real.sqrt (t / Real.log t)))
                   (Real.sqrt (c.localizationClock t / Real.log t))) := by
  obtain ⟨C,est⟩ := c.localization_position_envelope hf
  refine ⟨|C|+‖O‖+515,by positivity,?_⟩
  intro t t1 h1 bt s hs
  let H:=Real.log t
  let B:=c.localizationClock t
  let x:=Real.sqrt (Real.sqrt (t/H))
  let y:=Real.sqrt (B/H)
  let v:=max 1 (max x y)
  have tp : 0<t := by linarith
  have hp : 0<H := lt_of_lt_of_le zero_lt_one h1
  have bp : 0≤B := intervalIntegral.integral_nonneg_of_forall t1 c.localizationDensity_nonneg
  have xp : 0≤x := Real.sqrt_nonneg _
  have yp : 0≤y := Real.sqrt_nonneg _
  have x4 : x^4=t/H := by
    calc
      _ = (x^2)^2 := by ring
      _ = _ := by dsimp [x];rw [Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt (div_nonneg tp.le hp.le)]
  have y2 : y^2=B/H := Real.sq_sqrt (div_nonneg bp hp.le)
  have v1 : 1≤v := le_max_left _ _
  have vp : 0<v := zero_lt_one.trans_le v1
  have xv : x≤v := (le_max_left _ _).trans (le_max_right _ _)
  have yv : y≤v := (le_max_right _ _).trans (le_max_right _ _)
  have vt : v≤t := by
    refine max_le t1 (max_le ?_ ?_)
    · have t4 : t≤t^4 := by
        simpa only [pow_one] using pow_le_pow_right₀ t1 (by norm_num : (1:ℕ)≤4)
      have h4 : x^4≤t^4 := by rw [x4];exact (div_le_self tp.le h1).trans t4
      exact (pow_le_pow_iff_left₀ xp tp.le (by norm_num : (4:ℕ)≠0)).mp h4
    · have h2 : y^2≤t^2 := by rw [y2];exact (div_le_self bp h1).trans bt
      exact (pow_le_pow_iff_left₀ yp tp.le (by norm_num : (2:ℕ)≠0)).mp h2
  let a:=1/v
  have ap : 0<a := one_div_pos.mpr vp
  have a1 : a≤1 := (div_le_one vp).mpr v1
  have av : a*v=1 := by dsimp [a];field_simp
  have xt : t≤H*v^4 := by
    have eq := (div_eq_iff hp.ne').mp x4.symm
    nlinarith only [eq,mul_le_mul_of_nonneg_right (pow_le_pow_left₀ xp xv 4) hp.le]
  have yb : B≤H*v^2 := by
    have eq := (div_eq_iff hp.ne').mp y2.symm
    nlinarith only [eq,mul_le_mul_of_nonneg_right (pow_le_pow_left₀ yp yv 2) hp.le]
  have aa : a^4*s≤H := by
    calc
      _ ≤ a^4*t := mul_le_mul_of_nonneg_left hs.2 (pow_nonneg ap.le _)
      _ ≤ a^4*(H*v^4) := mul_le_mul_of_nonneg_left xt (pow_nonneg ap.le _)
      _ = H := by dsimp [a];field_simp
  have bs : c.localizationClock s≤B := by
    have z := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      (c.localizationDensity_continuous.intervalIntegrable 1 s)
      (c.localizationDensity_continuous.intervalIntegrable s t)
    have n := intervalIntegral.integral_nonneg_of_forall (μ:=volume) hs.2 c.localizationDensity_nonneg
    dsimp [B,localizationClock];linarith only [z,n]
  have ab : a^2*c.localizationClock s≤H := by
    calc
      _ ≤ a^2*(H*v^2) := mul_le_mul_of_nonneg_left (bs.trans yb) (sq_nonneg _)
      _ = H := by dsimp [a];field_simp
  have loga : -H≤Real.log a := by simpa [a,H] using neg_le_neg (Real.log_le_log vp vt)
  obtain ⟨u,_,uval⟩:=c.fixedOriginRadius_attained O (by linarith [hs.1] : 0≤s)
  have h:=est s hs.1 a ap a1 u
  have hu:=norm_sub_le (c.position s u) O
  have cc : C≤ |C| * H := (le_abs_self _).trans (by simpa using mul_le_mul_of_nonneg_left h1 (abs_nonneg C))
  have oo : a*‖O‖≤‖O‖*H := (by
    calc
      _ ≤ ‖O‖ := by simpa using mul_le_mul_of_nonneg_right a1 (norm_nonneg O)
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left h1 (norm_nonneg O))
  rw [uval]
  change _ ≤ (|C|+‖O‖+515)*H*v
  apply (mul_le_mul_iff_right₀ ap).mp
  calc
    _ ≤ (|C|+‖O‖+515)*H := by nlinarith only [h,mul_le_mul_of_nonneg_left hu ap.le,cc,oo,aa,ab,loga,hp]
    _ = _ := by rw [show a*((|C|+‖O‖+515)*H*v)=(|C|+‖O‖+515)*H*(a*v) by ring,av,mul_one]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.radius_prefix_clock_bound
