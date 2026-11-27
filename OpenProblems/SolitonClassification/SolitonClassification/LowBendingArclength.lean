import SolitonClassification.NoClosedTranslators
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Spatial estimates for the independent classification project. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.LowBending

structure ClosedFrenetCurve where
  period : ℝ
  period_pos : 0 < period
  curve : ℝ → ℂ
  tangent : ℝ → ℂ
  curvature : ℝ → ℝ
  curvature₁ : ℝ → ℝ
  curvature₂ : ℝ → ℝ
  curve_periodic : Function.Periodic curve period
  tangent_periodic : Function.Periodic tangent period
  curvature_periodic : Function.Periodic curvature period
  curvature₁_periodic : Function.Periodic curvature₁ period
  curve_deriv : ∀ s, HasDerivAt curve (tangent s) s
  tangent_deriv : ∀ s, HasDerivAt tangent
    ((curvature s : ℂ) * (Complex.I * tangent s)) s
  curvature_deriv : ∀ s, HasDerivAt curvature (curvature₁ s) s
  curvature₁_deriv : ∀ s, HasDerivAt curvature₁ (curvature₂ s) s
  curvature₂_continuous : Continuous curvature₂
  tangent_unit : ∀ s, ‖tangent s‖ = 1

namespace ClosedFrenetCurve

variable (c : ClosedFrenetCurve)

def normal (s : ℝ) : ℂ := Complex.I * c.tangent s
def force (s : ℝ) : ℝ := c.curvature₂ s + c.curvature s ^ 3 / 2
def stress (s : ℝ) : ℂ :=
  ((c.curvature s : ℂ) ^ 2 / 2) * c.tangent s +
    (c.curvature₁ s : ℂ) * c.normal s
theorem tangent_continuous : Continuous c.tangent :=
  continuous_iff_continuousAt.mpr fun s => (c.tangent_deriv s).continuousAt

theorem curvature_continuous : Continuous c.curvature :=
  continuous_iff_continuousAt.mpr fun s => (c.curvature_deriv s).continuousAt

theorem curvature₁_continuous : Continuous c.curvature₁ :=
  continuous_iff_continuousAt.mpr fun s => (c.curvature₁_deriv s).continuousAt

theorem normal_deriv (s : ℝ) :
    HasDerivAt c.normal (-(c.curvature s : ℂ) * c.tangent s) s := by
  convert! (c.tangent_deriv s).const_mul Complex.I using 1
  calc
    _ = (Complex.I * Complex.I) * ((c.curvature s : ℂ) * c.tangent s) := by
      rw [Complex.I_mul_I]; ring
    _ = _ := by ring

theorem normal_unit (s : ℝ) : ‖c.normal s‖ = 1 := by
  simp [normal, c.tangent_unit]

theorem force_continuous : Continuous c.force := by
  exact c.curvature₂_continuous.add ((c.curvature_continuous.pow 3).div_const 2)

theorem stress_deriv (s : ℝ) :
    HasDerivAt c.stress ((c.force s : ℂ) * c.normal s) s := by
  have hk := (c.curvature_deriv s).ofReal_comp
  have hk₁ := (c.curvature₁_deriv s).ofReal_comp
  convert! (((hk.mul hk).div_const 2).mul (c.tangent_deriv s)).add
    (hk₁.mul (c.normal_deriv s)) using 1
  · funext x
    simp [stress, pow_two]
  · simp only [force, normal, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_ofNat, Pi.mul_apply]
    ring

theorem stress_continuous : Continuous c.stress :=
  continuous_iff_continuousAt.mpr fun s => (c.stress_deriv s).continuousAt

theorem tangent_integral_zero : (∫ s in 0..c.period, c.tangent s) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => c.curve_deriv s) (c.tangent_continuous.intervalIntegrable _ _)]
  have h := c.curve_periodic 0
  simpa using sub_eq_zero.mpr (by simpa using h)

theorem stress_factor (s : ℝ) : c.stress s =
    ((c.curvature s : ℂ)^2 / 2 + (c.curvature₁ s : ℂ) * Complex.I) *
      c.tangent s := by
  dsimp [stress, normal]
  ring

theorem tangent_mul_star (s : ℝ) :
    c.tangent s * star (c.tangent s) = 1 := by
  change c.tangent s * conj (c.tangent s) = 1
  rw [Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, c.tangent_unit]

theorem tangent_mul_star_stress (s : ℝ) :
    c.tangent s * star (c.stress s) =
      (c.curvature s : ℂ)^2 / 2 - (c.curvature₁ s : ℂ) * Complex.I := by
  change c.tangent s * conj (c.stress s) = _
  rw [c.stress_factor]
  simp only [map_mul, map_add, map_div₀, map_pow, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  calc
    _ = ((c.curvature s : ℂ)^2 / 2 - (c.curvature₁ s : ℂ) * Complex.I) *
        (c.tangent s * conj (c.tangent s)) := by ring
    _ = _ := by
      have h := c.tangent_mul_star s
      change c.tangent s * conj (c.tangent s) = 1 at h
      rw [h]; ring

end ClosedFrenetCurve
theorem interval_integral_mul_sq_le {f g : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hab : a ≤ b) :
    (∫ s in a..b, f s * g s)^2 ≤
      (∫ s in a..b, f s ^ 2) * (∫ s in a..b, g s ^ 2) := by
  let A := ∫ s in a..b, f s ^ 2
  let B := ∫ s in a..b, f s * g s
  let C := ∫ s in a..b, g s ^ 2
  have hpoly : ∀ t : ℝ, 0 ≤ C * (t*t) + (2*B)*t + A := by
    intro t
    have hpos : 0 ≤ ∫ s in a..b, (f s + t * g s)^2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun s => sq_nonneg _)
    have heq : (fun s => (f s + t*g s)^2) =
        (fun s => f s^2 + (2*t)*(f s*g s) + (t*t)*(g s^2)) := by
      funext s
      ring
    rw [heq, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hpos
    · dsimp [A, B, C]
      nlinarith
    · exact (hf.pow 2).intervalIntegrable _ _
    · exact ((hf.mul hg).const_mul (2*t)).intervalIntegrable _ _
    · exact ((hf.pow 2).add ((hf.mul hg).const_mul (2*t))).intervalIntegrable _ _
    · exact ((hg.pow 2).const_mul (t*t)).intervalIntegrable _ _
  have hdisc := discrim_le_zero hpoly
  dsimp [discrim] at hdisc
  change B^2 ≤ A*C
  nlinarith


end ClosedSimilarity.LowBending
namespace ClosedSimilarity.LowBending

theorem periodic_wirtinger {L : ℝ} (hL : 0<L) (f g : ℝ → ℂ) (hper : f L = f 0)
    (hf : ∀ s, HasDerivAt f (g s) s) (hg : Continuous g)
    (hmean : (∫ s in 0..L, f s) = 0) :
    (2*Real.pi)^2 * (∫ s in 0..L, ‖f s‖^2) ≤ L^2 * (∫ s in 0..L, ‖g s‖^2) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  have lp (v : ℝ → ℂ) (hv : Continuous v) : MemLp v 2 (volume.restrict (Ioc 0 L)) := by
    apply (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr
    exact ((hv.norm.pow 2).intervalIntegrable 0 L).1
  have point (n : ℤ) : (2*Real.pi)^2 * ‖fourierCoeffOn hL f n‖^2 ≤
      L^2 * ‖fourierCoeffOn hL g n‖^2 := by
    by_cases hn : n=0
    · subst n
      have hz : fourierCoeffOn hL f 0 = 0 := by
        rw [fourierCoeffOn_eq_integral]; simp [hmean]
      rw [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero]
      positivity
    · have h := fourierCoeffOn_of_hasDerivAt hL hn (fun x _ => hf x) (hg.intervalIntegrable _ _)
      rw [hper,sub_self,mul_zero,zero_sub] at h
      have eqn := congrArg norm h
      simp only [norm_mul,norm_div,norm_one,norm_neg,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_I,mul_one,Complex.norm_intCast,abs_of_pos hL,abs_of_pos Real.pi_pos,
        Complex.ofReal_zero,sub_zero,Complex.norm_ofNat] at eqn
      have hnat : (1:ℝ) ≤ |(n:ℝ)| := by
        exact_mod_cast Int.one_le_abs hn
      have hprod : ‖fourierCoeffOn hL f n‖ * (2*Real.pi*|(n:ℝ)|) =
          L * ‖fourierCoeffOn hL g n‖ := by
        rw [eqn]
        field_simp [Real.pi_ne_zero, (by linarith : |(n:ℝ)| ≠ 0)]
      have hp : (2*Real.pi)*‖fourierCoeffOn hL f n‖ ≤ L*‖fourierCoeffOn hL g n‖ := by
        rw [← hprod]
        nlinarith only [mul_le_mul_of_nonneg_left hnat (show 0 ≤ (2*Real.pi)*‖fourierCoeffOn hL f n‖ by positivity)]
      simpa [mul_pow] using pow_le_pow_left₀ (by positivity) hp 2
  have bound := hasSum_le point
    ((hasSum_sq_fourierCoeffOn hL (lp f hc)).mul_left ((2*Real.pi)^2))
    ((hasSum_sq_fourierCoeffOn hL (lp g hg)).mul_left (L^2))
  simp only [sub_zero, smul_eq_mul] at bound
  apply (le_of_mul_le_mul_left (a:=L⁻¹) _ (inv_pos.mpr hL))
  linarith only [bound,show L⁻¹ * ((2*Real.pi)^2 * (∫ s in 0..L, ‖f s‖^2)) =
        (2*Real.pi)^2 * (L⁻¹ * (∫ s in 0..L, ‖f s‖^2)) by ring,
    show L⁻¹*(L^2*(∫ s in 0..L, ‖g s‖^2))=L^2*(L⁻¹*(∫ s in 0..L, ‖g s‖^2)) by ring]

end ClosedSimilarity.LowBending
namespace ClosedSimilarity.LowBending.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)
theorem stress_periodic : Function.Periodic c.stress c.period := by
  intro s
  simp only [stress, normal, c.curvature_periodic s, c.curvature₁_periodic s,
    c.tangent_periodic s]

def energy : ℝ := (∫ s in 0..c.period, c.curvature s ^ 2) / 2
def dissipation : ℝ := ∫ s in 0..c.period, c.force s ^ 2
def curvatureGradientSquare : ℝ := ∫ s in 0..c.period, c.curvature₁ s ^ 2

theorem curvature_gradient_identity : c.curvatureGradientSquare =
    (∫ s in 0..c.period, c.curvature s^4)/2 -
      (∫ s in 0..c.period, c.curvature s*c.force s) := by
  have hk := c.curvature_continuous
  have hk₁ := c.curvature₁_continuous
  have hk₂ := c.curvature₂_continuous
  have hd : ∀ s, HasDerivAt (fun u => c.curvature u*c.curvature₁ u)
      (c.curvature₁ s*c.curvature₁ s+c.curvature s*c.curvature₂ s) s := by
    intro s
    exact (c.curvature_deriv s).mul (c.curvature₁_deriv s)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) (((hk₁.mul hk₁).add (hk.mul hk₂)).intervalIntegrable 0 c.period)
  have hp : c.curvature c.period = c.curvature 0 := by
    simpa using c.curvature_periodic 0
  have hp₁ : c.curvature₁ c.period = c.curvature₁ 0 := by
    simpa using c.curvature₁_periodic 0
  rw [hp, hp₁, sub_self, intervalIntegral.integral_add
    (f := fun s => c.curvature₁ s*c.curvature₁ s)
    (g := fun s => c.curvature s*c.curvature₂ s)
    ((hk₁.mul hk₁).intervalIntegrable _ _) ((hk.mul hk₂).intervalIntegrable _ _)] at hi
  have heq : (fun s => c.curvature s*c.force s) =
      (fun s => c.curvature s*c.curvature₂ s+(1/2:ℝ)*c.curvature s^4) := by
    funext s
    dsimp [force]
    ring
  rw [heq, intervalIntegral.integral_add
    (f := fun s => c.curvature s*c.curvature₂ s)
    (g := fun s => (1/2:ℝ)*c.curvature s^4)
    ((hk.mul hk₂).intervalIntegrable _ _)
    (((hk.pow 4).const_mul (1/2)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  dsimp [curvatureGradientSquare]
  simp only [← pow_two] at hi
  linarith

def arclengthCentroid : ℂ := c.period⁻¹ • (∫ s in 0..c.period, c.curve s)

private theorem sharp_tangent_norm_integral : (∫ s in 0..c.period, ‖c.tangent s‖^2)=c.period := by
  simp [c.tangent_unit]

theorem sharp_energy_length : 2*Real.pi^2 ≤ c.energy*c.period := by
  let g := fun s => (c.curvature s : ℂ)*c.normal s
  have hn : Continuous c.normal := continuous_iff_continuousAt.mpr (fun s => (c.normal_deriv s).continuousAt)
  have hg : Continuous g := (Complex.continuous_ofReal.comp c.curvature_continuous).mul hn
  have h := periodic_wirtinger c.period_pos c.tangent g (by simpa using c.tangent_periodic 0)
    c.tangent_deriv hg c.tangent_integral_zero
  have hi : (∫ s in 0..c.period, ‖g s‖^2)=2*c.energy := by
    unfold energy
    rw [show ∀ z:ℝ, 2*(z/2)=z by intro z; ring]
    apply intervalIntegral.integral_congr
    intro s _
    simp [g,c.normal_unit,Real.norm_eq_abs,sq_abs]
  rw [c.sharp_tangent_norm_integral,hi] at h
  by_contra! hn
  nlinarith only [h,mul_pos c.period_pos (sub_pos.mpr hn)]

private theorem stress_inner_tangent (s : ℝ) :
    inner ℝ (c.stress s) (c.tangent s)=(c.curvature s)^2/2 := by
  have h := congrArg Complex.re (c.tangent_mul_star_stress s)
  change (c.tangent s*star (c.stress s)).re=_
  rw [h]
  norm_num [← Complex.ofReal_pow]

/-- About every fixed point, the true force paired with centered normal
support integrates to minus the bending energy. -/
theorem centered_dilation_virial (z : ℂ) :
    (∫ s in 0..c.period, c.force s*inner ℝ (c.normal s) (c.curve s-z))= -c.energy := by
  let g := fun s => c.force s*inner ℝ (c.normal s) (c.curve s-z)
  have hc : Continuous c.curve := continuous_iff_continuousAt.mpr (fun s => (c.curve_deriv s).continuousAt)
  have hn : Continuous c.normal := continuous_iff_continuousAt.mpr (fun s => (c.normal_deriv s).continuousAt)
  have hg : Continuous g := c.force_continuous.mul (hn.inner (hc.sub continuous_const))
  have hD (s : ℝ) : HasDerivAt (fun u => inner ℝ (c.stress u) (c.curve u-z))
      (g s+(c.curvature s)^2/2) s := by
    apply ((c.stress_deriv s).inner ℝ ((c.curve_deriv s).sub_const z)).congr_deriv
    rw [← Complex.real_smul,real_inner_smul_left,c.stress_inner_tangent]
    exact add_comm _ _
  have hs := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := c.period)
    (fun s _ => hD s) ((hg.add ((c.curvature_continuous.pow 2).div_const 2)).intervalIntegrable _ _)
  have hper := c.stress_periodic 0
  have hpos := c.curve_periodic 0
  simp only [zero_add] at hper hpos
  rw [hper,hpos,sub_self,intervalIntegral.integral_add (f := g) (g := fun s => c.curvature s^2/2) (hg.intervalIntegrable _ _)
    (((c.curvature_continuous.pow 2).div_const 2).intervalIntegrable _ _),intervalIntegral.integral_div] at hs
  change (∫ s in 0..c.period, g s) = -((∫ s in 0..c.period, c.curvature s^2)/2)
  linarith

theorem sharp_virial : 4*Real.pi^2*c.energy^2 ≤ c.dissipation*c.period^3 := by
  let y := fun s => c.curve s-c.arclengthCentroid
  let p := fun s => inner ℝ (c.normal s) (y s)
  have hc : Continuous c.curve := continuous_iff_continuousAt.mpr (fun s => (c.curve_deriv s).continuousAt)
  have hy : Continuous y := hc.sub continuous_const
  have hn : Continuous c.normal := continuous_iff_continuousAt.mpr (fun s => (c.normal_deriv s).continuousAt)
  have hp : Continuous p := hn.inner hy
  have hz : (∫ s in 0..c.period, y s)=0 := by
    unfold y arclengthCentroid
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const,sub_zero,smul_smul,mul_inv_cancel₀ c.period_pos.ne',one_smul,sub_self]
  have hmean := periodic_wirtinger c.period_pos y c.tangent
    (by dsimp [y]; rw [show c.curve c.period = c.curve 0 by simpa using c.curve_periodic 0])
    (fun s => (c.curve_deriv s).sub_const _) c.tangent_continuous hz
  rw [c.sharp_tangent_norm_integral] at hmean
  have hv : (∫ s in 0..c.period, c.force s*p s)= -c.energy := c.centered_dilation_virial _
  have hcs := interval_integral_mul_sq_le c.force_continuous hp c.period_pos.le
  change (∫ s in 0..c.period, c.force s*p s)^2 ≤ c.dissipation*(∫ s in 0..c.period, p s^2) at hcs
  rw [hv,neg_sq] at hcs
  have hproj : (∫ s in 0..c.period, p s^2) ≤ ∫ s in 0..c.period, ‖y s‖^2 := by
    apply intervalIntegral.integral_mono_on c.period_pos.le ((hp.pow 2).intervalIntegrable _ _)
      ((hy.norm.pow 2).intervalIntegrable _ _)
    intro s _
    have h := abs_real_inner_le_norm (c.normal s) (y s)
    rw [c.normal_unit,one_mul] at h
    change p s ^ 2 ≤ ‖y s‖^2
    rw [← sq_abs (p s)]
    exact pow_le_pow_left₀ (abs_nonneg (p s)) h 2
  have hD : 0≤c.dissipation := intervalIntegral.integral_nonneg_of_forall c.period_pos.le (fun s => sq_nonneg _)
  have h1 := hcs.trans (mul_le_mul_of_nonneg_left hproj hD)
  have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (2*Real.pi))
  have h3 := mul_le_mul_of_nonneg_left hmean hD
  nlinarith only [h2,h3]

theorem energy_pos : 0<c.energy := by
  exact pos_of_mul_pos_left ((by positivity : 0<2*Real.pi^2).trans_le c.sharp_energy_length) c.period_pos.le
def growthResidual (s : ℝ) : ℝ := c.force s-c.energy/(2*c.period)*c.curvature s

theorem growthResidual_continuous : Continuous c.growthResidual :=
  c.force_continuous.sub (c.curvature_continuous.const_mul _)

theorem growthResidual_square :
    (∫s in 0..c.period,c.growthResidual s^2) = c.dissipation -
      (2*(c.energy/(2*c.period)))*(∫s in 0..c.period,c.curvature s*c.force s)+
      (c.energy/(2*c.period))^2*(2*c.energy) := by
  let b := c.energy/(2*c.period)
  have hk := c.curvature_continuous
  have hf := c.force_continuous
  have mixed := (hk.mul hf).const_mul (2*b)
  have curv := (hk.pow 2).const_mul (b^2)
  have point (s:ℝ) : c.growthResidual s^2 = c.force s^2 -
      (2*b)*(c.curvature s*c.force s)+b^2*c.curvature s^2 := by
    dsimp [growthResidual,b]
    ring
  simp_rw [point]
  rw [intervalIntegral.integral_add (f:=fun s => c.force s^2-2*b*(c.curvature s*c.force s))
    (g:=fun s => b^2*c.curvature s^2) (((hf.pow 2).sub mixed).intervalIntegrable _ _) (curv.intervalIntegrable _ _),
    intervalIntegral.integral_sub (f:=fun s => c.force s^2) (g:=fun s => 2*b*(c.curvature s*c.force s))
      ((hf.pow 2).intervalIntegrable _ _) (mixed.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  unfold energy dissipation
  dsimp [b]
  unfold energy
  ring
/-- The integral of the actual Frenet curvature rotates the initial
unit tangent to the tangent at the other endpoint. -/
theorem tangent_eq_exp_integral_curvature (a b : ℝ) :
    c.tangent b=Complex.exp (((∫s in a..b,c.curvature s):ℝ)*Complex.I)*c.tangent a := by
  let θ:ℝ→ℝ := fun s=>∫z in a..s,c.curvature z
  have dθ (s:ℝ) : HasDerivAt θ (c.curvature s) s :=
    intervalIntegral.integral_hasDerivAt_right (c.curvature_continuous.intervalIntegrable a s)
      c.curvature_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter c.curvature_continuous.continuousAt
  let H:=fun s=>Complex.exp (-((θ s:ℂ)*Complex.I))*c.tangent s
  have hd (s:ℝ) : HasDerivAt H 0 s := by
    change HasDerivAt (fun x=>Complex.exp (-((θ x:ℂ)*Complex.I))*c.tangent x) 0 s
    convert! ((((dθ s).ofReal_comp.mul_const Complex.I).neg.cexp).mul (c.tangent_deriv s)) using 1
    ring
  have eq:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=b) (fun s _=>hd s)
    (intervalIntegrable_const (c:=(0:ℂ)))
  have θa : θ a=0:=by simp [θ]
  simp only [intervalIntegral.integral_zero,H,θa,Complex.ofReal_zero,zero_mul,neg_zero,
    Complex.exp_zero,one_mul] at eq
  have hh:=eq_sub_iff_add_eq.mp eq
  simp only [zero_add] at hh
  change c.tangent b=Complex.exp ((θ b:ℂ)*Complex.I)*c.tangent a
  rw [hh,←mul_assoc,←Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul]

end ClosedSimilarity.LowBending.ClosedFrenetCurve
