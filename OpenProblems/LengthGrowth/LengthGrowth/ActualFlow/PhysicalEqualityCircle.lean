import LengthGrowth.ActualFlow.SaturationEquality
import LengthGrowth.ActualFlow.SharpCircle

noncomputable section
open Set MeasureTheory Complex
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- The arclength position makes one full turn, with either orientation. -/
theorem growthResidual_equality_circle
    (sharp : (∫s in 0..c.period,c.growthResidual s^2)*c.period^3=Real.pi^2*c.energy^2) :
    ∃ b : ℝ, |b|=2*Real.pi/c.period ∧
      (∀s,c.curve s=c.arclengthCentroid+(c.curve 0-c.arclengthCentroid)*circleMap 0 1 (b*s)) ∧
      InjOn c.curve (Ico 0 c.period) := by
  obtain ⟨radius,zero,_⟩ := c.growthResidual_equality_geometry sharp
  let y := fun s => c.curve s-c.arclengthCentroid
  let p := fun s => inner ℝ (c.normal s) (y s)
  let a := p 0
  have ort (s : ℝ) : inner ℝ (c.normal s) (c.tangent s)=0 := by
    change (c.tangent s*conj (I*c.tangent s)).re=0
    have u := c.tangent_mul_star s
    change c.tangent s*conj (c.tangent s)=1 at u
    rw [map_mul,Complex.conj_I,show c.tangent s*(-I*conj (c.tangent s))=
      -I*(c.tangent s*conj (c.tangent s)) by ring,u,mul_one]
    simp
  have dp (s : ℝ) : HasDerivAt p 0 s := by
    apply ((c.normal_deriv s).inner ℝ ((c.curve_deriv s).sub_const c.arclengthCentroid)).congr_deriv
    rw [ort]
    have eq := zero s
    change inner ℝ (c.tangent s) (y s)=0 at eq
    rw [←Complex.ofReal_neg,←Complex.real_smul,real_inner_smul_left]
    change _ + _*inner ℝ (c.tangent s) (y s)=0
    rw [eq]
    ring
  have ps (s : ℝ) : p s=a :=
    is_const_of_deriv_eq_zero (fun t => (dp t).differentiableAt) (fun t => (dp t).deriv) s 0
  have frame (s : ℝ) : y s=(a:ℂ)*I*c.tangent s := by
    let w := y s*conj (c.tangent s)
    have q : w.re=0 := zero s
    have n : w.im=a := by
      have eq := ps s
      change (y s*conj (I*c.tangent s)).re=a at eq
      rw [map_mul,Complex.conj_I,show y s*(-I*conj (c.tangent s))=w*(-I) by dsimp [w]; ring] at eq
      simpa [Complex.mul_re] using eq
    have full : w=(a:ℂ)*I := by apply Complex.ext <;> simp [q,n,Complex.mul_re,Complex.mul_im]
    have u := c.tangent_mul_star s
    change c.tangent s*conj (c.tangent s)=1 at u
    calc
      _ = w*c.tangent s := by dsimp [w]; rw [mul_right_comm,mul_assoc,u,mul_one]
      _ = _ := by rw [full]
  have ha : |a|=c.period/(2*Real.pi) := by
    have hi := congrArg norm (frame 0)
    simp only [norm_mul,norm_real,Real.norm_eq_abs,norm_I,c.tangent_unit,mul_one] at hi
    exact hi.symm.trans (radius 0)
  have az : a≠0 := by
    have pos : 0<c.period/(2*Real.pi) := div_pos c.period_pos Real.two_pi_pos
    exact abs_pos.mp (ha.symm ▸ pos)
  let b := -a⁻¹
  have mag : |b|=2*Real.pi/c.period := by
    dsimp [b]
    rw [abs_neg,abs_inv,ha,inv_div]
  have direction (s : ℝ) : c.tangent s=(b:ℂ)*I*y s := by
    rw [frame]
    have nz : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr az
    dsimp [b]
    push_cast
    symm
    calc
      _ = -((a:ℂ)⁻¹*(a:ℂ))*(I*I)*c.tangent s := by ring
      _ = _ := by rw [inv_mul_cancel₀ nz,Complex.I_mul_I]; ring
  let v := fun s => circleMap 0 1 (b*s)
  have vn (s : ℝ) : v s≠0 := by simp [v,circleMap,Complex.exp_ne_zero]
  have vd (s : ℝ) : HasDerivAt v ((b:ℂ)*I*v s) s := by
    have h := (hasDerivAt_circleMap 0 1 (b*s)).scomp s ((hasDerivAt_id s).const_mul b)
    apply h.congr_deriv
    rw [Complex.real_smul]
    dsimp [v]
    ring_nf
  have d (s : ℝ) : HasDerivAt (fun t => y t/v t) 0 s := by
    apply (((c.curve_deriv s).sub_const c.arclengthCentroid).div (vd s) (vn s)).congr_deriv
    rw [direction]
    change (((b:ℂ)*I*y s)*v s-y s*((b:ℂ)*I*v s))/v s^2=0
    ring
  have pos (s : ℝ) : c.curve s=c.arclengthCentroid+(c.curve 0-c.arclengthCentroid)*v s := by
    have eq := is_const_of_deriv_eq_zero (fun t => (d t).differentiableAt) (fun t => (d t).deriv) s 0
    change y s / v s=y 0 / v 0 at eq
    have v0 : v 0=1 := by simp [v,circleMap]
    rw [v0,div_one,div_eq_iff (vn s)] at eq
    dsimp [y] at eq
    linear_combination eq
  refine ⟨b,mag,pos,?_⟩
  intro s hs t ht he
  rw [pos s,pos t,add_right_inj] at he
  have y0 : c.curve 0-c.arclengthCentroid≠0 := by
    apply norm_pos_iff.mp
    rw [radius]
    exact div_pos c.period_pos Real.two_pi_pos
  have ve := mul_left_cancel₀ y0 he
  have diff : |b*s-b*t|<2*Real.pi := by
    rw [←mul_sub,abs_mul,mag]
    have bd : |s-t|<c.period := abs_lt.mpr ⟨by linarith only [hs.1,ht.2],by linarith only [hs.2,ht.1]⟩
    calc
      _ < (2*Real.pi/c.period)*c.period := mul_lt_mul_of_pos_left bd (div_pos Real.two_pi_pos c.period_pos)
      _ = _ := div_mul_cancel₀ _ c.period_pos.ne'
  have eq := eq_of_circleMap_eq (R:=1) (c:=0) (by norm_num) diff ve
  exact mul_left_cancel₀ (neg_ne_zero.mpr (inv_ne_zero az)) eq
end LengthGrowth.ClosedFrenetCurve

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

private theorem equality_residual_of_pi (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t)
    (eq : c.productGrowthFraction t=1/2-Real.pi^2/c.normalizedProduct t) :
    let p := (c.regularPositionAt ht.le).closedFrenetCurve
    (∫s in 0..p.period,p.growthResidual s^2)*p.period^3=Real.pi^2*p.energy^2 := by
  let p := (c.regularPositionAt ht.le).closedFrenetCurve
  let r := ∫s in 0..p.period,p.growthResidual s^2
  have ep := c.energy_pos ht.le
  have lp : 0<c.length t := p.period_pos
  have raw := c.productGrowthFraction_residual hf ht
  change 1/2-c.productGrowthFraction t=c.length t^2/c.energy t^3*r at raw
  rw [eq,normalizedProduct] at raw
  field_simp [ep.ne',lp.ne'] at raw
  change r*p.period^3=Real.pi^2*p.energy^2
  have he : p.energy=c.energy t := (c.regularPositionAt ht.le).closedFrenetCurve_energy
  have hl : p.period=c.length t := rfl
  rw [he,hl]
  nlinarith only [raw]

theorem productGrowthFraction_equal_pi_iff_minimal (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t) :
    c.productGrowthFraction t=1/2-Real.pi^2/c.normalizedProduct t ↔
      c.normalizedProduct t=2*Real.pi^2 := by
  let p := (c.regularPositionAt ht.le).closedFrenetCurve
  constructor
  · intro eq
    have h := (p.growthResidual_equality_geometry (c.equality_residual_of_pi hf ht eq)).2.2
    have he : p.energy=c.energy t := (c.regularPositionAt ht.le).closedFrenetCurve_energy
    change c.energy t*c.length t=_
    rwa [he] at h
  · intro eq
    have hmin : IsLocalMin c.normalizedProduct t := by
      filter_upwards [lt_mem_nhds ht] with x hx
      rw [eq]
      exact c.sharp_energy_length hx.le
    rw [productGrowthFraction,hmin.deriv_eq_zero,eq,mul_zero,zero_div]
    field_simp [Real.pi_ne_zero]
    ring

theorem productGrowthFraction_equal_pi_single_circle (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t)
    (eq : c.productGrowthFraction t=1/2-Real.pi^2/c.normalizedProduct t) :
    let p := c.regularPositionAt ht.le
    ∃ z : ℂ, ∃ b : ℝ, |b|=2*Real.pi/c.length t ∧
      (∀u,c.position t u=z+(c.position t 0-z)*circleMap 0 1 (b*p.arclength u)) ∧
      InjOn (c.position t) (Ico 0 c.period) := by
  let p := c.regularPositionAt ht.le
  have shape := p.closedFrenetCurve.growthResidual_equality_circle (c.equality_residual_of_pi hf ht eq)
  obtain ⟨b,mag,hcurve,inj⟩ := shape
  have pos (u : ℝ) : p.closedFrenetCurve.curve (p.arclength u)=c.position t u := by
    change c.position t (p.arclengthInverse (p.arclength u))=_
    rw [p.arclength_inverse_right]
  have z0 : p.closedFrenetCurve.curve 0=c.position t 0 := by simpa only [p.arclength_zero] using pos 0
  refine ⟨p.closedFrenetCurve.arclengthCentroid,b,mag,?_,?_⟩
  · intro u
    simpa only [pos,z0] using hcurve (p.arclength u)
  · intro u hu v hv same
    have range (x : ℝ) (hx : x∈Ico 0 c.period) : p.arclength x∈Ico 0 p.closedFrenetCurve.period := by
      refine ⟨?_,?_⟩
      · simpa only [p.arclength_zero] using p.arclength_strictMono.monotone hx.1
      · change p.arclength x<p.length
        rw [←p.arclength_length]
        exact p.arclength_strictMono hx.2
    apply p.arclength_strictMono.injective
    apply inj (range u hu) (range v hv)
    rwa [pos,pos]
end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.ClosedFrenetCurve.growthResidual_equality_circle
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.productGrowthFraction_equal_pi_iff_minimal
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.productGrowthFraction_equal_pi_single_circle
