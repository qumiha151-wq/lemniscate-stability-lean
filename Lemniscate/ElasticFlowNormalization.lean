import Lemniscate.NormalGraphScalarConverse

/-! Scaling and time normalization of the actual projected elastic flow,
in both directions and including derivatives within an initial time set. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ComplexConjugate

def planarElasticForce (γ : ℝ → ℂ) (s : ℝ) : ℝ :=
  arclengthDerivative γ (arclengthDerivative γ (planarSignedCurvature γ)) s+
    (1/2:ℝ)*(planarSignedCurvature γ s)^3

private theorem normal_support_pair (γ : ℝ → ℂ) (s : ℝ) :
    (conj (γ s)*(I*deriv γ s/(‖deriv γ s‖:ℂ))).re=planarNormalSupport γ s := by
  rw [← mul_div_assoc,Complex.div_ofReal_re]
  change (conj (γ s)*(I*deriv γ s)).re/‖deriv γ s‖ =
    -(conj (γ s)*deriv γ s).im/‖deriv γ s‖
  rw [show conj (γ s)*(I*deriv γ s)=I*(conj (γ s)*deriv γ s) by ring]
  simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub]

theorem planar_similarity_elastic_geometry
    (γ : ℝ → ℂ) (hreg : ∀ s, deriv γ s≠0)
    (p R : ℂ) (r : ℝ) (hr : 0<r) (hR : ‖R‖=1) :
    let Y : ℝ → ℂ := fun s => p+((r:ℂ)*R)*γ s
    (∀ s, deriv Y s≠0 ∧
      I*deriv Y s/(‖deriv Y s‖:ℂ)=R*(I*deriv γ s/(‖deriv γ s‖:ℂ))) ∧
    ∀ s, planarElasticForce Y s=r⁻¹^3*planarElasticForce γ s := by
  let m : ℂ := (r:ℂ)*R
  let Y : ℝ → ℂ := fun s => p+m*γ s
  have hrne : r≠0 := ne_of_gt hr
  have hrC : (r:ℂ)≠0 := by exact_mod_cast hrne
  have hmnorm : ‖m‖=r := by
    dsimp only [m]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,hR,mul_one]
  have hmne : m≠0 := norm_ne_zero_iff.mp (by rw [hmnorm]; exact hrne)
  have hdY : deriv Y=fun s => m*deriv γ s := by
    funext s
    simp only [Y,deriv_const_add,deriv_const_mul_field]
  have hddY : deriv (deriv Y)=fun s => m*deriv (deriv γ) s := by
    rw [hdY]
    exact deriv_const_mul_field' m
  have hspeed (s : ℝ) : ‖deriv Y s‖=r*‖deriv γ s‖ := by rw [hdY,norm_mul,hmnorm]
  have hpair : conj m*m=((r^2:ℝ):ℂ) := by
    rw [Complex.conj_mul',hmnorm]
    simp only [Complex.ofReal_pow]
  have hcurv : planarSignedCurvature Y=fun s => r⁻¹*planarSignedCurvature γ s := by
    funext s
    change (conj (deriv Y s)*deriv (deriv Y) s).im/‖deriv Y s‖^3 =
      r⁻¹*((conj (deriv γ s)*deriv (deriv γ) s).im/‖deriv γ s‖^3)
    rw [congrArg (fun f : ℝ → ℂ => f s) hdY,
      congrArg (fun f : ℝ → ℂ => f s) hddY,norm_mul,hmnorm]
    have hc : conj (m*deriv γ s)*(m*deriv (deriv γ) s)=
        ((r^2:ℝ):ℂ)*(conj (deriv γ s)*deriv (deriv γ) s) := by
      rw [map_mul]
      calc
        _ = (conj m*m)*(conj (deriv γ s)*deriv (deriv γ) s) := by ring
        _ = _ := by rw [hpair]
    rw [hc]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    field_simp [hrne,norm_ne_zero_iff.mpr (hreg s)] <;> ring
  have hD (c : ℝ) (f : ℝ → ℝ) :
      arclengthDerivative Y (fun s => c*f s)=
        fun s => (c/r)*arclengthDerivative γ f s := by
    funext s
    dsimp only [arclengthDerivative]
    rw [deriv_const_mul_field,hspeed]
    field_simp [hrne,norm_ne_zero_iff.mpr (hreg s)] <;> ring
  refine ⟨?_,?_⟩
  · intro s
    refine ⟨by rw [hdY]; exact mul_ne_zero hmne (hreg s),?_⟩
    rw [hspeed,hdY]
    dsimp only [m]
    push_cast
    field_simp [hrC,Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hreg s))] <;> ring
  · intro s
    change arclengthDerivative Y (arclengthDerivative Y (planarSignedCurvature Y)) s+
      (1/2:ℝ)*(planarSignedCurvature Y s)^3 = r⁻¹^3*planarElasticForce γ s
    rw [hcurv,hD r⁻¹ (planarSignedCurvature γ),
      hD (r⁻¹/r) (arclengthDerivative γ (planarSignedCurvature γ))]
    dsimp only [planarElasticForce]
    field_simp [hrne] <;> ring

private theorem normalized_scalar_iff (d c h F v : ℝ) (hd : d ≠ 0) :
    d*(c*h+v)=-(d*F) ↔ v=-(F+c*h) := by
  rw [← mul_neg]
  constructor
  · intro heq
    have hh := mul_left_cancel₀ hd heq
    linarith only [hh]
  · intro heq
    congr 1
    linarith only [heq]

/-- Undoing the physical scale and time changes is an equivalence of the
actual scalar normal-velocity equations. Spatial regularity, the unit
normal and the time derivative are proved for the reconstructed curve. -/
theorem elastic_flow_normalization_equivalence
    (γ : ℝ → ℂ) (hreg : ∀ s, deriv γ s ≠ 0)
    (R : ℂ) (hR : ‖R‖=1) (X : ℝ → ℝ → ℂ) (Vx : ℝ → ℂ)
    (ρ σ : ℝ → ℝ) (S J : Set ℝ) (p₀ : ℂ) (t₀ c : ℝ)
    (hX : ∀ s, X (σ t₀) s=R*γ s)
    (hXd : ∀ s, HasDerivWithinAt (fun z => X z s) (Vx s) J (σ t₀))
    (hρ : 0<ρ t₀)
    (hρd : HasDerivWithinAt ρ (c*(ρ t₀)⁻¹^3) S t₀)
    (hσd : HasDerivWithinAt σ ((ρ t₀)⁻¹^4) S t₀)
    (hσmap : MapsTo σ S J) :
    let Y : ℝ → ℝ → ℂ := fun z s => p₀+(ρ z:ℂ)*X (σ z) s
    ∃ Vy : ℝ → ℂ, ∀ s,
      let ν := I*deriv (Y t₀) s/(‖deriv (Y t₀) s‖:ℂ)
      HasDerivWithinAt (fun z => Y z s) (Vy s) S t₀ ∧
      deriv (Y t₀) s ≠ 0 ∧ ‖ν‖=1 ∧
      ((conj (Vy s)*ν).re=-(planarElasticForce (Y t₀) s) ↔
        (conj (Vx s)*(R*(I*deriv γ s/(‖deriv γ s‖:ℂ)))).re=
          -(planarElasticForce γ s+c*planarNormalSupport γ s)) := by
  dsimp only
  let r := ρ t₀
  let Y : ℝ → ℝ → ℂ := fun z s => p₀+(ρ z:ℂ)*X (σ z) s
  have hsimilar := planar_similarity_elastic_geometry γ hreg p₀ R r hρ hR
  have hYeq : Y t₀=fun s => p₀+((r:ℂ)*R)*γ s := by
    funext s
    change p₀+(ρ t₀:ℂ)*X (σ t₀) s=_
    rw [hX s]
    change p₀+(r:ℂ)*(R*γ s)=_
    ring
  let Vy : ℝ → ℂ := fun s =>
    (((c*r⁻¹^3:ℝ):ℂ)*(R*γ s)+((r*r⁻¹^4:ℝ):ℂ)*Vx s)
  refine ⟨Vy,?_⟩
  intro s
  let ν := I*deriv γ s/(‖deriv γ s‖:ℂ)
  have hnormal : I*deriv (Y t₀) s/(‖deriv (Y t₀) s‖:ℂ)=R*ν := by
    rw [hYeq]
    exact (hsimilar.1 s).2
  have hforce : planarElasticForce (Y t₀) s=r⁻¹^3*planarElasticForce γ s := by
    rw [hYeq]
    exact hsimilar.2 s
  have hregY : deriv (Y t₀) s≠0 := by rw [hYeq]; exact (hsimilar.1 s).1
  have hν : ‖ν‖=1 := by
    dsimp only [ν]
    rw [norm_div,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr (hreg s))
  have hYd := (hρd.ofReal_comp.mul ((hXd s).scomp t₀ hσd hσmap)).const_add p₀
  have hYd' : HasDerivWithinAt (fun z => Y z s) (Vy s) S t₀ := by
    apply hYd.congr_deriv
    simp only [real_smul,Function.comp_def,hX s]
    dsimp only [Vy,r]
    push_cast
    ring
  refine ⟨hYd',hregY,?_,?_⟩
  · rw [hnormal,norm_mul,hR,hν,one_mul]
  · rw [hnormal,hforce]
    have hcoef : r*r⁻¹^4=r⁻¹^3 := by
      field_simp [ne_of_gt hρ] <;> ring
    have hpair : (conj (Vy s)*(R*ν)).re=
        r⁻¹^3*(c*planarNormalSupport γ s+(conj (Vx s)*(R*ν)).re) := by
      dsimp only [Vy]
      rw [real_normal_pairing_add,unit_complex_pairing _ _ _ hR,
        normal_support_pair γ s,hcoef]
      ring
    rw [hpair]
    exact normalized_scalar_iff (r⁻¹^3) c (planarNormalSupport γ s)
      (planarElasticForce γ s) ((conj (Vx s)*(R*ν)).re)
      (pow_ne_zero 3 (inv_ne_zero (ne_of_gt hρ)))

end Lemniscate
