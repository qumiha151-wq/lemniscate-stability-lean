import Migration.LowDefectMaterialModes
import Migration.LowDefectModeSums
import Migration.LowDefectUnitCorrelation

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.LowDefect.Tangent

theorem constant_nonzero_coefficient {n : ℤ} (hn : n≠0) :
    coeff (fun _=>1) n=0 := by
  have hh := coeff_der (f:=fun _=>1) (g:=fun _=>0)
    (fun x=>hasDerivAt_const x (1:ℂ)) continuous_const rfl n
  have hz : coeff (fun _=>0) n=0 := by simp [coeff,fourierCoeffOn_eq_integral]
  rw [hz] at hh
  have omega_ne : (omega n:ℂ)≠0 := by
    exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (Int.cast_ne_zero.mpr hn)
  exact (mul_eq_zero.mp hh.symm).resolve_left (mul_ne_zero omega_ne Complex.I_ne_zero)

theorem coefficient_leakage {T : ℝ→ℂ} (ct : Continuous T) (unit : ∀x,‖T x‖=1)
    (closed : (∫x in (0:ℝ)..1,T x)=0) :
    ‖coeff T 2‖ * ‖coeff T 1‖ ≤ 1-energy T 1 := by
  let e : C(ℝ,ℂ) := ⟨fun x : ℝ=>fourier 1 (x : AddCircle ((1:ℝ)-0)),
    (fourier 1).continuous.comp continuous_quotient_mk'⟩
  have ce : ∀x,‖e x‖=1 := fun x=>Circle.norm_coe _
  have e0 : (∫x in (0:ℝ)..1,e x)=0 := by
    have c := constant_nonzero_coefficient (n:= -1) (by decide)
    simpa only [coeff,fourierCoeffOn_eq_integral,neg_neg,sub_zero,div_one,
      one_smul,smul_eq_mul,mul_one,e,ContinuousMap.coe_mk] using c
  have f1 : coeff T 1=∫x in (0:ℝ)..1,conj (e x)*T x := by
    simp only [coeff,fourierCoeffOn_eq_integral,sub_zero,div_one,one_smul,
      smul_eq_mul,e,ContinuousMap.coe_mk,←fourier_neg]
  have f2 : coeff T 2=∫x in (0:ℝ)..1,(conj (e x))^2*T x := by
    simp only [coeff,fourierCoeffOn_eq_integral,sub_zero,div_one,one_smul,
      smul_eq_mul,e,ContinuousMap.coe_mk,←fourier_neg,pow_two,←fourier_add]
    rfl
  have h := unit_correlation (⟨T,ct⟩ : C(ℝ,ℂ)) e closed e0 unit ce
  change ‖∫x in (0:ℝ)..1,(conj (e x))^2*T x‖*‖∫x in (0:ℝ)..1,conj (e x)*T x‖ ≤
    1-‖∫x in (0:ℝ)..1,conj (e x)*T x‖^2 at h
  simpa only [energy,f1,f2] using h

end MigrationGeometry.Flow.LowDefect.Tangent
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- First-harmonic concentration and the quadratic upper bound on the
second coefficient, directly on the actual oriented material slice. -/
theorem material_second_harmonic_bounds {t : ℝ} (ht : t ∈ I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2 ≤ 14/100) :
    let T := (c.materialSlice ht).fractionalTangent
    let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
    1-LowDefect.Tangent.energy T 1 ≤ (26/100)*D ∧
      ‖LowDefect.Tangent.coeff T 2‖ ≤ (266/1000)*D := by
  let p := c.materialSlice ht
  let T := p.fractionalTangent
  let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
  let m := LowDefect.Tangent.energy T
  have hm (n : ℤ) : 0 ≤ m n := sq_nonneg _
  have tc : Continuous T := continuous_iff_continuousAt.mpr
    fun x=>(p.fractionalTangent_hasDerivAt x).continuousAt
  have id := c.material_tangent_fourier_data ht turn
  obtain ⟨h0,ha,hn,hd⟩ := id
  have zero : m 0=0 := by
    change ‖LowDefect.Tangent.coeff (c.materialSlice ht).fractionalTangent 0‖^2=0
    rw [h0];norm_num
  have wm := LowDefect.leakage_from_moments hm zero ha hn hd
  have uc := LowDefect.Tangent.coefficient_leakage tc
    (fun x=>tangent_unit p.regular _) p.fractionalTangent_mean
  have uc2 := pow_le_pow_left₀ (by positivity) uc 2
  have zz : ‖LowDefect.Tangent.coeff T 2‖^2*(1-(1-m 1))≤(1-m 1)^2 := by
    change _≤(1-‖LowDefect.Tangent.coeff T 1‖^2)^2
    simpa [m,LowDefect.Tangent.energy,mul_pow] using uc2
  have dp : 0 ≤ D := div_nonneg (c.curvatureOscillation_nonneg ht _) (sq_nonneg _)
  exact LowDefect.mass_bootstrap dp small wm.1 zz wm.2.1 wm.2.2

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.material_second_harmonic_bounds
