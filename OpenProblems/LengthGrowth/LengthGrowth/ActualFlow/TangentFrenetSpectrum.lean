import LengthGrowth.ActualFlow.TangentSignedMoment
import LengthGrowth.ActualFlow.TangentFourthMoment
import LengthGrowth.ElasticStress
namespace LengthGrowth.ClosedFrenetCurve
noncomputable section
open Real Set MeasureTheory TangentSpectrum
variable (c : ClosedFrenetCurve)
def unitT (u : ℝ) := c.tangent (c.period*u)
def unitK (u : ℝ) := c.period*c.curvature (c.period*u)
def unitB (u : ℝ) := c.period^2*c.curvature₁ (c.period*u)
def unitC (u : ℝ) := c.period^3*c.curvature₂ (c.period*u)
def unitV (u : ℝ) := (c.unitK u:ℂ)*Complex.I*c.unitT u
def unitA (u : ℝ) := ((c.unitB u:ℂ)*Complex.I-(c.unitK u:ℂ)^2)*c.unitT u

theorem unitT_der (u : ℝ) : HasDerivAt c.unitT (c.unitV u) u := by
  have h:=(c.tangent_deriv (c.period*u)).scomp u ((hasDerivAt_id u).const_mul c.period)
  convert! h using 1
  simp [unitT,unitV,unitK,Algebra.smul_def];ring

theorem unitK_der (u : ℝ) : HasDerivAt c.unitK (c.unitB u) u := by
  have h:=((c.curvature_deriv (c.period*u)).scomp u ((hasDerivAt_id u).const_mul c.period)).const_mul c.period
  convert! h using 1
  simp [unitB];ring
theorem unitB_der (u : ℝ) : HasDerivAt c.unitB (c.unitC u) u := by
  have h:=((c.curvature₁_deriv (c.period*u)).scomp u ((hasDerivAt_id u).const_mul c.period)).const_mul (c.period^2)
  convert! h using 1
  simp [unitC];ring
theorem unitV_der (u : ℝ) : HasDerivAt c.unitV (c.unitA u) u := by
  have s:=(((c.unitK_der u).ofReal_comp.mul_const Complex.I).mul (c.unitT_der u))
  convert! s using 1
  simp only [unitA,unitV]
  linear_combination (norm := ring_nf) -((c.unitK u:ℂ)^2*c.unitT u)*Complex.I_sq
theorem unitA_norm (u : ℝ) : ‖c.unitA u‖^2=c.unitB u^2+c.unitK u^4 := by
  rw [unitA,norm_mul,unitT,c.tangent_unit,mul_one,Complex.sq_norm]
  simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,pow_two];ring
theorem unitT_spectral (X : ℝ) (xp : 0<X)
    (mass : (∫u in 0..1,c.unitK u^2)=2*X^3)
    (stress : ∀u,|c.unitK u|^6≤(2^25:ℝ)*X^12)
    (work : 0≤∫u in 0..1,c.unitK u*(c.unitC u+c.unitK u^3/2)) :
    HasSum (fun n : ℤ=>omega n*energy c.unitT n) (∫u in 0..1,c.unitK u) ∧
    HasSum (fun n : ℤ=>|omega n|^2*energy c.unitT n) (2*X^3) ∧
    ∃M, HasSum (fun n : ℤ=>|omega n|^4*energy c.unitT n) M ∧ M≤1024*X^7 := by
  have cc : Continuous c.unitC := continuous_const.mul (c.curvature₂_continuous.comp (continuous_const.mul continuous_id))
  have ck : Continuous c.unitK := continuous_iff_continuousAt.mpr fun u=>(c.unitK_der u).continuousAt
  have cb : Continuous c.unitB := continuous_iff_continuousAt.mpr fun u=>(c.unitB_der u).continuousAt
  have ct : Continuous c.unitT := continuous_iff_continuousAt.mpr fun u=>(c.unitT_der u).continuousAt
  have cv : Continuous c.unitV := continuous_iff_continuousAt.mpr fun u=>(c.unitV_der u).continuousAt
  have ca : Continuous c.unitA := by change Continuous (fun u=>((c.unitB u:ℂ)*Complex.I-(c.unitK u:ℂ)^2)*c.unitT u);fun_prop
  have tk : c.unitK 1=c.unitK 0 := by simp [unitK,c.curvature_periodic.eq]
  have tb : c.unitB 1=c.unitB 0 := by simp [unitB,c.curvature₁_periodic.eq]
  have pt : c.unitT 1=c.unitT 0 := by simp [unitT,c.tangent_periodic.eq]
  have pV : c.unitV 1=c.unitV 0 := by simp only [unitV,tk,pt]
  have sums:=fourier_energy_moments c.unitT_der c.unitV_der ca pt pV
  have en (u : ℝ) : ‖c.unitV u‖^2=c.unitK u^2 := by
    simp only [unitV,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,unitT,c.tangent_unit,sq_abs]
  simp_rw [en,mass] at sums
  refine ⟨signed_moment c.unitT_der cv pt (fun u=>c.tangent_unit _) (fun _=>rfl),sums.1,_,sums.2,?_⟩
  exact second_tangent_estimate xp c.unitK_der c.unitB_der cc tk tb c.unitA_norm mass stress work
end
end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.unitT_spectral
