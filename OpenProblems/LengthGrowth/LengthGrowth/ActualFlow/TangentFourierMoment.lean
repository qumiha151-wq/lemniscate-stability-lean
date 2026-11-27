import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
namespace LengthGrowth.TangentSpectrum
noncomputable section
open Set MeasureTheory Real
def coeff (f : ℝ→ℂ) (n : ℤ) := fourierCoeffOn (by norm_num : (0:ℝ)<1) f n
def omega (n : ℤ)  := 2*Real.pi*(n:ℝ)
def energy (f : ℝ→ℂ) (n : ℤ) := ‖coeff f n‖^2
theorem parseval (f : ℝ→ℂ) (cf : Continuous f) : HasSum (energy f) (∫x in 0..1,‖f x‖^2) := by
  have lp : MemLp f 2 (volume.restrict (Ioc 0 1)) := by
    exact (memLp_two_iff_integrable_sq_norm cf.aestronglyMeasurable).mpr ((cf.norm.pow 2).intervalIntegrable 0 1).1
  change HasSum (fun n=>‖fourierCoeffOn (by norm_num : (0:ℝ)<1) f n‖^2) _
  simpa only [sub_zero,inv_one,one_smul] using hasSum_sq_fourierCoeffOn (by norm_num : (0:ℝ)<1) lp

theorem coeff_der {f g : ℝ→ℂ} (df : ∀x,HasDerivAt f (g x) x) (cg : Continuous g)
    (p : f 1=f 0) (n : ℤ) : coeff g n=(omega n:ℂ)*Complex.I*coeff f n := by
  by_cases hz : n=0
  · subst n
    have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1)
      (fun x _=>df x) (cg.intervalIntegrable 0 1)
    rw [p,sub_self] at eq
    simp [coeff,omega,fourierCoeffOn_eq_integral,eq]
  · have eq := fourierCoeffOn_of_hasDerivAt (by norm_num : (0:ℝ)<1) hz (fun x _=>df x) (cg.intervalIntegrable 0 1)
    rw [p,sub_self,mul_zero,zero_sub] at eq
    norm_num only [Complex.ofReal_one,Complex.ofReal_zero,sub_zero,one_mul] at eq
    change fourierCoeffOn _ g n=_
    dsimp only [coeff]
    rw [eq]
    have hn : (n:ℂ)≠0 := by exact_mod_cast hz
    have hpi : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
    unfold omega;push_cast
    field_simp [hn,hpi,Complex.I_ne_zero]

theorem energy_der {f g : ℝ→ℂ} (df : ∀x,HasDerivAt f (g x) x) (cg : Continuous g)
    (p : f 1=f 0) (n : ℤ) : energy g n=|omega n|^2*energy f n := by
  simp only [energy,coeff_der df cg p,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_I,mul_one,mul_pow]

theorem fourier_energy_moments {T V A : ℝ→ℂ} (T' : ∀x,HasDerivAt T (V x) x)
    (V' : ∀x,HasDerivAt V (A x) x) (cA : Continuous A) (per : T 1=T 0) (pv : V 1=V 0) :
    HasSum (fun n=>|omega n|^2*energy T n) (∫x in 0..1,‖V x‖^2) ∧
      HasSum (fun n=>|omega n|^4*energy T n) (∫x in 0..1,‖A x‖^2) := by
  have cv : Continuous V := continuous_iff_continuousAt.mpr fun x=>(V' x).continuousAt
  constructor
  · simpa only [←energy_der T' cv per] using parseval V cv
  · have eq (n : ℤ) : |omega n|^4*energy T n=energy A n := by
      rw [energy_der V' cA pv,energy_der T' cv per];ring
    simp_rw [eq];exact parseval A cA

end
end LengthGrowth.TangentSpectrum
#print axioms LengthGrowth.TangentSpectrum.fourier_energy_moments
