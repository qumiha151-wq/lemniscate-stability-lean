import Lemniscate.LinearParabolicEnergy
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Explicit solutions of the finite diagonal parabolic Galerkin equations.
The integrating-factor formula supplies the actual derivative and initial
condition. The previously proved energy theorem then gives a bound depending
only on the prescribed forcing and initial data, uniformly in the mode count.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

/-- Integrating-factor solution, with oriented interval integrals for all
real times. Positivity of the rates is needed only for the energy estimate. -/
def finiteModeParabolicSolution {ι : Type*}
    (a : ι → ℝ) (u0 : ι → ℂ) (F : ι → ℝ → ℂ) : ι → ℝ → ℂ :=
  fun i t => (Real.exp (-(a i)*t) : ℂ)*
    (u0 i+∫ s in (0:ℝ)..t, (Real.exp (a i*s) : ℂ)*F i s)

private theorem finite_mode_parabolic_solution_deriv {ι : Type*}
    (a : ι → ℝ) (u0 : ι → ℂ) (F : ι → ℝ → ℂ)
    (hF : ∀ i, Continuous (F i)) (i : ι) (t : ℝ) :
    HasDerivAt (finiteModeParabolicSolution a u0 F i)
      (F i t-a i • finiteModeParabolicSolution a u0 F i t) t := by
  let G : ℝ → ℂ := fun s => (Real.exp (a i*s) : ℂ)*F i s
  have hGc : Continuous G := by dsimp only [G]; fun_prop
  have hI : HasDerivAt (fun r : ℝ => ∫ s in (0:ℝ)..r, G s) (G t) t :=
    intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable 0 t)
      hGc.aestronglyMeasurable.stronglyMeasurableAtFilter hGc.continuousAt
  have hB : HasDerivAt (fun r : ℝ => u0 i+∫ s in (0:ℝ)..r, G s) (G t) t :=
    hI.const_add (u0 i)
  have he : HasDerivAt (fun r : ℝ => (Real.exp (-(a i)*r) : ℂ))
      ((-(a i):ℂ)*(Real.exp (-(a i)*t) : ℂ)) t := by
    simpa only [id_eq,mul_one,Complex.ofReal_mul,Complex.ofReal_neg,mul_comm] using!
      (((hasDerivAt_id t).const_mul (-(a i))).exp).ofReal_comp
  have hcancel : (Real.exp (-(a i)*t) : ℂ)*(Real.exp (a i*t) : ℂ) = 1 := by
    have hreal : Real.exp (-(a i)*t)*Real.exp (a i*t) = 1 := by
      rw [← Real.exp_add]
      have hz : -(a i)*t+a i*t = 0 := by ring
      rw [hz,Real.exp_zero]
    exact_mod_cast hreal
  apply (he.mul hB).congr_deriv
  dsimp only [finiteModeParabolicSolution,G]
  rw [real_smul]
  rw [← mul_assoc (Real.exp (-(a i)*t) : ℂ) (Real.exp (a i*t) : ℂ) (F i t),
    hcancel,one_mul]
  ring

/-- The explicitly constructed finite-mode solution satisfies its prescribed
initial condition and equation, together with the exact energy identity and
an estimate uniform in time and in the number of modes. -/
theorem finite_mode_parabolic_solvability {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (u0 : ι → ℂ) (F : ι → ℝ → ℂ) (hF : ∀ i, Continuous (F i)) :
    let u := finiteModeParabolicSolution a u0 F
    let v : ι → ℝ → ℂ := fun i s => F i s-a i • u i s
    (∀ i, u i 0 = u0 i) ∧
      (∀ i s, HasDerivAt (u i) (v i s) s) ∧
      ∀ t : ℝ, 0 ≤ t →
        let D : ℝ → ℝ := fun s => ∑ i, (‖v i s‖^2+(a i)^2*‖u i s‖^2)
        (∫ s in (0:ℝ)..t, D s)+(∑ i, a i*‖u i t‖^2) =
            (∫ s in (0:ℝ)..t, ∑ i, ‖F i s‖^2)+(∑ i, a i*‖u0 i‖^2) ∧
          ∀ s ∈ Set.Icc (0:ℝ) t,
            (∫ r in (0:ℝ)..t, D r)+(∑ i, a i*‖u i s‖^2) ≤
              2*((∫ r in (0:ℝ)..t, ∑ i, ‖F i r‖^2)+
                (∑ i, a i*‖u0 i‖^2)) := by
  let u := finiteModeParabolicSolution a u0 F
  let v : ι → ℝ → ℂ := fun i s => F i s-a i • u i s
  have hinit (i : ι) : u i 0 = u0 i := by
    simp only [u,finiteModeParabolicSolution,mul_zero,Real.exp_zero,
      intervalIntegral.integral_same,add_zero,Complex.ofReal_one,one_mul]
  have hd (i : ι) (s : ℝ) : HasDerivAt (u i) (v i s) s :=
    finite_mode_parabolic_solution_deriv a u0 F hF i s
  have hu (i : ι) : Continuous (u i) :=
    continuous_iff_continuousAt.mpr fun s => (hd i s).continuousAt
  have hv (i : ι) : Continuous (v i) := (hF i).sub ((hu i).const_smul (a i))
  refine ⟨hinit,hd,fun t ht => ?_⟩
  have h := finite_mode_parabolic_energy u v a t ht ha hd hv
  simpa only [v,sub_add_cancel,hinit] using h

end Lemniscate
