import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Lean.Util.CollectAxioms

/-! Smoothness and time translation of C² solutions of the tilted quartic oscillator. -/
noncomputable section
open scoped ContDiff
namespace LengthGrowth.OscillatorSmooth

def acceleration (y : ℝ) : ℝ := -y^3/2+y/4+1/4

theorem smooth_of_c2 {z : ℝ → ℝ} (hz : ContDiff ℝ 2 z)
    (ode : ∀ t, deriv (deriv z) t = acceleration (z t)) : ContDiff ℝ ∞ z := by
  have dz := hz.differentiable (by decide)
  have dv := hz.differentiable_deriv_two
  have hn (n : ℕ) : ContDiff ℝ n z ∧ ContDiff ℝ n (deriv z) := by
    induction n with
    | zero => exact ⟨contDiff_zero.mpr dz.continuous,contDiff_zero.mpr dv.continuous⟩
    | succ n ih =>
      rw [Nat.cast_succ,contDiff_succ_iff_deriv,contDiff_succ_iff_deriv]
      refine ⟨⟨dz,by simp,ih.2⟩,dv,by simp,?_⟩
      rw [show deriv (deriv z) = fun t => acceleration (z t) from funext ode]
      exact ((((ih.1.pow 3).neg.div_const 2).add (ih.1.div_const 4)).add contDiff_const)
  rw [contDiff_iff_forall_nat_le]
  exact fun n _ => (hn n).1

theorem translate_solution {z : ℝ → ℝ} (hz : ContDiff ℝ 2 z)
    (ode : ∀ t, deriv (deriv z) t = acceleration (z t)) (x : ℝ) :
    let y := fun t => z (t-x)
    ContDiff ℝ ∞ y ∧ (∀ t, deriv (deriv y) t = acceleration (y t)) ∧
      y x=z 0 ∧ deriv y x=deriv z 0 := by
  have hs := smooth_of_c2 hz ode
  have hd (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
      deriv (fun t => f (t-x)) = fun t => deriv f (t-x) := by
    funext t
    have h := ((hf (t-x)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const x)).deriv
    change deriv (fun y => f (y-x)) t = deriv f (t-x)*1 at h
    simpa only [mul_one] using h
  dsimp only
  refine ⟨hs.comp (contDiff_id.sub contDiff_const),?_,by simp,?_⟩
  · intro t
    rw [hd z (hz.differentiable (by decide)),hd (deriv z) hz.differentiable_deriv_two]
    exact ode (t-x)
  · rw [hd z (hz.differentiable (by decide))]
    simp

/-- A global C² solver posed at zero suffices to solve smoothly with
prescribed position and velocity at any base time. -/
theorem exists_smooth_at
    (solve₀ : ∀ b v : ℝ, ∃ z : ℝ → ℝ, ContDiff ℝ 2 z ∧ z 0=b ∧ deriv z 0=v ∧
      ∀ t, deriv (deriv z) t = acceleration (z t)) (x b v : ℝ) :
    ∃ y : ℝ → ℝ, ContDiff ℝ ∞ y ∧ (∀ t, deriv (deriv y) t = acceleration (y t)) ∧
      y x=b ∧ deriv y x=v := by
  obtain ⟨z,hz,hpos,hvel,ode⟩ := solve₀ b v
  obtain ⟨hs,eqn,hx,hdx⟩ := translate_solution hz ode x
  exact ⟨fun t => z (t-x),hs,eqn,hx.trans hpos,hdx.trans hvel⟩

#print axioms smooth_of_c2
#print axioms translate_solution
#print axioms exists_smooth_at
end LengthGrowth.OscillatorSmooth
