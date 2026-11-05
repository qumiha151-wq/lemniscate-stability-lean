import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv

/-! Joint continuity of positions and actual spatial velocities is
preserved by a continuous time change, continuous similarities and a
fixed C1 spatial parameter change. -/
noncomputable section
namespace Lemniscate

/-- This transfers the normalized graph's C1 geometry to physical time
and to the original initial parametrization in one step. -/
theorem curve_family_similarity_continuity
    {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (G : X × ℝ → ℂ) (hG : Continuous G)
    (hGv : Continuous (fun q : X × ℝ => deriv (fun s => G (q.1,s)) q.2))
    (hGd : ∀ x : X,Differentiable ℝ (fun s => G (x,s)))
    (σ : Z → X) (hσ : Continuous σ)
    (p z : Z → ℂ) (hp : Continuous p) (hz : Continuous z)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) :
    let Γ := fun q : Z × ℝ => p q.1+z q.1*G (σ q.1,χ q.2)
    Continuous Γ ∧
      Continuous (fun q : Z × ℝ => deriv (fun s => Γ (q.1,s)) q.2) := by
  dsimp only
  let Γ := fun q : Z × ℝ => p q.1+z q.1*G (σ q.1,χ q.2)
  let F := fun q : Z × ℝ => (σ q.1,χ q.2)
  have hF : Continuous F :=
    (hσ.comp continuous_fst).prodMk (hχ.continuous.comp continuous_snd)
  have hΓ : Continuous Γ := (hp.comp continuous_fst).add
    ((hz.comp continuous_fst).mul (hG.comp hF))
  have hd (x : Z) (s : ℝ) : HasDerivAt (fun u => Γ (x,u))
      (z x*(((deriv χ s:ℝ):ℂ)*deriv (fun u => G (σ x,u)) (χ s))) s := by
    have hχd : HasDerivAt χ (deriv χ s) s :=
      (hχ.differentiable (by simp)).differentiableAt.hasDerivAt
    have houter : HasDerivAt (fun u : ℝ => G (σ x,u))
        (deriv (fun u => G (σ x,u)) (χ s)) (χ s) :=
      ((hGd (σ x)).differentiableAt (x:=χ s)).hasDerivAt
    have hcomp : HasDerivAt (fun u : ℝ => G (σ x,χ u))
        ((deriv χ s:ℝ) • deriv (fun u => G (σ x,u)) (χ s)) s :=
      houter.scomp s hχd
    simpa only [Γ,Function.comp_def,Complex.real_smul] using!
      (hcomp.const_mul (z x)).const_add (p x)
  refine ⟨hΓ,?_⟩
  have heq : (fun q : Z × ℝ => deriv (fun s => Γ (q.1,s)) q.2)=
      (fun q : Z × ℝ => z q.1*(((deriv χ q.2:ℝ):ℂ)*
        deriv (fun s => G (σ q.1,s)) (χ q.2))) :=
    funext fun q => (hd q.1 q.2).deriv
  rw [heq]
  have hχv : Continuous (fun q : Z × ℝ => ((deriv χ q.2:ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp ((hχ.continuous_deriv le_rfl).comp continuous_snd)
  exact (hz.comp continuous_fst).mul (hχv.mul (hGv.comp hF))

end Lemniscate
