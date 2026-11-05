import Lemniscate.PeriodicSobolevClassicalJet
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Continuous H2 normal heights give jointly continuous curve positions
and actual spatial velocities. This is the C1 continuity used to pass to
limits of oriented curve equivalences; no time differentiability is needed. -/
noncomputable section
namespace Lemniscate
open Complex

/-- The normal-graph family associated with a continuous H2 path is
continuous together with its actual first spatial derivative, also after
continuous similarities and a fixed change of spatial scale. -/
theorem normal_graph_sobolev_family_continuity
    (T : ℝ) [Fact (0<T)]
    {X : Type*} [TopologicalSpace X]
    (u : X → CircleSobolevSpace T 2) (hu : Continuous u)
    (p z : X → ℂ) (hp : Continuous p) (hz : Continuous z)
    (β ν : ℝ → ℂ) (hβ : ContDiff ℝ 1 β) (hν : ContDiff ℝ 1 ν)
    (a : ℝ) :
    let H := fun x : X => fun s : ℝ =>
      circleSobolevClassicalJet T 1 (u x) 0 ((a*s):AddCircle T)
    let Γ := fun q : X × ℝ => p q.1+z q.1*(β q.2+H q.1 q.2*ν q.2)
    Continuous Γ ∧
      Continuous (fun q : X × ℝ => deriv (fun s => Γ (q.1,s)) q.2) := by
  dsimp only
  let D := fun x : X => circleSobolevClassicalJet T 1 (u x)
  let H := fun (j : Fin 2) (q : X × ℝ) => D q.1 j ((a*q.2):AddCircle T)
  let Γ := fun q : X × ℝ => p q.1+z q.1*(β q.2+H 0 q*ν q.2)
  have hD : Continuous D := (circleSobolevClassicalJet T 1).continuous.comp hu
  have hH (j : Fin 2) : Continuous (H j) := by
    have hf : Continuous (fun q : X × ℝ => D q.1 j) :=
      (continuous_apply j).comp (hD.comp continuous_fst)
    have hx : Continuous (fun q : X × ℝ => ((a*q.2):AddCircle T)) :=
      (AddCircle.continuous_mk' T).comp (continuous_const.mul continuous_snd)
    exact continuous_eval.comp (hf.prodMk hx)
  have hΓ : Continuous Γ := (hp.comp continuous_fst).add
    ((hz.comp continuous_fst).mul ((hβ.continuous.comp continuous_snd).add
      ((hH 0).mul (hν.continuous.comp continuous_snd))))
  have hderiv (x : X) (s : ℝ) :
      HasDerivAt (fun s => Γ (x,s))
        (z x*(deriv β s+(a:ℂ)*H 1 (x,s)*ν s+H 0 (x,s)*deriv ν s)) s := by
    have hd : HasDerivAt (fun t : ℝ => D x 0 (t:AddCircle T))
        (D x 1 ((a*s):AddCircle T)) (a*s) :=
      circle_sobolev_classical_jet_deriv T 1 (u x) 0 (a*s)
    have hh : HasDerivAt (fun t : ℝ => H 0 (x,t)) ((a:ℂ)*H 1 (x,s)) s := by
      simpa only [H,Function.comp_def,mul_one,Complex.real_smul,mul_comm] using!
        hd.scomp s ((hasDerivAt_id s).const_mul a)
    have hβd := (hβ.differentiable (by norm_num)).differentiableAt.hasDerivAt (x:=s)
    have hνd := (hν.differentiable (by norm_num)).differentiableAt.hasDerivAt (x:=s)
    simpa only [Γ,add_assoc] using!
      ((hβd.add (hh.mul hνd)).const_mul (z x)).const_add (p x)
  refine ⟨hΓ,?_⟩
  have heq : (fun q : X × ℝ => deriv (fun s => Γ (q.1,s)) q.2)=
      (fun q : X × ℝ => z q.1*(deriv β q.2+(a:ℂ)*H 1 q*ν q.2+
        H 0 q*deriv ν q.2)) := funext fun q => (hderiv q.1 q.2).deriv
  rw [heq]
  exact (hz.comp continuous_fst).mul
    (((hβ.continuous_deriv (by norm_num)).comp continuous_snd).add
      ((continuous_const.mul (hH 1)).mul (hν.continuous.comp continuous_snd)) |>.add
        ((hH 0).mul ((hν.continuous_deriv (by norm_num)).comp continuous_snd)))

end Lemniscate
