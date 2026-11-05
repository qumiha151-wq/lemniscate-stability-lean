import Lemniscate.ElasticFlowNormalization

/-! The projected normal-velocity equation of planar free elastic flow.
The immersion condition and actual one-sided time derivative are part of
the equation; spatial and joint regularity are stated by the main theorem. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ComplexConjugate Topology

/-- A regular parametrized curve satisfies planar free elastic flow at
every nonnegative time, with the actual right derivative at the initial
time. Tangential velocity is unrestricted. -/
def IsFreeElasticFlow (Y : ℝ → ℝ → ℂ) : Prop :=
  ∀ t : ℝ,0≤t → ∀ s : ℝ,∃ v : ℂ,
    HasDerivWithinAt (fun r => Y r s) v (Ici (0:ℝ)) t ∧
    deriv (Y t) s≠0 ∧
    let n := I*deriv (Y t) s/(‖deriv (Y t) s‖:ℂ)
    (((conj v*n).re:ℂ)*n)=-(planarElasticForce (Y t) s:ℂ)*n

/-- At positive times the actual time derivative has the prescribed
normal component. This is the scalar form used by normal coordinates. -/
theorem free_elastic_flow_normal_equation
    (Y : ℝ → ℝ → ℂ) (hY : IsFreeElasticFlow Y)
    (t : ℝ) (ht : 0<t) (s : ℝ) :
    (conj (deriv (fun r => Y r s) t)*
      (I*deriv (Y t) s/(‖deriv (Y t) s‖:ℂ))).re=
        -planarElasticForce (Y t) s := by
  obtain ⟨v,hv,hreg,hflow⟩ := hY t ht.le s
  have hvt := hv.hasDerivAt (Ici_mem_nhds ht)
  rw [hvt.deriv]
  have hnorm : (‖deriv (Y t) s‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hreg)
  have hn : I*deriv (Y t) s/(‖deriv (Y t) s‖:ℂ)≠0 :=
    div_ne_zero (mul_ne_zero I_ne_zero hreg) hnorm
  have heq : ((conj v*(I*deriv (Y t) s/(‖deriv (Y t) s‖:ℂ))).re:ℂ)=
      -(planarElasticForce (Y t) s:ℂ) := mul_right_cancel₀ hn hflow
  exact_mod_cast heq

end Lemniscate
