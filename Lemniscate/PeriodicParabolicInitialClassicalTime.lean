import Lemniscate.PeriodicParabolicGlobalSolution
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The initial right derivative passes from the actual first parabolic
segment to the same global curve by its affine time coordinate. -/
noncomputable section
namespace Lemniscate
open Set Filter
open scoped Topology NNReal

/-- The first actual segment determines the global initial right time
derivative. The displayed value space may also be a space of continuous
spatial functions; no regularity of the abstract state space is assumed. -/
theorem circle_initial_classical_time_derivative
    {H V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (τ : ℝ) (hτ : 0 < τ) (value : H → V)
    (u : ℝ≥0 → H) (q : unitInterval → H) (v : V)
    (hrep : ∀ r, u (circleParabolicSegmentTime τ hτ 0 r)=q r)
    (hlocal : HasDerivWithinAt
      (fun r : ℝ => value (q (Set.projIcc (0:ℝ) 1 zero_le_one r)))
      (τ • v) (Icc (0:ℝ) 1) 0) :
    HasDerivWithinAt (fun s : ℝ => value (u (Real.toNNReal s))) v (Ici (0:ℝ)) 0 := by
  have hmap : MapsTo (fun s : ℝ => s/τ) (Icc (0:ℝ) τ) (Icc (0:ℝ) 1) := by
    intro s hs
    exact ⟨div_nonneg hs.1 hτ.le,(div_le_one hτ).mpr hs.2⟩
  have hdivAt : HasDerivAt (fun s : ℝ => s/τ) τ⁻¹ 0 := by
    simpa only [one_div,id_eq] using! ((hasDerivAt_id (0:ℝ)).div_const τ)
  have hdiv : HasDerivWithinAt (fun s : ℝ => s/τ) τ⁻¹ (Icc (0:ℝ) τ) 0 :=
    hdivAt.hasDerivWithinAt
  have hscaled : HasDerivWithinAt
      (fun s : ℝ => value (q (Set.projIcc (0:ℝ) 1 zero_le_one (s/τ))))
      v (Icc (0:ℝ) τ) 0 := by
    apply (hlocal.scomp_of_eq (0:ℝ) hdiv hmap (by simp)).congr_deriv
    simp only [smul_smul,inv_mul_cancel₀ hτ.ne',one_smul]
  have heq (s : ℝ) (hs : s ∈ Icc (0:ℝ) τ) :
      value (u (Real.toNNReal s))=
        value (q (Set.projIcc (0:ℝ) 1 zero_le_one (s/τ))) := by
    let r : unitInterval := ⟨s/τ,hmap hs⟩
    have hclamp : Set.projIcc (0:ℝ) 1 zero_le_one (s/τ)=r :=
      Set.projIcc_of_mem zero_le_one r.property
    have hreal : (circleParabolicSegmentTime τ hτ 0 r:ℝ)=s := by
      simp only [circleParabolicSegmentTime,Nat.cast_zero,zero_div,zero_add,r]
      change τ*(s/τ)=s
      field_simp [hτ.ne'] <;> ring
    have hchart : circleParabolicSegmentTime τ hτ 0 r=Real.toNNReal s :=
      Subtype.ext (hreal.trans (Real.coe_toNNReal s hs.1).symm)
    rw [hclamp]
    exact congrArg value ((congrArg u hchart.symm).trans (hrep r))
  have hactual : HasDerivWithinAt (fun s : ℝ => value (u (Real.toNNReal s)))
      v (Icc (0:ℝ) τ) 0 :=
    hscaled.congr_of_mem heq (show (0:ℝ) ∈ Icc (0:ℝ) τ from ⟨le_rfl,hτ.le⟩)
  exact hactual.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hτ)

end Lemniscate
