import Lemniscate.PeriodicParabolicGlobalSolution
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual interior time derivatives pass from the overlapping parabolic
segments to the same global curve. This is only an affine chart argument;
the local differential equation remains the one proved for each segment.

-/
noncomputable section
namespace Lemniscate
open Set Filter
open scoped Topology NNReal

/-- Local classical time derivatives on the actual overlapping segments
give the global derivative at every positive physical time. The state
space H needs no topology; only its displayed value in V is differentiated.
-/
theorem circle_global_classical_time_derivative
    {H V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (τ : ℝ) (hτ : 0<τ) (value : H → V)
    (u : ℝ≥0 → H) (q : ℕ → unitInterval → H) (v : ℝ → V)
    (hrep : ∀ n r, u (circleParabolicSegmentTime τ hτ n r)=q n r)
    (hcover : ∀ t : ℝ≥0, 0<t → ∃ (n : ℕ) (r : unitInterval),
      0<(r:ℝ) ∧ (r:ℝ)<1 ∧ circleParabolicSegmentTime τ hτ n r=t)
    (hlocal : ∀ (n : ℕ) (r : unitInterval), 0<(r:ℝ) → (r:ℝ)<1 →
      HasDerivAt (fun s : ℝ => value (q n (Set.projIcc (0:ℝ) 1 zero_le_one s)))
        (τ • v (circleParabolicSegmentTime τ hτ n r)) (r:ℝ)) :
    ∀ σ : ℝ, 0<σ → HasDerivAt (fun s : ℝ => value (u (Real.toNNReal s))) (v σ) σ := by
  intro σ hσ
  obtain ⟨n,r,hr0,hr1,hr⟩ := hcover (Real.toNNReal σ) (Real.toNNReal_pos.mpr hσ)
  have htime : (circleParabolicSegmentTime τ hτ n r:ℝ)=σ :=
    (congrArg (fun t : ℝ≥0 => (t:ℝ)) hr).trans (Real.coe_toNNReal σ hσ.le)
  let ρ : ℝ → ℝ := fun s => s/τ-(n:ℝ)/2
  have hρσ : ρ σ=(r:ℝ) := by
    change σ/τ-(n:ℝ)/2=(r:ℝ)
    rw [← htime]
    change (τ*((n:ℝ)/2+(r:ℝ)))/τ-(n:ℝ)/2=(r:ℝ)
    field_simp [hτ.ne'] <;> ring
  have hρ : HasDerivAt ρ τ⁻¹ σ := by
    simpa only [one_div,id_eq] using!
      ((hasDerivAt_id σ).div_const τ).sub_const ((n:ℝ)/2)
  have hlocalσ : HasDerivAt
      (fun s : ℝ => value (q n (Set.projIcc (0:ℝ) 1 zero_le_one s)))
      (τ • v σ) (ρ σ) := by
    rw [hρσ]
    exact (hlocal n r hr0 hr1).congr_deriv (congrArg (fun t => τ • v t) htime)
  have hcomposed : HasDerivAt
      (fun s : ℝ => value (q n (Set.projIcc (0:ℝ) 1 zero_le_one (ρ s))))
      (v σ) σ := by
    apply (hlocalσ.scomp σ hρ).congr_deriv
    simp only [smul_smul,inv_mul_cancel₀ hτ.ne',one_smul]
  have hρ0 : 0<ρ σ := by rw [hρσ]; exact hr0
  have hρ1 : ρ σ<1 := by rw [hρσ]; exact hr1
  have hinside : ∀ᶠ s in 𝓝 σ, ρ s∈Ioo (0:ℝ) 1 :=
    hρ.continuousAt.eventually (Ioo_mem_nhds hρ0 hρ1)
  have hagree : (fun s : ℝ => value (u (Real.toNNReal s))) =ᶠ[𝓝 σ]
      (fun s : ℝ => value (q n (Set.projIcc (0:ℝ) 1 zero_le_one (ρ s)))) := by
    filter_upwards [hinside,isOpen_Ioi.mem_nhds hσ] with s hs hpos
    let r' : unitInterval := ⟨ρ s,hs.1.le,hs.2.le⟩
    have hclamp : Set.projIcc (0:ℝ) 1 zero_le_one (ρ s)=r' :=
      Set.projIcc_of_mem zero_le_one r'.property
    have hchart : circleParabolicSegmentTime τ hτ n r'=Real.toNNReal s := by
      apply Subtype.ext
      change τ*((n:ℝ)/2+ρ s)=(Real.toNNReal s:ℝ)
      rw [Real.coe_toNNReal s hpos.le]
      dsimp only [ρ]
      field_simp [hτ.ne'] <;> ring
    change value (u (Real.toNNReal s))=
      value (q n (Set.projIcc (0:ℝ) 1 zero_le_one (ρ s)))
    rw [hclamp]
    exact congrArg value ((congrArg u hchart.symm).trans (hrep n r'))
  exact hcomposed.congr_of_eventuallyEq hagree

end Lemniscate
