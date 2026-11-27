import SolitonClassification.CentreRayLimit
import SolitonClassification.CentreFirstSection

noncomputable section
open Set
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open OuterStress

/-- Independent of the choice of the incoming chart. Every certified first
crossing of any sufficiently high section is reached along the same positive
vertical sector in the centre laboratory frame, uniformly up to the marker. -/
theorem first_section_positive_ray :
    ∃ H₀≥2, ∀ ε>0, ∃ B>0, ∀ b≥B, ∀ (bp : 0<b) (H : ℝ), H₀≤H →
      ∀ (τ : ℝ), (∀s∈Ico (1:ℝ) τ, H < -height (centreAt b s)) →
      (∀s∈Ico (1:ℝ) τ, regular (centreAt b s) ∧ 1 ≤ innerRoot (centreAt b s)) →
      ∀ t∈Icc (1/2:ℝ) τ,
        let z := centreData b bp
        |z.labX z.laboratoryAngle t|≤ε ∧ 1/2400-ε≤z.labY z.laboratoryAngle t := by
  obtain ⟨L,hL,C,_,rays⟩ := OuterStress.Data.central_shot_positive_ray
  have lp : 0<L := by linarith
  refine ⟨(1200*L)^2+2,by nlinarith [sq_nonneg (1200*L)],?_⟩
  intro ε he
  obtain ⟨d,dp,dir⟩ := rays L le_rfl ε he
  let B := max (32*L) (1/d)
  have bw : 32*L≤B := le_max_left ..
  have bd : 1/d≤B := le_max_right ..
  refine ⟨B,(by positivity : (0:ℝ)<32*L).trans_le bw,?_⟩
  intro b big bp H high τ before chart t ht
  have tiny : b⁻¹≤1/(32*L) := by
    rw [←one_div]; exact one_div_le_one_div_of_le (by positivity) (bw.trans big)
  have small : b⁻¹≤d := by
    rw [←one_div]; apply (div_le_iff₀ bp).mpr
    linarith [(div_le_iff₀ dp).mp (bd.trans big)]
  let z := centreData b bp
  have inits : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by
    simp [z,centreData,ofSupport,solution_zero,bp.ne']
  obtain ⟨T,hT,crit,strip,orient⟩ := dir z (inv_pos.mpr bp) small inits.1 inits.2.1 inits.2.2.1 inits.2.2.2
  have order := first_section_before_critical bp hL high tiny hT crit strip before chart
  exact orient t ⟨ht.1,ht.2.trans order⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.first_section_positive_ray
