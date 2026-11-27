import SolitonClassification.IncomingSectionOrientation
import SolitonClassification.MatchedCrossingSequence

noncomputable section
open Set
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open OuterStress

/-- On the whole late part of the same physical quarter, including the flight
from its first incoming section to its actual seam, the scaled x-coordinate
is uniformly small and the scaled y-coordinate is bounded away from zero. -/
theorem full_quarter_orientation :
    ∃ H₀≥2, ∀ {H E B : ℝ} (c : CentreChart H E B) (w : WindingChart H E)
      (_a : c.FirstIncoming) (f : w.Flight), H₀≤H →
      ∀ ε>0, ∃ Q>0, ∀ (b : Ici B), Q≤(b:ℝ) → ∀ (bp : 0<(b:ℝ)) (p : ChartDomain E),
      ∀ t∈Icc (1/2:ℝ) (Real.sqrt (b:ℝ)⁻¹*(c.time b+f.length p)),
        let z := centreData b bp
        |z.labX z.laboratoryAngle t|≤ε ∧ 1/4800≤z.labY z.laboratoryAngle t := by
  obtain ⟨H₀,h₀,ray⟩ := first_section_positive_ray
  refine ⟨H₀,h₀,?_⟩
  intro H E B c w a f high ε he
  obtain ⟨M,hM,length⟩ := f.bounded_length
  let m := min (1/12000:ℝ) (ε/2)
  have mp : 0<m := lt_min (by norm_num) (by positivity)
  have mcap : m≤1/12000 := min_le_left ..
  have me : m≤ε/2 := min_le_right ..
  obtain ⟨Q,hQ,first⟩ := ray m mp
  refine ⟨max Q ((M/m)^2),hQ.trans_le (le_max_left ..),?_⟩
  intro b big bp p t ht
  have bQ := (le_max_left ..).trans big
  have bM := (le_max_right ..).trans big
  let g := Real.sqrt (b:ℝ)⁻¹
  let r := Real.sqrt (b:ℝ)
  have rp : 0<r := Real.sqrt_pos.mpr bp
  have gp : 0<g := Real.sqrt_pos.mpr (inv_pos.mpr bp)
  have gm : g=r⁻¹ := Real.sqrt_inv _
  have wdt : M/m≤r := le_of_sq_le_sq (bM.trans_eq (Real.sq_sqrt bp.le).symm) rp.le
  have small : g*|f.length p|≤m := by
    apply (mul_le_mul_of_nonneg_left (length p) gp.le).trans
    rw [gm,inv_mul_eq_div]
    exact (div_le_iff₀ rp).mpr (by linarith [(div_le_iff₀ mp).mp wdt])
  have endtime : g*(c.time b+f.length p)=a.slow b+g*f.length p := by
    rw [a.arclength b]
    change g*(a.slow b/g+f.length p)=_
    field_simp [gp.ne']
  change t∈Icc (1/2:ℝ) (g*(c.time b+f.length p)) at ht
  rw [endtime] at ht
  let s := min t (a.slow b)
  have hs : s∈Icc (1/2:ℝ) (a.slow b) :=
    ⟨le_min ht.1 (by linarith [(a.time_bounds b).1]),min_le_right ..⟩
  have st : s≤t := min_le_left ..
  have ds : t-s≤m := by
    by_cases before : t≤a.slow b
    · simp only [s,min_eq_left before,sub_self]; exact mp.le
    · rw [show s=a.slow b from min_eq_right (le_of_not_ge before)]
      linarith [ht.2,mul_le_mul_of_nonneg_left (le_abs_self (f.length p)) gp.le]
  let z := centreData b bp
  have atS := first b bQ bp H high (a.slow b) (a.earlier b)
    (fun x hx => let h := a.segment b x (Ico_subset_Icc_self hx); ⟨h.1,h.2.1⟩) s hs
  have changePos := z.lab_lipschitz st (inv_pos.mpr bp) (θ:=z.laboratoryAngle)
    (fun x _ => z.laboratoryAngle_rate x)
  change |z.labX z.laboratoryAngle s|≤m ∧ 1/2400-m≤z.labY z.laboratoryAngle s at atS
  have chord := abs_sub_le (z.labX z.laboratoryAngle t) (z.labX z.laboratoryAngle s) 0
  simp only [sub_zero] at chord
  exact ⟨by linarith [changePos.1,atS.1],by linarith [(abs_le.mp changePos.2).1,atS.2]⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.full_quarter_orientation

