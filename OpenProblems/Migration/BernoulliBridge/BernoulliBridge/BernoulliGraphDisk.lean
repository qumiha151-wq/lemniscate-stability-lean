import Lemniscate.LemniscateStabilityStatement
import Lemniscate.BernoulliLocalFlowChartData
import Lemniscate.ArclengthOrbitCharacterization
import Migration.BernoulliPerturbation

noncomputable section
namespace Lemniscate
open Set MeasureTheory Complex
open MigrationGeometry

private def physicalRotation (α : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  { DistribMulAction.toLinearEquiv ℝ ℂ (Circle.exp α) with
    norm_map' x := by
      change ‖((Circle.exp α:Circle):ℂ)*x‖=‖x‖
      rw [norm_mul,Circle.norm_coe,one_mul] }

/-- The actual arclength reference of the stability theorem traverses the
same rational trigonometric curve used in the physical hull estimate. -/
theorem bernoulli_reference_disk_range (e : ℝ ≃o ℝ) :
    range (lemniscateReference e)=range BernoulliDisk.profile := by
  have eq (θ : ℝ) : bernoulliCurve θ=BernoulliDisk.profile θ := by
    apply Complex.ext
    · simp only [bernoulliCurve,BernoulliDisk.profile,Complex.add_re,Complex.mul_I_re,
        Complex.ofReal_re,Complex.ofReal_im,neg_zero,add_zero]
    · simp only [bernoulliCurve,BernoulliDisk.profile,Complex.add_im,Complex.mul_I_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_add]
      ring
  ext z
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨_,(eq (e.symm (Real.sqrt 2*s))).symm⟩
  · rintro ⟨θ,rfl⟩
    refine ⟨e θ/Real.sqrt 2,?_⟩
    change bernoulliCurve (e.symm (Real.sqrt 2*(e θ/Real.sqrt 2)))=_
    rw [show Real.sqrt 2*(e θ/Real.sqrt 2)=e θ by field_simp,e.symm_apply_apply,eq]

/-- A graph in the genuine oriented Bernoulli orbit gives a two-sided
physical Hausdorff bound. The original orientation-preserving change of
parameter and the physical rotation are both retained. -/
theorem bernoulli_oriented_graph_tracks (e : ℝ ≃o ℝ)
    (he : ∀u,e u=∫t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (h : ℝ→ℝ) (p : ℂ) (α ρ ε ell : ℝ) (hρ : 0<ρ) (height : ∀s,|h s|≤ε)
    (Yslice : ℝ→ℂ)
    (orbit : OrientedCurveEquivalent Yslice (fun s=>p+(ρ:ℂ)*(exp ((α:ℂ)*I)*
      normalGraphCurve (lemniscateReference e) (fun v=>I*bernoulliAuxiliaryTangent e (Real.sqrt 2*v)) h s))
      (2*Real.pi) ell) : BernoulliDisk.Tracks (range Yslice) p ρ ε := by
  let β := lemniscateReference e
  let ν := fun s=>I*bernoulliAuxiliaryTangent e (Real.sqrt 2*s)
  let G := fun s=>p+(ρ:ℂ)*(exp ((α:ℂ)*I)*normalGraphCurve β ν h s)
  obtain ⟨χ,_,_,_,tracking⟩ := orbit
  have same : range Yslice=range G := by
    ext z
    constructor
    · rintro ⟨u,rfl⟩
      refine ⟨χ.symm u,?_⟩
      have val := (tracking (χ.symm u)).symm
      simpa only [χ.apply_symm_apply] using val
    · rintro ⟨u,rfl⟩
      exact ⟨χ u,tracking u⟩
  rw [same]
  apply BernoulliDisk.tracks_of_parametrized_error G β (bernoulli_reference_disk_range e) p ρ ε (physicalRotation α)
  intro s
  have unit : ‖ν s‖=1 := by
    change ‖I * bernoulliAuxiliaryTangent e (Real.sqrt 2*s)‖=1
    rw [norm_mul,norm_I,one_mul]
    exact (bernoulli_arclength_frame e he s).2.1
  have rot : ‖exp ((α:ℂ)*I)‖=1 := by simp [Complex.norm_exp]
  rw [dist_eq_norm,Complex.real_smul]
  change ‖G s-(p+(ρ:ℂ)*(exp ((α:ℂ)*I)*β s))‖≤ρ*ε
  have delta : G s-(p+(ρ:ℂ)*(exp ((α:ℂ)*I)*β s))=
      (ρ:ℂ)*(exp ((α:ℂ)*I)*((h s:ℂ)*ν s)) := by
    dsimp only [G,normalGraphCurve];ring
  rw [delta,norm_mul,norm_mul,norm_mul,rot,unit,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hρ,mul_one,one_mul]
  exact mul_le_mul_of_nonneg_left (height s) hρ.le

theorem bernoulli_oriented_graph_disk_of_height (e : ℝ ≃o ℝ)
    (he : ∀u,e u=∫t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (h : ℝ→ℝ) (p : ℂ) (α ρ ell d : ℝ) (hρ : 0<ρ) (hd : d<BernoulliDisk.radius)
    (height : ∀s,|h s|≤d) (Yslice : ℝ→ℂ)
    (cont : Continuous Yslice) (per : Function.Periodic Yslice (2*Real.pi))
    (orbit : OrientedCurveEquivalent Yslice (fun s=>p+(ρ:ℂ)*(exp ((α:ℂ)*I)*
      normalGraphCurve (lemniscateReference e) (fun v=>I*bernoulliAuxiliaryTangent e (Real.sqrt 2*v)) h s))
      (2*Real.pi) ell) :
    Metric.closedBall p (ρ*(BernoulliDisk.radius-d)) ⊆ convexHull ℝ (range Yslice) := by
  have compact : IsCompact (range Yslice) := by
    have eq : range Yslice=Yslice '' Icc 0 (2*Real.pi) := by
      ext z
      constructor
      · rintro ⟨u,rfl⟩
        obtain ⟨v,hv,same⟩ := per.exists_mem_Ico₀ (by positivity) u
        exact ⟨v,⟨hv.1,hv.2.le⟩,same.symm⟩
      · rintro ⟨u,_,rfl⟩
        exact mem_range_self u
    rw [eq]
    exact isCompact_Icc.image cont
  have fit := bernoulli_oriented_graph_tracks e he h p α ρ _ ell hρ height Yslice orbit
  exact (BernoulliDisk.disk_squeeze compact hρ hd fit).1

theorem bernoulli_oriented_graph_disk (e : ℝ ≃o ℝ)
    (he : ∀u,e u=∫t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (h : ℝ→ℝ) (p : ℂ) (α ρ ell : ℝ) (hρ : 0<ρ)
    (height : ∀s,|h s|≤BernoulliDisk.radius/2) (Yslice : ℝ→ℂ)
    (cont : Continuous Yslice) (per : Function.Periodic Yslice (2*Real.pi))
    (orbit : OrientedCurveEquivalent Yslice (fun s=>p+(ρ:ℂ)*(exp ((α:ℂ)*I)*
      normalGraphCurve (lemniscateReference e) (fun v=>I*bernoulliAuxiliaryTangent e (Real.sqrt 2*v)) h s))
      (2*Real.pi) ell) :
    Metric.closedBall p (ρ*(BernoulliDisk.radius/2)) ⊆ convexHull ℝ (range Yslice) := by
  have disk := bernoulli_oriented_graph_disk_of_height e he h p α ρ ell _ hρ
    (by linarith [BernoulliDisk.radius_pos]) height Yslice cont per orbit
  rwa [show BernoulliDisk.radius-BernoulliDisk.radius/2=BernoulliDisk.radius/2 by ring] at disk

end Lemniscate
#print axioms Lemniscate.bernoulli_oriented_graph_disk
