import SolitonClassification.FullQuarterOrientation
import SolitonClassification.CentreFastCoordinates

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open CrossingResponse

namespace MatchedSequence
variable {H E B : ℝ} {c : CentreChart H E B} {w : WindingChart H E} {f : w.Flight}
variable (s : MatchedSequence c w f)

def physicalSeam (i : ℕ) := c.time (s.marker i)+f.length (s.seamParameter i)
def slowEnd (i : ℕ) := Real.sqrt (s.marker i:ℝ)⁻¹*s.physicalSeam i
def fastEnd (i : ℕ) := Real.sqrt (s.marker i:ℝ)*s.physicalSeam i
def raySlope (i : ℕ) :=
  X (((s.marker i:ℝ)^2)⁻¹) (s.fastEnd i) / Y (((s.marker i:ℝ)^2)⁻¹) (s.fastEnd i)

theorem fastEnd_eq (i : ℕ) (bp : 0<(s.marker i:ℝ)) :
    (s.marker i:ℝ)*s.slowEnd i=s.fastEnd i := by
  let q : ℝ := s.marker i
  have rs : (Real.sqrt q)^2=q := Real.sq_sqrt bp.le
  change q*(Real.sqrt q⁻¹*s.physicalSeam i)=Real.sqrt q*s.physicalSeam i
  have cancel : q*(Real.sqrt q)⁻¹=Real.sqrt q := by
    rw [←div_eq_mul_inv]
    apply (div_eq_iff (Real.sqrt_pos.mpr bp).ne').mpr
    nlinarith only [rs]
  rw [Real.sqrt_inv,←mul_assoc,cancel]

theorem slowEnd_large (a : c.FirstIncoming) (i : ℕ) (bp : 0<(s.marker i:ℝ)) :
    1/2≤s.slowEnd i := by
  let g := Real.sqrt (s.marker i:ℝ)⁻¹
  have gp : 0<g := Real.sqrt_pos.mpr (inv_pos.mpr bp)
  have eql : s.slowEnd i=a.slow (s.marker i)+g*f.length (s.seamParameter i) := by
    unfold slowEnd physicalSeam
    rw [a.arclength]
    change g*(_/g+_)=_
    field_simp [gp.ne']
  rw [eql]
  linarith [(a.time_bounds (s.marker i)).1,mul_pos gp (s.flight_positive i)]

end MatchedSequence

/-- The seam slope tends to zero along every unbounded sequence of matched
physical shooting data. The companion uniform estimate covers every point of
the late quarter, in the same fast coordinates used to count its crossings. -/
theorem matched_seam_ray_limit :
    ∃ H₀≥2, ∀ {H E B : ℝ} (c : CentreChart H E B) (w : WindingChart H E)
      (_a : c.FirstIncoming) (f : w.Flight), H₀≤H → ∀ s : MatchedSequence c w f,
      Tendsto s.raySlope atTop (𝓝 0) ∧
      ∀ ε>0, ∀ᶠ i in atTop, ∀ u∈Icc (1/2:ℝ) (s.slowEnd i),
        let b : ℝ := s.marker i
        |X ((b^2)⁻¹) (b*u)|≤b*ε ∧ b/4800≤Y ((b^2)⁻¹) (b*u) := by
  obtain ⟨H₀,h₀,full⟩ := full_quarter_orientation
  refine ⟨H₀,h₀,?_⟩
  intro H E B c w a f high s
  have uniform (ε : ℝ) (he : 0<ε) :
      ∀ᶠ i in atTop, ∀ u∈Icc (1/2:ℝ) (s.slowEnd i),
        let b : ℝ := s.marker i
        |X ((b^2)⁻¹) (b*u)|≤b*ε ∧ b/4800≤Y ((b^2)⁻¹) (b*u) := by
    obtain ⟨Q,hQ,use⟩ := full c w a f high ε he
    filter_upwards [s.unbounded_marker.eventually_ge_atTop Q] with i large
    let b : ℝ := s.marker i
    have bp : 0<b := hQ.trans_le large
    intro u hu
    have h := use (s.marker i) large bp (s.seamParameter i) u hu
    obtain ⟨hx,hy⟩ := slow_fast_position bp u
    change |(centreData b bp).labX (centreData b bp).laboratoryAngle u|≤ε ∧
      1/4800≤(centreData b bp).labY (centreData b bp).laboratoryAngle u at h
    rw [hx,hy,abs_mul,abs_of_pos (inv_pos.mpr bp)] at h
    constructor
    · have g := mul_le_mul_of_nonneg_left h.1 bp.le
      rwa [←mul_assoc,mul_inv_cancel₀ bp.ne',one_mul] at g
    · have g := mul_le_mul_of_nonneg_left h.2 bp.le
      rw [←mul_assoc,mul_inv_cancel₀ bp.ne',one_mul] at g
      linarith only [g]
  refine ⟨?_,uniform⟩
  apply Metric.tendsto_nhds.mpr
  intro ε he
  filter_upwards [uniform (ε/9600) (by positivity),s.unbounded_marker.eventually_gt_atTop 0] with i data bp
  have h := data (s.slowEnd i) ⟨s.slowEnd_large a i bp,le_rfl⟩
  let b : ℝ := s.marker i
  change |X ((b^2)⁻¹) (b*s.slowEnd i)|≤b*(ε/9600) ∧ b/4800≤Y ((b^2)⁻¹) (b*s.slowEnd i) at h
  rw [show b*s.slowEnd i=s.fastEnd i from s.fastEnd_eq i bp] at h
  have yp : 0<Y ((b^2)⁻¹) (s.fastEnd i) := (by positivity : (0:ℝ)<b/4800).trans_le h.2
  rw [Real.dist_eq,sub_zero,MatchedSequence.raySlope,abs_div,abs_of_pos yp]
  apply (div_lt_iff₀ yp).mpr
  nlinarith only [h.1,mul_le_mul_of_nonneg_left h.2 he.le,mul_pos bp he]

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.matched_seam_ray_limit

