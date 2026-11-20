import SolitonClassification.FrozenEscapeScalar

noncomputable section
open Set
namespace ClosedSimilarity.FrozenStress.Orbit
variable (z : Orbit)

def outgoingHeight := correctedOutgoing z.root z.shape z.slope z.along z.across

theorem angle_bounds (x : ℝ) : |z.p x|≤1 ∧ |z.q x|≤1 := by
  have u := z.unit x
  constructor <;> apply abs_le.mpr <;> constructor <;> nlinarith [sq_nonneg (z.p x),sq_nonneg (z.q x)]

theorem large_amplitude_height {x : ℝ} (ha : 12≤z.amplitude x) :
    |z.outgoingHeight x+z.radial x| ≤ 1 ∧ 1/4≤deriv z.outgoingHeight x := by
  have ap : 0<z.amplitude x := by linarith
  have rs := z.normalized_rates x ap
  have r2 : z.root x^2=z.amplitude x := Real.sq_sqrt ap.le
  have rp := rs.pos
  have rbig : 3≤z.root x := by nlinarith
  have r3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) rbig 3
  have ch := chi_bound rs.oscillator rs.unit
  have ra : z.root x^2*z.along x=z.radial x := by rw [r2,Orbit.along]; field_simp
  constructor
  · change |-(z.root x^2*z.along x)-_/z.root x+z.radial x|≤1
    rw [ra,show ∀ x y : ℝ, -x-y+x = -y by intros; ring,abs_neg,abs_div,abs_of_pos rp]
    exact (div_le_iff₀ rp).mpr (by linarith)
  · have hr := (abs_lt.mp (z.corrector_rates_bounded x ap).2).1
    change -(1.66/z.root x^3)<deriv z.outgoingHeight x-(1+z.along x^2)/3 at hr
    have small : 1.66/z.root x^3≤1/12 := (div_le_iff₀ (pow_pos rp _)).mpr (by norm_num at r3; linarith)
    nlinarith only [hr,small,sq_nonneg (z.along x)]

theorem radial_antitone : Antitone z.radial :=
  antitone_of_deriv_nonpos (fun s => (z.radial_hasDerivAt s).differentiableAt)
    (fun s => by rw [(z.radial_hasDerivAt s).deriv]; exact neg_nonpos.mpr (sq_nonneg _))

/-- A putative lower radial barrier bounds the transverse stress as well.
Large transverse stress would supply a long entire interval of rapid outgoing
drift because the transverse coordinate has speed at most one. -/
theorem transverse_bound_of_radial_barrier {M : ℝ} (hM : 0≤M) (zero : z.radial 0=0)
    (barrier : ∀ t≥0,-z.radial t≤M) (s : ℝ) (hs : 0≤s) :
    |z.transverse s|≤12+4*(M+4) := by
  let T := 4*(M+4)
  have tp : 0<T := by dsimp [T]; linarith
  by_contra! far
  have vb (x : ℝ) (_ : 0≤x) : |z.p x*z.q x|≤1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (z.angle_bounds x).1 (z.angle_bounds x).2 (abs_nonneg _) zero_le_one
  have high (x : ℝ) (hx : x∈Icc s (s+T)) : 12≤z.amplitude x := by
    have l := scalar_segment_bound z.transverse_hasDerivAt hs hx.1 vb
    have tri := abs_add_le (z.transverse s-z.transverse x) (z.transverse x)
    rw [sub_add_cancel,abs_sub_comm] at tri
    have big : 12≤|z.transverse x| := by change 12+T < |z.transverse s| at far; linarith [hx.2]
    have amp : 0≤z.amplitude x := Real.sqrt_nonneg _
    have e := z.stress_unit x
    have aa : |z.transverse x|≤z.amplitude x := by nlinarith [sq_abs (z.transverse x),sq_nonneg (z.radial x)]
    exact big.trans aa
  have sub : s<s+T := by linarith
  have d (x : ℝ) (hx : x∈Icc s (s+T)) : DifferentiableAt ℝ z.outgoingHeight x :=
    (z.corrected_outgoing_rate x (by linarith [high x hx])).differentiableAt
  obtain ⟨x,hx,e⟩ := exists_deriv_eq_slope z.outgoingHeight sub
    (fun x hx => (d x hx).continuousAt.continuousWithinAt)
    (fun x hx => (d x ⟨hx.1.le,hx.2.le⟩).differentiableWithinAt)
  rw [add_sub_cancel_left] at e
  have step := (le_div_iff₀ tp).mp ((z.large_amplitude_height (high x ⟨hx.1.le,hx.2.le⟩)).2.trans_eq e)
  have h1 := (abs_le.mp (z.large_amplitude_height (high s ⟨le_rfl,sub.le⟩)).1).1
  have h2 := (abs_le.mp (z.large_amplitude_height (high (s+T) ⟨sub.le,le_rfl⟩)).1).2
  have lo := z.radial_antitone hs
  rw [zero] at lo
  have hi := barrier (s+T) (by linarith)
  dsimp [T] at step
  linarith

end ClosedSimilarity.FrozenStress.Orbit
#print axioms ClosedSimilarity.FrozenStress.Orbit.transverse_bound_of_radial_barrier
