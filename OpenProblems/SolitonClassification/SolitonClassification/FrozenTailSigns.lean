import SolitonClassification.FrozenStressBounds
import SolitonClassification.FrozenStressTail

/-! Strict signs on complete outgoing tails. The uniform estimate already
    places the negative trajectory inside the region of the sharper estimate,
    so the argument needs no bootstrap at a hypothetical first crossing. -/
noncomputable section
namespace ClosedSimilarity.FrozenStress.Orbit
open Set

def rawI (z : Orbit) (s : ℝ) := z.root s*z.across s
abbrev J (z : Orbit) := correctedImpact z.root z.shape z.slope z.along z.across
abbrev H (z : Orbit) := correctedOutgoing z.root z.shape z.slope z.along z.across

private theorem radial_monotone (z : Orbit) : Antitone z.radial :=
  antitone_of_deriv_nonpos (fun s => (z.radial_hasDerivAt s).differentiableAt)
    (fun s => by rw [(z.radial_hasDerivAt s).deriv]; exact neg_nonpos.mpr (sq_nonneg _))

private structure Late (z : Orbit) (s : ℝ) : Prop where
  pos : 0 < z.amplitude s
  lower : 3.4 < z.root s
  cap : z.H s-0.15 ≤ z.amplitude s
  radial : |z.H s+z.radial s| ≤ 0.15
  impact : |z.rawI s-z.J s| ≤ 0.04
  dh : 0.28 ≤ deriv z.H s
  dj : |deriv z.J s| ≤ 0.77/z.amplitude s^2
  sharp : |z.rawI s| ≤ 0.37 → 0.61 ≤ deriv z.H s ∧ |deriv z.J s| ≤ 0.37/z.amplitude s^2

private theorem late_data (z : Orbit) (s : ℝ) (large : 12 < -z.radial s) : Late z s := by
  have amp_nonneg : 0 ≤ z.amplitude s := Real.sqrt_nonneg _
  have ar : -z.radial s ≤ z.amplitude s := by
    nlinarith [z.stress_unit s,sq_nonneg (z.transverse s)]
  have big : 12 < z.amplitude s := large.trans_le ar
  have pos : 0 < z.amplitude s := by linarith
  have rates := z.normalized_rates s pos
  have rsq : z.root s^2=z.amplitude s := Real.sq_sqrt pos.le
  have rootpos := rates.pos
  have rootbig : 3.4 < z.root s := by nlinarith
  have cube : (3.4:ℝ)^3 ≤ z.root s^3 := pow_le_pow_left₀ (by norm_num) rootbig.le _
  have fourth : z.root s^4=z.amplitude s^2 := by rw [←rsq]; ring
  have along : z.root s^2*z.along s=z.radial s := by
    rw [rsq,Orbit.along]; field_simp [pos.ne']
  have chi := chi_bound rates.oscillator rates.unit
  have psi := psi_bound rates.oscillator rates.unit
  have rad : |z.H s+z.radial s| ≤ 0.15 := by
    change |-(z.root s^2*z.along s)-_/z.root s+z.radial s| ≤ _
    rw [along,show ∀ x v : ℝ, -x-v+x = -v by intros; ring,abs_neg,abs_div,abs_of_pos rootpos]
    apply (div_le_iff₀ rootpos).mpr
    linarith
  have raw : |z.rawI s-z.J s| ≤ 0.04 := by
    change |z.root s*z.across s-(z.root s*z.across s-_/z.root s^2)| ≤ _
    rw [sub_sub_cancel,abs_div,abs_of_pos (pow_pos rootpos 2),rsq]
    apply (div_le_iff₀ pos).mpr
    linarith
  obtain ⟨jrate,hrate⟩ := z.corrector_rates_bounded s pos
  have small : 1.66/z.root s^3 < 0.043 := (div_lt_iff₀ (pow_pos rootpos 3)).mpr (by norm_num at cube; linarith)
  have dh := (abs_lt.mp hrate).1
  change -(1.66/z.root s^3) < deriv z.H s - (1+z.along s^2)/3 at dh
  refine ⟨pos,rootbig,by linarith [(abs_le.mp rad).2],rad,raw,by nlinarith [sq_nonneg (z.along s)],?_,?_⟩
  · simpa only [fourth] using jrate.le
  · intro hI
    change |z.root s*z.across s| ≤ 0.37 at hI
    rw [abs_mul,abs_of_pos rootpos] at hI
    have ac : |z.across s| ≤ 0.121 := by
      by_contra! bad
      nlinarith [mul_le_mul_of_nonneg_left bad.le rootpos.le]
    have uy := rates.unit
    have b2 := pow_le_pow_left₀ (abs_nonneg _) ac 2
    rw [sq_abs] at b2
    exact ⟨by nlinarith,by simpa only [fourth] using (z.corrector_impact_small s pos ac).le⟩

private theorem drift_from (z : Orbit) {S T B c : ℝ} (st : S ≤ T) (big : 12 < -z.radial S)
    (hB : 0 ≤ B) (hc : 0 < c)
    (rates : ∀ x ∈ Icc S T, c ≤ deriv z.H x ∧ |deriv z.J x| ≤ B/(z.amplitude x)^2) :
    |z.J T-z.J S| ≤ B/(c*(z.H S-0.15)) := by
  have rad (x : ℝ) (hx : x ∈ Icc S T) := (radial_monotone z hx.1)
  have good (x : ℝ) (hx : x ∈ Icc S T) := late_data z x (by linarith [rad x hx])
  apply corrected_tail st hB hc
    (fun x hx => (z.corrected_outgoing_rate x (good x hx).pos).continuousAt.continuousWithinAt)
    (fun x hx => (z.corrected_impact_rate x (good x hx).pos).continuousAt.continuousWithinAt)
    (fun x hx => by linarith [(abs_le.mp (good x hx).radial).1,rad x hx])
  intro x hx
  have inside : x ∈ Icc S T := ⟨hx.1.le,hx.2.le⟩
  have G := good x inside
  exact ⟨(z.corrected_outgoing_rate x G.pos).differentiableAt,(z.corrected_impact_rate x G.pos).differentiableAt,
    (rates x inside).1,(rates x inside).2,G.cap⟩

/-- A far positive endpoint has a uniformly positive *uncorrected*
    impact at every subsequent time of the actual frozen ODE. -/
theorem positive_raw_tail (z : Orbit) {S : ℝ} (big : 12 < -z.radial S) (start : 0.8 < z.J S)
    {t : ℝ} (st : S ≤ t) : 0.52 < z.rawI t := by
  have G (x : ℝ) (hx : S ≤ x) := late_data z x (by linarith [radial_monotone z hx])
  have d := drift_from z st big (by norm_num : (0:ℝ) ≤ 0.77) (by norm_num : (0:ℝ) < 0.28)
    (fun x hx => ⟨(G x hx.1).dh,(G x hx.1).dj⟩)
  have lower : 11.7 < z.H S-0.15 := by linarith [(abs_le.mp (G S le_rfl).radial).1]
  have tiny : 0.77/(0.28*(z.H S-0.15)) < 0.24 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
  linarith [(abs_le.mp (G t st).impact).1,(abs_le.mp d).1]

/-- A negative outgoing certificate keeps the actual impact strictly on the
    negative side on the entire tail, already before passage to a limit. -/
theorem negative_raw_tail (z : Orbit) {S : ℝ} (big : 13 < -z.radial S)
    (lo : -0.10 < z.J S) (hi : z.J S < -0.09) {t : ℝ} (st : S ≤ t) : z.rawI t < -0.002 := by
  have large : 12 < -z.radial S := by linarith
  have G (x : ℝ) (hx : S ≤ x) := late_data z x (by linarith [radial_monotone z hx])
  have lower : 12.7 < z.H S-0.15 := by linarith [(abs_le.mp (G S le_rfl).radial).1]
  have easy : 0.77/(0.28*(z.H S-0.15)) < 0.22 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
  have inside (x : ℝ) (hx : S ≤ x) : |z.rawI x| ≤ 0.37 := by
    have d := drift_from z hx large (by norm_num : (0:ℝ) ≤ 0.77) (by norm_num : (0:ℝ) < 0.28)
      (fun y hy => ⟨(G y hy.1).dh,(G y hy.1).dj⟩)
    have p := abs_le.mp (G x hx).impact
    have q := abs_le.mp d
    exact abs_le.mpr ⟨by linarith [p.1,q.1],by linarith [p.2,q.2]⟩
  have d := drift_from z st large (by norm_num : (0:ℝ) ≤ 0.37) (by norm_num : (0:ℝ) < 0.61)
    (fun y hy => (G y hy.1).sharp (inside y hy.1))
  have tiny : 0.37/(0.61*(z.H S-0.15)) < 0.048 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
  linarith [(abs_le.mp (G t st).impact).2,(abs_le.mp d).2]

end ClosedSimilarity.FrozenStress.Orbit
#print axioms ClosedSimilarity.FrozenStress.Orbit.negative_raw_tail
#print axioms ClosedSimilarity.FrozenStress.Orbit.positive_raw_tail
