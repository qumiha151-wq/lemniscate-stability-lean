import SolitonClassification.FrozenSeamSection
import SolitonClassification.FrozenUniformEscape
import SolitonClassification.FrozenTailSigns
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.FrozenStress.Orbit

/-- The raw, physical transverse coordinate has a uniform Cauchy error on
    every tail starting beyond radial stress R. -/
theorem scattering_tail (z : Orbit) {R S T : ℝ} (hR : 12 ≤ R) (hs : R ≤ -z.radial S)
    (st : S ≤ T) : |z.rawI T-z.rawI S| ≤ 8/R := by
  have Rpos : 0<R := by linarith
  have radial (x : ℝ) (hx : S≤x) : R ≤ -z.radial x := by linarith [z.radial_antitone hx]
  have dom (x : ℝ) : -z.radial x ≤ z.amplitude x := by
    nlinarith [show 0 ≤ z.amplitude x from Real.sqrt_nonneg _,z.stress_unit x,sq_nonneg (z.transverse x)]
  have pos (x : ℝ) (hx : S≤x) : 0 < z.amplitude x := Rpos.trans_le ((radial x hx).trans (dom x))
  have good (x : ℝ) (hx : S≤x) := z.large_amplitude_height ((hR.trans (radial x hx)).trans (dom x))
  have diff (x : ℝ) (hx : S≤x) : |z.rawI x-z.J x| ≤ 1/R := by
    have P := pos x hx
    have rates := z.normalized_rates x P
    have psi := psi_bound rates.oscillator rates.unit
    change |z.root x*z.across x - (z.root x*z.across x-_/(z.root x)^2)| ≤ _
    rw [sub_sub_cancel,abs_div,show z.root x^2=z.amplitude x from Real.sq_sqrt P.le,abs_of_pos P]
    apply (div_le_div_iff₀ P Rpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : |FrozenStress.psi (z.shape x)
      (z.slope x) (z.along x) (z.across x)| ≤ 1) Rpos.le,radial x hx,dom x]
  have drift : |z.J T-z.J S| ≤ 0.77/((1/4)*(z.outgoingHeight S-1)) := by
    apply corrected_tail (h := z.outgoingHeight) (A := z.amplitude) st (by norm_num) (by norm_num)
      (fun x hx => (z.corrected_outgoing_rate x (pos x hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => (z.corrected_impact_rate x (pos x hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => by linarith [(abs_le.mp (good x hx.1).1).1,radial x hx.1])
    intro x hx
    have P := pos x hx.1.le
    have rsq : z.root x^4 = z.amplitude x^2 := by
      rw [← Real.sq_sqrt P.le]; unfold root; ring
    refine ⟨(z.corrected_outgoing_rate x P).differentiableAt,(z.corrected_impact_rate x P).differentiableAt,
      (good x hx.1.le).2,by simpa only [rsq] using (z.corrector_rates_bounded x P).1.le,?_⟩
    linarith [(abs_le.mp (good x hx.1.le).1).2,dom x]
  have start := (abs_le.mp (good S le_rfl).1).1
  have denom : 0 < (1/4:ℝ)*(z.outgoingHeight S-1) := by linarith
  have budget : (0.77:ℝ)/((1/4)*(z.outgoingHeight S-1)) ≤ 6/R :=
    (div_le_div_iff₀ denom Rpos).mpr (by linarith)
  have b := abs_sub_le (z.rawI T) (z.J T) (z.J S)
  have c := abs_sub_le (z.rawI T) (z.J S) (z.rawI S)
  rw [abs_sub_comm (z.J S) (z.rawI S)] at c
  calc
    _ ≤ 1/R+6/R+1/R := c.trans (add_le_add (b.trans (add_le_add (diff T st) (drift.trans budget))) (diff S le_rfl))
    _ = _ := by ring

end ClosedSimilarity.FrozenStress.Orbit

namespace ClosedSimilarity.GlobalSupport
open FrozenStress

private lemma radial_cont (t : ℝ) : Continuous (fun c => (seam c).radial t) := by
  have h (i : Fin 4) := ((continuous_apply i).comp continuous_seam_coordinates).comp
    (continuous_const (y := t) |>.prodMk (continuous_id (X := ℝ)))
  exact ((((h 0).pow 2).div_const 2).mul (h 3)).add ((h 1).mul (h 2))

private lemma raw_cont {t : ℝ} (ht : 0<t) : Continuous (fun c => (seam c).rawI t) := by
  have h (i : Fin 4) := ((continuous_apply i).comp continuous_seam_coordinates).comp
    (continuous_const (y := t) |>.prodMk (continuous_id (X := ℝ)))
  have trans := continuous_seam_transverse.comp (continuous_const (y := t) |>.prodMk continuous_id)
  have amp : Continuous (fun c => (seam c).amplitude t) :=
    (((((h 0).pow 2).div_const 2).pow 2).add ((h 1).pow 2)).sqrt
  apply amp.sqrt.mul (trans.div amp ?_)
  intro c
  have r := seam_radial_strict c ht
  intro hz
  have e := (seam c).stress_unit t
  rw [hz] at e
  nlinarith [sq_pos_of_neg r,sq_nonneg ((seam c).transverse t)]

private lemma uniform_raw_cauchy (a b : ℝ) : UniformCauchySeqOn (fun t c => (seam c).rawI t)
    atTop (Icc a b) := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  let R := 12+16/ε
  have Rge : 12≤R := le_add_of_nonneg_right (by positivity)
  have small : 8/R<ε := (div_lt_iff₀ (by linarith : 0<R)).mpr (by
    dsimp [R]; field_simp; nlinarith [sq_nonneg ε])
  obtain ⟨T,_,large⟩ := uniform_seam_entrance (fun (c : Icc a b) => seam c)
    (fun c => by obtain ⟨_,hv,_,hq⟩ := seam_initial c; simp [Orbit.radial,hv,hq])
    (fun c => (seam_initial c).2.2.1) (fun t => (radial_cont t).comp continuous_subtype_val) R
  refine ⟨T,?_⟩
  intro s hs t ht c hc
  rw [Real.dist_eq]
  rcases le_total t s with h | h
  · exact ((seam c).scattering_tail Rge (large ⟨c,hc⟩ t ht).le h).trans_lt small
  · rw [abs_sub_comm]
    exact ((seam c).scattering_tail Rge (large ⟨c,hc⟩ s hs).le h).trans_lt small

theorem exists_scattering_impact (c : ℝ) : ∃ L : ℝ, Tendsto (seam c).rawI atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete ((uniform_raw_cauchy c c).cauchySeq (left_mem_Icc.mpr le_rfl))

def scatteringImpact (c : ℝ) : ℝ := (exists_scattering_impact c).choose

theorem scatteringImpact_limit (c : ℝ) : Tendsto (seam c).rawI atTop (𝓝 (scatteringImpact c)) :=
  (exists_scattering_impact c).choose_spec

/-- Uniform on every bounded interval of actual seam curvatures, including
    curvatures for which the stress may vanish inside the finite flight. -/
theorem uniform_scatteringImpact (a b : ℝ) :
    TendstoUniformlyOn (fun t c => (seam c).rawI t) scatteringImpact atTop (Icc a b) :=
  (uniform_raw_cauchy a b).tendstoUniformlyOn_of_tendsto (fun c _ => scatteringImpact_limit c)

theorem continuous_scatteringImpact : Continuous scatteringImpact := by
  rw [continuous_iff_continuousAt]
  intro c
  have cont := (uniform_scatteringImpact (c-1) (c+1)).continuousOn
    (((eventually_gt_atTop (0:ℝ)).mono fun t ht => (raw_cont ht).continuousOn).frequently)
  exact (cont c ⟨by linarith,by linarith⟩).continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- One fixed seam parameter, simultaneously in both infinite time directions. -/
theorem exists_zero_scattering {a b m n : ℝ} (hab : a<b) (hm : m<0) (hn : 0<n)
    (ha : ∀ᶠ t in atTop, (seam a).rawI t ≤ m) (hb : ∀ᶠ t in atTop, n ≤ (seam b).rawI t) :
    ∃ c ∈ Ioo a b, Tendsto (seam c).rawI atTop (𝓝 0) ∧ Tendsto (seam c).rawI atBot (𝓝 0) := by
  have lo := (le_of_tendsto (scatteringImpact_limit a) ha).trans_lt hm
  have hi := hn.trans_le (ge_of_tendsto (scatteringImpact_limit b) hb)
  obtain ⟨c,hc,hzero⟩ := intermediate_value_Ioo hab.le continuous_scatteringImpact.continuousOn
    (show (0:ℝ) ∈ Ioo (scatteringImpact a) (scatteringImpact b) from ⟨lo,hi⟩)
  have plus := hzero ▸ scatteringImpact_limit c
  have sym (t : ℝ) : (seam c).rawI (-t) = (seam c).rawI t :=
    ((seam c).seam_impact_radial_parity (seam_initial c).2.1 (seam_initial c).2.2.2 t).1
  refine ⟨c,hc,plus,?_⟩
  exact (plus.comp tendsto_neg_atBot_atTop).congr (fun t => sym t)

end ClosedSimilarity.GlobalSupport

namespace ClosedSimilarity.FrozenStress.Orbit

/-- At zero scattering impact the unnormalized transverse component itself
    vanishes at infinity. Quantitatively, its square is O(1/|radial|). -/
theorem transverse_decay_at_zero (z : Orbit) (zero : Tendsto z.rawI atTop (𝓝 0)) {s : ℝ}
    (hs : 12 ≤ -z.radial s) : (z.transverse s)^2 * (-z.radial s) ≤ 128 := by
  let H := -z.radial s
  let A := z.amplitude s
  let B := z.transverse s
  let I := z.rawI s
  let r := z.root s
  have hH : 12≤H := hs
  have P : 0<H := by linarith
  have hr : 0≤r := Real.sqrt_nonneg _
  have ap : 0≤A := Real.sqrt_nonneg _
  have rsq : r^2=A := Real.sq_sqrt ap
  have stress : H^2+B^2=A^2 := by simpa [H,B,A] using z.stress_unit s
  have apos : 0<A := by nlinarith [sq_nonneg B]
  have rel : B=I*r := by
    change z.transverse s=z.root s*(z.transverse s/z.amplitude s)*z.root s
    field_simp [show z.amplitude s≠0 from apos.ne']
    exact congrArg (z.transverse s * ·) rsq.symm
  have bound : |I|≤8/H := by
    have h := (zero.sub_const I).abs
    have d := le_of_tendsto h ((eventually_ge_atTop s).mono fun t ht => z.scattering_tail hs le_rfl ht)
    simpa only [zero_sub,abs_neg] using d
  have cap : |I| ≤ 1 := bound.trans ((div_le_one P).mpr (by linarith))
  have li := pow_le_pow_left₀ (abs_nonneg I) cap 2
  rw [sq_abs] at li
  have b2 : B^2=I^2*A := by rw [rel,mul_pow,rsq]
  have ab : B^2 ≤ A := by nlinarith only [b2,mul_le_mul_of_nonneg_right li ap]
  have maxA : A≤2*H := by
    by_contra! hn
    nlinarith only [stress,ab,hn,hH,mul_nonneg (by linarith : 0≤A-2*H)
      (by linarith : 0≤A+2*H-1),sq_nonneg (H-1)]
  have k := pow_le_pow_left₀ (mul_nonneg (abs_nonneg I) P.le) ((le_div_iff₀ P).mp bound) 2
  rw [mul_pow,sq_abs] at k
  change B^2*H≤128
  have fin := mul_le_mul_of_nonneg_left maxA (mul_nonneg (sq_nonneg I) P.le)
  rw [b2]
  nlinarith only [fin,k]

theorem transverse_tendsto_of_zero (z : Orbit) (initial : z.radial 0=0) (p0 : z.p 0=1)
    (zero : Tendsto z.rawI atTop (𝓝 0)) : Tendsto z.transverse atTop (𝓝 0) := by
  have escape := z.outgoing_radial_tendsto_atTop initial p0
  have lim : Tendsto (fun t => 128/(-z.radial t)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop escape
  have cap : Tendsto (fun t => Real.sqrt (128/(-z.radial t))) atTop (𝓝 0) := by simpa using lim.sqrt
  apply squeeze_zero_norm' _ cap
  filter_upwards [escape.eventually_ge_atTop 12] with s hs
  exact Real.abs_le_sqrt ((le_div_iff₀ (by linarith)).mpr (z.transverse_decay_at_zero zero hs))

end ClosedSimilarity.FrozenStress.Orbit
#print axioms ClosedSimilarity.GlobalSupport.continuous_scatteringImpact
#print axioms ClosedSimilarity.GlobalSupport.exists_zero_scattering
