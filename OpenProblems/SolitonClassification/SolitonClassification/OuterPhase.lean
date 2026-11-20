import SolitonClassification.OuterStress
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A real angle for the quartic oscillator along moving physical shots.
    The coordinate chart has no singularity at a curvature extremum or zero. -/
noncomputable section
namespace ClosedSimilarity.OuterStress.Angle
open Set MeasureTheory

def sn (U : ℝ → ℝ) (x : ℝ) := U x / Real.sqrt 2
def cs (U w : ℝ → ℝ) (x : ℝ) := w x / Real.sqrt (1+U x^2/2)
def fast (δ : ℝ) (r U w a b : ℝ → ℝ) (x : ℝ) :=
  r x/δ+U x*(w x*a x+U x^2/2*b x)/(2*r x^2)
def spin (δ : ℝ) (r U w a b : ℝ → ℝ) (x : ℝ) :=
  Real.sqrt (1+U x^2/2)/Real.sqrt 2 * fast δ r U w a b x

theorem angular_derivatives {δ s : ℝ} {r U w a b : ℝ → ℝ} (d : Rates δ s r U w a b) :
    HasDerivAt (sn U) (cs U w s*spin δ r U w a b s) s ∧
    HasDerivAt (cs U w) (-sn U s*spin δ r U w a b s) s := by
  let v := fast δ r U w a b s
  let h := Real.sqrt (1+U s^2/2)
  have hp : 0 < h := Real.sqrt_pos.mpr (by positivity)
  have hh : h^2=1+U s^2/2 := Real.sq_sqrt (by positivity)
  have two : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have tp : 0 < Real.sqrt 2 := by positivity
  have du : HasDerivAt U (w s*v) s := d.dU
  have dw : HasDerivAt w (-U s^3/2*v) s := d.dw
  have da : HasDerivAt (fun x => 1+U x^2/2) (U s*w s*v) s := by
    convert! ((du.pow 2).div_const 2).const_add 1 using 1
    ring
  have dh := da.sqrt (by positivity : (1+U s^2/2) ≠ 0)
  constructor
  · convert! du.div_const (Real.sqrt 2) using 1
    change w s/h*(h/Real.sqrt 2*v)=_
    field_simp [hp.ne',tp.ne']
  · convert! dw.div dh hp.ne' using 1
    change -(U s/Real.sqrt 2)*(h/Real.sqrt 2*v)=(-U s^3/2*v*h-w s*(U s*w s*v/(2*h)))/h^2
    field_simp [hp.ne',tp.ne']
    rw [two]
    linear_combination -2 * U s*v*(h^2+1-U s^2/2)*hh + 2*U s*v*d.oscillator

theorem spin_continuousAt {δ s : ℝ} {r U w a b : ℝ → ℝ} (d : Rates δ s r U w a b) :
    ContinuousAt (spin δ r U w a b) s := by
  unfold spin fast
  have rr := d.dr.continuousAt
  have uu := d.dU.continuousAt
  have ww := d.dw.continuousAt
  have aa := d.da.continuousAt
  have bb := d.db.continuousAt
  have hh := d.pos
  have dd := d.delta_pos
  fun_prop (disch := positivity)

/-- An integral of the true spin lifts the oscillator continuously through
    its entire passage along every positive-amplitude interval. -/
theorem physical_phase_lift {δ S T : ℝ} {r U w a b : ℝ → ℝ} (st : S ≤ T)
    (rates : ∀ x ∈ Icc S T, Rates δ x r U w a b)
    (zero : sn U S=0) (one : cs U w S=1) :
    let θ (x : ℝ) := ∫ t in S..x, spin δ r U w a b t
    ∀ x ∈ Icc S T, sn U x=Real.sin (θ x) ∧ cs U w x=Real.cos (θ x) := by
  let g := spin δ r U w a b
  let θ (x : ℝ) := ∫ t in S..x, g t
  change ∀ x ∈ Icc S T, sn U x=Real.sin (θ x) ∧ cs U w x=Real.cos (θ x)
  have cg : ContinuousOn g (Icc S T) := fun x hx => (spin_continuousAt (rates x hx)).continuousWithinAt
  have cg' : ContinuousOn g (uIcc S T) := by rwa [uIcc_of_le st]
  have ct : ContinuousOn θ (Icc S T) := by
    simpa only [uIcc_of_le st] using intervalIntegral.continuousOn_primitive_interval
      (cg'.integrableOn_compact isCompact_uIcc (μ := volume))
  have der (x : ℝ) (hx : x ∈ Ioo S T) : HasDerivAt θ (g x) x := by
    have sub : uIcc S x ⊆ Icc S T := by rw [uIcc_of_le hx.1.le]; exact Icc_subset_Icc_right hx.2.le
    apply intervalIntegral.integral_hasDerivAt_right (cg.mono sub |>.intervalIntegrable)
    · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (cg.mono Ioo_subset_Icc_self) x hx
    · exact spin_continuousAt (rates x ⟨hx.1.le,hx.2.le⟩)
  let D (x : ℝ) := (sn U x-Real.sin (θ x))^2+(cs U w x-Real.cos (θ x))^2
  have csn : ContinuousOn (sn U) (Icc S T) :=
    fun x hx => (angular_derivatives (rates x hx)).1.continuousAt.continuousWithinAt
  have ccs : ContinuousOn (cs U w) (Icc S T) :=
    fun x hx => (angular_derivatives (rates x hx)).2.continuousAt.continuousWithinAt
  have cD : ContinuousOn D (Icc S T) := ((csn.sub (Real.continuous_sin.comp_continuousOn ct)).pow 2).add
    ((ccs.sub (Real.continuous_cos.comp_continuousOn ct)).pow 2)
  have dD (x : ℝ) (hx : x ∈ Ioo S T) : HasDerivAt D 0 x := by
    obtain ⟨ds,dc⟩ := angular_derivatives (rates x ⟨hx.1.le,hx.2.le⟩)
    convert! (((ds.sub (der x hx).sin).pow 2).add ((dc.sub (der x hx).cos).pow 2)) using 1
    simp only [Pi.sub_apply,Nat.cast_ofNat,g]
    ring
  have desc : AntitoneOn D (Icc S T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) cD
    · rw [interior_Icc]; exact fun x hx => (dD x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; exact fun x hx => (dD x hx).deriv.le
  intro x hx
  have eq := desc (show S ∈ Icc S T from ⟨le_rfl,st⟩) hx hx.1
  have eq0 : D S=0 := by simp [D,θ,zero,one]
  rw [eq0] at eq
  change (sn U x-Real.sin (θ x))^2+(cs U w x-Real.cos (θ x))^2≤0 at eq
  exact ⟨by nlinarith [sq_nonneg (cs U w x-Real.cos (θ x))],by nlinarith [sq_nonneg (sn U x-Real.sin (θ x))]⟩

/-- Quantitative winding before the small-amplitude region. -/
theorem spin_lower {δ s M : ℝ} {r U w a b : ℝ → ℝ} (d : Rates δ s r U w a b)
    (ha : |a s| ≤ M) (hb : |b s| ≤ M) (above : 4*M*δ ≤ r s^3) :
    r s/(4*δ) ≤ spin δ r U w a b s := by
  have osc := d.oscillator
  have ru : (U s)^2/2 ≤ 1 := by nlinarith [sq_nonneg (w s),sq_nonneg ((U s)^2/2-1)]
  have bw : |w s| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg ((U s)^2/2)],
    by nlinarith [sq_nonneg ((U s)^2/2)]⟩
  have bu : |U s| ≤ 2 := abs_le.mpr ⟨by nlinarith [sq_nonneg (U s+1)],by nlinarith [sq_nonneg (U s-1)]⟩
  have ua : |(U s)^2/2| ≤ 1 := by rwa [abs_of_nonneg (by positivity)]
  have M0 := (abs_nonneg _).trans ha
  have p : |w s*a s+U s^2/2*b s| ≤ 2*M := by
    calc
      _ ≤ |w s*a s| + |U s^2/2*b s| := abs_add_le _ _
      _ ≤ 1*M + 1*M := by rw [abs_mul,abs_mul]; gcongr
      _ = _ := by ring
  have v := mul_le_mul bu p (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  rw [←abs_mul] at v
  have q := mul_le_mul_of_nonneg_right (abs_le.mp v).1 d.delta_pos.le
  have hpos := d.pos
  have dd := d.delta_pos
  have lower : r s/(2*δ) ≤ fast δ r U w a b s := by
    unfold fast
    field_simp
    nlinarith
  have rd : 1 ≤ Real.sqrt (1+U s^2/2) := by
    exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg (U s)])
  have two : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have factor : 1/2 ≤ Real.sqrt (1+U s^2/2)/Real.sqrt 2 :=
    (le_div_iff₀ (by positivity)).mpr (by linarith)
  calc
    _ = (1/2)*(r s/(2*δ)) := by ring
    _ ≤ _ := mul_le_mul factor lower (by positivity) (by positivity)

theorem winding_on_interval {δ S T M m : ℝ} {r U w a b : ℝ → ℝ} (st : S ≤ T)
    (rates : ∀ x ∈ Icc S T, Rates δ x r U w a b ∧ |a x| ≤ M ∧ |b x| ≤ M ∧
      4*M*δ ≤ r x^3 ∧ m ≤ r x) :
    (T-S)*m/(4*δ) ≤ ∫ t in S..T, spin δ r U w a b t := by
  have dd := (rates S ⟨le_rfl,st⟩).1.delta_pos
  have cont : ContinuousOn (spin δ r U w a b) (uIcc S T) := by
    rw [uIcc_of_le st]
    exact fun x hx => (spin_continuousAt (rates x hx).1).continuousWithinAt
  have it := intervalIntegral.integral_mono_on (μ := volume) st
    (intervalIntegrable_const (c := m/(4*δ))) cont.intervalIntegrable
    (fun x hx => by
      obtain ⟨d,ha,hb,above,low⟩ := rates x hx
      exact (div_le_div_of_nonneg_right low (by positivity)).trans (spin_lower d ha hb above))
  rw [intervalIntegral.integral_const,smul_eq_mul] at it
  simpa only [mul_div_assoc] using it

end ClosedSimilarity.OuterStress.Angle
#print axioms ClosedSimilarity.OuterStress.Angle.physical_phase_lift
#print axioms ClosedSimilarity.OuterStress.Angle.winding_on_interval
