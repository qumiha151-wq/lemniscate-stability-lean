import SolitonClassification.OuterStress
import SolitonClassification.ReflectedArc
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Normalization of the actual support ODE on the initial-marker time scale. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace ClosedSimilarity.OuterStress

open ClosedSimilarity.ReflectedArc

structure Data (δ : ℝ) where
  K : ℝ → ℝ
  V : ℝ → ℝ
  p : ℝ → ℝ
  q : ℝ → ℝ
  dK (s : ℝ) : HasDerivAt K (V s/δ) s
  dV (s : ℝ) : HasDerivAt V (-(K s)^3/(2*δ)-p s) s
  dp (s : ℝ) : HasDerivAt p (-K s*q s/δ) s
  dq (s : ℝ) : HasDerivAt q (1+K s*p s/δ) s

/-- The slow coordinate is physical arclength times the square root of δ. -/
def ofSupport {δ : ℝ} (delta : 0<δ) (z : ℝ → Support)
    (hz : ∀s, HasDerivAt z (supportField (z s)) s) : Data δ := by
  let f := Real.sqrt δ
  have hf : 0<f := Real.sqrt_pos.mpr delta
  have fsq : f^2=δ := Real.sq_sqrt delta.le
  refine
    { K := fun x => f * z (x/f) 0
      V := fun x => δ * z (x/f) 1
      p := fun x => f * z (x/f) 2
      q := fun x => f * z (x/f) 3
      dK := ?_, dV := ?_, dp := ?_, dq := ?_ }
  all_goals
    intro s
    have h := hasDerivAt_pi.mp (hz (s/f))
    have dk : HasDerivAt (fun t => z t 0) (z (s/f) 1) (s/f) := h 0
    have dv : HasDerivAt (fun t => z t 1) (-(z (s/f) 0)^3/2-z (s/f) 2) (s/f) := h 1
    have dp : HasDerivAt (fun t => z t 2) (-z (s/f) 0*z (s/f) 3) (s/f) := h 2
    have dq : HasDerivAt (fun t => z t 3) (1+z (s/f) 0*z (s/f) 2) (s/f) := h 3
    have clk := (hasDerivAt_id s).div_const f
  · convert! (dk.comp s clk).const_mul f using 1
    field_simp [hf.ne',delta.ne']
  · convert! (dv.comp s clk).const_mul δ using 1
    rw [←fsq]
    field_simp [hf.ne']
  · convert! (dp.comp s clk).const_mul f using 1
    rw [←fsq]
    field_simp [hf.ne']
  · convert! (dq.comp s clk).const_mul f using 1
    rw [←fsq]
    field_simp [hf.ne']

namespace Data
variable {δ : ℝ} (z : Data δ)
def radial (s : ℝ) := z.K s^2/2*z.q s+z.V s*z.p s
def transverse (s : ℝ) := z.K s^2/2*z.p s-z.V s*z.q s
def amplitude (s : ℝ) := Real.sqrt ((z.K s^2/2)^2+z.V s^2)

theorem radial_hasDerivAt (s : ℝ) (delta : 0<δ) :
    HasDerivAt z.radial (z.K s^2/2-(z.p s)^2) s := by
  convert! ((((z.dK s).pow 2).div_const 2).mul (z.dq s) |>.add ((z.dV s).mul (z.dp s))) using 1
  simp only [Pi.pow_apply]
  field_simp [delta.ne']
  ring

theorem transverse_hasDerivAt (s : ℝ) (delta : 0<δ) :
    HasDerivAt z.transverse (z.p s*z.q s-z.V s) s := by
  convert! ((((z.dK s).pow 2).div_const 2).mul (z.dp s) |>.sub ((z.dV s).mul (z.dq s))) using 1
  simp only [Pi.pow_apply]
  field_simp [delta.ne']
  ring

theorem amplitude_sq (s : ℝ) : z.amplitude s^2=(z.K s^2/2)^2+z.V s^2 :=
  Real.sq_sqrt (by positivity)

theorem amplitude_hasDerivAt (s : ℝ) (A : 0<z.amplitude s) (delta : 0<δ) :
    HasDerivAt z.amplitude (-z.p s*z.V s/z.amplitude s) s := by
  have de : HasDerivAt (fun x => (z.K x^2/2)^2+z.V x^2) (-2*z.V s*z.p s) s := by
    convert! ((((z.dK s).pow 2).div_const 2).pow 2 |>.add ((z.dV s).pow 2)) using 1
    simp only [Pi.pow_apply]
    field_simp [delta.ne']
    ring
  have nn : 0<(z.K s^2/2)^2+z.V s^2 := by rw [← z.amplitude_sq]; positivity
  convert! de.sqrt nn.ne' using 1
  change _= -2*z.V s*z.p s/(2*z.amplitude s)
  field_simp [A.ne']

def root (s : ℝ) := Real.sqrt (z.amplitude s)
def shape (s : ℝ) := z.K s/z.root s
def slope (s : ℝ) := z.V s/z.amplitude s
def along (s : ℝ) := z.radial s/z.amplitude s
def across (s : ℝ) := z.transverse s/z.amplitude s

theorem normalized_rates (s : ℝ) (A : 0<z.amplitude s) (delta : 0<δ) :
    Rates δ s z.root z.shape z.slope z.along z.across := by
  let r := z.root s
  let U := z.shape s
  let w := z.slope s
  let a := z.along s
  let b := z.across s
  have rp : 0<r := Real.sqrt_pos.mpr A
  have root_sq : r^2 = z.amplitude s := Real.sq_sqrt A.le
  have k : z.K s=r*U := by dsimp [r,U,shape]; field_simp [show z.root s≠0 from rp.ne']
  have v : z.V s=r^2*w := by rw [root_sq]; dsimp [w,slope]; field_simp [A.ne']
  have radial : z.radial s=r^2*a := by rw [root_sq]; dsimp [a,along]; field_simp [A.ne']
  have transverse : z.transverse s=r^2*b := by rw [root_sq]; dsimp [b,across]; field_simp [A.ne']
  have osc : (U^2/2)^2+w^2=1 := by
    have he := z.amplitude_sq s
    rw [←root_sq,k,v] at he
    apply (mul_right_cancel₀ (pow_ne_zero 4 rp.ne'))
    calc
      ((U^2/2)^2+w^2)*r^4 = ((r*U)^2/2)^2+(r^2*w)^2 := by ring
      _ = 1*r^4 := by rw [←he]; ring
  have ar : a = U^2/2*z.q s+w*z.p s := by
    have h := radial
    unfold Data.radial at h
    rw [k,v] at h
    apply (mul_left_cancel₀ (pow_ne_zero 2 rp.ne'))
    calc
      r^2*a = _ := h.symm
      _ = _ := by ring
  have br : b = U^2/2*z.p s-w*z.q s := by
    have h := transverse
    unfold Data.transverse at h
    rw [k,v] at h
    apply (mul_left_cancel₀ (pow_ne_zero 2 rp.ne'))
    calc
      r^2*b = _ := h.symm
      _ = _ := by ring
  have p : w*a+U^2/2*b=z.p s := by rw [ar,br]; linear_combination z.p s * osc
  have q : U^2/2*a-w*b=z.q s := by rw [ar,br]; linear_combination z.q s * osc
  have damp : HasDerivAt z.amplitude (-z.p s*w) s := by
    convert! z.amplitude_hasDerivAt s A delta using 1
    rw [v,←root_sq]
    field_simp [rp.ne']
  have dr : HasDerivAt z.root (-z.p s*w/(2*r)) s := damp.sqrt A.ne'
  refine ⟨delta,rp,osc,?_,?_,?_,?_,?_⟩
  · change HasDerivAt _ (-(w*a+U^2/2*b)*w/(2*r)) s
    rwa [p]
  · change HasDerivAt _ (w*(r/δ+U*(w*a+U^2/2*b)/(2*r^2))) s
    rw [p]
    convert! (z.dK s).div dr rp.ne' using 1
    change _=((z.V s/δ)*r-z.K s*(-z.p s*w/(2*r)))/r^2
    rw [v,k]
    field_simp [rp.ne',delta.ne']
    ring
  · change HasDerivAt _ (-U^3/2*(r/δ+U*(w*a+U^2/2*b)/(2*r^2))) s
    rw [p]
    convert! (z.dV s).div damp A.ne' using 1
    rw [v,k,←root_sq]
    field_simp [rp.ne',delta.ne']
    linear_combination -4*δ*z.p s * osc
  · change HasDerivAt _ (U^2/2-(w*a+U^2/2*b)*(U^2/2)*b/r^2) s
    rw [p]
    convert! (z.radial_hasDerivAt s delta).div damp A.ne' using 1
    rw [radial,k,←root_sq]
    field_simp [rp.ne']
    linear_combination -2*z.p s * p
  · change HasDerivAt _ (-w+(w*a+U^2/2*b)*(U^2/2)*a/r^2) s
    rw [p]
    convert! (z.transverse_hasDerivAt s delta).div damp A.ne' using 1
    rw [transverse,v,←root_sq]
    field_simp [rp.ne']
    linear_combination 2*z.p s * q

theorem radius_sq (s : ℝ) (A : 0<z.amplitude s) :
    z.along s^2+z.across s^2=z.p s^2+z.q s^2 := by
  unfold along across
  field_simp [A.ne']
  rw [amplitude_sq]
  unfold radial transverse
  ring

theorem uniform_physical_rates (M : ℝ) (hm : 0≤M) :
    ∃ C ≥ 0, ∀ {δ : ℝ} (delta : 0<δ) (z : ℝ → Support)
      (hz : ∀x, HasDerivAt z (supportField (z x)) x) (s : ℝ),
      let y:=ofSupport delta z hz
      0<y.amplitude s → y.amplitude s≤1 → y.p s^2+y.q s^2≤M^2 →
      |deriv (impact δ y.root y.shape y.slope y.along y.across) s| ≤ C*δ/y.root s^4 ∧
      |deriv (OuterStress.amplitude δ y.root y.shape y.slope y.along y.across) s+
        2*y.along s/3| ≤ C*δ/y.root s^3 := by
  obtain ⟨C,hC,uniform⟩:=uniform_rates M
  refine ⟨C,hC,?_⟩
  intro δ delta z hz s
  let y:=ofSupport delta z hz
  change 0<y.amplitude s → _
  intro ha small cap
  have bound := (y.radius_sq s ha).le.trans cap
  have hs : y.root s^2≤1 := (Real.sq_sqrt ha.le).le.trans small
  apply uniform (y.normalized_rates s ha delta) hs
  · exact abs_le.mpr ⟨by nlinarith [sq_nonneg (y.across s)],by nlinarith [sq_nonneg (y.across s)]⟩
  · exact abs_le.mpr ⟨by nlinarith [sq_nonneg (y.along s)],by nlinarith [sq_nonneg (y.along s)]⟩

end Data
end ClosedSimilarity.OuterStress

#print axioms ClosedSimilarity.OuterStress.Data.uniform_physical_rates
