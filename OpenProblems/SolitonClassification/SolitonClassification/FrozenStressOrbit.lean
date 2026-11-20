import SolitonClassification.FrozenStress

noncomputable section
set_option maxHeartbeats 1600000
namespace ClosedSimilarity.FrozenStress.Orbit
variable (z : Orbit)

def root (s : ℝ) := Real.sqrt (z.amplitude s)
def shape (s : ℝ) := z.k s/z.root s
def slope (s : ℝ) := z.v s/z.amplitude s
def along (s : ℝ) := z.radial s/z.amplitude s
def across (s : ℝ) := z.transverse s/z.amplitude s

/-- Every nonzero stress of an actual solution of the frozen polynomial ODE
supplies the normalized oscillator data for the two differential identities. -/
theorem normalized_rates (s : ℝ) (A : 0<z.amplitude s) :
    Rates s z.root z.shape z.slope z.along z.across := by
  let r := z.root s
  let U := z.shape s
  let w := z.slope s
  let a := z.along s
  let b := z.across s
  have rp : 0<r := Real.sqrt_pos.mpr A
  have root_sq : r^2 = z.amplitude s := Real.sq_sqrt A.le
  have k : z.k s=r*U := by dsimp [r,U,shape]; field_simp [show z.root s≠0 from rp.ne']
  have v : z.v s=r^2*w := by rw [root_sq]; dsimp [w,slope]; field_simp [A.ne']
  have radial : z.radial s=r^2*a := by rw [root_sq]; dsimp [a,along]; field_simp [A.ne']
  have transverse : z.transverse s=r^2*b := by rw [root_sq]; dsimp [b,across]; field_simp [A.ne']
  have osc : (U^2/2)^2+w^2=1 := by
    have he := z.amplitude_sq s
    rw [←root_sq,k,v] at he
    apply (mul_right_cancel₀ (pow_ne_zero 4 rp.ne'))
    calc
      ((U^2/2)^2+w^2)*r^4 = ((r*U)^2/2)^2+(r^2*w)^2 := by ring
      _ = 1*r^4 := by rw [←he]; ring
  have un : a^2+b^2=1 := by
    have hs := z.stress_unit s
    rw [radial,transverse,←root_sq] at hs
    apply (mul_right_cancel₀ (pow_ne_zero 4 rp.ne'))
    calc
      (a^2+b^2)*r^4 = (r^2*a)^2+(r^2*b)^2 := by ring
      _ = 1*r^4 := by rw [hs]; ring
  have ar : a = U^2/2*z.q s+w*z.p s := by
    have h := radial
    unfold Orbit.radial at h
    rw [k,v] at h
    apply (mul_left_cancel₀ (pow_ne_zero 2 rp.ne'))
    calc
      r^2*a = _ := h.symm
      _ = _ := by ring
  have br : b = U^2/2*z.p s-w*z.q s := by
    have h := transverse
    unfold Orbit.transverse at h
    rw [k,v] at h
    apply (mul_left_cancel₀ (pow_ne_zero 2 rp.ne'))
    calc
      r^2*b = _ := h.symm
      _ = _ := by ring
  have p : w*a+U^2/2*b=z.p s := by
    rw [ar,br]
    linear_combination z.p s * osc
  have q : U^2/2*a-w*b=z.q s := by
    rw [ar,br]
    linear_combination z.q s * osc
  have damp : HasDerivAt z.amplitude (-z.p s*w) s := by
    convert! z.amplitude_hasDerivAt s A using 1
    rw [v,←root_sq]
    field_simp [rp.ne']
  have dr : HasDerivAt z.root (-z.p s*w/(2*r)) s := by
    exact damp.sqrt A.ne'
  refine ⟨rp,osc,un,?_,?_,?_,?_,?_⟩
  · change HasDerivAt _ (-(w*a+U^2/2*b)*w/(2*r)) s
    rwa [p]
  · change HasDerivAt _ (w*(r+U*(w*a+U^2/2*b)/(2*r^2))) s
    rw [p]
    convert! (z.dk s).div dr rp.ne' using 1
    change _=(z.v s*r-z.k s*(-z.p s*w/(2*r)))/r^2
    rw [v,k]
    field_simp [rp.ne']
    ring
  · change HasDerivAt _ (-U^3/2*(r+U*(w*a+U^2/2*b)/(2*r^2))) s
    rw [p]
    convert! (z.dv s).div damp A.ne' using 1
    rw [v,k,←root_sq]
    field_simp [rp.ne']
    linear_combination -4*z.p s * osc
  · change HasDerivAt _ (-(w*a+U^2/2*b)*(U^2/2)*b/r^2) s
    rw [p]
    convert! (z.radial_hasDerivAt s).div damp A.ne' using 1
    rw [radial,←root_sq]
    field_simp [rp.ne']
    linear_combination -2*z.p s * p
  · change HasDerivAt _ ((w*a+U^2/2*b)*(U^2/2)*a/r^2) s
    rw [p]
    convert! (z.transverse_hasDerivAt s).div damp A.ne' using 1
    rw [transverse,←root_sq]
    field_simp [rp.ne']
    linear_combination 2*z.p s * q

theorem corrected_impact_rate (s : ℝ) (A : 0<z.amplitude s) :
    HasDerivAt (correctedImpact z.root z.shape z.slope z.along z.across)
    (remJ (z.shape s) (z.slope s) (z.along s) (z.across s)
      (z.slope s*z.along s+z.shape s^2/2*z.across s)/z.root s^4) s :=
  correctedImpact_hasDerivAt (z.normalized_rates s A)

theorem corrected_outgoing_rate (s : ℝ) (A : 0<z.amplitude s) :
    HasDerivAt (correctedOutgoing z.root z.shape z.slope z.along z.across)
    ((1+z.along s^2)/3+remH (z.shape s) (z.slope s) (z.along s) (z.across s)
      (z.slope s*z.along s+z.shape s^2/2*z.across s)/z.root s^3) s :=
  correctedOutgoing_hasDerivAt (z.normalized_rates s A)

end ClosedSimilarity.FrozenStress.Orbit
