import SolitonClassification.OneSignCurvature
import SolitonClassification.SupportODE

/-! The physical graph equation for a similarity profile with dilation rate one.
The graph jets are pulled back to arclength. Their arclength derivatives
are the next graph jets multiplied by the horizontal tangent component. -/

noncomputable section
namespace ClosedSimilarity.GraphProfile

def slope (u w : ℝ) : ℝ := w / u
def secondJet (k u : ℝ) : ℝ := k / u^3
def thirdJet (k v u w : ℝ) : ℝ := v / u^4 + 3*k^2*w / u^5

/-- The fourth Cartesian graph derivative at the point (x,y). -/
def fourthJet (b x y m a j : ℝ) : ℝ :=
  10*m*a*j/(1+m^2) + (5/2-15*m^2)*a^3/(1+m^2)^2
    - (1+m^2)^2*(y-x*m+b*(x+y*m))

private theorem fourth_identity {u w : ℝ} (hu : u ≠ 0)
    (unit : u^2+w^2 = 1) (k v b x y : ℝ) :
    (-(k^3)/2 - (x*(-w)+y*u) - b*(x*u+y*w))/u^4 +
      10*k*v*w/u^5 + 3*k^3/u^4 + 15*k^3*w^2/u^6 =
      fourthJet b x y (slope u w) (secondJet k u) (thirdJet k v u w)*u := by
  have h : 1 + (w/u)^2 = 1/u^2 := by
    field_simp
    linear_combination unit
  unfold fourthJet slope secondJet thirdJet
  rw [h]
  field_simp
  ring

/-- In any nonvertical tangent frame, the four derivatives are the jets
of the actual normalized profile, including its full rotation term. -/
theorem graph_jet_derivatives {b L : ℝ} (z : PeriodicSupportProfile 1 b L)
    (θ : ℝ → ℝ) (s : ℝ) (hθ : HasDerivAt θ (z.k s) s)
    (hu : Real.cos (θ s) ≠ 0) :
    let u := fun t => Real.cos (θ t)
    let w := fun t => Real.sin (θ t)
    let x := profileX z.p z.q θ
    let y := profileY z.p z.q θ
    let m := fun t => slope (u t) (w t)
    let a := fun t => secondJet (z.k t) (u t)
    let j := fun t => thirdJet (z.k t) (z.v t) (u t) (w t)
    HasDerivAt x (u s) s ∧ HasDerivAt y (m s*u s) s ∧
      HasDerivAt m (a s*u s) s ∧ HasDerivAt a (j s*u s) s ∧
      HasDerivAt j (fourthJet b (x s) (y s) (m s) (a s) (j s)*u s) s := by
  dsimp only
  let u := fun t => Real.cos (θ t)
  let w := fun t => Real.sin (θ t)
  have hu' : u s ≠ 0 := hu
  have unit : (u s)^2+(w s)^2=1 := Real.cos_sq_add_sin_sq _
  have du : HasDerivAt u (-w s*z.k s) s := hθ.cos
  have dw : HasDerivAt w (u s*z.k s) s := hθ.sin
  have dx := profileX_hasDerivAt z.k z.p z.q θ s (z.dp s) (z.dq s) hθ
  have dy := profileY_hasDerivAt z.k z.p z.q θ s (z.dp s) (z.dq s) hθ
  refine ⟨dx, ?_, ?_, ?_, ?_⟩
  · simpa [slope, hu] using dy
  · change HasDerivAt (fun t => w t/u t) (z.k s/(u s)^3*u s) s
    convert! (dw.div du hu') using 1
    field_simp
    linear_combination -(z.k s) * unit
  · change HasDerivAt (fun t => z.k t/(u t)^3)
      (thirdJet (z.k s) (z.v s) (u s) (w s)*u s) s
    convert! (z.dk s).div (du.pow 3) (pow_ne_zero 3 hu') using 1
    unfold thirdJet
    simp only [Pi.pow_apply]
    field_simp
    ring
  · change HasDerivAt (fun t => z.v t/(u t)^4 + 3*(z.k t)^2*w t/(u t)^5)
      (fourthJet b _ _ (slope (u s) (w s)) (secondJet (z.k s) (u s))
        (thirdJet (z.k s) (z.v s) (u s) (w s))*u s) s
    rw [← fourth_identity hu' unit]
    have hp := normal_support z.p z.q θ s
    have hq := tangent_support z.p z.q θ s
    change _ * (-w s) + _ * u s = _ at hp
    change _ * u s + _ * w s = _ at hq
    rw [hp, hq]
    convert! ((z.dv s).div (du.pow 4) (pow_ne_zero 4 hu')).add
      (((((z.dk s).pow 2).const_mul 3).mul dw).div (du.pow 5) (pow_ne_zero 5 hu')) using 1
    simp only [Pi.pow_apply, Pi.mul_apply]
    field_simp
    ring

end ClosedSimilarity.GraphProfile

#print axioms ClosedSimilarity.GraphProfile.graph_jet_derivatives
