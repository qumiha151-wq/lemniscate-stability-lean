import SolitonClassification.RationalIndicialJet

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Filter Set
open scoped Topology
namespace ClosedSimilarity.RationalCurvature

/-- The first possible change from a constant at the singular point of the
Euler operator. Terms of greater exponent have no effect on the coefficient. -/
def Variation (f : ℂ→ℂ) (n : ℤ) (c v : ℂ) := Jet (fun z=>f z-c) 0 n v

namespace Variation
variable {f g : ℂ→ℂ} {n : ℤ} {c d v u : ℂ}

theorem tag (h : Variation f n c v) {c' v' : ℂ} (hc : c=c') (hv : v=v') :
    Variation f n c' v' := hc ▸ hv ▸ h

theorem add (h : Variation f n c v) (k : Variation g n d u) :
    Variation (fun z=>f z+g z) n (c+d) (v+u) :=
  (Jet.add h k).congr (Eventually.of_forall fun z=>by dsimp; ring)

theorem sub (h : Variation f n c v) (k : Variation g n d u) :
    Variation (fun z=>f z-g z) n (c-d) (v-u) :=
  (Jet.sub h k).congr (Eventually.of_forall fun z=>by dsimp; ring)

theorem smul (h : Variation f n c v) (r : ℂ) :
    Variation (fun z=>r*f z) n (r*c) (r*v) :=
  (Jet.smul h r).congr (Eventually.of_forall fun z=>by dsimp; ring)

theorem mul (h : Variation f n c v) (k : Variation g n d u) (pos : 0<n) :
    Variation (fun z=>f z*g z) n (c*d) (c*u+d*v) := by
  have J := ((Jet.smul k c).add (Jet.smul h d)).add ((Jet.mul h k).weaken (m:=n) (by omega))
  exact (J.retag rfl (add_zero _)).congr (Eventually.of_forall fun z=>by dsimp; ring)

theorem sq (h : Variation f n c v) (pos : 0<n) :
    Variation (fun z=>f z^2) n (c^2) (2*c*v) := by
  simpa only [pow_two] using (h.mul h pos).tag rfl (by ring)

theorem cube (h : Variation f n c v) (pos : 0<n) :
    Variation (fun z=>f z^3) n (c^3) (3*c^2*v) := by
  simpa only [pow_succ c 2,pow_succ _ 2] using ((h.sq pos).mul h pos).tag rfl (by ring)

theorem sixth (h : Variation f n c v) (pos : 0<n) :
    Variation (fun z=>f z^6) n (c^6) (6*c^5*v) := by
  have J := (h.cube pos).sq pos
  simp only [←pow_mul] at J
  exact J.tag rfl (by ring)

theorem diff (h : Variation f n c v) (μ : ℂ) :
    Variation (euler μ f) n 0 (μ*n*v) := by
  apply ((euler_at_zero (μ:=μ) h).retag rfl (by ring)).congr
  exact Eventually.of_forall fun z=>by simp [euler,deriv_sub_const]

end Variation

/-- The indicial polynomial obtained by varying the full nonlinear scalar
ODE about a constant curvature, in an actual punctured analytic germ. -/
theorem residual_variation {f : ℂ→ℂ} {n : ℤ} {c v : ℂ}
    (h : Variation f n c v) (pos : 0<n) (μ a b : ℂ) :
    Variation (residual μ a b f) n (c^6-2*a*c^2)
      ((2*c*(μ*n)^4+5*c^3*(μ*n)^2-2*b*(μ*n)+6*c^5-4*a*c)*v) := by
  have h₁ := h.diff μ
  have h₂ := h₁.diff μ
  have h₃ := h₂.diff μ
  have h₄ := h₃.diff μ
  have j₂ := (((h.mul h₄ pos).sub (h₁.mul h₃ pos)).smul 2)
  have j₄ := ((((h.sq pos).mul (h₁.sq pos) pos).smul 3).add (((h.cube pos).mul h₂ pos).smul 5))
  have J := ((((j₂.add j₄).add (h.sixth pos)).sub ((h.sq pos).smul (2*a))).sub (h₁.smul (2*b)))
  exact J.tag (by ring) (by ring)

/-- The value at a regular Euler singular point satisfies the constant
coefficient equation, without assuming the solution is constant. -/
theorem residual_constant {f : ℂ→ℂ} {μ a b c : ℂ} (j : Jet f 0 0 c)
    (germ : residual μ a b f=ᶠ[𝓝[≠] 0] fun _=>0) : c^6-2*a*c^2=0 := by
  have J := FourJet.at_zero (μ:=μ) j
  have q₂ : Jet (quadratic μ f) 0 0 0 := by simpa using J.jquadratic
  have q₄ : Jet (quartic μ f) 0 0 0 := by simpa using J.jquartic
  have h6 : Jet (fun z=>f z^6) 0 0 (c^6) := by simpa using j.pow 6
  have h2 : Jet (fun z=>2*a*f z^2) 0 0 (2*a*c^2) := by simpa using (j.pow 2).smul (2*a)
  have h1 : Jet (fun z=>2*b*euler μ f z) 0 0 0 := by simpa using J.j₁.smul (2*b)
  simpa using ((((q₂.add q₄).add h6).sub h2).sub h1).eq_zero_of_germ_zero germ

end ClosedSimilarity.RationalCurvature
