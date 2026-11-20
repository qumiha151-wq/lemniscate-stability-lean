import SolitonClassification.ExactPhysicalMatching
import SolitonClassification.RectangleCrossing

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set ReflectedArc SolitonClassification.Reflected.Rectangle

/-- The bounded and winding lifts use the same regular oscillator circle.
    Matching modulo a whole turn recovers both signed oscillator coordinates. -/
def hasAngle (x : Phase) (θ : ℝ) :=
  Real.sin θ=shape x/Real.sqrt 2 ∧ Real.cos θ=slope x/Real.sqrt (1+(shape x)^2/2)

theorem equal_phase {x y : Phase} {θ φ : ℝ} (hx : hasAngle x θ) (hy : hasAngle y φ)
    (n : ℕ) (eq : θ=φ+n*(2*Real.pi)) : shape x=shape y ∧ slope x=slope y := by
  have sn := hx.1
  have cs := hx.2
  rw [eq,Real.sin_add_nat_mul_two_pi,hy.1] at sn
  rw [eq,Real.cos_add_nat_mul_two_pi,hy.2] at cs
  have u := (div_left_inj' (by positivity : Real.sqrt 2 ≠ 0)).mp sn
  rw [u] at cs
  exact ⟨u.symm,((div_left_inj' (by positivity : Real.sqrt (1+(shape x)^2/2) ≠ 0)).mp cs).symm⟩

def centreSlice (b s : ℝ) := solution 1 ![0,b,0,0] s
def sectionImpact (x : Phase) := root x/scale x*across x

/-- A statement directly about periodic immersed solutions: if the actual
    centre shots wind along a large incoming section and the two actual seam
    faces straddle them, arbitrarily large centre slopes close. -/
theorem winding_closes_curves (b₀ c d M : ℝ) (hcd : c ≤ d)
    (s phase : ℝ → ℝ) (t seamPhase : ℝ × ℝ → ℝ) (seam : ℝ × ℝ → Phase)
    (X : ℝ → Phase) (Y : ℝ × ℝ → Phase)
    (xdef : ∀ b, X b = centreSlice b (s b)) (ydef : ∀ z, Y z = solution 1 (seam z) (t z))
    (wind : ∀ B ≥ b₀, ∀ v : ℝ, ∃ B' ≥ B, v < phase B')
    (regular : ∀ B ≥ b₀, ∀ B' ≥ B, ContinuousOn (fun z : ℝ × ℝ =>
      (phase z.1-seamPhase z,sectionImpact (Y z)-sectionImpact (X z.1))) (box B B' c d))
    (bound : ∀ b ≥ b₀, ∀ y ∈ Icc c d, |seamPhase (b,y)| ≤ M)
    (low : ∀ b ≥ b₀, sectionImpact (Y (b,c)) < sectionImpact (X b))
    (high : ∀ b ≥ b₀, sectionImpact (X b) < sectionImpact (Y (b,d)))
    (incoming : ∀ b ≥ b₀, 0<s b ∧ MovingSeam.regular (X b) ∧
      4 ≤ root (X b)/scale (X b) ∧ 0 ≤ along (X b) ∧ hasAngle (X b) (phase b))
    (family : ∀ b ≥ b₀, ∀ y ∈ Icc c d, let z := (b,y)
      t z<0 ∧ seam z 1=0 ∧ seam z 3=0 ∧ MovingSeam.regular (Y z) ∧
      4 ≤ root (Y z)/scale (Y z) ∧ 0 ≤ along (Y z) ∧
      scale (X b)=scale (Y z) ∧ height (X b)=height (Y z) ∧ hasAngle (Y z) (seamPhase z)) :
    ∀ B ≥ b₀, ∃ b ≥ B, ∃ L > (0:ℝ), Nonempty (ZeroTurnExpander L b) := by
  have p : 0 < 2*Real.pi := by positivity
  intro B hB
  obtain ⟨b,hb,y,hy,n,angle,hit⟩ := unbounded_matching_markers b₀ c d (2*Real.pi) M hcd p
    phase (fun b => sectionImpact (X b)) seamPhase (fun z => sectionImpact (Y z))
    wind regular bound low high B hB
  obtain ⟨sp,xr,xb,xa,xθ⟩ := incoming b (hB.trans hb)
  obtain ⟨tn,v,q,yr,yb,ya,r,H,yθ⟩ := family b (hB.trans hb) y hy
  obtain ⟨U,w⟩ := equal_phase xθ yθ n angle
  have close := exact_physical_matching (b:=b) sp tn v q
  dsimp only at close
  have xx : solution 1 ![0,b,0,0] (s b) = X b := (xdef b).symm
  rw [xx,←ydef (b,y)] at close
  exact ⟨b,hb,4*(s b-t (b,y)),by linarith,close xr yr xb yb xa ya r U w hit H⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.winding_closes_curves
