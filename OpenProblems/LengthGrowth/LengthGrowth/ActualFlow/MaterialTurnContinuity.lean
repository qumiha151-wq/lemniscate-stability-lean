import LengthGrowth.ActualFlow.MaterialTurnFlux
import LengthGrowth.ActualFlow.TurningQuarterFlow
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Set Function MeasureTheory
namespace LengthGrowth.ActualFlow.ForwardImmersion

private def clipPoint (p : (ℝ×ℝ)×ℝ) : ℝ×ℝ := (max 0 p.1.1,p.2)
private def density (c : ForwardImmersion) (p : ℝ×ℝ) : ℝ := curvature (c.position p.1) p.2 * speed (c.position p.1) p.2

theorem arcTurn_joint_continuous (c : ForwardImmersion) :
    ContinuousOn (fun q : ℝ×ℝ => arcTurn (c.position q.1) 0 q.2) (Ici 0 ×ˢ univ) := by
  have cmap : Continuous clipPoint :=
    (continuous_const.max (continuous_fst.comp continuous_fst)).prodMk continuous_snd
  have maps (p : (ℝ×ℝ)×ℝ) : clipPoint p∈(Ici (0:ℝ))×ˢ (univ : Set ℝ) :=
    ⟨(show (0:ℝ)≤max 0 p.1.1 from le_max_left _ _),mem_univ _⟩
  have cd : ContinuousOn (density c) (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) :=
    c.curvature_continuousOn.mul c.speed_continuousOn
  have full : Continuous (density c ∘ clipPoint) := cd.comp_continuous cmap maps
  let f : (ℝ×ℝ)→ℝ→ℝ := fun p u => density c (max 0 p.1,u)
  have cf : Continuous f.uncurry := full
  have ct := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (X:=ℝ×ℝ) (a₀:=0) (μ:=volume) (f:=f) cf (s:=Prod.snd) continuous_snd
  apply ct.continuousOn.congr
  intro p hp
  have hp0 : 0≤p.1 := hp.1
  change arcTurn (c.position p.1) 0 p.2=(∫ u in 0..p.2, density c (max 0 p.1,u))
  rw [max_eq_right hp0]
  rfl

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.arcTurn_joint_continuous
