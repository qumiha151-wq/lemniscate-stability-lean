import SolitonClassification.PeriodicConeRigidity

noncomputable section
namespace ClosedSimilarity.RotatingBifurcation.Cone
open Filter Set Topology

/-- A pitch-preserving family whose derivative at fixed pitch has exactly
    one neutral direction, with multiplier +1, admits no moving finite
    cycles sufficiently near the base point. Inputs use the three fixed-pitch
    eigencoordinates. No assumption is made on the derivative in pitch. -/
theorem local_periodic_points_are_fixed
    (F : Section × ℝ → Section) (base : Section × ℝ)
    (A : (Section × ℝ) →L[ℝ] Section) (strict : HasStrictFDerivAt F A base)
    (a u : ℝ) (ha : |a|<1) (hu : 1< |u|)
    (axes : ∀ v : Section, A (v,0) 0=a*v 0 ∧ A (v,0) 1=v 1 ∧ A (v,0) 2=u*v 2) :
    ∃ W ∈ 𝓝 base, ∀ {I : Type} [Finite I] (next : Equiv.Perm I) (x : I → Section) (ω : ℝ),
      (∀ i, (x i,ω) ∈ W) → (∀ i, F (x i,ω)=x (next i)) → ∀ i, F (x i,ω)=x i := by
  let e := min ((1-|a|)/4) ((|u|-1)/4)
  have ep : 0<e := lt_min (by linarith) (by linarith)
  have s : |a|+2*e<1 := by linarith [show e≤(1-|a|)/4 from min_le_left ..]
  have unstable : 1+2*e< |u| := by linarith [show e≤(|u|-1)/4 from min_le_right ..]
  let good := {p : (Section×ℝ)×(Section×ℝ) |
    ‖F p.1-F p.2-A (p.1-p.2)‖≤e*‖p.1-p.2‖}
  have h : good ∈ (𝓝 base) ×ˢ (𝓝 base) := by
    rw [←nhds_prod_eq]
    exact strict.isLittleO.def ep
  obtain ⟨V,hV,Z,hZ,sub⟩ := Filter.mem_prod_iff.mp h
  refine ⟨V∩Z,inter_mem hV hZ,?_⟩
  intro I _ next x ω contained orbit
  have estimate (i : I) : let v := fun j => x (next j)-x j
      ‖v (next i)-A (v i,0)‖ ≤ e*‖v i‖ := by
    have val := sub (show ((x (next i),ω),(x i,ω))∈V×ˢZ from
        ⟨(contained (next i)).1,(contained i).2⟩)
    have diff : (x (next i),ω)-(x i,ω)=(x (next i)-x i,0) := Prod.ext rfl (sub_self _)
    change ‖F (x (next i),ω)-F (x i,ω)-A ((x (next i),ω)-(x i,ω))‖≤
      e*‖(x (next i),ω)-(x i,ω)‖ at val
    simpa only [diff,orbit,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] using val
  have fixed := finite_cycles_fixed next x a u e ep.le s unstable (by
    intro v i
    have each (j : Fin 3) := (norm_le_pi_norm (v (next i)-A (v i,0)) j).trans (estimate i)
    have parts := axes (v i)
    refine ⟨?_,?_,?_⟩
    · simpa only [Pi.sub_apply,Real.norm_eq_abs,parts.1] using each 0
    · simpa only [Pi.sub_apply,Real.norm_eq_abs,parts.2.1] using each 1
    · simpa only [Pi.sub_apply,Real.norm_eq_abs,parts.2.2] using each 2)
  exact fun i => (orbit i).trans (fixed i)

end ClosedSimilarity.RotatingBifurcation.Cone
#print axioms ClosedSimilarity.RotatingBifurcation.Cone.local_periodic_points_are_fixed
