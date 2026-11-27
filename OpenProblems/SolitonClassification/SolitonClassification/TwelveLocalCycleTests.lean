import SolitonClassification.LocalSpectralRigidity
import SolitonClassification.QuarterRankIntervals

noncomputable section
namespace ClosedSimilarity.RotatingBifurcation.Cone
open Filter Set Topology

/-- A fixed Poincaré point gives a zero of the flow residual with its
    actual variable return time as one of the even coordinates. An
    injective odd block and reversibility then force its pitch to vanish. -/
theorem fixed_pitch_of_odd_residual
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : Section × ℝ → Section) (base : Section × ℝ)
    (Z : Section × ℝ → Section × (Fin 2 → ℝ)) (even : Section)
    (chart : Tendsto Z (𝓝 base) (𝓝 (even,0)))
    (pitch : ∀ y, (Z y).2 1=y.2)
    (G : Section × (Fin 2 → ℝ) → Y) (D : (Section × (Fin 2 → ℝ)) →L[ℝ] Y)
    (smooth : HasStrictFDerivAt G D (even,0)) {c : ℝ} (cp : 0<c)
    (rank : ∀ v : Fin 2 → ℝ, c*‖v‖≤‖D (0,v)‖)
    (reverse : ∀ᶠ y in 𝓝 (even,(0:Fin 2→ℝ)), G y=0 → G (y.1,-y.2)=0)
    (hit : ∀ᶠ y in 𝓝 base, F y=y.1 → G (Z y)=0) :
    ∀ᶠ y in 𝓝 base, F y=y.1 → y.2=0 := by
  have zero := ClosedSimilarity.OddLocalRigidity.eventually_odd_eq_zero smooth cp rank reverse
  filter_upwards [chart.eventually zero,hit] with y hy hz
  intro h
  rw [←pitch y,hy (hz h)]
  rfl

private theorem reciprocal_bounds {a u t : ℝ} (order : a≤u) (prod : a*u=1)
    (sum : a+u=t^2-2) (trace : 2 < |t|) : |a|<1 ∧ 1 < |u| := by
  have sq := pow_lt_pow_left₀ trace (by norm_num : (0:ℝ)≤2) (by decide : (2:ℕ)≠0)
  rw [sq_abs] at sq
  have up : 1<u := by linarith
  have ap : 0<a := by
    by_contra! neg
    nlinarith only [mul_nonpos_of_nonpos_of_nonneg neg (zero_le_one.trans up.le),prod]
  rw [abs_of_pos ap,abs_of_pos (zero_lt_one.trans up)]
  exact ⟨by nlinarith only [mul_lt_mul_of_pos_left up ap,prod],up⟩

/-- Applies the cone argument to the three fixed-pitch section multipliers
    in each rational quarter box. The chart, monodromy identities, enclosure
    of the physical input, and fixed-point rigidity are stated explicitly. -/
theorem twelve_local_cycle_test (i : Fin 12) (inputs : QuarterBounds.Input → ℝ)
    (box : ∀ j, (QuarterBounds.enclosure i j).Contains (inputs j))
    (F : Section × ℝ → Section) (base : Section × ℝ)
    (A : (Section × ℝ) →L[ℝ] Section) (strict : HasStrictFDerivAt F A base)
    (a u : ℝ) (order : a≤u) (prod : a*u=1)
    (sum : a+u=(QuarterBounds.halfTrace.real inputs)^2-2)
    (axes : ∀ v : Section, A (v,0) 0=a*v 0 ∧ A (v,0) 1=v 1 ∧ A (v,0) 2=u*v 2)
    (fixed : ∀ᶠ y in 𝓝 base, F y=y.1 → y.2=0) :
    ∃ W ∈ 𝓝 base, ∀ {I : Type} [Finite I] [Nonempty I] (next : Equiv.Perm I)
      (x : I → Section) (ω : ℝ), (∀ j, (x j,ω)∈W) → (∀ j, F (x j,ω)=x (next j)) →
      ω=0 ∧ ∀ j, F (x j,ω)=x j := by
  obtain ⟨_,_,trace⟩ := QuarterBounds.twelve_quarter_boxes i box
  obtain ⟨ha,hu⟩ := reciprocal_bounds order prod sum trace
  obtain ⟨V,hV,cycles⟩ := local_periodic_points_are_fixed F base A strict a u ha hu axes
  refine ⟨V∩{y | F y=y.1 → y.2=0},inter_mem hV fixed,?_⟩
  intro I _ ni next x ω near orbit
  have stop := cycles next x ω (fun j => (near j).1) orbit
  obtain ⟨j⟩ := ni
  exact ⟨(near j).2 (stop j),stop⟩

end ClosedSimilarity.RotatingBifurcation.Cone
#print axioms ClosedSimilarity.RotatingBifurcation.Cone.twelve_local_cycle_test
