import LengthGrowth.ActualFlow.MulticoverOutwardBoundary
import LengthGrowth.ActualFlow.MulticoverOutwardReflection
import LengthGrowth.ActualFlow.TrigonometricOutwardBoundary

noncomputable section
open Set Filter Topology
namespace LengthGrowth.Multicover.Outward
open LengthGrowth.ActualFlow

/-- One constant works for every signed integer winding, including zero.
Every exact geometric boundary above this linear scale admits an outward
smooth closed immersed position. -/
theorem signed_linear_outward :
    ∃C:ℝ,0<C ∧ ∀(m:ℤ) (K:ℝ),C*(1+|(m:ℝ)|)≤K →
      ∃g:PeriodicRegularPosition,materialSignedCurvature g.position g.period=2*Real.pi*(m:ℝ) ∧
        2*materialEnergy g.position g.period*g.length-(2*Real.pi*(m:ℝ))^2=K ∧
        0<materialEnergy g.position g.period*materialLengthRate g.position g.period-
          g.length*materialDissipation g.position g.period:=by
  obtain ⟨R,hr,high⟩:=high_winding_outward
  let b:ℝ:=(2*Real.pi)^2*(4097/2048)*2000000^2
  let C:=max (30000*R) (b*(1+1000*R))
  have cp : 0<C:=(show 0<30000*R by linarith).trans_le (le_max_left ..)
  refine ⟨C,cp,fun m K hK=>?_⟩
  let n:=m.natAbs
  have eq : (n:ℝ)=|(m:ℝ)|:=by dsimp [n];rw [Nat.cast_natAbs,Int.cast_abs]
  have nn:=abs_nonneg (m:ℝ)
  by_cases large : 1000*R≤(n:ℝ)
  · have cut : 30000*R*(n:ℝ)≤K:=by
      have r:=mul_le_mul_of_nonneg_right (show 30000*R≤C from le_max_left ..) nn
      rw [eq]
      linarith only [hK,r,cp]
    obtain ⟨g,turn,hit,out⟩:=high n K large cut
    rw [eq] at turn hit
    by_cases sign : 0≤(m:ℝ)
    · rw [abs_of_nonneg sign] at turn hit
      exact ⟨g,turn,hit,out⟩
    rw [abs_of_neg (lt_of_not_ge sign)] at turn hit
    obtain ⟨q,_,len,rev,E,J,D⟩:=reflect_material g
    refine ⟨q,?_,?_,?_⟩
    · rw [rev,turn];ring
    · rw [E,len];linarith only [hit]
    · rwa [E,J,D,len]
  · apply LengthGrowth.Multicover.Trigonometric.prescribed_outward_exact_level
    have en : 1+|(m:ℝ)|≤1+1000*R:=by rw [←eq];linarith only [lt_of_not_ge large]
    have bp : 0≤b:=by dsimp [b];positivity
    have t:=mul_le_mul_of_nonneg_left en bp
    have s:=mul_le_mul_of_nonneg_right (t.trans (show b*(1+1000*R)≤C from le_max_right ..)) (by linarith : 0≤1+|(m:ℝ)|)
    have z : (2*Real.pi)^2*(4097/2048)*(2000000*(1+|(m:ℝ)|))^2=
        (b*(1+|(m:ℝ)|))*(1+|(m:ℝ)|):=by dsimp [b];ring
    rw [z];exact s.trans hK

theorem actual_exit_from_position {g:PeriodicRegularPosition} (c:ForwardImmersion) (hf:c.IsNormalFEF)
    (γ:c.position 0=g.position) (p:c.period=g.period) {m:ℤ} {K:ℝ}
    (hit:2*materialEnergy g.position g.period*g.length-(2*Real.pi*(m:ℝ))^2=K)
    (out:0<materialEnergy g.position g.period*materialLengthRate g.position g.period-g.length*materialDissipation g.position g.period) :
    ∀ᶠt in 𝓝[>] (0:ℝ),K<2*c.normalizedProduct t-(2*Real.pi*(m:ℝ))^2:=by
  apply leaves_boundary c hf
  · change 2*(materialEnergy (c.position 0) c.period*materialLength (c.position 0) c.period)-(2*Real.pi*(m:ℝ))^2=K
    rw [γ,p];change 2*(materialEnergy g.position g.period*g.length)-(2*Real.pi*(m:ℝ))^2=K
    linarith only [hit]
  · change 0<materialEnergy (c.position 0) c.period*materialLengthRate (c.position 0) c.period-
      materialLength (c.position 0) c.period*materialDissipation (c.position 0) c.period
    rwa [γ,p]

end LengthGrowth.Multicover.Outward
#print axioms LengthGrowth.Multicover.Outward.signed_linear_outward
#print axioms LengthGrowth.Multicover.Outward.actual_exit_from_position
