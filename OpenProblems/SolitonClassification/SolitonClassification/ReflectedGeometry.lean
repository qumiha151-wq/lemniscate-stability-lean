import SolitonClassification.ReflectedArc

/-! Geometric reconstruction of the zero-turn profile from a reflected quarter arc. -/
noncomputable section
namespace ClosedSimilarity.ReflectedArc
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- A smooth, closed unit-speed immersion with signed curvature measured from
the position derivatives and a specified curvature derivative at the centre. -/
structure ZeroTurnExpander (L b : ℝ) where
  X : ℝ → ℝ
  Y : ℝ → ℝ
  k : ℝ → ℝ
  k_smooth : ContDiff ℝ ∞ k
  X_smooth : ContDiff ℝ ∞ X
  Y_smooth : ContDiff ℝ ∞ Y
  closed_X : Function.Periodic X L
  closed_Y : Function.Periodic Y L
  unit_speed : ∀ s, deriv X s ^ 2 + deriv Y s ^ 2 = 1
  curvature : ∀ s, deriv X s * deriv (deriv Y) s - deriv Y s * deriv (deriv X) s = k s
  total_curvature : (∫ s in 0..L, k s) = 0
  dilation_equation : ∀ s, deriv (deriv k) s + (k s)^3 / 2 =
    -(X s * (-deriv Y s) + Y s * deriv X s)
  center_crossing : X 0 = 0 ∧ Y 0 = 0 ∧ k 0 = 0 ∧ deriv k 0 = b

/-- Vanishing of the two terminal shooting coordinates suffices for the actual
geometric dilation equation, with no endpoint derivatives or winding assumed. -/
theorem exists_zeroTurnExpander_of_quarter {z : ℝ → Support} {L b : ℝ} (hL : 0<L)
    (cz : Continuous z) (hz : ∀ t∈Icc 0 L, HasDerivAt z (supportField (z t)) t)
    (hi : z 0=![0,b,0,0]) (hv : z L 1=0) (hq : z L 3=0) :
    Nonempty (ZeroTurnExpander (4*L) b) := by
  obtain ⟨y,per,sm,dy,agree,hb,_⟩ := closed_state_of_quarter hL cz hz hi hv hq
  let c (i : Fin 5) (s : ℝ) := y s i
  have d (s : ℝ) (i : Fin 5) : HasDerivAt (c i) (field (y s) i) s :=
    hasDerivAt_pi.mp (dy s) i
  have dc (i : Fin 5) : ContDiff ℝ ∞ (c i) := contDiff_pi.mp sm i
  have pc (i : Fin 5) : Function.Periodic (c i) (4*L) :=
    fun s => congrFun (per s) i
  have dk (s : ℝ) : HasDerivAt (c 0) (c 1 s) s := d s 0
  have dv (s : ℝ) : HasDerivAt (c 1) (-(c 0 s)^3/2-c 2 s-0*c 3 s) s := by
    simp only [zero_mul,sub_zero]
    exact d s 1
  have dp (s : ℝ) : HasDerivAt (c 2) (-c 0 s*c 3 s) s := d s 2
  have dq (s : ℝ) : HasDerivAt (c 3) (1+c 0 s*c 2 s) s := d s 3
  have da (s : ℝ) : HasDerivAt (c 4) (c 0 s) s := d s 4
  obtain ⟨px,py⟩ := profile_periodic (c 2) (c 3) (c 4) (4*L) 0 (pc 2) (pc 3)
    (fun s => by simpa using pc 4 s)
  refine ⟨{
    X := profileX (c 2) (c 3) (c 4)
    Y := profileY (c 2) (c 3) (c 4)
    k := c 0
    k_smooth := dc 0
    X_smooth := ((dc 3).mul (dc 4).cos).sub ((dc 2).mul (dc 4).sin)
    Y_smooth := ((dc 3).mul (dc 4).sin).add ((dc 2).mul (dc 4).cos)
    closed_X := px
    closed_Y := py
    unit_speed := fun s => profile_unit_speed _ _ _ _ s (dp s) (dq s) (da s)
    curvature := profile_signed_curvature _ _ _ _ dp dq da
    total_curvature := ?_
    dilation_equation := ?_
    center_crossing := ?_ }⟩
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => da s) ((dc 0).continuous.intervalIntegrable _ _)]
    have he := pc 4 0
    simpa only [zero_add,sub_eq_zero] using he
  · intro s
    rw [(profileX_hasDerivAt _ _ _ _ s (dp s) (dq s) (da s)).deriv,
      (profileY_hasDerivAt _ _ _ _ s (dp s) (dq s) (da s)).deriv]
    simpa only [zero_mul,sub_zero] using profile_soliton_equation 0 _ _ _ _ _ dk dv s
  · have e := agree 0 ⟨le_rfl,hL.le⟩
    simp [profileX,profileY,c,e,withAngle,hi,(dk 0).deriv]

end ClosedSimilarity.ReflectedArc
