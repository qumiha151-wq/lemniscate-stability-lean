import SolitonClassification.TangentForceLaw
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! A single-valued force law on the oriented unit tangent determines a
centered, possibly multiply covered circle. The force and curvature in
the geometric conclusion are calculated from the position coordinates. -/

noncomputable section
namespace ClosedSimilarity.ClosedUnitFrenetCurve
open MeasureTheory

private theorem unit_angle {u v : ℝ} (h : u^2 + v^2 = 1) :
    ∃ θ : ℝ, Real.cos θ = u ∧ Real.sin θ = v := by
  let w : ℂ := ⟨u,v⟩
  have hn : ‖w‖ = 1 := by
    have he := Complex.sq_norm w
    change ‖w‖^2 = u*u + v*v at he
    nlinarith only [he, h, norm_nonneg w]
  refine ⟨w.arg, ?_, ?_⟩
  · simpa [hn,w] using Complex.norm_mul_cos_arg w
  · simpa [hn,w] using Complex.norm_mul_sin_arg w

private theorem circle_tangent_parameter (C : ClosedUnitFrenetCurve) {c : ℝ}
    (hk : ∀ s, C.k s = c) :
    ∃ α : ℝ, ∀ s, C.tx s = Real.cos (α+c*s) ∧ C.ty s = Real.sin (α+c*s) := by
  obtain ⟨α,hx,hy⟩ := unit_angle (C.unit 0)
  let X s := C.tx s - Real.cos (α+c*s)
  let Y s := C.ty s - Real.sin (α+c*s)
  have angle (s : ℝ) : HasDerivAt (fun t => α+c*t) c s := by
    simpa using (((hasDerivAt_id s).const_mul c).const_add α)
  have dX (s : ℝ) : HasDerivAt X (-c*Y s) s := by
    convert! (C.dtx s).sub (angle s).cos using 1
    simp only [Y,hk]
    ring
  have dY (s : ℝ) : HasDerivAt Y (c*X s) s := by
    convert! (C.dty s).sub (angle s).sin using 1
    simp only [X,hk]
    ring
  have dR (s : ℝ) : HasDerivAt (fun t => X t^2 + Y t^2) 0 s := by
    convert! ((dX s).pow 2).add ((dY s).pow 2) using 1
    ring
  refine ⟨α,fun s => ?_⟩
  have hr := is_const_of_deriv_eq_zero (fun t => (dR t).differentiableAt)
    (fun t => (dR t).deriv) s 0
  have hzero : X s^2 + Y s^2 = 0 := by simpa [X,Y,hx,hy] using hr
  have ex : X s = 0 := by nlinarith only [hzero,sq_nonneg (Y s),sq_nonneg (X s)]
  have ey : Y s = 0 := by nlinarith only [hzero,sq_nonneg (Y s),sq_nonneg (X s)]
  exact ⟨sub_eq_zero.mp ex,sub_eq_zero.mp ey⟩

/-- The support system of the given position, relative to the origin used
in the normal similarity equation, for arbitrary similarity coefficients. -/
def centeredSupportProfile (C : ClosedUnitFrenetCurve) {a b : ℝ}
    (hp : ∀ s, C.positionForce s = -a * C.normalSupport s - b * C.tangentSupport s) :
    PeriodicSupportProfile a b C.period where
  k := C.k
  v := C.v
  p := C.normalSupport
  q := C.tangentSupport
  dk := C.dk
  dv := fun s => by
    convert C.dv s using 1
    have h := hp s
    rw [C.positionForce_eq] at h
    dsimp only [force] at h
    linarith
  dp := C.normalSupport_hasDerivAt
  dq := C.tangentSupport_hasDerivAt
  periodic_k := C.periodic_k
  periodic_v := C.periodic_v
  periodic_p := C.periodic_normalSupport
  periodic_q := C.periodic_tangentSupport

/-- Any force function on oriented unit directions suffices. The two
coordinate identities give the position itself in the rotating frame. -/
theorem centered_circle_of_tangent_force_law (C : ClosedUnitFrenetCurve) {a b : ℝ}
    (hp : ∀ s, C.positionForce s = -a * C.normalSupport s - b * C.tangentSupport s)
    (G : ℝ → ℝ → ℝ) (law : ∀ s, C.positionForce s = G (C.tx s) (C.ty s)) :
    ∃ c : ℝ, c ≠ 0 ∧ c^4 = 2*a ∧
      (∀ s, C.positionCurvature s = c) ∧
      (∀ s, C.positionForce s = c^3/2) ∧
      (∀ s, C.x s = C.ty s / c ∧ C.y s = -C.tx s / c) ∧
      (∀ s, C.x s^2 + C.y s^2 = (1/c)^2) := by
  let z := C.centeredSupportProfile hp
  let θ (s : ℝ) := ∫ u in (0:ℝ)..s, C.k u
  have hd (s : ℝ) : HasDerivAt θ (C.k s) s :=
    intervalIntegral.integral_hasDerivAt_right (C.continuous_k.intervalIntegrable 0 s)
      C.continuous_k.aestronglyMeasurable.stronglyMeasurableAtFilter C.continuous_k.continuousAt
  have force_eq (s : ℝ) : z.force s = C.positionForce s := (hp s).symm
  have equal (l r : ℝ) (h : θ l = θ r) : z.force l = z.force r := by
    obtain ⟨hx,hy⟩ := C.tangent_eq_of_angle_eq hd h
    rw [force_eq, force_eq, law, law, hx, hy]
  obtain ⟨c,hc,hc4,hk,_,hN,hT⟩ := z.circle_of_equal_angle_force C.period_pos hd equal
  have kconst : C.positionCurvature = fun _ => c := by
    rw [C.positionCurvature_eq]
    exact funext hk
  have pos (s : ℝ) : C.x s = C.ty s / c ∧ C.y s = -C.tx s / c := by
    have normal : -C.x s*C.ty s + C.y s*C.tx s = -1/c := hN s
    have tangent : C.x s*C.tx s + C.y s*C.ty s = 0 := hT s
    field_simp [hc] at normal
    constructor
    · apply (eq_div_iff hc).2
      linear_combination -(C.ty s)*normal + c*(C.tx s)*tangent - (c*C.x s)*(C.unit s)
    · apply (eq_div_iff hc).2
      linear_combination (C.tx s)*normal + c*(C.ty s)*tangent - (c*C.y s)*(C.unit s)
  refine ⟨c,hc,hc4,fun s => congrFun kconst s,?_,pos,?_⟩
  · intro s
    simp [positionForce, kconst]
  · intro s
    rw [(pos s).1, (pos s).2]
    field_simp [hc]
    nlinarith only [C.unit s]

/-- Closure of the actual tangent gives the integer multiplicity. Every
unit direction is attained, so the prescribed law has one value on the
entire unit circle. Its values elsewhere are arbitrary. -/
theorem covering_and_law_of_tangent_force (C : ClosedUnitFrenetCurve) {a b : ℝ}
    (hp : ∀ s, C.positionForce s = -a * C.normalSupport s - b * C.tangentSupport s)
    (G : ℝ → ℝ → ℝ) (law : ∀ s, C.positionForce s = G (C.tx s) (C.ty s)) :
    ∃ (c α : ℝ) (n : ℤ), c ≠ 0 ∧ n ≠ 0 ∧ c^4 = 2*a ∧ c*C.period = (n:ℝ)*(2*Real.pi) ∧
      (∀ s, C.x s = Real.sin (α+c*s)/c ∧ C.y s = -Real.cos (α+c*s)/c) ∧
      (∀ u v : ℝ, u^2+v^2=1 → G u v = c^3/2) := by
  obtain ⟨c,hc,hc4,hk,hF,hpos,_⟩ := C.centered_circle_of_tangent_force_law hp G law
  rw [C.positionCurvature_eq] at hk
  obtain ⟨α,frame⟩ := circle_tangent_parameter C hk
  have periodX : C.tx C.period=C.tx 0 := by simpa using C.periodic_tx 0
  have periodY : C.ty C.period=C.ty 0 := by simpa using C.periodic_ty 0
  have hx := (frame C.period).1.symm.trans (periodX.trans (frame 0).1)
  have hy := (frame C.period).2.symm.trans (periodY.trans (frame 0).2)
  simp only [mul_zero,add_zero] at hx hy
  have cos1 : Real.cos (c*C.period) = 1 := by
    rw [show c*C.period = (α+c*C.period)-α by ring, Real.cos_sub,hx,hy]
    nlinarith only [Real.sin_sq_add_cos_sq α]
  obtain ⟨n,hn⟩ := (Real.cos_eq_one_iff _).mp cos1
  have hnz : n ≠ 0 := by
    intro h
    rw [h] at hn
    simp only [Int.cast_zero,zero_mul] at hn
    exact (mul_ne_zero hc C.period_pos.ne') hn.symm
  refine ⟨c,α,n,hc,hnz,hc4,hn.symm,?_,?_⟩
  · intro s
    simpa only [(frame s).1,(frame s).2] using hpos s
  · intro u v huv
    obtain ⟨θ,hu,hv⟩ := unit_angle huv
    let s := (θ-α)/c
    have angle : α+c*s=θ := by dsimp only [s]; field_simp [hc]; ring
    have dir := frame s
    rw [angle,hu,hv] at dir
    rw [←dir.1,←dir.2,←law,hF]

/-- Every admissible phase, orientation and covering is realized by a
closed Frenet curve satisfying the two laws in the given coordinates. -/
theorem exists_circle_with_tangent_force {a c L : ℝ} (b α : ℝ) (n : ℤ)
    (hc : c ≠ 0) (hL : 0 < L) (cover : c*L = (n:ℝ)*(2*Real.pi))
    (ha : c^4 = 2*a) (G : ℝ → ℝ → ℝ)
    (hG : ∀ u v : ℝ, u^2+v^2=1 → G u v = c^3/2) :
    ∃ C : ClosedUnitFrenetCurve, C.period=L ∧
      (∀ s, C.x s = Real.sin (α+c*s)/c ∧ C.y s = -Real.cos (α+c*s)/c) ∧
      (∀ s, C.positionForce s = -a*C.normalSupport s - b*C.tangentSupport s) ∧
      (∀ s, C.positionForce s = G (C.tx s) (C.ty s)) := by
  let tx s := Real.cos (α+c*s)
  let ty s := Real.sin (α+c*s)
  have angle (s : ℝ) : HasDerivAt (fun t => α+c*t) c s := by
    simpa using (((hasDerivAt_id s).const_mul c).const_add α)
  have dtx (s : ℝ) : HasDerivAt tx (-c*ty s) s := by
    convert! (angle s).cos using 1
    dsimp only [ty]
    ring
  have dty (s : ℝ) : HasDerivAt ty (c*tx s) s := by
    convert! (angle s).sin using 1
    dsimp only [tx]
    ring
  have per {f : ℝ → ℝ} (h : Function.Periodic f (2*Real.pi)) :
      Function.Periodic (fun s => f (α+c*s)) L := by
    intro s
    change f (α+c*(s+L))=f (α+c*s)
    rw [mul_add,←add_assoc,cover]
    exact h.int_mul n _
  have px : Function.Periodic tx L := per Real.cos_periodic
  have py : Function.Periodic ty L := per Real.sin_periodic
  have unit (s : ℝ) : tx s^2+ty s^2=1 := by
    simpa only [tx,ty,add_comm] using Real.sin_sq_add_cos_sq (α+c*s)
  let C : ClosedUnitFrenetCurve := {
    period := L, period_pos := hL, x := fun s => ty s/c, y := fun s => -tx s/c,
    tx := tx, ty := ty, k := fun _ => c, v := fun _ => 0, w := fun _ => 0,
    dx := fun s => by simpa [hc] using (dty s).div_const c,
    dy := fun s => by simpa [hc] using (dtx s).neg.div_const c,
    dtx := dtx, dty := dty, dk := fun s => hasDerivAt_const s c,
    dv := fun s => hasDerivAt_const s 0, continuous_w := continuous_const,
    unit := unit, periodic_x := fun s => by simp only [py s],
    periodic_y := fun s => by simp only [px s], periodic_tx := px, periodic_ty := py,
    periodic_k := fun _ => rfl, periodic_v := fun _ => rfl }
  have hF (s : ℝ) : C.positionForce s=c^3/2 := by
    rw [C.positionForce_eq]
    change 0+c^3/2=c^3/2
    exact zero_add _
  refine ⟨C,rfl,fun _ => ⟨rfl,rfl⟩,?_,?_⟩
  · intro s
    have hN : C.normalSupport s = -1/c := by
      change -(ty s/c)*ty s+(-tx s/c)*tx s = -1/c
      field_simp [hc]
      nlinarith only [unit s]
    have hT : C.tangentSupport s = 0 := by
      change (ty s/c)*tx s+(-tx s/c)*ty s=0
      ring
    rw [hF,hN,hT]
    field_simp [hc]
    nlinarith only [ha]
  · intro s
    exact (hF s).trans (hG _ _ (unit s)).symm

/-- Complete existence criterion for prescribed dilation, rotation and
force function. Only the values of the law on the unit circle enter. -/
theorem tangent_force_solvable_iff (a b : ℝ) (G : ℝ → ℝ → ℝ) :
    (∃ C : ClosedUnitFrenetCurve,
      (∀ s, C.positionForce s = -a*C.normalSupport s-b*C.tangentSupport s) ∧
      (∀ s, C.positionForce s = G (C.tx s) (C.ty s))) ↔
    ∃ c : ℝ, c ≠ 0 ∧ c^4=2*a ∧ (∀ u v : ℝ, u^2+v^2=1 → G u v=c^3/2) := by
  constructor
  · rintro ⟨C,hp,hl⟩
    obtain ⟨c,_,_,hc,_,hca,_,_,hG⟩ := C.covering_and_law_of_tangent_force hp G hl
    exact ⟨c,hc,hca,hG⟩
  · rintro ⟨c,hc,hca,hG⟩
    have period : ∃ (L : ℝ) (n : ℤ), 0<L ∧ c*L=(n:ℝ)*(2*Real.pi) := by
      rcases lt_or_gt_of_ne hc with hn|hp
      · refine ⟨-(2*Real.pi)/c,-1,div_pos_of_neg_of_neg (by linarith [Real.pi_pos]) hn,?_⟩
        push_cast
        field_simp [hc]
      · refine ⟨(2*Real.pi)/c,1,div_pos (by positivity) hp,?_⟩
        push_cast
        field_simp [hc]
    obtain ⟨L,n,hL,cover⟩ := period
    obtain ⟨C,_,_,hp,hl⟩ := exists_circle_with_tangent_force b 0 n hc hL cover hca G hG
    exact ⟨C,hp,hl⟩

end ClosedSimilarity.ClosedUnitFrenetCurve

#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.centered_circle_of_tangent_force_law
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.covering_and_law_of_tangent_force
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.exists_circle_with_tangent_force
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.tangent_force_solvable_iff
