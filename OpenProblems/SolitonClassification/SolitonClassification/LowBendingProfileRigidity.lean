import SolitonClassification.LowBendingRate

noncomputable section
namespace ClosedSimilarity.ClosedUnitFrenetCurve
open MeasureTheory Set
variable (c : ClosedUnitFrenetCurve)

/-- Complex coordinates for the native classification curve carry exactly
the same period and signed curvature jets. -/
def lowBendingCurve : LowBending.ClosedFrenetCurve where
  period := c.period
  period_pos := c.period_pos
  curve := fun s => (c.x s:ℂ)+(c.y s:ℂ)*Complex.I
  tangent := fun s => (c.tx s:ℂ)+(c.ty s:ℂ)*Complex.I
  curvature := c.k
  curvature₁ := c.v
  curvature₂ := c.w
  curve_periodic := fun s => by dsimp only; rw [c.periodic_x s,c.periodic_y s]
  tangent_periodic := fun s => by dsimp only; rw [c.periodic_tx s,c.periodic_ty s]
  curvature_periodic := c.periodic_k
  curvature₁_periodic := c.periodic_v
  curve_deriv := fun s => (c.dx s).ofReal_comp.add ((c.dy s).ofReal_comp.mul_const Complex.I)
  tangent_deriv := by
    intro s
    apply ((c.dtx s).ofReal_comp.add ((c.dty s).ofReal_comp.mul_const Complex.I)).congr_deriv
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  curvature_deriv := c.dk
  curvature₁_deriv := c.dv
  curvature₂_continuous := c.continuous_w
  tangent_unit := by
    intro s
    have h := Complex.normSq_add_mul_I (c.tx s) (c.ty s)
    rw [Complex.normSq_eq_norm_sq,c.unit s] at h
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    simpa only [one_pow] using h

/-- The periodic support profile is constructed from position for any
dilation–rotation law about the origin. -/
def lowBendingSupport (a b : ℝ)
    (shape : ∀s, c.force s= -a*c.normalSupport s-b*c.tangentSupport s) :
    PeriodicSupportProfile a b c.period where
  k := c.k
  v := c.v
  p := c.normalSupport
  q := c.tangentSupport
  dk := c.dk
  dv := by
    intro s
    apply (c.dv s).congr_deriv
    have hs := shape s
    unfold force at hs
    linarith
  dp := c.normalSupport_hasDerivAt
  dq := c.tangentSupport_hasDerivAt
  periodic_k := c.periodic_k
  periodic_v := c.periodic_v
  periodic_p := c.periodic_normalSupport
  periodic_q := c.periodic_tangentSupport

/-- A closed shape satisfying the actual physical similarity equation and
the initial bending cap has constant curvature and exactly one full turn. -/
theorem low_bending_similarity_rigidity (a b : ℝ)
    (shape : ∀s, c.force s= -a*c.normalSupport s-b*c.tangentSupport s)
    (cap : c.period*(∫ s in 0..c.period,c.k s^2)≤4*Real.pi^2+36) :
    ∃ K : ℝ, (K*c.period=2*Real.pi ∨ K*c.period= -(2*Real.pi)) ∧ ∀s,c.k s=K := by
  let p := c.lowBendingCurve
  let z := c.lowBendingSupport a b shape
  have B : z.bending=2*p.energy := by
    change (∫ s in 0..c.period,c.k s^2)=2*((∫ s in 0..c.period,c.k s^2)/2); ring
  have fs : ∀s,p.force s=z.force s := shape
  have ej := z.integral_k_force
  change (∫ s in 0..c.period,c.k s*z.force s)=a*c.period at ej
  have j : (∫ s in 0..p.period,p.curvature s*p.force s)=a*p.period := by
    simp_rw [fs]; exact ej
  have ds : p.dissipation=a*p.energy := by
    unfold LowBending.ClosedFrenetCurve.dissipation
    simp_rw [fs]
    change z.forceSquare=a*p.energy
    rw [z.forceSquare_eq,B]; ring
  have pcap : 2*p.energy*p.period≤4*Real.pi^2+36 := by
    change 2*((∫ s in 0..c.period,c.k s^2)/2)*c.period≤_
    linarith only [cap]
  have exactfloor : 2*p.energy*p.period=4*Real.pi^2 := by
    have lo := p.sharp_energy_length
    by_contra! hn
    have greater : 4*Real.pi^2<2*p.energy*p.period := by
      have le : 4*Real.pi^2≤2*p.energy*p.period := by linarith
      exact lt_of_le_of_ne le (Ne.symm hn)
    have h := p.bending_sublevel_strict greater pcap
    rw [j,ds] at h; linarith
  let K := (∫ s in 0..c.period,c.k s)/c.period
  have km : c.period*K=(∫ s in 0..c.period,c.k s) := by
    dsimp only [K]; field_simp [c.period_pos.ne']
  have turns := p.low_product_turning pcap
  change (∫ s in 0..c.period,c.k s)=_ ∨ (∫ s in 0..c.period,c.k s)=_ at turns
  have one : K*c.period=2*Real.pi ∨ K*c.period= -(2*Real.pi) := by
    simpa only [mul_comm K c.period,km] using turns
  refine ⟨K,one,?_⟩
  have two := (LowBending.BendingSublevel.centered_moments c.continuous_k km.symm).2.1
  have sq : (K*c.period)^2=4*Real.pi^2 := by rcases one with h|h <;> rw [h] <;> ring
  change (∫ s in 0..c.period,c.k s^2)=c.period*K^2+(∫ s in 0..c.period,(c.k s-K)^2) at two
  change 2*((∫ s in 0..c.period,c.k s^2)/2)*c.period=4*Real.pi^2 at exactfloor
  have zero : (∫ s in 0..c.period,(c.k s-K)^2)=0 := by
    apply (mul_eq_zero.mp (show c.period*(∫ s in 0..c.period,(c.k s-K)^2)=0 by
      linarith only [exactfloor,sq,congrArg (fun x:ℝ => x*c.period) two])).resolve_left c.period_pos.ne'
  have interval := ClosedSimilarity.continuous_nonneg_zero_of_integral_zero c.period_pos
    ((c.continuous_k.sub continuous_const).pow 2) (fun s _ => sq_nonneg (c.k s-K)) zero
  intro s
  obtain ⟨t,ht,eq⟩ := c.periodic_k.exists_mem_Ico₀ c.period_pos s
  rw [eq]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (interval t ⟨ht.1,ht.2.le⟩))

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.low_bending_similarity_rigidity
