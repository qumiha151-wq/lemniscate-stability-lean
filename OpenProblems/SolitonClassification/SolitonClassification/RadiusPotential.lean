import SolitonClassification.SolitonDilation

/-! The exact radius balance for the normalized similarity support equations,
including arbitrary rotation coefficient. The radius cap is measured from
the similarity centre. -/
noncomputable section
open MeasureTheory Set
namespace ClosedSimilarity.PeriodicSupportProfile
variable {b L : ℝ} (z : PeriodicSupportProfile 1 b L)

def radiusPotential (c s : ℝ) : ℝ :=
  z.dilationStress s - b * z.rotationStress s + c * z.q s

def radiusDefect (R c s : ℝ) : ℝ :=
  (z.k s + c*z.p s)^2/2 + (1+c^2/2)*(R^2-(z.p s)^2) + b^2*(z.q s)^2

/-- The corrected squared radius multiplied by the pitch. This form
avoids division and its differential identity remains valid at zero pitch. -/
def correctedRadius (s : ℝ) : ℝ := b*((z.p s)^2+(z.q s)^2)/2+z.v s

theorem correctedRadius_hasDerivAt (s : ℝ) :
    HasDerivAt z.correctedRadius (-(z.k s)^3/2-z.p s) s := by
  convert (((((z.dp s).pow 2).add ((z.dq s).pow 2)).const_mul b).div_const 2).add
    (z.dv s) using 1 <;> first | rfl | dsimp [correctedRadius]; ring

theorem radiusPotential_hasDerivAt (R c s : ℝ) :
    HasDerivAt (z.radiusPotential c) (z.radiusDefect R c s - ((1+c^2/2)*R^2-c)) s := by
  convert ((z.dilationStress_hasDerivAt s).sub ((z.rotationStress_hasDerivAt s).const_mul b)).add
    ((z.dq s).const_mul c) using 1 <;> first | rfl | dsimp [radiusPotential,radiusDefect,force]; ring

theorem continuous_radiusDefect (R c : ℝ) : Continuous (z.radiusDefect R c) := by
  unfold radiusDefect
  have hk := z.continuous_k
  have hp := z.continuous_p
  have hq := z.continuous_q
  fun_prop

theorem integral_radiusDefect (R c : ℝ) :
    (∫ s in 0..L, z.radiusDefect R c s) = L*((1+c^2/2)*R^2-c) := by
  let e := (1+c^2/2)*R^2-c
  have der (s : ℝ) : HasDerivAt (fun t => z.radiusPotential c t + e*t)
      (z.radiusDefect R c s) s := by
    convert (z.radiusPotential_hasDerivAt R c s).add ((hasDerivAt_id s).const_mul e) using 1 <;>
      first | rfl | change _ = _ + e * 1; dsimp only [e]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => der s)
    ((z.continuous_radiusDefect R c).intervalIntegrable 0 L)]
  simp only [radiusPotential,dilationStress,rotationStress,
    show z.k L = z.k 0 by simpa using z.periodic_k 0,
    show z.v L = z.v 0 by simpa using z.periodic_v 0,
    show z.p L = z.p 0 by simpa using z.periodic_p 0,
    show z.q L = z.q 0 by simpa using z.periodic_q 0]
  dsimp [e]
  ring

theorem radiusDefect_nonneg {R c : ℝ} (cap : ∀s, (z.p s)^2+(z.q s)^2≤R^2) (s : ℝ) :
    0≤z.radiusDefect R c s := by
  have h : 0≤R^2-(z.p s)^2 := by linarith [cap s,sq_nonneg (z.q s)]
  unfold radiusDefect
  positivity

/-- Every radius cap around the similarity centre is at least
\(2^{-1/4}\), with the dilation coefficient normalized to one. -/
theorem one_le_twice_radius_fourth (hL : 0<L) {R : ℝ} (hR : 0<R)
    (cap : ∀s, (z.p s)^2+(z.q s)^2≤R^2) : 1≤2*R^4 := by
  let c := 1/R^2
  have hh := intervalIntegral.integral_nonneg_of_forall (μ:=volume) hL.le
    (z.radiusDefect_nonneg (c:=c) cap)
  rw [z.integral_radiusDefect] at hh
  have e := (mul_nonneg_iff_of_pos_left hL).mp hh
  dsimp [c] at e
  field_simp [hR.ne'] at e
  nlinarith only [e]

/-- At the critical radius all support data are those of a centred
circle. The statement includes covers and both curvature orientations. -/
theorem centered_circle_at_critical_radius (hL : 0<L) {R : ℝ} (hR : 0<R)
    (cap : ∀s, (z.p s)^2+(z.q s)^2≤R^2) (crit : 2*R^4=1) :
    ∃ k₀ : ℝ, k₀ ≠ 0 ∧ k₀^4=2 ∧ (∀s,z.k s=k₀) ∧ (∀s,z.v s=0) ∧
      (∀s,z.p s= -1/k₀) ∧ (∀s,z.q s=0) := by
  let c := 1/R^2
  have cp : 0<c := by dsimp [c]; positivity
  have e : (1+c^2/2)*R^2-c=0 := by
    dsimp [c]
    field_simp [hR.ne']
    nlinarith only [crit]
  have hi := z.integral_radiusDefect R c
  rw [e,mul_zero] at hi
  have zeroI := continuous_nonneg_zero_of_integral_zero hL (z.continuous_radiusDefect R c)
    (fun s _ => z.radiusDefect_nonneg cap s) hi
  have per : Function.Periodic (z.radiusDefect R c) L := by
    intro s
    simp only [radiusDefect,z.periodic_k s,z.periodic_p s,z.periodic_q s]
  have nz (s : ℝ) : z.k s ≠ 0 := by
    intro ks
    obtain ⟨t,ht,he⟩ := per.exists_mem_Ico₀ hL s
    have hz := he.trans (zeroI t ⟨ht.1,ht.2.le⟩)
    have h : 0≤R^2-(z.p s)^2 := by linarith [cap s,sq_nonneg (z.q s)]
    have pos : 0<1+c^2/2 := by positivity
    have a := mul_nonneg pos.le h
    have d : 0≤b^2*(z.q s)^2 := by positivity
    dsimp [radiusDefect] at hz
    rw [ks,zero_add] at hz
    have m : (c*z.p s)^2=0 := by nlinarith only [hz,a,d,sq_nonneg (c*z.p s)]
    have ps := (mul_eq_zero.mp (sq_eq_zero_iff.mp m)).resolve_left cp.ne'
    rw [ps] at hz
    have hstrict : 0<(1+c^2/2)*R^2 := mul_pos pos (sq_pos_of_pos hR)
    nlinarith only [hz,d,hstrict]
  have sign : (∀s, 0≤z.k s) ∨ (∀s, z.k s≤0) := by
    by_cases h : ∀s, 0≤z.k s
    · exact Or.inl h
    · right
      push Not at h
      obtain ⟨s,hs⟩ := h
      intro t
      by_contra! ht
      obtain ⟨x,hx⟩ := intermediate_value_univ s t z.continuous_k
        (show (0:ℝ) ∈ Icc (z.k s) (z.k t) from ⟨hs.le,ht.le⟩)
      exact nz x hx
  simpa using z.one_sign_centered_circle_of_period hL sign

end ClosedSimilarity.PeriodicSupportProfile
#print axioms ClosedSimilarity.PeriodicSupportProfile.correctedRadius_hasDerivAt
#print axioms ClosedSimilarity.PeriodicSupportProfile.integral_radiusDefect
#print axioms ClosedSimilarity.PeriodicSupportProfile.one_le_twice_radius_fourth
#print axioms ClosedSimilarity.PeriodicSupportProfile.centered_circle_at_critical_radius
