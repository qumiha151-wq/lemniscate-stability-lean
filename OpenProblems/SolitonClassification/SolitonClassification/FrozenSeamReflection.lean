import SolitonClassification.GlobalSupportFlow
import SolitonClassification.FrozenStressOrbit

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.FrozenStress.Orbit
open GlobalSupport

/-- Reversing arclength through a seam with zero curvature derivative and
zero tangential support fixes the frozen trajectory up to two signs. -/
theorem seam_reflection (z : Orbit) (hv : z.v 0 = 0) (hq : z.q 0 = 0) (s : ℝ) :
    z.k (-s) = z.k s ∧ z.v (-s) = -z.v s ∧
    z.p (-s) = z.p s ∧ z.q (-s) = -z.q s := by
  let X := fun u : ℝ => (![z.k u,z.v u,z.p u,z.q u] : Phase)
  let Y := fun u : ℝ => (![z.k (-u),-z.v (-u),z.p (-u),-z.q (-u)] : Phase)
  have h0 : Y 0 = X 0 := by simp [Y,X,hv,hq]
  have DX (u : ℝ) : HasDerivAt X (rhs 0 (X u)) u := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact z.dk u
    · exact z.dv u
    · exact z.dp u
    · simpa [X,rhs] using z.dq u
  have DY (u : ℝ) : HasDerivAt Y (rhs 0 (Y u)) u := by
    have hn : HasDerivAt (fun v : ℝ => -v) (-1) u := by
      simpa [Pi.neg_def,id_def] using (hasDerivAt_id u).neg
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [Y,rhs,Function.comp_def] using (z.dk (-u)).comp u hn
    · simpa [Y,rhs,Function.comp_def,Pi.neg_def] using ((z.dv (-u)).comp u hn).neg
    · simpa [Y,rhs,Function.comp_def] using (z.dp (-u)).comp u hn
    · simpa [Y,rhs,Function.comp_def,Pi.neg_def] using ((z.dq (-u)).comp u hn).neg
  have h := (exists_unique_solution 0 (X 0)).unique ⟨h0,DY⟩ ⟨rfl,DX⟩
  have eqv (i : Fin 4) := congrFun (congrFun h s) i
  exact ⟨eqv 0,neg_eq_iff_eq_neg.mp (eqv 1),eqv 2,neg_eq_iff_eq_neg.mp (eqv 3)⟩

/-- The raw impact is identical on the incoming and outgoing sides and the
radial stress changes sign. This holds at vanishing stress as well. -/
theorem seam_impact_radial_parity (z : Orbit) (hv : z.v 0 = 0) (hq : z.q 0 = 0) (s : ℝ) :
    z.root (-s) * z.across (-s) = z.root s * z.across s ∧
    z.radial (-s) = -z.radial s := by
  obtain ⟨hk,hv',hp,hq'⟩ := z.seam_reflection hv hq s
  have ha : z.amplitude (-s) = z.amplitude s := by simp [amplitude,hk,hv']
  have ht : z.transverse (-s) = z.transverse s := by simp [transverse,hk,hv',hp,hq']
  constructor
  · simp [root,across,ha,ht]
  · rw [radial,radial,hk,hv',hp,hq']; ring

end ClosedSimilarity.FrozenStress.Orbit
#print axioms ClosedSimilarity.FrozenStress.Orbit.seam_reflection
#print axioms ClosedSimilarity.FrozenStress.Orbit.seam_impact_radial_parity
