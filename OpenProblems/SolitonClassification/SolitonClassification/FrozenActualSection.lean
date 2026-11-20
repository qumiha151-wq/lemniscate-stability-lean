import SolitonClassification.FrozenSectionMap
import SolitonClassification.FrozenSeamSection

noncomputable section
open Set
namespace ClosedSimilarity.GlobalSupport
open FrozenStress

/-- Reflection at a frozen seam reverses the corrected radial height. The
    formula is valid even where the stress vanishes (division is total). -/
theorem reflected_height (c t : ℝ) : (seam c).outgoingHeight (-t) = -(seam c).outgoingHeight t := by
  let z := seam c
  obtain ⟨_,hv,_,hq⟩ := seam_initial c
  obtain ⟨k,v,p,q⟩ := z.seam_reflection hv hq t
  have ha : z.amplitude (-t)=z.amplitude t := by simp [Orbit.amplitude,k,v]
  have hr : z.radial (-t) = -z.radial t := (z.seam_impact_radial_parity hv hq t).2
  have hb : z.transverse (-t) = z.transverse t := by simp [Orbit.transverse,k,v,p,q]
  change z.outgoingHeight (-t) = -z.outgoingHeight t
  simp only [Orbit.outgoingHeight,correctedOutgoing,chi,Orbit.shape,Orbit.slope,
    Orbit.along,Orbit.across,Orbit.root,ha,k,v,hr,hb,neg_div]
  ring

def seamImpact (c t : ℝ) := (seam c).root t * (seam c).across t

structure SeamSection (a b S H : ℝ) where
  time : Icc a b → ℝ
  continuous_time : Continuous time
  late : ∀ c : Icc a b, S ≤ time c
  outgoing : ∀ c : Icc a b, (seam c).outgoingHeight (time c) = H
  incoming : ∀ c : Icc a b, -(seam c).outgoingHeight (-time c) = H
  transverse_rate : ∀ c : Icc a b, 1/4 ≤ deriv (seam c).outgoingHeight (time c)
  unique_outgoing : ∀ c : Icc a b, ∀ t≥S, (seam c).outgoingHeight t = H → t = time c
  unique_incoming : ∀ c : Icc a b, ∀ t≤-S, -(seam c).outgoingHeight t = H → t = -time c
  continuous_incoming_state : Continuous (fun c : Icc a b => coords (seam c) (-time c))
  continuous_incoming_impact : Continuous (fun c : Icc a b => seamImpact c (-time c))
  paired_impact : ∀ c : Icc a b, seamImpact c (-time c) = seamImpact c (time c)

/-- Every sufficiently high incoming section of the globally realized frozen
    seam family has continuous impact and a continuous flight to the seam.
    Times are at least twenty, permitting the finite endpoint certificates to
    determine the signs at the actual crossings. -/
theorem actual_seam_sections (a b : ℝ) :
    ∃ S≥20, ∃ H₀ : ℝ, ∀ H≥H₀, Nonempty (SeamSection a b S H) := by
  let Z := fun c : Icc a b => seam c
  have coord (i : Fin 4) (t : ℝ) :
      Continuous (fun c : Icc a b => coords (Z c) t i) :=
    (continuous_apply i).comp (continuous_seam_coordinates.comp
      (continuous_const.prodMk continuous_subtype_val))
  have init (c : Icc a b) : (Z c).radial 0=0 := by
    obtain ⟨_,hv,_,hq⟩ := seam_initial c
    simp [Z,Orbit.radial,hv,hq]
  obtain ⟨S,hS,H₀,selector⟩ := continuous_corrected_seam_crossing Z init
    (fun c => (seam_initial c).2.2.1) (coord 0) (coord 1) (coord 2) (coord 3) 20
  refine ⟨S,hS,H₀,?_⟩
  intro H hH
  obtain ⟨τ,hτ,sel⟩ := selector H hH
  have state : Continuous (fun c : Icc a b => coords (seam c) (-τ c)) :=
    continuous_seam_coordinates.comp (hτ.neg.prodMk continuous_subtype_val)
  have h (i : Fin 4) := (continuous_apply i).comp state
  have cA : Continuous (fun c : Icc a b => (seam c).amplitude (-τ c)) :=
    Real.continuous_sqrt.comp ((((h 0).pow 2).div_const 2).pow 2 |>.add ((h 1).pow 2))
  have ct : Continuous (fun c : Icc a b => (seam c).transverse (-τ c)) :=
    continuous_seam_transverse.comp (hτ.neg.prodMk continuous_subtype_val)
  have amp (c : Icc a b) : (seam c).amplitude (-τ c) ≠ 0 := by
    obtain ⟨_,hv,_,hq⟩ := seam_initial c
    have pos : 0<τ c := by linarith [(sel c).1]
    have ra := (seam c).seam_impact_radial_parity hv hq (τ c) |>.2
    have rn : 0<(seam c).radial (-τ c) := by linarith [seam_radial_strict c pos]
    intro eq
    have ident := (seam c).stress_unit (-τ c)
    rw [eq] at ident
    nlinarith [sq_pos_of_pos rn,sq_nonneg ((seam c).transverse (-τ c))]
  refine ⟨⟨τ,hτ,fun c => (sel c).1,fun c => (sel c).2.1,?_,
    fun c => (sel c).2.2.1,fun c => (sel c).2.2.2,?_,state,
    (Real.continuous_sqrt.comp cA).mul (ct.div cA amp),?_⟩⟩
  · intro c
    rw [reflected_height,neg_neg]
    exact (sel c).2.1
  · intro c t ht hit
    have eq := reflected_height c (-t)
    rw [neg_neg] at eq
    have pos := (sel c).2.2.2 (-t) (by linarith) (by change (seam c).outgoingHeight (-t)=H; linarith)
    linarith
  · intro c
    obtain ⟨_,hv,_,hq⟩ := seam_initial c
    exact ((seam c).seam_impact_radial_parity hv hq _).1

/-- Tail signs for two seam curvatures determine a whole interval of impacts
    attained at each common radial section on both sides of the seam. -/
theorem SeamSection.realizes_interval {a b S H α β : ℝ} (w : SeamSection a b S H)
    (hab : a≤b) (neg : ∀ t≥S, seamImpact a t < α)
    (pos : ∀ t≥S, β < seamImpact b t) {v : ℝ} (hv : v∈Icc α β) :
    ∃ c : Icc a b, (c:ℝ)∈Ioo a b ∧ seamImpact c (-w.time c)=v ∧ seamImpact c (w.time c)=v := by
  let left : Icc a b := ⟨a,le_rfl,hab⟩
  let right : Icc a b := ⟨b,hab,le_rfl⟩
  let I := fun c : Icc a b => seamImpact c (-w.time c)
  have lo : I left < v := (w.paired_impact left).trans_lt ((neg _ (w.late left)).trans_le hv.1)
  have hi : v < I right := (hv.2.trans_lt (pos _ (w.late right))).trans_eq (w.paired_impact right).symm
  let : PreconnectedSpace (Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  obtain ⟨c,hit⟩ := intermediate_value_univ left right w.continuous_incoming_impact ⟨lo.le,hi.le⟩
  change I c=v at hit
  have ca : (c:ℝ)≠a := by
    intro e
    have ee : c=left := Subtype.ext e
    exact lo.ne (ee ▸ hit)
  have cb : (c:ℝ)≠b := by
    intro e
    have ee : c=right := Subtype.ext e
    exact hi.ne (ee ▸ hit.symm)
  exact ⟨c,⟨lt_of_le_of_ne c.property.1 ca.symm, lt_of_le_of_ne c.property.2 cb⟩,
    hit,(w.paired_impact c).symm.trans hit⟩

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.GlobalSupport.actual_seam_sections
#print axioms ClosedSimilarity.GlobalSupport.SeamSection.realizes_interval
