import SolitonClassification.Rotating.IntegerEndpointClosure
import SolitonClassification.Rotating.RotatingClosedProfileClosure
import SolitonClassification.ReflectedArc

/-! Periodic extension for the winding-one shooting interval in the original,
unclipped field. The construction at the seam uses both endpoint derivatives. -/
namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Extension
def periodize (f : ℝ → State) {T : ℝ} (hT : 0 < T) (t : ℝ) : State :=
  f (toIcoMod hT 0 t)

lemma periodize_periodic (f : ℝ → State) {T : ℝ} (hT : 0 < T) :
    Function.Periodic (periodize f hT) T := by
  intro t
  simp [periodize, toIcoMod_add_right]

lemma periodize_sub_zsmul (f : ℝ → State) {T : ℝ} (hT : 0 < T) (t : ℝ) (n : ℤ) :
    periodize f hT (t - n • T) = periodize f hT t := by
  simp [periodize]

lemma periodize_eq {f : ℝ → State} {T : ℝ} (hT : 0 < T) (hend : f 0 = f T)
    {t : ℝ} (ht : t ∈ Icc 0 T) : periodize f hT t = f t := by
  by_cases heq : t = T
  · subst t
    change f (toIcoMod hT 0 T) = f T
    rw [show toIcoMod hT 0 T = 0 by
      simpa only [zero_add] using toIcoMod_apply_right hT 0]
    exact hend
  · have hlt : t < T := lt_of_le_of_ne ht.2 heq
    rw [periodize, (toIcoMod_eq_self hT).2 (by simpa using And.intro ht.1 hlt)]

/-- Differentiability at the joining point uses both endpoint derivatives. -/
lemma periodize_derivative_zero (V : State → State) {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (h0 : HasDerivAt f (V (f 0)) 0)
    (h1 : HasDerivAt f (V (f T)) T) :
    HasDerivAt (periodize f hT) (V (periodize f hT 0)) 0 := by
  have heq0 : periodize f hT 0 = f 0 := periodize_eq hT hend ⟨le_rfl, hT.le⟩
  have hr : HasDerivWithinAt (periodize f hT) (V (f 0)) (Ici 0) 0 := by
    apply h0.hasDerivWithinAt.congr_of_eventuallyEq _ heq0
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with s hs hsT
    exact periodize_eq hT hend ⟨hs, hsT.le⟩
  have hshift : HasDerivAt (fun s : ℝ => f (s + T)) (V (f 0)) 0 := by
    have hd : HasDerivAt (fun s : ℝ => s + T) 1 0 := (hasDerivAt_id 0).add_const T
    have h1' : HasDerivAt f (V (f 0)) (0 + T) := by simpa [hend] using h1
    convert! h1'.scomp 0 hd using 1
    simp
  have hl : HasDerivWithinAt (periodize f hT) (V (f 0)) (Iic 0) 0 := by
    apply hshift.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show -T < (0:ℝ) by linarith)).filter_mono nhdsWithin_le_nhds]
        with s hs hsT
      rw [← periodize_periodic f hT s]
      exact periodize_eq hT hend ⟨by linarith, by linarith [Set.mem_Iic.mp hs]⟩
    · simpa [heq0] using hend
  have hh := hl.union hr
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at hh
  simpa [heq0] using hh

lemma periodize_derivative_Ico (V : State → State) {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (hf : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt f (V (f t)) t)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivAt (periodize f hT) (V (periodize f hT t)) t := by
  by_cases ht0 : t = 0
  · subst t
    exact periodize_derivative_zero V hT hend (hf 0 ⟨le_rfl, hT.le⟩) (hf T ⟨hT.le, le_rfl⟩)
  · have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have heq : periodize f hT =ᶠ[𝓝 t] f := by
      filter_upwards [eventually_gt_nhds hpos, eventually_lt_nhds ht.2] with s hs0 hsT
      exact periodize_eq hT hend ⟨hs0.le, hsT.le⟩
    have hd := (hf t ⟨ht.1, ht.2.le⟩).congr_of_eventuallyEq heq
    simpa [periodize_eq hT hend ⟨ht.1, ht.2.le⟩] using hd

theorem periodize_solves (V : State → State) {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (hf : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt f (V (f t)) t) (t : ℝ) :
    HasDerivAt (periodize f hT) (V (periodize f hT t)) t := by
  let n := toIcoDiv hT 0 t
  have hm : t - n • T = toIcoMod hT 0 t := self_sub_toIcoDiv_zsmul hT 0 t
  have hmem : t - n • T ∈ Ico (0:ℝ) T := by
    rw [hm]
    exact toIcoMod_mem_Ico' hT t
  have hd := periodize_derivative_Ico V hT hend hf hmem
  have hc : HasDerivAt (fun s : ℝ => s - n • T) 1 t := (hasDerivAt_id t).sub_const _
  have hh := hd.scomp t hc
  simpa only [Function.comp_def, one_smul, periodize_sub_zsmul] using hh

theorem periodize_smooth (V : State → State) (hs : ContDiff ℝ (⊤ : ℕ∞) V) {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (hf : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt f (V (f t)) t) :
    ContDiff ℝ (⊤ : ℕ∞) (periodize f hT) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (periodize f hT) (Icc (t-1) (t+1)) := by
    apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun (_ : ℝ) z => V z) (u := univ)
    · exact (hs.comp contDiff_snd).contDiffOn
    · intro s hs
      exact (periodize_solves V hT hend hf s).hasDerivWithinAt
    · intro s hs
      exact mem_univ _
  exact hd.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))


end Extension

theorem angle_smul (q d : ℝ) : q • angleVector d=angleVector (q*d) := by
  ext i
  by_cases hi : i=5 <;> simp [angleVector,hi]

theorem field_sub_angle (x : State) (q d : ℝ) :
    field (x-q • angleVector d)=field x := by
  rw [angle_smul,sub_eq_add_neg,show -angleVector (q*d)=angleVector (-(q*d)) by
    ext i; by_cases h : i=5 <;> simp [angleVector,h]]
  exact field_angle_invariant _ _

/-- A matched original ODE segment extends to a globally smooth original
solution with its exact additive angle holonomy. The full input segment is
retained, including its two endpoints. -/
theorem extend_matched_segment {T d : ℝ} (hT : 0<T) (z : ℝ → State)
    (hder : ∀ t∈Icc (-T) T, HasDerivAt z (field (z t)) t)
    (hmatch : z T=z (-T)+angleVector d) :
    ∃ Z : ℝ → State, ContDiff ℝ (⊤ : ℕ∞) Z ∧
      (∀s, HasDerivAt Z (field (Z s)) s) ∧
      (∀s∈Icc (-T) T, Z s=z s) ∧
      (∀s, Z (s+2*T)=Z s+angleVector d) := by
  let P := 2*T
  have hP : 0<P := by dsimp [P]; positivity
  let v := angleVector (d/P)
  let f := fun t : ℝ => z (t-T)-t • v
  let V := fun x : State => field x-v
  have hfv : ∀t∈Icc 0 P, HasDerivAt f (V (f t)) t := by
    intro t ht
    have hin : t-T∈Icc (-T) T := ⟨by linarith [ht.1],by dsimp [P] at ht; linarith [ht.2]⟩
    have hd := (hder _ hin).scomp t ((hasDerivAt_id t).sub_const T)
    have hv := (hasDerivAt_id t).smul_const v
    have h := hd.sub hv
    change HasDerivAt f (field (z (t-T)-t • angleVector (d/P))-v) t
    rw [field_sub_angle]
    simpa only [f,Function.comp_def,id_eq,one_smul,Pi.sub_def] using h
  have increment : P • v=angleVector d := by
    dsimp [v]
    rw [angle_smul,show P*(d/P)=d by field_simp]
  have hend : f 0=f P := by
    dsimp only [f]
    rw [zero_smul,sub_zero,zero_sub,show P-T=T by dsimp [P];ring,hmatch,increment,add_sub_cancel_right]
  let g := Extension.periodize f hP
  have dg := Extension.periodize_solves V hP hend hfv
  have cg := Extension.periodize_smooth V (field_smooth.sub contDiff_const) hP hend hfv
  let Z := fun s : ℝ => g (s+T)+(s+T) • v
  refine ⟨Z, (cg.comp (contDiff_id.add contDiff_const)).add
    ((contDiff_id.add contDiff_const).smul contDiff_const),?_,?_,?_⟩
  · intro s
    have hd := (dg (s+T)).scomp s ((hasDerivAt_id s).add_const T)
    have hv := ((hasDerivAt_id s).add_const T).smul_const v
    have h := hd.add hv
    have inv : field (Z s)=field (g (s+T)) := by
      unfold Z v
      rw [angle_smul,field_angle_invariant]
    rw [inv]
    simpa only [Z,g,V,Function.comp_def,id_eq,one_smul,sub_add_cancel,Pi.add_def] using h
  · intro s hs
    have hi : s+T∈Icc 0 P := ⟨by linarith [hs.1],by dsimp [P]; linarith [hs.2]⟩
    dsimp only [Z,g]
    rw [Extension.periodize_eq hP hend hi]
    simp [f]
  · intro s
    change g (s+P+T)+(s+P+T) • v=g (s+T)+(s+T) • v+angleVector d
    have ge : g (s+T+P)=g (s+T) := Extension.periodize_periodic f hP (s+T)
    rw [show s+P+T=(s+T)+P by ring,ge,add_smul,increment,add_assoc]

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.extend_matched_segment
