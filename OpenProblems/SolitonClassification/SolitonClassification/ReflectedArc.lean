import SolitonClassification.SupportODE
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

/-! Two reversible seams close a pure dilation orbit with zero total turning.
The fifth state coordinate is the continuous real tangent angle. -/
noncomputable section
namespace ClosedSimilarity.ReflectedArc
open Set Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

abbrev State := Fin 5 → ℝ
abbrev Support := Fin 4 → ℝ

def supportField (z : Support) : Support := ![z 1, -(z 0)^3/2-z 2, -z 0*z 3, 1+z 0*z 2]
def field (z : State) : State := ![z 1, -(z 0)^3/2-z 2, -z 0*z 3, 1+z 0*z 2, z 0]

def atAxis (θ : ℝ) (z : State) : State := ![z 0,-z 1,z 2,-z 3,2*θ-z 4]
def atCenter (z : State) : State := ![-z 0,z 1,-z 2,-z 3,z 4]

theorem field_smooth (n : ℕ∞) : ContDiff ℝ n field := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [field] <;> fun_prop

def Reverses (r : State → State) : Prop :=
  ∀ (z : ℝ → State) (L t : ℝ), HasDerivAt z (field (z (2*L-t))) (2*L-t) →
    HasDerivAt (fun s => r (z (2*L-s))) (field (r (z (2*L-t)))) t

private theorem reversed_deriv {z : ℝ → State} {L t : ℝ}
    (h : HasDerivAt z (field (z (2*L-t))) (2*L-t)) :
    HasDerivAt (fun s => z (2*L-s)) (-(field (z (2*L-t)))) t := by
  have ht : HasDerivAt (fun s : ℝ => 2*L-s) (-1) t := by
    convert! (hasDerivAt_id t).const_sub (2*L) using 1
  simpa only [Function.comp_def,neg_one_smul] using h.scomp t ht

theorem axis_reverses (θ : ℝ) : Reverses (atAxis θ) := by
  intro z L t h
  have hd := hasDerivAt_pi.mp (reversed_deriv h)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [atAxis,field] using hd 0
  · convert! (hd 1).neg using 1; simp [atAxis,field]
  · simpa [atAxis,field] using hd 2
  · convert! (hd 3).neg using 1; simp [atAxis,field]
  · simpa [atAxis,field] using (hd 4).const_sub (2*θ)

theorem center_reverses : Reverses atCenter := by
  intro z L t h
  have hd := hasDerivAt_pi.mp (reversed_deriv h)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! (hd 0).neg using 1; simp [atCenter,field]
  · convert! hd 1 using 1; simp [atCenter,field]; ring
  · convert! (hd 2).neg using 1; simp [atCenter,field]
  · convert! (hd 3).neg using 1; simp [atCenter,field]
  · simpa [atCenter,field] using hd 4

def extendArc (r : State → State) (z : ℝ → State) (L t : ℝ) : State :=
  if t≤L then z t else r (z (2*L-t))

-- Reuse the geometric seam and periodic extension arguments in the repository.
/-- Two genuine derivatives with equal value and derivative glue at the seam. -/
lemma hasDerivAt_join {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {c : ℝ} {v : E}
    (hf : HasDerivAt f v c) (hg : HasDerivAt g v c) (hfg : f c = g c) :
    HasDerivAt (fun t => if t ≤ c then f t else g t) v c := by
  have hl : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) v (Set.Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro t ht
      simp [Set.mem_Iic.mp ht]
    · simp
  have hr : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) v (Set.Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      by_cases h : t ≤ c
      · have : t = c := le_antisymm h ht
        subst t
        simpa using hfg
      · simp [h]
    · simpa using hfg
  have hh := hl.union hr
  simpa only [Set.Iic_union_Ici, hasDerivWithinAt_univ] using hh

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
lemma periodize_derivative_zero {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (h0 : HasDerivAt f (field (f 0)) 0)
    (h1 : HasDerivAt f (field (f T)) T) :
    HasDerivAt (periodize f hT) (field (periodize f hT 0)) 0 := by
  have heq0 : periodize f hT 0 = f 0 := periodize_eq hT hend ⟨le_rfl, hT.le⟩
  have hr : HasDerivWithinAt (periodize f hT) (field (f 0)) (Ici 0) 0 := by
    apply h0.hasDerivWithinAt.congr_of_eventuallyEq _ heq0
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with s hs hsT
    exact periodize_eq hT hend ⟨hs, hsT.le⟩
  have hshift : HasDerivAt (fun s : ℝ => f (s + T)) (field (f 0)) 0 := by
    have hd : HasDerivAt (fun s : ℝ => s + T) 1 0 := (hasDerivAt_id 0).add_const T
    have h1' : HasDerivAt f (field (f 0)) (0 + T) := by simpa [hend] using h1
    convert! h1'.scomp 0 hd using 1
    simp
  have hl : HasDerivWithinAt (periodize f hT) (field (f 0)) (Iic 0) 0 := by
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

lemma periodize_derivative_Ico {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (hf : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt f (field (f t)) t)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivAt (periodize f hT) (field (periodize f hT t)) t := by
  by_cases ht0 : t = 0
  · subst t
    exact periodize_derivative_zero hT hend (hf 0 ⟨le_rfl, hT.le⟩) (hf T ⟨hT.le, le_rfl⟩)
  · have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have heq : periodize f hT =ᶠ[𝓝 t] f := by
      filter_upwards [eventually_gt_nhds hpos, eventually_lt_nhds ht.2] with s hs0 hsT
      exact periodize_eq hT hend ⟨hs0.le, hsT.le⟩
    have hd := (hf t ⟨ht.1, ht.2.le⟩).congr_of_eventuallyEq heq
    simpa [periodize_eq hT hend ⟨ht.1, ht.2.le⟩] using hd

theorem periodize_solves {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (hf : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt f (field (f t)) t) (t : ℝ) :
    HasDerivAt (periodize f hT) (field (periodize f hT t)) t := by
  let n := toIcoDiv hT 0 t
  have hm : t - n • T = toIcoMod hT 0 t := self_sub_toIcoDiv_zsmul hT 0 t
  have hmem : t - n • T ∈ Ico (0:ℝ) T := by
    rw [hm]
    exact toIcoMod_mem_Ico' hT t
  have hd := periodize_derivative_Ico hT hend hf hmem
  have hc : HasDerivAt (fun s : ℝ => s - n • T) 1 t := (hasDerivAt_id t).sub_const _
  have hh := hd.scomp t hc
  simpa only [Function.comp_def, one_smul, periodize_sub_zsmul] using hh

theorem periodize_smooth {f : ℝ → State} {T : ℝ} (hT : 0 < T)
    (hend : f 0 = f T)
    (hf : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt f (field (f t)) t) :
    ContDiff ℝ (⊤ : ℕ∞) (periodize f hT) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (periodize f hT) (Icc (t-1) (t+1)) := by
    apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun (_ : ℝ) z => field z) (u := univ)
    · exact ((field_smooth ⊤).comp contDiff_snd).contDiffOn
    · intro s hs
      exact (periodize_solves hT hend hf s).hasDerivWithinAt
    · intro s hs
      exact mem_univ _
  exact hd.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))

theorem extendArc_deriv {r : State → State} {z : ℝ → State} {L : ℝ}
    (hr : Reverses r) (hz : ∀ t∈Icc 0 L, HasDerivAt z (field (z t)) t)
    (hend : r (z L)=z L) {t : ℝ} (ht : t∈Icc 0 (2*L)) :
    HasDerivAt (extendArc r z L) (field (extendArc r z L t)) t := by
  have hc : 2*L-L=L := by ring
  obtain hlt|he|hgt := lt_trichotomy t L
  · have e : extendArc r z L =ᶠ[𝓝 t] z := by
      filter_upwards [eventually_lt_nhds hlt] with y hy
      simp [extendArc,hy.le]
    simpa only [extendArc,if_pos hlt.le] using (hz t ⟨ht.1,hlt.le⟩).congr_of_eventuallyEq e
  · subst t
    have h0 := hz L ⟨ht.1,le_rfl⟩
    have h1 := hr z L L (by simpa only [hc] using h0)
    rw [hc,hend] at h1
    rw [show field (extendArc r z L L) = field (z L) by simp [extendArc]]
    exact
      (hasDerivAt_join h0 h1 (by simpa only [hc] using hend.symm))
  · have e : extendArc r z L =ᶠ[𝓝 t] (fun y => r (z (2*L-y))) := by
      filter_upwards [eventually_gt_nhds hgt] with y hy
      simp [extendArc,not_le.mpr hy]
    have h1 := hr z L t (hz _ ⟨by linarith only [ht.2],by linarith⟩)
    simpa only [extendArc,if_neg (not_le.mpr hgt)] using h1.congr_of_eventuallyEq e

def withAngle (z : ℝ → Support) (s : ℝ) : State :=
  ![z s 0,z s 1,z s 2,z s 3,∫ x in 0..s,z x 0]

theorem withAngle_deriv {z : ℝ → Support} {L : ℝ} (cz : Continuous z)
    (hz : ∀ t∈Icc 0 L, HasDerivAt z (supportField (z t)) t)
    {t : ℝ} (ht : t∈Icc 0 L) :
    HasDerivAt (withAngle z) (field (withAngle z t)) t := by
  have hd := hasDerivAt_pi.mp (hz t ht)
  have ck : Continuous (fun s => z s 0) := (continuous_apply 0).comp cz
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hd 0
  · exact hd 1
  · exact hd 2
  · exact hd 3
  · exact intervalIntegral.integral_hasDerivAt_right (ck.intervalIntegrable 0 t)
      ck.aestronglyMeasurable.stronglyMeasurableAtFilter ck.continuousAt

/-- A single quarter starting at the center and ending on the symmetry
axis gives a smooth entire periodic support, including a periodic real angle. -/
theorem closed_state_of_quarter {z : ℝ → Support} {L b : ℝ} (hL : 0<L)
    (cz : Continuous z) (hz : ∀ t∈Icc 0 L, HasDerivAt z (supportField (z t)) t)
    (hi : z 0=![0,b,0,0]) (hv : z L 1=0) (hq : z L 3=0) :
    ∃ y : ℝ → State, Function.Periodic y (4*L) ∧ ContDiff ℝ ∞ y ∧
      (∀ t, HasDerivAt y (field (y t)) t) ∧
      (∀ t∈Icc 0 L, y t=withAngle z t) ∧ y 0 1=b ∧ y (2*L) 1= -b := by
  let f := withAngle z
  let r := atAxis (f L 4)
  let g := extendArc r f L
  let w := extendArc atCenter g (2*L)
  have h0 : f 0=![0,b,0,0,0] := by ext i; fin_cases i <;> simp [f,withAngle,hi]
  have haxis : r (f L)=f L := by
    ext i
    fin_cases i <;> simp [r,f,atAxis,withAngle,hv,hq]; ring
  have dg : ∀ t∈Icc 0 (2*L), HasDerivAt g (field (g t)) t := fun _ ht =>
    extendArc_deriv (axis_reverses (f L 4)) (fun t h => withAngle_deriv cz hz h) haxis ht
  have g0 : g 0=f 0 := by simp [g,extendArc,hL.le]
  have ge : g (2*L)= r (f 0) := by simp [g,extendArc,show ¬2*L≤L by linarith]
  have cfix : atCenter (g (2*L))=g (2*L) := by
    rw [ge,h0]
    ext i
    fin_cases i <;> simp [atCenter,r,atAxis]
  have gt : 0<2*L := by linarith
  have d4 : ∀ t∈Icc 0 (4*L), HasDerivAt w (field (w t)) t := by
    intro t ht
    apply extendArc_deriv center_reverses dg cfix
    simpa only [show 2*(2*L)=4*L by ring] using ht
  have w0 : w 0=f 0 := by simp [w,extendArc,gt.le,g0]
  have w4 : w (4*L)=f 0 := by
    simp only [w,extendArc,if_neg (show ¬4*L≤2*L by linarith),
      show 2*(2*L)-4*L=0 by ring,g0,h0]
    ext i
    fin_cases i <;> simp [atCenter]
  have h4 : 0<4*L := by linarith
  have seam := w0.trans w4.symm
  refine ⟨periodize w h4,periodize_periodic _ _,periodize_smooth h4 seam d4,
    periodize_solves h4 seam d4,?_,?_,?_⟩
  · intro t ht
    rw [periodize_eq h4 seam ⟨ht.1,by linarith only [ht.2,hL]⟩]
    simp only [w,g,extendArc,if_pos (show t≤2*L by linarith only [ht.2,hL]),if_pos ht.2,f]
  · rw [periodize_eq h4 seam ⟨le_rfl,h4.le⟩,w0,h0]
    rfl
  · rw [periodize_eq h4 seam ⟨gt.le,by linarith⟩]
    simp [w,extendArc,ge,h0,r,atAxis]

end ClosedSimilarity.ReflectedArc

