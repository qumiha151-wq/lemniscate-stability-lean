import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Set
namespace LengthGrowth.ActualFlow.MacroscopicTurning

/-- Endpoints of a whole component of nonzero curvature, after cutting at a zero. -/
structure Lobe (k : ℝ → ℝ) (a b : ℝ) (I : ℝ × ℝ) : Prop where
  left : a ≤ I.1
  ordered : I.1 < I.2
  right : I.2 ≤ b
  zero_left : k I.1 = 0
  zero_right : k I.2 = 0
  nonzero : ∀ x ∈ Ioo I.1 I.2, k x ≠ 0

private theorem exists_lobe {k : ℝ → ℝ} (hk : Continuous k) {a b x : ℝ}
    (ha : k a = 0) (hb : k b = 0) (hx : x ∈ Icc a b) (hn : k x ≠ 0) :
    ∃ I, Lobe k a b I ∧ x ∈ Ioo I.1 I.2 := by
  let Z := {t : ℝ | k t = 0}
  have cz : IsClosed Z := isClosed_eq hk continuous_const
  obtain ⟨l,hl⟩ := ((isCompact_Icc (a:=a) (b:=x)).inter_right cz).exists_isGreatest
    (show (Icc a x ∩ Z).Nonempty from ⟨a,⟨le_rfl,hx.1⟩,ha⟩)
  obtain ⟨r,hr⟩ := ((isCompact_Icc (a:=x) (b:=b)).inter_right cz).exists_isLeast
    (show (Icc x b ∩ Z).Nonempty from ⟨b,⟨hx.2,le_rfl⟩,hb⟩)
  have lx : l<x := lt_of_le_of_ne hl.1.1.2 (fun e => hn (e ▸ hl.1.2))
  have xr : x<r := lt_of_le_of_ne hr.1.1.1 (fun e => hn (e.symm ▸ hr.1.2))
  refine ⟨(l,r), ⟨hl.1.1.1,lx.trans xr,hr.1.1.2,hl.1.2,hr.1.2,?_⟩,lx,xr⟩
  intro s hs hzero
  by_cases h : s≤x
  · exact (not_le_of_gt hs.1) (hl.2 ⟨⟨hl.1.1.1.trans hs.1.le,h⟩,hzero⟩)
  · exact (not_le_of_gt hs.2) (hr.2 ⟨⟨(le_of_not_ge h),hs.2.le.trans hr.1.1.2⟩,hzero⟩)

private theorem equal_of_overlap {k : ℝ → ℝ} {a b : ℝ} {I J : ℝ × ℝ}
    (i : Lobe k a b I) (j : Lobe k a b J) {x : ℝ}
    (hi : x ∈ Ioo I.1 I.2) (hj : x ∈ Ioo J.1 J.2) : I=J := by
  apply Prod.ext
  · rcases lt_trichotomy I.1 J.1 with h | h | h
    · exact False.elim (i.nonzero _ ⟨h,hj.1.trans hi.2⟩ j.zero_left)
    · exact h
    · exact False.elim (j.nonzero _ ⟨h,hi.1.trans hj.2⟩ i.zero_left)
  · rcases lt_trichotomy I.2 J.2 with h | h | h
    · exact False.elim (j.nonzero _ ⟨hj.1.trans hi.2,h⟩ i.zero_right)
    · exact h
    · exact False.elim (i.nonzero _ ⟨hi.1.trans hj.2,h⟩ j.zero_right)

/-- All points of curvature at least h in magnitude are in finitely many
whole sign components, even for a smooth curve with infinitely many zeros. -/
theorem finite_lobe_cover {k : ℝ → ℝ} (hk : Continuous k) {a b h : ℝ}
    (ha : k a = 0) (hb : k b = 0) (hh : 0<h) :
    ∃ S : Finset (ℝ × ℝ), (∀ I∈S, Lobe k a b I) ∧
      (∀ I∈S,∀ J∈S, I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2)) ∧
      ∀ x∈Icc a b, h≤|k x| → ∃ I∈S, x∈Ioo I.1 I.2 := by
  classical
  let K := Icc a b ∩ {x : ℝ | h≤|k x|}
  have hc : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const hk.abs)
  let A := {I : ℝ × ℝ // Lobe k a b I}
  let U := fun I:A => Ioo I.val.1 I.val.2
  have cover : K ⊆ ⋃ I:A,U I := by
    intro x hx
    have nz : k x ≠ 0 := by
      intro hz
      have hh' := hx.2
      change h≤|k x| at hh'
      rw [hz,abs_zero] at hh'
      linarith
    obtain ⟨I,hi,hxi⟩ := exists_lobe hk ha hb hx.1 nz
    exact mem_iUnion.mpr ⟨⟨I,hi⟩,hxi⟩
  obtain ⟨t,ht⟩ := hc.elim_finite_subcover U (fun _ => isOpen_Ioo) cover
  let S := t.image Subtype.val
  have good (I) (hI:I∈S) : Lobe k a b I := by
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hI
    exact i.property
  refine ⟨S,good,?_,?_⟩
  · intro I hi J hj ne
    exact disjoint_left.mpr (fun _ hxi hxj => ne (equal_of_overlap (good _ hi) (good _ hj) hxi hxj))
  · intro x hx high
    obtain ⟨i,hi⟩:=mem_iUnion.mp (ht (show x∈K from ⟨hx,high⟩))
    obtain ⟨hit,hxi⟩:=mem_iUnion.mp hi
    exact ⟨i.val,Finset.mem_image.mpr ⟨i,hit,rfl⟩,hxi⟩

end LengthGrowth.ActualFlow.MacroscopicTurning
#print axioms LengthGrowth.ActualFlow.MacroscopicTurning.finite_lobe_cover
